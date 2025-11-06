// Copyright (c) 2025 The Raven Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "amount.h"
#include "base58.h"
#include "chain.h"
#include "chainparams.h"
#include "consensus/consensus.h"
#include "consensus/merkle.h"
#include "consensus/params.h"
#include "consensus/validation.h"
#include "core_io.h"
#include "init.h"
#include "validation.h"
#include "miner.h"
#include "net.h"
#include "policy/fees.h"
#include "pow.h"
#include "primitives/block.h"
#include "rpc/blockchain.h"
#include "rpc/mining.h"
#include "rpc/server.h"
#include "script/standard.h"
#include "txmempool.h"
#include "util.h"
#include "utilstrencodings.h"
#include "validationinterface.h"
#include "warnings.h"

#include <memory>
#include <stdint.h>
#include <list>
#include <map>
#include <string>

#include <univalue.h>

// LRU Cache for storing transactions and merkle path data
// Implements a simple LRU cache with maximum size limit
class MerklePathCache {
private:
    // Maximum number of entries to cache
    static const size_t MAX_CACHE_SIZE = 100;

    // List to maintain LRU order (most recent at front)
    // Stores pairs of (key, value)
    std::list<std::pair<uint256, std::vector<CTransactionRef>>> lruList;

    // Map for O(1) lookup: key -> iterator to position in lruList
    std::map<uint256, std::list<std::pair<uint256, std::vector<CTransactionRef>>>::iterator> cacheMap;

public:
    // Get value from cache, moving it to front (most recently used)
    bool get(const uint256& key, std::vector<CTransactionRef>& value) {
        auto it = cacheMap.find(key);
        if (it == cacheMap.end()) {
            return false; // Not found
        }

        // Move to front of LRU list (most recently used)
        lruList.splice(lruList.begin(), lruList, it->second);
        value = it->second->second;
        return true;
    }

    // Put value in cache (or update if exists)
    void put(const uint256& key, const std::vector<CTransactionRef>& value) {
        auto it = cacheMap.find(key);

        if (it != cacheMap.end()) {
            // Key exists, update value and move to front
            it->second->second = value;
            lruList.splice(lruList.begin(), lruList, it->second);
            return;
        }

        // Key doesn't exist, add new entry
        if (cacheMap.size() >= MAX_CACHE_SIZE) {
            // Evict least recently used (back of list)
            auto last = lruList.back();
            cacheMap.erase(last.first);
            lruList.pop_back();
        }

        // Add to front of list
        lruList.push_front(std::make_pair(key, value));
        cacheMap[key] = lruList.begin();
    }

    size_t size() const {
        return cacheMap.size();
    }
};

static MerklePathCache merkleCache;
static CCriticalSection cs_merkleCache;

// Build merkle branch hashes for the coinbase transaction (position 0)
// Returns the merkle branches needed to compute merkle root from coinbase hash
std::vector<uint256> BuildMerkleBranchesForCoinbase(const CBlock& block)
{
    // Use existing BlockMerkleBranch function with position 0 for coinbase
    return BlockMerkleBranch(block, 0);
}

// Compute hash of merkle path for cache lookup
uint256 ComputeMerklePathHash(const std::vector<uint256>& merkleBranch)
{
    CHashWriter ss(SER_GETHASH, 0);
    for (const auto& hash : merkleBranch) {
        ss << hash;
    }
    return ss.GetHash();
}

UniValue getshortblocktemplate(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 0)
        throw std::runtime_error(
            "getshortblocktemplate\n"
            "\nReturns a compact block template for mining.\n"
            "This is a lightweight alternative to getblocktemplate that returns only:\n"
            "- Header bytes (with zero merkle root and nonce)\n"
            "- Coinbase value (block subsidy + fees)\n"
            "- Merkle branches for computing merkle root from coinbase\n"
            "- Block height\n"
            "\nThis format is suitable for mining pools that construct their own coinbase transactions.\n"
            "\nResult:\n"
            "{\n"
            "  \"headerbytes\" : \"hex\",     (string) Serialized block header with zero merkle root and nonce\n"
            "  \"coinbasevalue\" : n,        (numeric) Total coinbase value in satoshis (subsidy + fees)\n"
            "  \"height\" : n,               (numeric) Block height\n"
            "  \"merklepath\" : [            (array) Merkle branch hashes (hex-encoded)\n"
            "    \"hash\",                    (string) Merkle branch hash\n"
            "    ...\n"
            "  ]\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("getshortblocktemplate", "")
            + HelpExampleRpc("getshortblocktemplate", "")
        );

    LOCK(cs_main);

    // Check node is ready
    if (!g_connman)
        throw JSONRPCError(RPC_CLIENT_P2P_DISABLED, "Error: Peer-to-peer functionality missing or disabled");

    if (g_connman->GetNodeCount(CConnman::CONNECTIONS_ALL) == 0 && !gArgs.GetBoolArg("-bypassdownload", false))
        throw JSONRPCError(RPC_CLIENT_NOT_CONNECTED, "Ravencoin is not connected!");

    if (IsInitialBlockDownload() && !gArgs.GetBoolArg("-bypassdownload", false))
        throw JSONRPCError(RPC_CLIENT_IN_INITIAL_DOWNLOAD, "Ravencoin is downloading blocks...");

    // Get mining address from config
    CScript scriptPubKey;
    std::string address = gArgs.GetArg("-miningaddress", "");
    if (!address.empty()) {
        CTxDestination dest = DecodeDestination(address);
        if (IsValidDestination(dest)) {
            scriptPubKey = GetScriptForDestination(dest);
        } else {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "-miningaddress is not a valid address");
        }
    } else {
        scriptPubKey = CScript() << OP_TRUE;
    }

    // Create new block
    bool fSupportsSegwit = GetParams().GetConsensus().nSegwitEnabled;
    std::unique_ptr<CBlockTemplate> pblocktemplate = BlockAssembler(GetParams()).CreateNewBlock(scriptPubKey, fSupportsSegwit);
    if (!pblocktemplate)
        throw JSONRPCError(RPC_OUT_OF_MEMORY, "Out of memory");

    CBlock* pblock = &pblocktemplate->block;
    const Consensus::Params& consensusParams = GetParams().GetConsensus();

    // Update nTime
    CBlockIndex* pindexPrev = chainActive.Tip();
    UpdateTime(pblock, consensusParams, pindexPrev);

    // Save original values
    uint256 originalMerkleRoot = pblock->hashMerkleRoot;
    uint32_t originalHeight = pblock->nHeight;
    uint64_t originalNonce64 = pblock->nNonce64;
    uint256 originalMixHash = pblock->mix_hash;

    // Zero out merkle root and KAWPOW fields for template
    // Note: For KAWPOW blocks, nHeight is serialized where nNonce would be in Bitcoin
    pblock->hashMerkleRoot.SetNull();
    pblock->nHeight = 0;  // This gets serialized as bytes 76-79 for KAWPOW blocks
    pblock->nNonce64 = 0;
    pblock->mix_hash.SetNull();

    // Serialize header to bytes
    CDataStream ssHeader(SER_NETWORK, PROTOCOL_VERSION);
    ssHeader << pblock->GetBlockHeader();
    std::string headerHex = HexStr(ssHeader.begin(), ssHeader.end());

    // Restore original values (in case block template is cached/reused)
    pblock->hashMerkleRoot = originalMerkleRoot;
    pblock->nHeight = originalHeight;
    pblock->nNonce64 = originalNonce64;
    pblock->mix_hash = originalMixHash;

    // Calculate coinbase value
    CAmount coinbaseValue = pblock->vtx[0]->GetValueOut();

    // Build merkle branches for coinbase (position 0)
    std::vector<uint256> merkleBranch = BuildMerkleBranchesForCoinbase(*pblock);

    UniValue merklePath(UniValue::VARR);
    for (const auto& hash : merkleBranch) {
        // Return merkle branches in little-endian (internal storage order)
        // NOT reversed like GetHex() does
        merklePath.push_back(HexStr(hash.begin(), hash.end()));
    }

    // Cache transactions (excluding coinbase) for later reconstruction
    {
        LOCK(cs_merkleCache);

        // Compute merkle path hash for cache key
        uint256 merklePathHash = ComputeMerklePathHash(merkleBranch);

        // Store transactions excluding coinbase
        std::vector<CTransactionRef> cachedTxs;
        for (size_t i = 1; i < pblock->vtx.size(); i++) {
            cachedTxs.push_back(pblock->vtx[i]);
        }

        // Store in LRU cache (automatically evicts oldest if size > 100)
        merkleCache.put(merklePathHash, cachedTxs);
    }

    // Build result
    UniValue result(UniValue::VOBJ);
    result.push_back(Pair("headerbytes", headerHex));
    result.push_back(Pair("coinbasevalue", coinbaseValue));
    result.push_back(Pair("height", (int64_t)(pindexPrev->nHeight + 1)));
    result.push_back(Pair("merklepath", merklePath));

    return result;
}

UniValue submitshortblocktemplate(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 3)
        throw std::runtime_error(
            "submitshortblocktemplate \"headerhex\" \"coinbasehex\" [\"merklepath\",...]\n"
            "\nReconstructs and submits a block from short block template format.\n"
            "\nArguments:\n"
            "1. \"headerhex\"       (string, required) Hex-encoded block header with filled merkle root and nonce\n"
            "2. \"coinbasehex\"     (string, required) Hex-encoded coinbase transaction\n"
            "3. \"merklepath\"      (array, required) Merkle branch hashes used to look up cached transactions\n"
            "     [\n"
            "       \"hash\",        (string) Merkle branch hash\n"
            "       ...\n"
            "     ]\n"
            "\nResult:\n"
            "null on success, or a string error message on failure\n"
            "\nExamples:\n"
            + HelpExampleCli("submitshortblocktemplate", "\"headerhex\" \"coinbasehex\" \"[\\\"hash1\\\",\\\"hash2\\\"]\"")
            + HelpExampleRpc("submitshortblocktemplate", "\"headerhex\", \"coinbasehex\", [\"hash1\",\"hash2\"]")
        );

    // Parse header hex - manually deserialize as KAWPOW format (120 bytes)
    std::string headerHex = request.params[0].get_str();
    if (!IsHex(headerHex))
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Header hex is not valid hex");

    std::vector<unsigned char> headerData = ParseHex(headerHex);

    // KAWPOW header must be exactly 120 bytes
    if (headerData.size() != 120) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR,
            strprintf("Invalid KAWPOW header size: expected 120 bytes, got %d bytes", headerData.size()));
    }

    // Deserialize header using standard Ravencoin deserialization
    CDataStream ssHeader(headerData, SER_NETWORK, PROTOCOL_VERSION);
    CBlockHeader header;
    try {
        ssHeader >> header;
    } catch (const std::exception& e) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, strprintf("Failed to deserialize header: %s", e.what()));
    }

    // Parse coinbase hex
    std::string coinbaseHex = request.params[1].get_str();
    if (!IsHex(coinbaseHex))
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Coinbase hex is not valid hex");

    CMutableTransaction coinbaseTx;
    if (!DecodeHexTx(coinbaseTx, coinbaseHex))
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Failed to decode coinbase transaction");

    // Parse merkle path
    // NOTE: Merkle branches are now in little-endian format (internal storage order)
    // We need to parse them as raw bytes, NOT using SetHex() which expects big-endian
    UniValue merklePathArray = request.params[2].get_array();
    std::vector<uint256> merkleBranch;
    for (unsigned int i = 0; i < merklePathArray.size(); i++) {
        std::string hexStr = merklePathArray[i].get_str();
        if (!IsHex(hexStr) || hexStr.length() != 64) {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR,
                strprintf("Invalid merkle branch hex at index %d", i));
        }

        std::vector<unsigned char> hashBytes = ParseHex(hexStr);
        uint256 hash;
        if (hashBytes.size() != 32) {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR,
                strprintf("Invalid merkle branch size at index %d", i));
        }
        memcpy(hash.begin(), hashBytes.data(), 32);
        merkleBranch.push_back(hash);
    }

    // Look up cached transactions (LRU cache keeps entries for resubmission)
    uint256 merklePathHash = ComputeMerklePathHash(merkleBranch);
    std::vector<CTransactionRef> cachedTxs;

    {
        LOCK(cs_merkleCache);
        if (!merkleCache.get(merklePathHash, cachedTxs)) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Merkle path not found in cache. Template may have been evicted.");
        }
        // Note: Entry remains in cache for potential resubmission
    }

    // Reconstruct full block
    CBlock block;
    block.nVersion = header.nVersion;
    block.hashPrevBlock = header.hashPrevBlock;
    block.hashMerkleRoot = header.hashMerkleRoot;
    block.nTime = header.nTime;
    block.nBits = header.nBits;
    block.nNonce = header.nNonce;
    block.nHeight = header.nHeight;
    block.nNonce64 = header.nNonce64;
    block.mix_hash = header.mix_hash;

    // Add coinbase transaction
    block.vtx.push_back(MakeTransactionRef(coinbaseTx));

    // Add cached transactions
    for (const auto& tx : cachedTxs) {
        block.vtx.push_back(tx);
    }

    // Verify merkle root but don't reject - let ProcessNewBlock validate it
    uint256 computedMerkleRoot = BlockMerkleRoot(block);
    if (block.hashMerkleRoot != computedMerkleRoot) {
        LogPrintf("submitshortblocktemplate: WARNING - Merkle root mismatch - hash=%s, expected=%s, got=%s, coinbase=%s, num_txs=%d (submitting anyway for node validation)\n",
                  block.GetHash().GetHex(), computedMerkleRoot.GetHex(), block.hashMerkleRoot.GetHex(),
                  coinbaseTx.GetHash().GetHex(), block.vtx.size());
    } else {
        LogPrintf("submitshortblocktemplate: Merkle root validation passed - merkle_root=%s\n",
                  computedMerkleRoot.GetHex());
    }

    // Check mix_hash validity for KAWPOW blocks (debugging check)
    if (block.nTime >= nKAWPOWActivationTime) {
        uint256 computedMixHash;
        uint256 blockHash = block.GetHashFull(computedMixHash);

        LogPrintf("submitshortblocktemplate: Mix hash debug - block_hash=%s, computed_mix=%s, submitted_mix=%s\n",
                  blockHash.GetHex(), computedMixHash.GetHex(), block.mix_hash.GetHex());

        if (computedMixHash != block.mix_hash) {
            LogPrintf("submitshortblocktemplate: WARNING - Mix hash MISMATCH (submitting anyway for node validation)\n");
        } else {
            LogPrintf("submitshortblocktemplate: Mix hash validation PASSED\n");
        }
    }

    // Submit block
    std::shared_ptr<const CBlock> shared_pblock = std::make_shared<const CBlock>(block);
    bool fNewBlock = false;
    if (!ProcessNewBlock(GetParams(), shared_pblock, true, &fNewBlock)) {
        LogPrintf("submitshortblocktemplate: Block rejected - hash=%s\n", block.GetHash().GetHex());
        return "rejected";
    }

    LogPrintf("submitshortblocktemplate: Block submitted successfully - hash=%s, height=%d, new_block=%d\n",
              block.GetHash().GetHex(), block.nHeight, fNewBlock);

    return NullUniValue;
}
