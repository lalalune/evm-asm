/-
  EvmAsm.Codegen.Programs

  Registry of programs the codegen tool knows how to emit, each as a
  `BuildUnit` (verified body + optional wrapping).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Evm64.Add.Program
import EvmAsm.Evm64.AddMod.Program
import EvmAsm.Evm64.And.Program
import EvmAsm.Evm64.Byte.Program
import EvmAsm.Evm64.DivMod.Callable
import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Evm64.Dup.Program
import EvmAsm.Evm64.Eq.Program
-- EXP wrapper is parametric over caller-saved registers (x6, x16)
-- that mul_callable clobbers; deferred until upstream lands a
-- fully callee-saved variant. import re-added when wiring lands.
-- import EvmAsm.Evm64.Exp.Program
import EvmAsm.Evm64.Gt.Program
import EvmAsm.Evm64.IsZero.Program
import EvmAsm.Evm64.Lt.Program
import EvmAsm.Evm64.MLoad.Program
import EvmAsm.Evm64.MStore.Program
import EvmAsm.Evm64.MStore8.Program
-- import EvmAsm.Evm64.Multiply.Callable -- only needed by EXP (deferred)
import EvmAsm.Evm64.Multiply.Program
import EvmAsm.Evm64.Not.Program
import EvmAsm.Evm64.Or.Program
import EvmAsm.Evm64.Pop.Program
import EvmAsm.Evm64.Push.Program
import EvmAsm.Evm64.SDiv.Program
import EvmAsm.Evm64.SMod.Program
import EvmAsm.Evm64.Sgt.Program
import EvmAsm.Evm64.Shift.Program
import EvmAsm.Evm64.SignExtend.Program
import EvmAsm.Evm64.Slt.Program
import EvmAsm.Evm64.Sub.Program
import EvmAsm.Evm64.Swap.Program
import EvmAsm.Evm64.Xor.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Dispatch
import EvmAsm.Stateless.Entry
import EvmAsm.Stateless.SSZ.HashTreeRoot.Program

import EvmAsm.Codegen.Programs.Evm
import EvmAsm.Codegen.Programs.ExpProperty
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HashProbes
import EvmAsm.Codegen.Programs.StatelessGuestData
import EvmAsm.Codegen.Programs.StatelessGuestEpilogue
import EvmAsm.Codegen.Programs.IntrinsicGas
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.MptEncode
import EvmAsm.Codegen.Programs.MptInternal
import EvmAsm.Codegen.Programs.MptNibbles
import EvmAsm.Codegen.Programs.Ssz
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.TxDecode
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.Bloom
import EvmAsm.Codegen.Programs.Block
import EvmAsm.Codegen.Programs.BlockBody
import EvmAsm.Codegen.Programs.BlockEmpty
import EvmAsm.Codegen.Programs.BlockValidate
import EvmAsm.Codegen.Programs.Account
import EvmAsm.Codegen.Programs.AccountFields
import EvmAsm.Codegen.Programs.BlockRoots
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.HeaderBaseFee
import EvmAsm.Codegen.Programs.HeaderDecode
import EvmAsm.Codegen.Programs.HeaderChain
import EvmAsm.Codegen.Programs.Chain
import EvmAsm.Codegen.Programs.ChainAggregator
import EvmAsm.Codegen.Programs.ChainBasefee
import EvmAsm.Codegen.Programs.ChainBlobCount
import EvmAsm.Codegen.Programs.ChainExcessBlobGas
import EvmAsm.Codegen.Programs.ChainTimestamp
import EvmAsm.Codegen.Programs.ChainEndpoints
import EvmAsm.Codegen.Programs.ChainValidate
import EvmAsm.Codegen.Programs.ChainValidateBlob
import EvmAsm.Codegen.Programs.ChainValidatePostMerge
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.BlockHashPredicates
import EvmAsm.Codegen.Programs.HeadersKeccak
import EvmAsm.Codegen.Programs.HeaderU64
import EvmAsm.Codegen.Programs.Receipt
import EvmAsm.Codegen.Programs.State
import EvmAsm.Codegen.Programs.StateCompose
import EvmAsm.Codegen.Programs.StatePredicates
import EvmAsm.Codegen.Programs.StateBalanceProof
import EvmAsm.Codegen.Programs.EvmOpcodes
import EvmAsm.Codegen.Programs.EvmOpcodesStorageRoot
import EvmAsm.Codegen.Programs.EvmOpcodesExtcodecopy
import EvmAsm.Codegen.Programs.StorageCompose
import EvmAsm.Codegen.Programs.EvmCodes
import EvmAsm.Codegen.Programs.TxRoot
import EvmAsm.Codegen.Programs.TxSignature
import EvmAsm.Codegen.Programs.TxSigningHash
import EvmAsm.Codegen.Programs.Withdrawal
import EvmAsm.Codegen.Programs.Address

namespace EvmAsm.Codegen

open EvmAsm.Rv64


/-! Misc programs moved to submodules:
    - K21..K26 MPT helpers -> Programs/Mpt.lean
    - K34/K35/K36/K37 + K121/K120/K123 rlp/account extractors + legacy decoders -> Programs/Tx.lean
    - K64 blob_gas_used_from_versioned_hashes -> Programs/Tx.lean
    - K138/K139 signature extractors -> Programs/TxSignature.lean -/


/-! More misc programs moved to submodules — see commit history and
    the per-PR header comments inside the destination files for details. -/


/-! ## MPT branch helpers K117 / K118 — moved to `Programs/Mpt.lean` (file-size hard cap). -/

/-! ## stateless_guest body — PR-K5 keccak hash field

    Replaces the zero-stub `new_payload_request_root` field in
    `Stateless.Entry.run_stateless_guest`'s SSZ output with the
    keccak256 of the entire SSZ-input byte string the host
    streamed in via `ziskemu -i`. Concretely:

    - Body: the unchanged `Stateless.Entry.run_stateless_guest`
      Program. It writes:
        bytes  0..32 : zero hash (placeholder)
        byte      32 : successful_validation (PR4/PR5 derived)
        bytes 33..41 : chain_id (PR3 from-decode)
        bytes 41..48 : zero gap
        bytes 48..56 : header_count diagnostic (PR6 from-decode)
    - Epilogue (raw asm): set up sp, load (data ptr, len) from
      INPUT_ADDR + (16, 8), set output = OUTPUT_ADDR + 0, and
      `jal ra, zkvm_keccak256`. The function overwrites
      OUTPUT[0..32] with keccak256(input bytes), clobbering the
      zero stub.

    The host-side `compute_new_payload_request_root` per the spec
    is SSZ `hash_tree_root` (SHA-256), not Keccak. PR-K5 stamps a
    *content-dependent* hash there so the test harness has a
    non-trivial value to verify and the keccak bridge is wired
    into the encoder pipeline end-to-end. Once PR-S series lands,
    the SHA-256 hash_tree_root replaces this keccak. -/
-- `statelessGuestValidatorPipeline` and `statelessGuestEpilogue`
-- live in `EvmAsm/Codegen/Programs/StatelessGuestEpilogue.lean`
-- (carved out here to satisfy the file-size hard cap; see
-- PR #5870 and PR #5900 for the established submodule pattern).

-- `statelessGuestDataSection` lives in
-- `EvmAsm/Codegen/Programs/StatelessGuestData.lean` (carved
-- out here to satisfy the file-size hard cap; see PR #5870
-- and PR #5900 for the established submodule pattern).

def statelessGuestUnit : BuildUnit := {
  body        := EvmAsm.Stateless.run_stateless_guest
  epilogueAsm := statelessGuestEpilogue
  dataAsm     := statelessGuestDataSection
}

/-! ## registry -/

/-- Second half of the program lookup, split off `lookupProgram` to
    keep the C-emitted match below clang's default 256 bracket-nesting
    limit. New PRs append arms here, not to `lookupProgram`. -/
def lookupProgramTail : String → Option BuildUnit
  | "zisk_bloom_eq" => some ziskBloomEqProbeUnit
  | "zisk_rlp_encode_u64" => some ziskRlpEncodeU64ProbeUnit
  | "zisk_receipt_encode" => some ziskReceiptEncodeProbeUnit
  | "zisk_single_leaf_trie_root" => some ziskSingleLeafTrieRootProbeUnit
  | "zisk_mpt_leaf_node_encode" => some ziskMptLeafNodeEncodeProbeUnit
  | "zisk_mpt_node_slot_encode" => some ziskMptNodeSlotEncodeProbeUnit
  | "zisk_mpt_extension_node_encode" => some ziskMptExtensionNodeEncodeProbeUnit
  | "zisk_mpt_branch_node_encode" => some ziskMptBranchNodeEncodeProbeUnit
  | "zisk_nibbles_common_prefix_len" => some ziskNibblesCommonPrefixLenProbeUnit
  | "zisk_mpt_branch_payload_two_slots" => some ziskMptBranchPayloadTwoSlotsProbeUnit
  | "zisk_mpt_leaf_node_encode_from_nibbles" => some ziskMptLeafNodeEncodeFromNibblesProbeUnit
  | "zisk_mpt_branch_node_keccak" => some ziskMptBranchNodeKeccakProbeUnit
  | "zisk_mpt_two_leaf_root_indexed" => some ziskMptTwoLeafRootIndexedProbeUnit
  | "zisk_mpt_one_leaf_root_indexed" => some ziskMptOneLeafRootIndexedProbeUnit
  | "zisk_block_validate_transactions_root_one_tx" => some ziskBlockValidateTransactionsRootOneTxProbeUnit
  | "zisk_block_validate_withdrawals_root_one_w" => some ziskBlockValidateWithdrawalsRootOneWProbeUnit
  | "zisk_block_validate_withdrawals_root_two_w" => some ziskBlockValidateWithdrawalsRootTwoWProbeUnit
  | "zisk_block_validate_receipts_root_one_receipt" => some ziskBlockValidateReceiptsRootOneReceiptProbeUnit
  | "zisk_block_validate_receipts_root_two_receipts" => some ziskBlockValidateReceiptsRootTwoReceiptsProbeUnit
  | "zisk_block_validate_transactions_root_two_tx" => some ziskBlockValidateTransactionsRootTwoTxProbeUnit
  | "zisk_block_hash_from_header" => some ziskBlockHashFromHeaderProbeUnit
  | "zisk_validate_parent_hash_link" => some ziskValidateParentHashLinkProbeUnit
  | "zisk_validate_header_pair" => some ziskValidateHeaderPairProbeUnit
  | "zisk_validate_header_chain" => some ziskValidateHeaderChainProbeUnit
  | "zisk_block_hash_array_from_chain" => some ziskBlockHashArrayFromChainProbeUnit
  | "zisk_validate_block_hash_chain_match" => some ziskValidateBlockHashChainMatchProbeUnit
  | "zisk_chain_compute_total_gas_used" => some ziskChainComputeTotalGasUsedProbeUnit
  | "zisk_chain_extract_number_range" => some ziskChainExtractNumberRangeProbeUnit
  | "zisk_header_extract_basefee" => some ziskHeaderExtractBasefeeProbeUnit
  | "zisk_chain_extract_basefee_range" => some ziskChainExtractBasefeeRangeProbeUnit
  | "zisk_chain_block_hashes_commitment" => some ziskChainBlockHashesCommitmentProbeUnit
  | "zisk_header_extract_state_root" => some ziskHeaderExtractStateRootProbeUnit
  | "zisk_validate_state_root_against_witness_node" => some ziskValidateStateRootAgainstWitnessNodeProbeUnit
  | "zisk_header_extract_parent_hash" => some ziskHeaderExtractParentHashProbeUnit
  | "zisk_header_extract_receipts_root" => some ziskHeaderExtractReceiptsRootProbeUnit
  | "zisk_header_extract_transactions_root" => some ziskHeaderExtractTransactionsRootProbeUnit
  | "zisk_header_extract_withdrawals_root" => some ziskHeaderExtractWithdrawalsRootProbeUnit
  | "zisk_header_extract_ommers_hash" => some ziskHeaderExtractOmmersHashProbeUnit
  | "zisk_header_extract_prev_randao" => some ziskHeaderExtractPrevRandaoProbeUnit
  | "zisk_header_extract_beneficiary" => some ziskHeaderExtractBeneficiaryProbeUnit
  | "zisk_block_hash_matches" => some ziskBlockHashMatchesProbeUnit
  | "zisk_header_extract_gas_used" => some ziskHeaderExtractGasUsedProbeUnit
  | "zisk_header_extract_gas_limit" => some ziskHeaderExtractGasLimitProbeUnit
  | "zisk_block_validate_block_hash_pair" => some ziskBlockValidateBlockHashPairProbeUnit
  | "zisk_block_hash_and_extract_number" => some ziskBlockHashAndExtractNumberProbeUnit
  | "zisk_blockhash_from_witness_headers" => some ziskBlockhashFromWitnessHeadersProbeUnit
  | "zisk_witness_headers_chain_validate" => some ziskWitnessHeadersChainValidateProbeUnit
  | "zisk_header_compute_summary_struct" => some ziskHeaderComputeSummaryStructProbeUnit
  | "zisk_header_extract_difficulty" => some ziskHeaderExtractDifficultyProbeUnit
  | "zisk_header_extract_extra_data" => some ziskHeaderExtractExtraDataProbeUnit
  | "zisk_header_extract_nonce" => some ziskHeaderExtractNonceProbeUnit
  | "zisk_header_validate_nonce_zero" => some ziskHeaderValidateNonceZeroProbeUnit
  | "zisk_header_validate_difficulty_zero" => some ziskHeaderValidateDifficultyZeroProbeUnit
  | "zisk_validate_header_post_merge_zeros" => some ziskValidateHeaderPostMergeZerosProbeUnit
  | "zisk_chain_validate_post_merge_zeros" => some ziskChainValidatePostMergeZerosProbeUnit
  | "zisk_chain_validate_full" => some ziskChainValidateFullProbeUnit
  | "zisk_chain_validate_increasing_timestamps" => some ziskChainValidateIncreasingTimestampsProbeUnit
  | "zisk_chain_validate_consecutive_numbers" => some ziskChainValidateConsecutiveNumbersProbeUnit
  | "zisk_chain_compute_total_blob_gas" => some ziskChainComputeTotalBlobGasProbeUnit
  | "zisk_header_extract_timestamp" => some ziskHeaderExtractTimestampProbeUnit
  | "zisk_header_extract_number" => some ziskHeaderExtractNumberProbeUnit
  | "zisk_account_validate_code_hash_empty" => some ziskAccountValidateCodeHashEmptyProbeUnit
  | "zisk_account_validate_storage_root_empty" => some ziskAccountValidateStorageRootEmptyProbeUnit
  | "zisk_chain_compute_max_gas_used" => some ziskChainComputeMaxGasUsedProbeUnit
  | "zisk_chain_compute_max_blob_gas_used" => some ziskChainComputeMaxBlobGasUsedProbeUnit
  | "zisk_chain_compute_min_gas_used" => some ziskChainComputeMinGasUsedProbeUnit
  | "zisk_chain_extract_timestamp_range" => some ziskChainExtractTimestampRangeProbeUnit
  | "zisk_chain_validate_gas_used_under_limit" => some ziskChainValidateGasUsedUnderLimitProbeUnit
  | "zisk_header_extract_blob_gas_used" => some ziskHeaderExtractBlobGasUsedProbeUnit
  | "zisk_account_validate_nonce_zero" => some ziskAccountValidateNonceZeroProbeUnit
  | "zisk_chain_compute_min_blob_gas_used" => some ziskChainComputeMinBlobGasUsedProbeUnit
  | "zisk_header_extract_excess_blob_gas" => some ziskHeaderExtractExcessBlobGasProbeUnit
  | "zisk_chain_extract_gas_used_range" => some ziskChainExtractGasUsedRangeProbeUnit
  | "zisk_chain_extract_blob_gas_used_range" => some ziskChainExtractBlobGasUsedRangeProbeUnit
  | "zisk_chain_extract_basefee_first_last" => some ziskChainExtractBasefeeFirstLastProbeUnit
  | "zisk_chain_compute_total_blob_count" => some ziskChainComputeTotalBlobCountProbeUnit
  | "zisk_chain_compute_total_basefee" => some ziskChainComputeTotalBasefeeProbeUnit
  | "zisk_chain_compute_max_basefee" => some ziskChainComputeMaxBasefeeProbeUnit
  | "zisk_chain_compute_min_basefee" => some ziskChainComputeMinBasefeeProbeUnit
  | "zisk_chain_compute_max_gas_limit" => some ziskChainComputeMaxGasLimitProbeUnit
  | "zisk_chain_compute_min_gas_limit" => some ziskChainComputeMinGasLimitProbeUnit
  | "zisk_chain_compute_total_gas_limit" => some ziskChainComputeTotalGasLimitProbeUnit
  | "zisk_chain_extract_gas_limit_first_last" => some ziskChainExtractGasLimitFirstLastProbeUnit
  | "zisk_chain_validate_constant_gas_limit" => some ziskChainValidateConstantGasLimitProbeUnit
  | "zisk_chain_validate_basefee_non_decreasing" => some ziskChainValidateBasefeeNonDecreasingProbeUnit
  | "zisk_chain_validate_basefee_non_increasing" => some ziskChainValidateBasefeeNonIncreasingProbeUnit
  | "zisk_chain_validate_gas_limit_non_decreasing" => some ziskChainValidateGasLimitNonDecreasingProbeUnit
  | "zisk_chain_validate_gas_limit_non_increasing" => some ziskChainValidateGasLimitNonIncreasingProbeUnit
  | "zisk_chain_extract_excess_blob_gas_first_last" => some ziskChainExtractExcessBlobGasFirstLastProbeUnit
  | "zisk_chain_compute_max_excess_blob_gas" => some ziskChainComputeMaxExcessBlobGasProbeUnit
  | "zisk_chain_compute_min_excess_blob_gas" => some ziskChainComputeMinExcessBlobGasProbeUnit
  | "zisk_chain_validate_excess_blob_gas_non_decreasing" => some ziskChainValidateExcessBlobGasNonDecreasingProbeUnit
  | "zisk_chain_validate_excess_blob_gas_non_increasing" => some ziskChainValidateExcessBlobGasNonIncreasingProbeUnit
  | "zisk_chain_compute_total_excess_blob_gas" => some ziskChainComputeTotalExcessBlobGasProbeUnit
  | "zisk_chain_validate_blob_gas_used_under_max" => some ziskChainValidateBlobGasUsedUnderMaxProbeUnit
  | "zisk_chain_validate_blob_gas_used_multiple" => some ziskChainValidateBlobGasUsedMultipleProbeUnit
  | "zisk_chain_compute_max_timestamp_gap" => some ziskChainComputeMaxTimestampGapProbeUnit
  | "zisk_chain_compute_min_timestamp_gap" => some ziskChainComputeMinTimestampGapProbeUnit
  | "zisk_header_extract_parent_beacon_block_root" => some ziskHeaderExtractParentBeaconBlockRootProbeUnit
  | "zisk_chain_extract_first_last_parent_beacon_block_root" => some ziskChainExtractFirstLastParentBeaconBlockRootProbeUnit
  | "zisk_header_extract_requests_hash" => some ziskHeaderExtractRequestsHashProbeUnit
  | "zisk_chain_extract_first_last_requests_hash" => some ziskChainExtractFirstLastRequestsHashProbeUnit
  | "zisk_chain_compute_max_blob_count" => some ziskChainComputeMaxBlobCountProbeUnit
  | "zisk_chain_compute_min_blob_count" => some ziskChainComputeMinBlobCountProbeUnit
  | "zisk_chain_validate_difficulty_zero" => some ziskChainValidateDifficultyZeroProbeUnit
  | "zisk_chain_validate_nonce_zero" => some ziskChainValidateNonceZeroProbeUnit
  | "zisk_chain_validate_ommers_hash_empty" => some ziskChainValidateOmmersHashEmptyProbeUnit
  | "zisk_chain_validate_post_merge_full" => some ziskChainValidatePostMergeFullProbeUnit
  | "zisk_chain_validate_extra_data_length" => some ziskChainValidateExtraDataLengthProbeUnit
  | "zisk_chain_compute_max_extra_data_length" => some ziskChainComputeMaxExtraDataLengthProbeUnit
  | "zisk_chain_extract_first_last_state_root" => some ziskChainExtractFirstLastStateRootProbeUnit
  | "zisk_chain_extract_first_last_block_hash" => some ziskChainExtractFirstLastBlockHashProbeUnit
  | "zisk_chain_extract_first_last_receipts_root" => some ziskChainExtractFirstLastReceiptsRootProbeUnit
  | "zisk_chain_extract_first_last_transactions_root" => some ziskChainExtractFirstLastTransactionsRootProbeUnit
  | "zisk_chain_extract_first_last_withdrawals_root" => some ziskChainExtractFirstLastWithdrawalsRootProbeUnit
  | "zisk_chain_extract_first_last_prev_randao" => some ziskChainExtractFirstLastPrevRandaoProbeUnit
  | "zisk_chain_extract_first_last_beneficiary" => some ziskChainExtractFirstLastBeneficiaryProbeUnit
  | "zisk_chain_extract_first_last_ommers_hash" => some ziskChainExtractFirstLastOmmersHashProbeUnit
  | "zisk_chain_validate_no_blob_txs" => some ziskChainValidateNoBlobTxsProbeUnit
  | "zisk_account_validate_balance_zero" => some ziskAccountValidateBalanceZeroProbeUnit
  | "zisk_block_validate_2tx_full" => some ziskBlockValidate2txFullProbeUnit
  | "zisk_block_body_extract_2tx" => some ziskBlockBodyExtract2txProbeUnit
  | "zisk_block_validate_2tx_full_with_body" => some ziskBlockValidate2txFullWithBodyProbeUnit
  | "zisk_block_validate_empty_ommers_hash" => some ziskBlockValidateEmptyOmmersHashProbeUnit
  | "zisk_block_validate_no_withdrawals_pair" => some ziskBlockValidateNoWithdrawalsPairProbeUnit
  | "zisk_block_body_extract_1tx" => some ziskBlockBodyExtract1txProbeUnit
  | "zisk_block_validate_1tx_full" => some ziskBlockValidate1txFullProbeUnit
  | "zisk_block_validate_1tx_full_with_body" => some ziskBlockValidate1txFullWithBodyProbeUnit
  | "zisk_block_validate_empty_receipts_root" => some ziskBlockValidateEmptyReceiptsRootProbeUnit
  | "zisk_block_validate_empty_block" => some ziskBlockValidateEmptyBlockProbeUnit
  | "zisk_validate_empty_block_with_parent" => some ziskValidateEmptyBlockWithParentProbeUnit
  | "zisk_validate_empty_block_chain" => some ziskValidateEmptyBlockChainProbeUnit
  | "zisk_block_body_extract_tx_count" => some ziskBlockBodyExtractTxCountProbeUnit
  | "zisk_block_body_extract_withdrawal_count" => some ziskBlockBodyExtractWithdrawalCountProbeUnit
  | "zisk_block_body_summary" => some ziskBlockBodySummaryProbeUnit
  | "zisk_block_body_validate_empty" => some ziskBlockBodyValidateEmptyProbeUnit
  | "zisk_chain_body_total_tx_count" => some ziskChainBodyTotalTxCountProbeUnit
  | "zisk_chain_body_total_withdrawal_count" => some ziskChainBodyTotalWithdrawalCountProbeUnit
  | "zisk_block_logs_bloom_from_receipts_list" => some ziskBlockLogsBloomFromReceiptsListProbeUnit
  | "zisk_block_validate_logs_bloom" => some ziskBlockValidateLogsBloomProbeUnit
  | "zisk_header_root_is_empty_trie" => some ziskHeaderRootIsEmptyTrieProbeUnit
  | "zisk_calldata_byte_counts" => some ziskCalldataByteCountsProbeUnit
  | "zisk_intrinsic_gas_calldata_floor_eip7623" => some ziskIntrinsicGasCalldataFloorEip7623ProbeUnit
  | "zisk_init_code_cost"       => some ziskInitCodeCostProbeUnit
  | "zisk_mpt_nibbles_to_compact" => some ziskMptNibblesToCompactProbeUnit
  | "zisk_mpt_compact_to_nibbles" => some ziskMptCompactToNibblesProbeUnit
  | "zisk_mpt_node_classify"      => some ziskMptNodeClassifyProbeUnit
  | "zisk_mpt_encode_internal_node" => some ziskMptEncodeInternalNodeProbeUnit
  | "zisk_mpt_branch_get_child" => some ziskMptBranchGetChildProbeUnit
  | "zisk_mpt_branch_get_value" => some ziskMptBranchGetValueProbeUnit
  | "zisk_mpt_leaf_extract"     => some ziskMptLeafExtractProbeUnit
  | "zisk_mpt_extension_extract" => some ziskMptExtensionExtractProbeUnit
  | "zisk_mpt_branch_used_count" => some ziskMptBranchUsedCountProbeUnit
  | "zisk_mpt_branch_first_used_index" => some ziskMptBranchFirstUsedIndexProbeUnit
  | "zisk_sha256_from_input"    => some ziskSha256FromInputProbeUnit
  | "zisk_ssz_pair_hash"        => some ziskSszPairHashProbeUnit
  | "zisk_ssz_zero_hashes"      => some ziskSszZeroHashesProbeUnit
  | "zisk_ssz_merkleize_pow2"   => some ziskSszMerkleizePow2ProbeUnit
  | "zisk_ssz_merkleize"        => some ziskSszMerkleizeProbeUnit
  | "zisk_ssz_pack_bytes"       => some ziskSszPackBytesProbeUnit
  | "zisk_ssz_hash_tree_root_bytes" => some ziskSszHashTreeRootBytesProbeUnit
  | "zisk_ssz_hash_tree_root_list_bytelist" => some ziskSszHashTreeRootListByteListProbeUnit
  | "zisk_ssz_hash_tree_root_execution_witness" => some ziskSszHashTreeRootExecutionWitnessProbeUnit
  | _                           => none

/-- Look up a program by name. Returns `none` for unknown names so the CLI
    can produce a clean error. -/
def lookupProgram : String → Option BuildUnit
  | "smoke"                     => some smokeUnit
  | "evm_add"                   => some evmAddUnit
  | "evm_div"                   => some evmDivUnit
  | "evm_div_from_input"        => some evmDivFromInputUnit
  | "evm_mod"                   => some evmModUnit
  | "evm_mod_from_input"        => some evmModFromInputUnit
  | "evm_sdiv"                  => some evmSdivV4Unit
  | "evm_sdiv_from_input"       => some evmSdivV4FromInputUnit
  | "evm_sdiv_v4"               => some evmSdivV4Unit
  | "evm_sdiv_v4_from_input"    => some evmSdivV4FromInputUnit
  | "evm_smod"                  => some evmSmodUnit
  | "evm_smod_from_input"       => some evmSmodFromInputUnit
  | "evm_smod_v4"               => some evmSmodV4Unit
  | "evm_smod_v4_from_input"    => some evmSmodV4FromInputUnit
  | "input_echo"                => some inputEchoUnit
  | "evm_exp_from_input"        => some evmExpFromInputUnit
  | "evm_add_from_input"        => some evmAddFromInputUnit
  | "tiny_interp_add"           => some tinyInterpAddUnit
  | "tiny_interp_add2"          => some tinyInterpAdd2Unit
  | "tiny_interp_dispatch_add"  => some tinyInterpDispatchAddUnit
  | "tiny_interp_dispatch_add2" => some tinyInterpDispatchAdd2Unit
  | "runtime_dispatcher"        => some runtimeDispatcherUnit
  | "stateless_guest"           => some statelessGuestUnit
  | "zisk_keccak_probe"         => some ziskKeccakProbeUnit
  | "zisk_keccak256_empty"      => some ziskKeccak256EmptyProbeUnit
  | "zisk_keccak256_abc"        => some ziskKeccak256AbcProbeUnit
  | "zisk_zkvm_keccak256"       => some ziskZkvmKeccak256ProbeUnit
  | "zisk_sha256_probe_le"      => some ziskSha256ProbeLeUnit
  | "zisk_zkvm_sha256"          => some ziskZkvmSha256ProbeUnit
  | "zisk_keccak256_from_input" => some ziskKeccak256FromInputProbeUnit
  | "zisk_headers_keccak_chain" => some ziskHeadersKeccakChainProbeUnit
  | "zisk_headers_keccak_array" => some ziskHeadersKeccakArrayProbeUnit
  | "zisk_headers_parent_hash"  => some ziskHeadersParentHashProbeUnit
  | "zisk_header_validate_parent_hash" => some ziskHeaderValidateParentHashProbeUnit
  | "zisk_header_chain_walk_step" => some ziskHeaderChainWalkStepProbeUnit
  | "zisk_account_validate_code_hash" => some ziskAccountValidateCodeHashProbeUnit
  | "zisk_account_storage_root_eq" => some ziskAccountStorageRootEqProbeUnit
  | "zisk_account_code_hash_eq" => some ziskAccountCodeHashEqProbeUnit
  | "zisk_account_nonce_eq" => some ziskAccountNonceEqProbeUnit
  | "zisk_account_is_eip161_empty" => some ziskAccountIsEip161EmptyProbeUnit
  | "zisk_account_extract_storage_root" => some ziskAccountExtractStorageRootProbeUnit
  | "zisk_account_extract_balance" => some ziskAccountExtractBalanceProbeUnit
  | "zisk_account_extract_nonce" => some ziskAccountExtractNonceProbeUnit
  | "zisk_account_extract_code_hash" => some ziskAccountExtractCodeHashProbeUnit
  | "zisk_account_is_empty"     => some ziskAccountIsEmptyProbeUnit
  | "zisk_account_has_empty_code" => some ziskAccountHasEmptyCodeProbeUnit
  | "zisk_account_storage_root_is_empty" => some ziskAccountStorageRootIsEmptyProbeUnit
  | "zisk_address_from_pubkey"  => some ziskAddressFromPubkeyProbeUnit
  | "zisk_address_compute_create2" => some ziskAddressComputeCreate2ProbeUnit
  | "zisk_address_compute_create" => some ziskAddressComputeCreateProbeUnit
  | "zisk_mpt_account_path_nibbles" => some ziskMptAccountPathNibblesProbeUnit
  | "zisk_headers_validate_chain" => some ziskHeadersValidateChainProbeUnit
  | "zisk_witness_lookup_by_hash" => some ziskWitnessLookupByHashProbeUnit
  | "zisk_rlp_list_nth_item"    => some ziskRlpListNthItemProbeUnit
  | "zisk_rlp_list_count_items" => some ziskRlpListCountItemsProbeUnit
  | "zisk_access_list_count"    => some ziskAccessListCountProbeUnit
  | "zisk_blob_gas_used_from_versioned_hashes" => some ziskBlobGasUsedFromVersionedHashesProbeUnit
  | "zisk_mpt_node_kind"        => some ziskMptNodeKindProbeUnit
  | "zisk_mpt_branch_child"     => some ziskMptBranchChildProbeUnit
  | "zisk_hp_decode_nibbles"    => some ziskHpDecodeNibblesProbeUnit
  | "zisk_mpt_walk"             => some ziskMptWalkProbeUnit
  | "zisk_bytes_to_nibbles"     => some ziskBytesToNibblesProbeUnit
  | "zisk_mpt_lookup_by_key"    => some ziskMptLookupByKeyProbeUnit
  | "zisk_account_decode"       => some ziskAccountDecodeProbeUnit
  | "zisk_account_at_address"   => some ziskAccountAtAddressProbeUnit
  | "zisk_state_balance_inclusion_proof_verify" => some ziskStateBalanceInclusionProofVerifyProbeUnit
  | "zisk_slot_at_index"        => some ziskSlotAtIndexProbeUnit
  | "zisk_rlp_encode_uint_be"   => some ziskRlpEncodeUintBeProbeUnit
  | "zisk_rlp_encode_bytes"     => some ziskRlpEncodeBytesProbeUnit
  | "zisk_rlp_encode_list_prefix" => some ziskRlpEncodeListPrefixProbeUnit
  | "zisk_withdrawal_rlp_encode" => some ziskWithdrawalRlpEncodeProbeUnit
  | "zisk_withdrawal_compute_hash" => some ziskWithdrawalComputeHashProbeUnit
  | "zisk_account_encode"       => some ziskAccountEncodeProbeUnit
  | "zisk_hp_encode_nibbles"    => some ziskHpEncodeNibblesProbeUnit
  | "zisk_state_root_single_account" => some ziskStateRootSingleAccountProbeUnit
  | "zisk_validate_witness_state_contains_root" => some ziskValidateWitnessStateContainsRootProbeUnit
  | "zisk_account_at_header_state_root" => some ziskAccountAtHeaderStateRootProbeUnit
  | "zisk_slot_at_header_state_root" => some ziskSlotAtHeaderStateRootProbeUnit
  | "zisk_code_at_header_state_root" => some ziskCodeAtHeaderStateRootProbeUnit
  | "zisk_extcodesize_at_header_state_root" => some ziskExtcodesizeAtHeaderStateRootProbeUnit
  | "zisk_extcodehash_at_header_state_root" => some ziskExtcodehashAtHeaderStateRootProbeUnit
  | "zisk_balance_at_header_state_root" => some ziskBalanceAtHeaderStateRootProbeUnit
  | "zisk_nonce_at_header_state_root" => some ziskNonceAtHeaderStateRootProbeUnit
  | "zisk_storage_root_at_header_state_root" => some ziskStorageRootAtHeaderStateRootProbeUnit
  | "zisk_sload_at_header_state_root" => some ziskSloadAtHeaderStateRootProbeUnit
  | "zisk_extcodecopy_at_header_state_root" => some ziskExtcodecopyAtHeaderStateRootProbeUnit
  | "zisk_account_exists_at_header_state_root" => some ziskAccountExistsAtHeaderStateRootProbeUnit
  | "zisk_account_is_empty_at_header_state_root" => some ziskAccountIsEmptyAtHeaderStateRootProbeUnit
  | "zisk_validate_storage_root_in_witness_storage" => some ziskValidateStorageRootInWitnessStorageProbeUnit
  | "zisk_has_code_or_nonce_at_header_state_root" => some ziskHasCodeOrNonceAtHeaderStateRootProbeUnit
  | "zisk_rlp_field_to_u64"     => some ziskRlpFieldToU64ProbeUnit
  | "zisk_rlp_field_to_u256_be" => some ziskRlpFieldToU256BeProbeUnit
  | "zisk_tx_legacy_decode"     => some ziskTxLegacyDecodeProbeUnit
  | "zisk_tx_eip1559_decode"    => some ziskTxEip1559DecodeProbeUnit
  | "zisk_derive_chain_id_from_v" => some ziskDeriveChainIdFromVProbeUnit
  | "zisk_tx_legacy_extract_signature" => some ziskTxLegacyExtractSignatureProbeUnit
  | "zisk_tx_eip1559_extract_signature" => some ziskTxEip1559ExtractSignatureProbeUnit
  | "zisk_tx_eip2930_extract_signature" => some ziskTxEip2930ExtractSignatureProbeUnit
  | "zisk_tx_eip4844_extract_signature" => some ziskTxEip4844ExtractSignatureProbeUnit
  | "zisk_tx_eip7702_extract_signature" => some ziskTxEip7702ExtractSignatureProbeUnit
  | "zisk_eip7702_authorization_extract_signature" => some ziskEip7702AuthorizationExtractSignatureProbeUnit
  | "zisk_rlp_list_truncate_to_n_fields" => some ziskRlpListTruncateToNFieldsProbeUnit
  | "zisk_tx_signing_hash" => some ziskTxSigningHashProbeUnit
  | "zisk_tx_signing_hash_legacy_eip155" => some ziskTxSigningHashLegacyEip155ProbeUnit
  | "zisk_eip7702_authorization_signing_hash" => some ziskEip7702AuthorizationSigningHashProbeUnit
  | "zisk_header_minimal_decode" => some ziskHeaderMinimalDecodeProbeUnit
  | "zisk_header_extended_decode" => some ziskHeaderExtendedDecodeProbeUnit
  | "zisk_coinbase_extract_from_header" => some ziskCoinbaseExtractFromHeaderProbeUnit
  | "zisk_header_extract_blob_gas_pair" => some ziskHeaderExtractBlobGasPairProbeUnit
  | "zisk_block_validate_blob_gas_max_cap" => some ziskBlockValidateBlobGasMaxCapProbeUnit
  | "zisk_header_extract_block_roots" => some ziskHeaderExtractBlockRootsProbeUnit
  | "zisk_validate_header_basic" => some ziskValidateHeaderBasicProbeUnit
  | "zisk_check_gas_limit"      => some ziskCheckGasLimitProbeUnit
  | "zisk_tx_validate_against_block" => some ziskTxValidateAgainstBlockProbeUnit
  | "zisk_calc_excess_blob_gas" => some ziskCalcExcessBlobGasProbeUnit
  | "zisk_header_validate_post_merge" => some ziskHeaderValidatePostMergeProbeUnit
  | "zisk_header_validate_extra_data_length" => some ziskHeaderValidateExtraDataLengthProbeUnit
  | "zisk_u256_add_be"          => some ziskU256AddBeProbeUnit
  | "zisk_u256_lt_be"           => some ziskU256LtBeProbeUnit
  | "zisk_u256_sub_be"          => some ziskU256SubBeProbeUnit
  | "zisk_u256_eq"              => some ziskU256EqProbeUnit
  | "zisk_u256_mul_u64_be"      => some ziskU256MulU64BeProbeUnit
  | "zisk_account_charge_gas_pre_exec" => some ziskAccountChargeGasPreExecProbeUnit
  | "zisk_account_refund_gas_post_exec" => some ziskAccountRefundGasPostExecProbeUnit
  | "zisk_eip1559_calc_base_fee_per_gas" => some ziskEip1559CalcBaseFeePerGasProbeUnit
  | "zisk_header_validate_base_fee" => some ziskHeaderValidateBaseFeeProbeUnit
  | "zisk_validate_header_full" => some ziskValidateHeaderFullProbeUnit
  | "zisk_u256_from_u64_be"     => some ziskU256FromU64BeProbeUnit
  | "zisk_u256_to_u64_be"       => some ziskU256ToU64BeProbeUnit
  | "zisk_u256_is_zero"         => some ziskU256IsZeroProbeUnit
  | "zisk_u256_min"             => some ziskU256MinProbeUnit
  | "zisk_u256_max"             => some ziskU256MaxProbeUnit
  | "zisk_u256_div_u64_be"      => some ziskU256DivU64BeProbeUnit
  | "zisk_priority_fee_per_gas_eip1559" => some ziskPriorityFeePerGasEip1559ProbeUnit
  | "zisk_effective_gas_price_eip1559" => some ziskEffectiveGasPriceEip1559ProbeUnit
  | "zisk_tx_cost_compute"      => some ziskTxCostComputeProbeUnit
  | "zisk_validate_transaction_balance" => some ziskValidateTransactionBalanceProbeUnit
  | "zisk_tx_type_dispatch"     => some ziskTxTypeDispatchProbeUnit
  | "zisk_tx_extract_nonce_and_gas" => some ziskTxExtractNonceAndGasProbeUnit
  | "zisk_tx_extract_to_address" => some ziskTxExtractToAddressProbeUnit
  | "zisk_tx_extract_value"     => some ziskTxExtractValueProbeUnit
  | "zisk_tx_extract_data_section" => some ziskTxExtractDataSectionProbeUnit
  | "zisk_tx_extract_gas_pricing"  => some ziskTxExtractGasPricingProbeUnit
  | "zisk_tx_eip2930_decode"    => some ziskTxEip2930DecodeProbeUnit
  | "zisk_tx_eip7702_decode"    => some ziskTxEip7702DecodeProbeUnit
  | "zisk_tx_eip4844_decode"    => some ziskTxEip4844DecodeProbeUnit
  | "zisk_tx_eip4844_compute_blob_gas" => some ziskTxEip4844ComputeBlobGasProbeUnit
  | "zisk_tx_calculate_total_blob_gas" => some ziskTxCalculateTotalBlobGasProbeUnit
  | "zisk_block_body_blob_gas_total" => some ziskBlockBodyBlobGasTotalProbeUnit
  | "zisk_block_validate_blob_gas_consistency" => some ziskBlockValidateBlobGasConsistencyProbeUnit
  | "zisk_tx_decode_dispatch"   => some ziskTxDecodeDispatchProbeUnit
  | "zisk_intrinsic_gas_legacy" => some ziskIntrinsicGasLegacyProbeUnit
  | "zisk_tx_validate_intrinsic_gas_legacy" => some ziskTxValidateIntrinsicGasLegacyProbeUnit
  | "zisk_validate_transaction_basic" => some ziskValidateTransactionBasicProbeUnit
  | "zisk_validate_transaction_full" => some ziskValidateTransactionFullProbeUnit
  | "zisk_withdrawal_decode"    => some ziskWithdrawalDecodeProbeUnit
  | "zisk_block_body_decode"    => some ziskBlockBodyDecodeProbeUnit
  | "zisk_block_validate_ommers_empty" => some ziskBlockValidateOmmersEmptyProbeUnit
  | "zisk_process_withdrawal"   => some ziskProcessWithdrawalProbeUnit
  | "zisk_process_withdrawals_block" => some ziskProcessWithdrawalsBlockProbeUnit
  | "zisk_withdrawals_sum_amounts" => some ziskWithdrawalsSumAmountsProbeUnit
  | "zisk_block_withdrawals_total" => some ziskBlockWithdrawalsTotalProbeUnit
  | "zisk_block_count_withdrawals" => some ziskBlockCountWithdrawalsProbeUnit
  | "zisk_block_count_transactions" => some ziskBlockCountTransactionsProbeUnit
  | "zisk_block_summary"        => some ziskBlockSummaryProbeUnit
  | "zisk_block_compute_tx_hashes" => some ziskBlockComputeTxHashesProbeUnit
  | "zisk_bloom_add_value" => some ziskBloomAddValueProbeUnit
  | "zisk_log_bloom_add" => some ziskLogBloomAddProbeUnit
  | "zisk_logs_list_bloom_add" => some ziskLogsListBloomAddProbeUnit
  | "zisk_bloom_or_into" => some ziskBloomOrIntoProbeUnit
  | "zisk_receipt_extract_logs_bloom" => some ziskReceiptExtractLogsBloomProbeUnit
  | "zisk_header_extract_logs_bloom" => some ziskHeaderExtractLogsBloomProbeUnit
  | s                           => lookupProgramTail s

/-- List of known program names, for use in CLI usage strings. -/
def knownProgramNames : List String :=
  ["smoke", "evm_add", "evm_div", "evm_mod", "evm_sdiv", "evm_sdiv_v4", "input_echo",
   "evm_exp_from_input",
   "evm_add_from_input", "evm_div_from_input", "evm_mod_from_input",
   "evm_sdiv_from_input", "evm_sdiv_v4_from_input",
   "evm_smod", "evm_smod_from_input",
   "evm_smod_v4", "evm_smod_v4_from_input",
   "tiny_interp_add", "tiny_interp_add2",
   "tiny_interp_dispatch_add", "tiny_interp_dispatch_add2",
   "runtime_dispatcher",
   "stateless_guest",
   "zisk_keccak_probe",
   "zisk_keccak256_empty",
   "zisk_keccak256_abc",
   "zisk_zkvm_keccak256",
   "zisk_sha256_probe_le",
   "zisk_zkvm_sha256",
   "zisk_keccak256_from_input",
   "zisk_headers_keccak_chain",
   "zisk_headers_keccak_array",
   "zisk_headers_parent_hash",
   "zisk_header_validate_parent_hash",
   "zisk_header_chain_walk_step",
   "zisk_account_validate_code_hash",
   "zisk_account_storage_root_eq",
   "zisk_account_code_hash_eq",
   "zisk_account_nonce_eq",
   "zisk_account_is_eip161_empty",
   "zisk_account_extract_storage_root",
   "zisk_account_extract_balance",
   "zisk_account_extract_nonce",
   "zisk_account_extract_code_hash",
   "zisk_account_is_empty",
   "zisk_account_has_empty_code",
   "zisk_account_storage_root_is_empty",
   "zisk_address_from_pubkey",
   "zisk_address_compute_create2",
   "zisk_address_compute_create",
   "zisk_mpt_account_path_nibbles",
   "zisk_headers_validate_chain",
   "zisk_witness_lookup_by_hash",
   "zisk_rlp_list_nth_item",
   "zisk_rlp_list_count_items",
   "zisk_access_list_count",
   "zisk_blob_gas_used_from_versioned_hashes",
   "zisk_mpt_node_kind",
   "zisk_mpt_branch_child",
   "zisk_hp_decode_nibbles",
   "zisk_mpt_walk",
   "zisk_bytes_to_nibbles",
   "zisk_mpt_lookup_by_key",
   "zisk_account_decode",
   "zisk_account_at_address",
   "zisk_state_balance_inclusion_proof_verify",
   "zisk_slot_at_index",
   "zisk_rlp_encode_uint_be",
   "zisk_rlp_encode_bytes",
   "zisk_rlp_encode_list_prefix",
   "zisk_withdrawal_rlp_encode",
   "zisk_withdrawal_compute_hash",
   "zisk_account_encode",
   "zisk_hp_encode_nibbles",
   "zisk_state_root_single_account",
   "zisk_validate_witness_state_contains_root",
   "zisk_account_at_header_state_root",
   "zisk_slot_at_header_state_root",
   "zisk_code_at_header_state_root",
   "zisk_extcodesize_at_header_state_root",
   "zisk_extcodehash_at_header_state_root",
   "zisk_balance_at_header_state_root",
   "zisk_nonce_at_header_state_root",
   "zisk_storage_root_at_header_state_root",
   "zisk_sload_at_header_state_root",
   "zisk_extcodecopy_at_header_state_root",
   "zisk_account_exists_at_header_state_root",
   "zisk_account_is_empty_at_header_state_root",
   "zisk_validate_storage_root_in_witness_storage",
   "zisk_has_code_or_nonce_at_header_state_root",
   "zisk_rlp_field_to_u64",
   "zisk_rlp_field_to_u256_be",
   "zisk_tx_legacy_decode",
   "zisk_tx_eip1559_decode",
   "zisk_derive_chain_id_from_v",
   "zisk_tx_legacy_extract_signature",
   "zisk_tx_eip1559_extract_signature",
   "zisk_tx_eip2930_extract_signature",
   "zisk_tx_eip4844_extract_signature",
   "zisk_tx_eip7702_extract_signature",
   "zisk_eip7702_authorization_extract_signature",
   "zisk_rlp_list_truncate_to_n_fields",
   "zisk_tx_signing_hash",
   "zisk_tx_signing_hash_legacy_eip155",
   "zisk_eip7702_authorization_signing_hash",
   "zisk_header_minimal_decode",
   "zisk_header_extended_decode",
   "zisk_coinbase_extract_from_header",
   "zisk_header_extract_blob_gas_pair",
   "zisk_block_validate_blob_gas_max_cap",
   "zisk_header_extract_block_roots",
   "zisk_validate_header_basic",
   "zisk_check_gas_limit",
   "zisk_tx_validate_against_block",
   "zisk_calc_excess_blob_gas",
   "zisk_header_validate_post_merge",
   "zisk_header_validate_extra_data_length",
   "zisk_u256_add_be",
   "zisk_u256_lt_be",
   "zisk_u256_sub_be",
   "zisk_u256_eq",
   "zisk_u256_mul_u64_be",
   "zisk_account_charge_gas_pre_exec",
   "zisk_account_refund_gas_post_exec",
   "zisk_eip1559_calc_base_fee_per_gas",
   "zisk_header_validate_base_fee",
   "zisk_validate_header_full",
   "zisk_u256_from_u64_be",
   "zisk_u256_to_u64_be",
   "zisk_u256_is_zero",
   "zisk_u256_min",
   "zisk_u256_max",
   "zisk_u256_div_u64_be",
   "zisk_priority_fee_per_gas_eip1559",
   "zisk_effective_gas_price_eip1559",
   "zisk_tx_cost_compute",
   "zisk_validate_transaction_balance",
   "zisk_tx_type_dispatch",
   "zisk_tx_extract_nonce_and_gas",
   "zisk_tx_extract_to_address",
   "zisk_tx_extract_value",
   "zisk_tx_extract_data_section",
   "zisk_tx_extract_gas_pricing",
   "zisk_tx_eip2930_decode",
   "zisk_tx_eip7702_decode",
   "zisk_tx_eip4844_decode",
   "zisk_tx_eip4844_compute_blob_gas",
   "zisk_tx_calculate_total_blob_gas",
   "zisk_block_body_blob_gas_total",
   "zisk_block_validate_blob_gas_consistency",
   "zisk_tx_decode_dispatch",
   "zisk_intrinsic_gas_legacy",
   "zisk_tx_validate_intrinsic_gas_legacy",
   "zisk_validate_transaction_basic",
   "zisk_validate_transaction_full",
   "zisk_withdrawal_decode",
   "zisk_block_body_decode",
   "zisk_block_validate_ommers_empty",
   "zisk_process_withdrawal",
   "zisk_process_withdrawals_block",
   "zisk_withdrawals_sum_amounts",
   "zisk_block_withdrawals_total",
   "zisk_block_count_withdrawals",
   "zisk_block_count_transactions",
   "zisk_block_summary",
   "zisk_block_compute_tx_hashes",
   "zisk_bloom_add_value",
   "zisk_log_bloom_add",
   "zisk_logs_list_bloom_add",
   "zisk_bloom_or_into",
   "zisk_receipt_extract_logs_bloom",
   "zisk_header_extract_logs_bloom",
   "zisk_bloom_eq",
   "zisk_rlp_encode_u64",
   "zisk_receipt_encode",
   "zisk_single_leaf_trie_root",
   "zisk_mpt_leaf_node_encode",
   "zisk_mpt_node_slot_encode",
   "zisk_mpt_extension_node_encode",
   "zisk_mpt_branch_node_encode",
   "zisk_nibbles_common_prefix_len",
   "zisk_mpt_branch_payload_two_slots",
   "zisk_mpt_leaf_node_encode_from_nibbles",
   "zisk_mpt_branch_node_keccak",
   "zisk_mpt_two_leaf_root_indexed",
   "zisk_mpt_one_leaf_root_indexed",
   "zisk_block_validate_transactions_root_one_tx",
   "zisk_block_validate_withdrawals_root_one_w",
   "zisk_block_validate_withdrawals_root_two_w",
   "zisk_block_validate_receipts_root_one_receipt",
   "zisk_block_validate_receipts_root_two_receipts",
   "zisk_block_validate_transactions_root_two_tx",
   "zisk_block_hash_from_header",
   "zisk_validate_parent_hash_link",
   "zisk_validate_header_pair",
   "zisk_validate_header_chain",
   "zisk_block_hash_array_from_chain",
   "zisk_validate_block_hash_chain_match",
   "zisk_chain_compute_total_gas_used",
   "zisk_chain_extract_number_range",
   "zisk_header_extract_basefee",
   "zisk_chain_extract_basefee_range",
   "zisk_chain_block_hashes_commitment",
   "zisk_header_extract_state_root",
   "zisk_validate_state_root_against_witness_node",
   "zisk_header_extract_parent_hash",
   "zisk_header_extract_receipts_root",
   "zisk_header_extract_transactions_root",
   "zisk_header_extract_withdrawals_root",
   "zisk_header_extract_ommers_hash",
   "zisk_header_extract_prev_randao",
   "zisk_header_extract_beneficiary",
   "zisk_block_hash_matches",
   "zisk_header_extract_gas_used",
   "zisk_header_extract_gas_limit",
   "zisk_block_validate_block_hash_pair",
   "zisk_block_hash_and_extract_number",
   "zisk_blockhash_from_witness_headers",
   "zisk_witness_headers_chain_validate",
   "zisk_header_compute_summary_struct",
   "zisk_header_extract_difficulty",
   "zisk_header_extract_extra_data",
   "zisk_header_extract_nonce",
   "zisk_header_validate_nonce_zero",
   "zisk_header_validate_difficulty_zero",
   "zisk_validate_header_post_merge_zeros",
   "zisk_chain_validate_post_merge_zeros",
   "zisk_chain_validate_full",
   "zisk_chain_validate_increasing_timestamps",
   "zisk_chain_validate_consecutive_numbers",
   "zisk_chain_compute_total_blob_gas",
   "zisk_header_extract_timestamp",
   "zisk_header_extract_number",
   "zisk_account_validate_code_hash_empty",
   "zisk_account_validate_storage_root_empty",
   "zisk_chain_compute_max_gas_used",
   "zisk_chain_compute_max_blob_gas_used",
   "zisk_chain_compute_min_gas_used",
   "zisk_chain_extract_timestamp_range",
   "zisk_chain_validate_gas_used_under_limit",
   "zisk_header_extract_blob_gas_used",
   "zisk_account_validate_nonce_zero",
   "zisk_chain_compute_min_blob_gas_used",
   "zisk_header_extract_excess_blob_gas",
   "zisk_chain_extract_gas_used_range",
   "zisk_chain_extract_blob_gas_used_range",
   "zisk_chain_extract_basefee_first_last",
   "zisk_chain_compute_total_blob_count",
   "zisk_chain_compute_total_basefee",
   "zisk_chain_compute_max_basefee",
   "zisk_chain_compute_min_basefee",
   "zisk_chain_compute_max_gas_limit",
   "zisk_chain_compute_min_gas_limit",
   "zisk_chain_compute_total_gas_limit",
   "zisk_chain_extract_gas_limit_first_last",
   "zisk_chain_validate_constant_gas_limit",
   "zisk_chain_validate_basefee_non_decreasing",
   "zisk_chain_validate_basefee_non_increasing",
   "zisk_chain_validate_gas_limit_non_decreasing",
   "zisk_chain_validate_gas_limit_non_increasing",
   "zisk_chain_extract_excess_blob_gas_first_last",
   "zisk_chain_compute_max_excess_blob_gas",
   "zisk_chain_compute_min_excess_blob_gas",
   "zisk_chain_validate_excess_blob_gas_non_decreasing",
   "zisk_chain_validate_excess_blob_gas_non_increasing",
   "zisk_chain_compute_total_excess_blob_gas",
   "zisk_chain_validate_blob_gas_used_under_max",
   "zisk_chain_validate_blob_gas_used_multiple",
   "zisk_chain_compute_max_timestamp_gap",
   "zisk_chain_compute_min_timestamp_gap",
   "zisk_header_extract_parent_beacon_block_root",
   "zisk_chain_extract_first_last_parent_beacon_block_root",
   "zisk_header_extract_requests_hash",
   "zisk_chain_extract_first_last_requests_hash",
   "zisk_chain_compute_max_blob_count",
   "zisk_chain_compute_min_blob_count",
   "zisk_chain_validate_difficulty_zero",
   "zisk_chain_validate_nonce_zero",
   "zisk_chain_validate_ommers_hash_empty",
   "zisk_chain_validate_post_merge_full",
   "zisk_chain_validate_extra_data_length",
   "zisk_chain_compute_max_extra_data_length",
   "zisk_chain_extract_first_last_state_root",
   "zisk_chain_extract_first_last_block_hash",
   "zisk_chain_extract_first_last_receipts_root",
   "zisk_chain_extract_first_last_transactions_root",
   "zisk_chain_extract_first_last_withdrawals_root",
   "zisk_chain_extract_first_last_prev_randao",
   "zisk_chain_extract_first_last_beneficiary",
   "zisk_chain_extract_first_last_ommers_hash",
   "zisk_chain_validate_no_blob_txs",
   "zisk_account_validate_balance_zero",
   "zisk_block_validate_2tx_full",
   "zisk_block_body_extract_2tx",
   "zisk_block_validate_2tx_full_with_body",
   "zisk_block_validate_empty_ommers_hash",
   "zisk_block_validate_no_withdrawals_pair",
   "zisk_block_body_extract_1tx",
   "zisk_block_validate_1tx_full",
   "zisk_block_validate_1tx_full_with_body",
   "zisk_block_validate_empty_receipts_root",
   "zisk_block_validate_empty_block",
   "zisk_validate_empty_block_with_parent",
   "zisk_validate_empty_block_chain",
   "zisk_block_body_extract_tx_count",
   "zisk_block_body_extract_withdrawal_count",
   "zisk_block_body_summary",
   "zisk_block_body_validate_empty",
   "zisk_chain_body_total_tx_count",
   "zisk_chain_body_total_withdrawal_count",
   "zisk_block_logs_bloom_from_receipts_list",
   "zisk_block_validate_logs_bloom",
   "zisk_header_root_is_empty_trie",
   "zisk_calldata_byte_counts",
   "zisk_intrinsic_gas_calldata_floor_eip7623",
   "zisk_init_code_cost",
   "zisk_mpt_nibbles_to_compact",
   "zisk_mpt_compact_to_nibbles",
   "zisk_mpt_node_classify",
   "zisk_mpt_encode_internal_node",
   "zisk_mpt_branch_get_child",
   "zisk_mpt_branch_get_value",
   "zisk_mpt_leaf_extract",
   "zisk_mpt_extension_extract",
   "zisk_mpt_branch_used_count",
   "zisk_mpt_branch_first_used_index",
   "zisk_sha256_from_input",
   "zisk_ssz_pair_hash",
   "zisk_ssz_zero_hashes",
   "zisk_ssz_merkleize_pow2",
   "zisk_ssz_merkleize",
   "zisk_ssz_pack_bytes",
   "zisk_ssz_hash_tree_root_bytes",
   "zisk_ssz_hash_tree_root_list_bytelist",
   "zisk_ssz_hash_tree_root_execution_witness"]

end EvmAsm.Codegen

/-! ## File-size guard

    Hard cap of 1500 lines on `Programs.lean` and every sibling under
    `EvmAsm/Codegen/Programs/`, to keep the registry hub and the
    extracted submodules from spiralling. When this guard trips, split
    a cluster of `*Function` / `zisk*` defs into a new (or existing)
    submodule, add it to the `paths` list below and to `Programs.lean`'s
    imports.

    Established splits so far:
      * PR-#5870 carved `Evm.lean` / `HashBridge.lean` / `Ssz.lean`.
      * PR-#5900 carved `RlpRead.lean` / `Mpt.lean`.
      * PR-#5948 carved `Tx.lean`.
      * PR-#7176 carved `EvmOpcodesStorageRoot.lean` /
        `EvmOpcodesExtcodecopy.lean`.

    Runs at elaboration time via `#eval`; adds zero runtime cost. -/

#eval show IO Unit from do
  let hardCap := 1500
  let paths := [
    "EvmAsm/Codegen/Programs.lean",
    "EvmAsm/Codegen/Programs/Account.lean",
    "EvmAsm/Codegen/Programs/AccountFields.lean",
    "EvmAsm/Codegen/Programs/Address.lean",
    "EvmAsm/Codegen/Programs/Block.lean",
    "EvmAsm/Codegen/Programs/BlockBody.lean",
    "EvmAsm/Codegen/Programs/BlockEmpty.lean",
    "EvmAsm/Codegen/Programs/BlockRoots.lean",
    "EvmAsm/Codegen/Programs/BlockValidate.lean",
    "EvmAsm/Codegen/Programs/Chain.lean",
    "EvmAsm/Codegen/Programs/ChainAggregator.lean",
    "EvmAsm/Codegen/Programs/ChainBasefee.lean",
    "EvmAsm/Codegen/Programs/ChainBlobCount.lean",
    "EvmAsm/Codegen/Programs/ChainExcessBlobGas.lean",
    "EvmAsm/Codegen/Programs/ChainTimestamp.lean",
    "EvmAsm/Codegen/Programs/ChainEndpoints.lean",
    "EvmAsm/Codegen/Programs/ChainValidate.lean",
    "EvmAsm/Codegen/Programs/ChainValidateBlob.lean",
    "EvmAsm/Codegen/Programs/ChainValidatePostMerge.lean",
    "EvmAsm/Codegen/Programs/Bloom.lean",
    "EvmAsm/Codegen/Programs/Evm.lean",
    "EvmAsm/Codegen/Programs/ExpProperty.lean",
    "EvmAsm/Codegen/Programs/HashBridge.lean",
    "EvmAsm/Codegen/Programs/HashProbes.lean",
    "EvmAsm/Codegen/Programs/IntrinsicGas.lean",
    "EvmAsm/Codegen/Programs/Header.lean",
    "EvmAsm/Codegen/Programs/HeaderBaseFee.lean",
    "EvmAsm/Codegen/Programs/HeaderDecode.lean",
    "EvmAsm/Codegen/Programs/HeaderChain.lean",
    "EvmAsm/Codegen/Programs/HeaderFields.lean",
    "EvmAsm/Codegen/Programs/BlockHashPredicates.lean",
    "EvmAsm/Codegen/Programs/HeadersKeccak.lean",
    "EvmAsm/Codegen/Programs/HeaderU64.lean",
    "EvmAsm/Codegen/Programs/Mpt.lean",
    "EvmAsm/Codegen/Programs/MptEncode.lean",
    "EvmAsm/Codegen/Programs/Noop.lean",
    "EvmAsm/Codegen/Programs/Storage.lean",
    "EvmAsm/Codegen/Programs/MptInternal.lean",
    "EvmAsm/Codegen/Programs/MptNibbles.lean",
    "EvmAsm/Codegen/Programs/Receipt.lean",
    "EvmAsm/Codegen/Programs/State.lean",
    "EvmAsm/Codegen/Programs/StateCompose.lean",
    "EvmAsm/Codegen/Programs/EvmOpcodes.lean",
    "EvmAsm/Codegen/Programs/EvmOpcodesStorageRoot.lean",
    "EvmAsm/Codegen/Programs/EvmOpcodesExtcodecopy.lean",
    "EvmAsm/Codegen/Programs/StorageCompose.lean",
    "EvmAsm/Codegen/Programs/EvmCodes.lean",
    "EvmAsm/Codegen/Programs/RlpRead.lean",
    "EvmAsm/Codegen/Programs/Ssz.lean",
    "EvmAsm/Codegen/Programs/StatelessGuestData.lean",
    "EvmAsm/Codegen/Programs/StatelessGuestEpilogue.lean",
    "EvmAsm/Codegen/Programs/Tx.lean",
    "EvmAsm/Codegen/Programs/TxDecode.lean",
    "EvmAsm/Codegen/Programs/TxExtract.lean",
    "EvmAsm/Codegen/Programs/TxRoot.lean",
    "EvmAsm/Codegen/Programs/TxSignature.lean",
    "EvmAsm/Codegen/Programs/TxSigningHash.lean",
    "EvmAsm/Codegen/Programs/U256.lean",
    "EvmAsm/Codegen/Programs/Withdrawal.lean"
  ]
  for path in paths do
    let contents ← IO.FS.readFile path
    let lineCount := (contents.splitOn "\n").length
    if lineCount > hardCap then
      throw <| IO.userError <|
        s!"{path} has {lineCount} lines; hard cap is {hardCap}. " ++
        "Extract a helper cluster into a new submodule under " ++
        "EvmAsm/Codegen/Programs/ (see PR #5870 and PR #5900 for the " ++
        "established pattern). Add the new submodule to the `paths` list " ++
        "and to `Programs.lean`'s imports."
