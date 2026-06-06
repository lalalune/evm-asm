/- EvmAsm.Codegen.Programs.RegistryTail
  Tail sub-registry for codegen programs.
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
-- EXP wrapper is parametric over caller-saved registers (x6, x16) that mul_callable clobbers; deferred until upstream lands a
-- fully callee-saved variant. import re-added when wiring lands.
-- import EvmAsm.Evm64.Exp.Program
import EvmAsm.Evm64.Gt.Program
import EvmAsm.Evm64.IsZero.Program
import EvmAsm.Evm64.Lt.Program
import EvmAsm.Evm64.MLoad.Program
import EvmAsm.Evm64.MStore.Program
import EvmAsm.Evm64.MStore8.Program
import EvmAsm.Evm64.Multiply.Callable -- EXP's inline mul_callable (Programs/Evm.lean)
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
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.EvmAccountWitness
import EvmAsm.Codegen.Programs.EIP7708Logs
import EvmAsm.Codegen.Programs.EvmBalance
import EvmAsm.Codegen.Programs.EvmExtcodecopy
import EvmAsm.Codegen.Programs.EvmArithUnits
import EvmAsm.Codegen.Programs.EvmDispatchUnits
import EvmAsm.Codegen.Programs.Clz
import EvmAsm.Codegen.Programs.ExpProperty
import EvmAsm.Codegen.Programs.CryptoRegistry
import EvmAsm.Codegen.Programs.Selfdestruct
import EvmAsm.Codegen.Programs.StatelessGuestData
import EvmAsm.Codegen.Programs.StatelessGuestEpilogue
import EvmAsm.Codegen.Programs.IntrinsicGas
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.MptSet
import EvmAsm.Codegen.Programs.MptSetAcc
import EvmAsm.Codegen.Programs.MptInsertWalk
import EvmAsm.Codegen.Programs.MptInsert
import EvmAsm.Codegen.Programs.MptInsertWalkDb
import EvmAsm.Codegen.Programs.MptInsertAcc
import EvmAsm.Codegen.Programs.MptStateRootIns
import EvmAsm.Codegen.Programs.MptIndexedTrieRoot
import EvmAsm.Codegen.Programs.WithdrawalsRootIndexed
import EvmAsm.Codegen.Programs.BlockVerdictReceiptRecords
import EvmAsm.Codegen.Programs.ReceiptsRootIndexed
import EvmAsm.Codegen.Programs.ReceiptsConsensus
import EvmAsm.Codegen.Programs.MptDeleteWalkDb
import EvmAsm.Codegen.Programs.MptDeleteAcc
import EvmAsm.Codegen.Programs.WithdrawalsStateRoot
import EvmAsm.Codegen.Programs.AccountBalance
import EvmAsm.Codegen.Programs.MptEncode
import EvmAsm.Codegen.Programs.SystemWrites
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.BalCodePreimages
import EvmAsm.Codegen.Programs.BalAccountHasStateChange
import EvmAsm.Codegen.Programs.BalAccountPath
import EvmAsm.Codegen.Programs.BalAccountPostFields
import EvmAsm.Codegen.Programs.BalAccountApplyPostFields
import EvmAsm.Codegen.Programs.BalAccountChangeValue
import EvmAsm.Codegen.Programs.BalAccountChangeDescriptor
import EvmAsm.Codegen.Programs.BalAccountNthDescriptor
import EvmAsm.Codegen.Programs.BalAccountDescriptorArray
import EvmAsm.Codegen.Programs.BalAccountStateRoot
import EvmAsm.Codegen.Programs.BalAccountRecordArray
import EvmAsm.Codegen.Programs.StorageWrite
import EvmAsm.Codegen.Programs.StorageEffectRecords
import EvmAsm.Codegen.Programs.SstoreGasRefund
import EvmAsm.Codegen.Programs.BlockAccessListHash
import EvmAsm.Codegen.Programs.BlockVerdictModeledSystem
import EvmAsm.Codegen.Programs.BlockGasRemaining
import EvmAsm.Codegen.Programs.BlockVerdictGasGate
import EvmAsm.Codegen.Programs.BlockhashRequiredHeaders
import EvmAsm.Codegen.Programs.Eip7702NonceReuseGuard
import EvmAsm.Codegen.Programs.AccountApplyStorage
import EvmAsm.Codegen.Programs.StorageRoot
import EvmAsm.Codegen.Programs.MptInternal
import EvmAsm.Codegen.Programs.MptNibbles
import EvmAsm.Codegen.Programs.Ssz
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.TxDecode
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.TxGasBalPostVerify
import EvmAsm.Codegen.Programs.TxGasSenderBalLookup
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
import EvmAsm.Codegen.Programs.ValidateHeaderPair
import EvmAsm.Codegen.Programs.BlockHeaderSszToRlp
import EvmAsm.Codegen.Programs.Step2Verdict
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
import EvmAsm.Codegen.Programs.WitnessCodesKeccakAtIndex
import EvmAsm.Codegen.Programs.ChainWalkOneStepBack
import EvmAsm.Codegen.Programs.ChainWalkNStepsBack
import EvmAsm.Codegen.Programs.StateRootChainWalkBack
import EvmAsm.Codegen.Programs.BlockNumberAtBlockHash
import EvmAsm.Codegen.Programs.StateSlotAtBlockNumber
import EvmAsm.Codegen.Programs.StateAccountAtBlockNumber
import EvmAsm.Codegen.Programs.BalanceAtBlockNumber
import EvmAsm.Codegen.Programs.NonceAtBlockNumber
import EvmAsm.Codegen.Programs.CodeHashAtBlockNumber
import EvmAsm.Codegen.Programs.StorageRootAtBlockNumber
import EvmAsm.Codegen.Programs.AccountExistsAtBlockNumber
import EvmAsm.Codegen.Programs.HasCodeOrNonceAtBlockNumber
import EvmAsm.Codegen.Programs.AccountIsEmptyAtBlockNumber
import EvmAsm.Codegen.Programs.ExtcodesizeAtBlockNumber
import EvmAsm.Codegen.Programs.ExtcodehashAtBlockNumber
import EvmAsm.Codegen.Programs.ExtcodecopyAtBlockNumber
import EvmAsm.Codegen.Programs.SloadAtBlockNumber
import EvmAsm.Codegen.Programs.LogsBloomKeccakAtBlockNumber
import EvmAsm.Codegen.Programs.TransactionsRootAtBlockNumber
import EvmAsm.Codegen.Programs.TimestampAtBlockNumber
import EvmAsm.Codegen.Programs.GasLimitAtBlockNumber
import EvmAsm.Codegen.Programs.GasUsedAtBlockNumber
import EvmAsm.Codegen.Programs.ReceiptsRootAtBlockNumber
import EvmAsm.Codegen.Programs.OmmersHashAtBlockNumber
import EvmAsm.Codegen.Programs.ParentBeaconBlockRootAtBlockNumber
import EvmAsm.Codegen.Programs.BeneficiaryAtBlockNumber
import EvmAsm.Codegen.Programs.WithdrawalsRootAtBlockNumber
import EvmAsm.Codegen.Programs.DifficultyAtBlockNumber
import EvmAsm.Codegen.Programs.PrevRandaoAtBlockNumber
import EvmAsm.Codegen.Programs.ExcessBlobGasAtBlockNumber
import EvmAsm.Codegen.Programs.BlobGasUsedAtBlockNumber
import EvmAsm.Codegen.Programs.ExtraDataAtBlockNumber
import EvmAsm.Codegen.Programs.ParentHashAtBlockNumber
import EvmAsm.Codegen.Programs.HeaderNonceAtBlockNumber
import EvmAsm.Codegen.Programs.BaseFeePerGasAtBlockNumber
import EvmAsm.Codegen.Programs.BlockHashAtBlockNumber
import EvmAsm.Codegen.Programs.CodeAtBlockNumber
import EvmAsm.Codegen.Programs.BlockHashAtStateRoot
import EvmAsm.Codegen.Programs.AccountStorageWalkable
import EvmAsm.Codegen.Programs.CodeAtStateRoot
import EvmAsm.Codegen.Programs.BlockNumberAtStateRoot
import EvmAsm.Codegen.Programs.StateRootAtBlockNumber
import EvmAsm.Codegen.Programs.CodeHashAtBlockHash
import EvmAsm.Codegen.Programs.WitnessHeadersFindIndexByBlockHash
import EvmAsm.Codegen.Programs.StorageRootAtBlockHash
import EvmAsm.Codegen.Programs.StateAccountAtBlockHash
import EvmAsm.Codegen.Programs.WitnessHeadersBlockHashAtIndex
import EvmAsm.Codegen.Programs.StateSlotAtBlockHash
import EvmAsm.Codegen.Programs.BalanceAtBlockHash
import EvmAsm.Codegen.Programs.NonceAtBlockHash
import EvmAsm.Codegen.Programs.CodeAtBlockHash
import EvmAsm.Codegen.Programs.HasCodeOrNonceAtBlockHash
import EvmAsm.Codegen.Programs.LogsBloomKeccakAtBlockHash
import EvmAsm.Codegen.Programs.GasLimitAtBlockHash
import EvmAsm.Codegen.Programs.BaseFeePerGasAtBlockHash
import EvmAsm.Codegen.Programs.GasUsedAtBlockHash
import EvmAsm.Codegen.Programs.TimestampAtBlockHash
import EvmAsm.Codegen.Programs.BeneficiaryAtBlockHash
import EvmAsm.Codegen.Programs.ParentHashAtBlockHash
import EvmAsm.Codegen.Programs.AccountExistsAtBlockHash
import EvmAsm.Codegen.Programs.ExtcodesizeAtBlockHash
import EvmAsm.Codegen.Programs.AccountIsEmptyAtBlockHash
import EvmAsm.Codegen.Programs.ExtcodehashAtBlockHash
import EvmAsm.Codegen.Programs.SloadAtBlockHash
import EvmAsm.Codegen.Programs.ExtcodecopyAtBlockHash
import EvmAsm.Codegen.Programs.StateProof
import EvmAsm.Codegen.Programs.StateStorageProof
import EvmAsm.Codegen.Programs.StateCodeHashProof
import EvmAsm.Codegen.Programs.StorageRootInWitness
import EvmAsm.Codegen.Programs.WitnessStorageKeccakAtIndex
import EvmAsm.Codegen.Programs.StateAccountSpecDefault
import EvmAsm.Codegen.Programs.StateExtractStorageRoot
import EvmAsm.Codegen.Programs.ChainLinkExtract
import EvmAsm.Codegen.Programs.StateRootInWitness
import EvmAsm.Codegen.Programs.StateExtractBalance
import EvmAsm.Codegen.Programs.StateWalkExtractSlot
import EvmAsm.Codegen.Programs.StateExtractCodeHash
import EvmAsm.Codegen.Programs.StateExtractNonce
import EvmAsm.Codegen.Programs.WitnessHeadersStateRootAtIndex
import EvmAsm.Codegen.Programs.WitnessHeadersAllChainLinksValidate
import EvmAsm.Codegen.Programs.WitnessStorageNodeKindDistribution
import EvmAsm.Codegen.Programs.WitnessHeadersAccountAtIndex
import EvmAsm.Codegen.Programs.WitnessHeadersChainLink
import EvmAsm.Codegen.Programs.StateRootPresentInWitnessState
import EvmAsm.Codegen.Programs.WitnessHeadersSlotAtIndex
import EvmAsm.Codegen.Programs.StateStorageRootProof
import EvmAsm.Codegen.Programs.WitnessNodeKindDistribution
import EvmAsm.Codegen.Programs.StateNonceProof
import EvmAsm.Codegen.Programs.StateBalanceProof
import EvmAsm.Codegen.Programs.WitnessStateKeccakAtIndex
import EvmAsm.Codegen.Programs.ChainLinkParentKeccak
import EvmAsm.Codegen.Programs.EvmOpcodes
import EvmAsm.Codegen.Programs.RuntimeAccountWitness
import EvmAsm.Codegen.Programs.EvmOpcodesStorageRoot
import EvmAsm.Codegen.Programs.EvmOpcodesExtcodecopy
import EvmAsm.Codegen.Programs.AccountFieldGetters
import EvmAsm.Codegen.Programs.WitnessValidation
import EvmAsm.Codegen.Programs.StorageProof
import EvmAsm.Codegen.Programs.Eip4788
import EvmAsm.Codegen.Programs.CodeVerify
import EvmAsm.Codegen.Programs.AccountVerify
import EvmAsm.Codegen.Programs.StorageVerify
import EvmAsm.Codegen.Programs.Eip2935
import EvmAsm.Codegen.Programs.StorageCompose
import EvmAsm.Codegen.Programs.EvmCodes
import EvmAsm.Codegen.Programs.TxRoot
import EvmAsm.Codegen.Programs.TxSignature
import EvmAsm.Codegen.Programs.TxSigningHash
import EvmAsm.Codegen.Programs.Withdrawal
import EvmAsm.Codegen.Programs.WithdrawalPath
import EvmAsm.Codegen.Programs.SszWithdrawal
import EvmAsm.Codegen.Programs.SszWitnessState
import EvmAsm.Codegen.Programs.SszPayloadWithdrawals
import EvmAsm.Codegen.Programs.SszParentHeader
import EvmAsm.Codegen.Programs.StatelessVerdict
import EvmAsm.Codegen.Programs.BlockVerdict
import EvmAsm.Codegen.Programs.BlockVerdictV2
import EvmAsm.Codegen.Programs.Address
import EvmAsm.Codegen.Programs.OmmersHashAtBlockHash
import EvmAsm.Codegen.Programs.ParentBeaconBlockRootAtBlockHash
import EvmAsm.Codegen.Programs.TransactionsRootAtBlockHash
import EvmAsm.Codegen.Programs.ReceiptsRootAtBlockHash
import EvmAsm.Codegen.Programs.WithdrawalsRootAtBlockHash
import EvmAsm.Codegen.Programs.PrevRandaoAtBlockHash
import EvmAsm.Codegen.Programs.DifficultyAtBlockHash
import EvmAsm.Codegen.Programs.HeaderNonceAtBlockHash
import EvmAsm.Codegen.Programs.ExtraDataAtBlockHash
import EvmAsm.Codegen.Programs.ExcessBlobGasAtBlockHash
import EvmAsm.Codegen.Programs.BlobGasUsedAtBlockHash
import EvmAsm.Codegen.Programs.BlobGasPairAtBlockHash
import EvmAsm.Codegen.Programs.PostMergeInvariantsAtBlockHash
import EvmAsm.Codegen.Programs.BlockRootsAtBlockHash
import EvmAsm.Codegen.Programs.NumberTimestampPairAtBlockHash
import EvmAsm.Codegen.Programs.GasPairAtBlockHash

namespace EvmAsm.Codegen

/-- Second half of the program lookup, split off `lookupProgram` to
    keep the C-emitted match below clang's default 256 bracket-nesting
    limit. New PRs append arms here, not to `lookupProgram`. -/
def lookupProgramTail : String → Option BuildUnit
  | "zisk_bloom_eq" => some ziskBloomEqProbeUnit
  | "zisk_rlp_encode_u64" => some ziskRlpEncodeU64ProbeUnit
  | "zisk_receipt_encode" => some ziskReceiptEncodeProbeUnit
  | "zisk_typed_receipt_encode" => some ziskTypedReceiptEncodeProbeUnit
  | "zisk_receipt_records_probe" => some ziskReceiptRecordsProbeUnit | "zisk_block_receipt_records_materialize" => some ziskBlockReceiptRecordsMaterializeProbeUnit | "zisk_eip7778_remaining_block_gas_check" => some ziskEip7778RemainingBlockGasCheckProbeUnit
  | "zisk_single_leaf_trie_root" => some ziskSingleLeafTrieRootProbeUnit
  | "zisk_system_write_descriptors" => some ziskSystemWriteDescriptorsProbeUnit
  | "zisk_bal_gas_valid"         => some ziskBalGasValidProbeUnit | "zisk_storage_access_gas" => some ziskStorageAccessGasProbeUnit
  | "zisk_bal_section_info"      => some ziskBalSectionInfoProbeUnit
  | "zisk_bal_account_path"      => some ziskBalAccountPathProbeUnit
  | "zisk_bal_account_post_fields" => some ziskBalAccountPostFieldsProbeUnit
  | "zisk_bal_account_apply_post_fields" => some ziskBalAccountApplyPostFieldsProbeUnit
  | "zisk_bal_account_change_value" => some ziskBalAccountChangeValueProbeUnit
  | "zisk_bal_account_change_descriptor" => some ziskBalAccountChangeDescriptorProbeUnit
  | "zisk_bal_account_nth_descriptor" => some ziskBalAccountNthDescriptorProbeUnit
  | "zisk_bal_account_descriptor_array" => some ziskBalAccountDescriptorArrayProbeUnit
  | "zisk_bal_account_final_descriptor_array" => some ziskBalAccountFinalDescriptorArrayProbeUnit
  | "zisk_bal_account_state_root" => some ziskBalAccountStateRootProbeUnit
  | "zisk_bal_account_state_root_auto" => some ziskBalAccountStateRootAutoProbeUnit
  | "zisk_bal_account_record_array" => some ziskBalAccountRecordArrayProbeUnit | "zisk_tx_gas_sender_bal_lookup" => some ziskTxGasSenderBalLookupProbeUnit | "zisk_tx_gas_bal_post_verify" => some ziskTxGasBalPostVerifyProbeUnit
  | "zisk_storage_root_single_slot" => some ziskStorageRootSingleSlotProbeUnit
  | "zisk_account_set_storage_root" => some ziskAccountSetStorageRootProbeUnit
  | "zisk_block_access_list_hash" => some ziskBlockAccessListHashProbeUnit
  | "zisk_account_apply_storage_slot" => some ziskAccountApplyStorageSlotProbeUnit | "zisk_storage_effect_records_probe" => some ziskStorageEffectRecordsProbeUnit | "zisk_sstore_gas_refund_outcome" => some ziskSstoreGasRefundOutcomeProbeUnit
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
  | "zisk_block_validate_withdrawals_root_indexed" => some ziskBlockValidateWithdrawalsRootIndexedProbeUnit
  | "zisk_block_validate_receipts_root_indexed" => some ziskBlockValidateReceiptsRootIndexedProbeUnit
  | "zisk_block_validate_receipts_consensus_list" => some ziskBlockValidateReceiptsConsensusListProbeUnit
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
  | "zisk_eip2935_blockhash_lookup" => some ziskEip2935BlockhashLookupProbeUnit
  | "zisk_eip4788_beacon_root_lookup" => some ziskEip4788BeaconRootLookupProbeUnit
  | "zisk_witness_headers_chain_validate" => some ziskWitnessHeadersChainValidateProbeUnit
  | "zisk_witness_headers_min_block_number" => some ziskWitnessHeadersMinBlockNumberProbeUnit
  | "zisk_witness_headers_max_block_number" => some ziskWitnessHeadersMaxBlockNumberProbeUnit
  | "zisk_blockhash_opcode_windowed" => some ziskBlockhashOpcodeWindowedProbeUnit
  | "zisk_parent_header_matches_witness_first" => some ziskParentHeaderMatchesWitnessFirstProbeUnit
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
  | "zisk_intrinsic_gas_amsterdam_counts" => some ziskIntrinsicGasAmsterdamCountsProbeUnit
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
  | "zisk_ssz_pair_hash"        => some ziskSszPairHashProbeUnit
  | "zisk_ssz_zero_hashes"      => some ziskSszZeroHashesProbeUnit
  | "zisk_ssz_merkleize_pow2"   => some ziskSszMerkleizePow2ProbeUnit
  | "zisk_ssz_merkleize"        => some ziskSszMerkleizeProbeUnit
  | "zisk_ssz_pack_bytes"       => some ziskSszPackBytesProbeUnit
  | "zisk_ssz_hash_tree_root_bytes" => some ziskSszHashTreeRootBytesProbeUnit
  | "zisk_ssz_hash_tree_root_list_bytelist" => some ziskSszHashTreeRootListByteListProbeUnit
  | "zisk_ssz_hash_tree_root_execution_witness" => some ziskSszHashTreeRootExecutionWitnessProbeUnit
  | "zisk_header_nonce_at_block_hash" => some ziskHeaderNonceAtBlockHashProbeUnit
  | "zisk_extra_data_at_block_hash" => some ziskExtraDataAtBlockHashProbeUnit
  | "zisk_excess_blob_gas_at_block_hash" => some ziskExcessBlobGasAtBlockHashProbeUnit
  | "zisk_blob_gas_used_at_block_hash" => some ziskBlobGasUsedAtBlockHashProbeUnit
  | "zisk_blob_gas_pair_at_block_hash" => some ziskBlobGasPairAtBlockHashProbeUnit
  | "zisk_post_merge_invariants_at_block_hash" => some ziskPostMergeInvariantsAtBlockHashProbeUnit
  | "zisk_block_roots_at_block_hash" => some ziskBlockRootsAtBlockHashProbeUnit
  | "zisk_number_timestamp_pair_at_block_hash" => some ziskNumberTimestampPairAtBlockHashProbeUnit
  | "zisk_gas_pair_at_block_hash" => some ziskGasPairAtBlockHashProbeUnit
  | _                           => none


end EvmAsm.Codegen
