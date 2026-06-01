/-
  EvmAsm.Codegen.Programs.BlockVerdict

  Step (d) of bead evm-asm-fhsxz.2.4.2.5 — the FULL state-transition verdict that
  composes the EIP-2935 + EIP-4788 system-contract storage writes with the
  withdrawal balance credits into ONE post-state-root recompute. This is what
  turns the verified bricks into actual EEST withdrawal full-matches.

    block_state_root: system_write_descriptors -> for each of the 2 system
      contracts: walk the pre-state account, account_apply_storage_slot, record a
      state-trie change; then the withdrawal changes (walk + account_add_balance);
      then mpt_state_root over ALL changes -> post-state root.
    block_verdict: block_header_ssz_to_rlp + validate_header_rlp_pair +
      block_state_root + memcmp(recomputed, payload.state_root).
    stateless_verdict_v2: the real-SSZ glue (= stateless_verdict_from_ssz) but
      calling block_verdict (system writes included) instead of step2_verdict.

  Conservative throughout: any walk miss / non-empty-storage system contract /
  insert-needed withdrawal -> status != 0 -> verdict 0 (a MISS, never a false
  positive). Reuses the stateless_verdict asm closure + data verbatim and adds the
  StorageWrite / SystemWrites / single_leaf functions.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.MptEncode
import EvmAsm.Codegen.Programs.StorageWrite
import EvmAsm.Codegen.Programs.SystemWrites
import EvmAsm.Codegen.Programs.AccountApplyStorage
import EvmAsm.Codegen.Programs.StatelessVerdict

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bsr_sys_change -- record one system-contract storage-write change.
    a0 = contract addr ptr (20 B)   a1 = slot_key ptr (32 B)
    a2 = value ptr   a3 = value len   a4 = change index
    Reads shared state from bsr_root_p / bsr_wit_p / bsr_wl_v; writes the change
    entry at bsr_changes[index]. a0 (output) = 0 ok / 1 conservative. -/
def bsrSysChangeFunction : String :=
  "bsr_sys_change:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  # keccak(addr, 20) -> bsr_kbuf\n" ++
  "  mv a0, s0; li a1, 20; la a2, bsr_kbuf; jal ra, zkvm_keccak256\n" ++
  "  # path = bsr_paths + 64*index; bytes_to_nibbles(bsr_kbuf, 32, path)\n" ++
  "  slli t0, s4, 6; la t1, bsr_paths; add t2, t1, t0\n" ++
  "  la t3, bsr_pathp; sd t2, 0(t3)              # stash path ptr\n" ++
  "  la a0, bsr_kbuf; li a1, 32; mv a2, t2; jal ra, bytes_to_nibbles\n" ++
  "  # mpt_walk(root, witness, wlen, path, 64, bsr_acct, bsr_acct_len)\n" ++
  "  la t0, bsr_root_p; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0)\n" ++
  "  la t0, bsr_pathp; ld a3, 0(t0); li a4, 64; la a5, bsr_acct; la a6, bsr_acct_len\n" ++
  "  jal ra, mpt_walk\n" ++
  "  bnez a0, .Lbsc_fail\n" ++
  "  # account_apply_storage_slot(acct, len, slot, val, vlen, newacct, bsr_tmplen)\n" ++
  "  la a0, bsr_acct; la t0, bsr_acct_len; ld a1, 0(t0); mv a2, s1; mv a3, s2; mv a4, s3\n" ++
  "  slli t0, s4, 7; la t1, bsr_newaccts; add a5, t1, t0; la a6, bsr_tmplen\n" ++
  "  jal ra, account_apply_storage_slot\n" ++
  "  bnez a0, .Lbsc_fail\n" ++
  "  # record change[index] = (path, 64, newacct, tmplen)\n" ++
  "  slli t0, s4, 5; la t1, bsr_changes; add t1, t1, t0\n" ++
  "  la t2, bsr_pathp; ld t2, 0(t2); sd t2, 0(t1); li t3, 64; sd t3, 8(t1)\n" ++
  "  slli t0, s4, 7; la t2, bsr_newaccts; add t2, t2, t0; sd t2, 16(t1)\n" ++
  "  la t2, bsr_tmplen; ld t2, 0(t2); sd t2, 24(t1)\n" ++
  "  li a0, 0; j .Lbsc_ret\n" ++
  ".Lbsc_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbsc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-! ## block_state_root -- post-state root after system writes + withdrawals.
    a0 = pre-state root ptr   a1 = witness   a2 = witness_len
    a3 = wds descriptors   a4 = n_wds   a5 = out_root   a6 = SSZ_BASE
    a0 (output) = 0 ok / 1 conservative (any miss / unsupported case). -/
def blockStateRootFunction : String :=
  "block_state_root:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s3, 24(sp); sd s4, 32(sp); sd s5, 40(sp)\n" ++
  "  la t0, bsr_root_p; sd a0, 0(t0)\n" ++
  "  la t0, bsr_wit_p;  sd a1, 0(t0)\n" ++
  "  la t0, bsr_wl_v;   sd a2, 0(t0)\n" ++
  "  mv s3, a3                   # wds descriptors\n" ++
  "  mv s4, a4                   # n_wds\n" ++
  "  mv s5, a5                   # out_root\n" ++
  "  # derive the system writes (SSZ_BASE in a6)\n" ++
  "  mv a0, a6; jal ra, system_write_descriptors\n" ++
  "  # system change 0 = EIP-2935\n" ++
  "  la a0, bsr_addr_2935; la a1, swd_2935_slot; la a2, swd_2935_val\n" ++
  "  la t0, swd_2935_vlen; ld a3, 0(t0); li a4, 0\n" ++
  "  jal ra, bsr_sys_change; bnez a0, .Lbsr_cons\n" ++
  "  # system change 1 = EIP-4788\n" ++
  "  la a0, bsr_addr_4788; la a1, swd_4788_slot; la a2, swd_4788_val\n" ++
  "  la t0, swd_4788_vlen; ld a3, 0(t0); li a4, 1\n" ++
  "  jal ra, bsr_sys_change; bnez a0, .Lbsr_cons\n" ++
  "  # withdrawal changes at index 2..2+n_wds\n" ++
  "  li s0, 0\n" ++
  ".Lbsr_wl:\n" ++
  "  beq s0, s4, .Lbsr_apply\n" ++
  "  addi s1, s0, 2               # change index\n" ++
  "  slli t0, s0, 4; add t0, s3, t0; ld a0, 0(t0); ld a1, 8(t0)   # wd[i] rlp ptr/len\n" ++
  "  slli t1, s1, 6; la t2, bsr_paths; add a2, t2, t1; la a3, bsr_delta\n" ++
  "  jal ra, withdrawal_to_path_delta; bnez a0, .Lbsr_cons\n" ++
  "  la t0, bsr_root_p; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0)\n" ++
  "  slli t1, s1, 6; la t2, bsr_paths; add a3, t2, t1; li a4, 64; la a5, bsr_acct; la a6, bsr_acct_len\n" ++
  "  jal ra, mpt_walk; bnez a0, .Lbsr_cons\n" ++
  "  la a0, bsr_acct; la t0, bsr_acct_len; ld a1, 0(t0); la a2, bsr_delta\n" ++
  "  slli t1, s1, 7; la t2, bsr_newaccts; add a3, t2, t1; la a4, bsr_tmplen\n" ++
  "  jal ra, account_add_balance; bnez a0, .Lbsr_cons\n" ++
  "  slli t0, s1, 5; la t1, bsr_changes; add t1, t1, t0\n" ++
  "  slli t2, s1, 6; la t3, bsr_paths; add t3, t3, t2; sd t3, 0(t1); li t3, 64; sd t3, 8(t1)\n" ++
  "  slli t2, s1, 7; la t3, bsr_newaccts; add t3, t3, t2; sd t3, 16(t1)\n" ++
  "  la t3, bsr_tmplen; ld t3, 0(t3); sd t3, 24(t1)\n" ++
  "  addi s0, s0, 1; j .Lbsr_wl\n" ++
  ".Lbsr_apply:\n" ++
  "  la t0, bsr_root_p; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0)\n" ++
  "  la a3, bsr_changes; addi a4, s4, 2; mv a5, s5\n" ++
  "  jal ra, mpt_state_root\n" ++
  "  j .Lbsr_ret\n" ++
  ".Lbsr_cons:\n" ++
  "  li a0, 1\n" ++
  ".Lbsr_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s3, 24(sp); ld s4, 32(sp); ld s5, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-! ## block_verdict -- step2_verdict with the FULL (system + withdrawal) recompute.
    a0 = params ptr (the step2_verdict struct)   a1 = SSZ_BASE
    a0 (output) = verdict bit. -/
def blockVerdictFunction : String :=
  "block_verdict:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # params\n" ++
  "  mv s3, a1                   # SSZ_BASE\n" ++
  "  ld a0, 0(s0); ld a1, 32(s0); ld a2, 40(s0); ld a3, 48(s0); ld a4, 56(s0)\n" ++
  "  la a5, sv_this_rlp; la a6, sv_this_rlp_len\n" ++
  "  jal ra, block_header_ssz_to_rlp\n" ++
  "  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0); ld a2, 8(s0); ld a3, 16(s0)\n" ++
  "  jal ra, validate_header_rlp_pair\n" ++
  "  mv s1, a0\n" ++
  "  ld a0, 24(s0); ld a1, 80(s0); ld a2, 88(s0); ld a3, 64(s0); ld a4, 72(s0)\n" ++
  "  la a5, sv_recomputed; mv a6, s3\n" ++
  "  jal ra, block_state_root\n" ++
  "  mv s2, a0\n" ++
  "  la t0, sv_recomputed; ld t1, 0(s0); addi t1, t1, 52; li t2, 32\n" ++
  ".Lbv_cmp:\n" ++
  "  beqz t2, .Lbv_cmpok\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbv_zero\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbv_cmp\n" ++
  ".Lbv_cmpok:\n" ++
  "  bnez s1, .Lbv_zero\n" ++
  "  bnez s2, .Lbv_zero\n" ++
  "  li a0, 1; j .Lbv_ret\n" ++
  ".Lbv_zero:\n" ++
  "  li a0, 0\n" ++
  ".Lbv_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-! ## stateless_verdict_v2 -- real-SSZ glue calling block_verdict (system writes). -/
def statelessVerdictV2Function : String :=
  "stateless_verdict_v2:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  li s0, 0x40000000\n" ++
  "  addi s0, s0, 18\n" ++
  "  mv a0, s0; la a1, svf_payload; la a2, svf_wds_ptr; la a3, svf_wds_count\n" ++
  "  jal ra, extract_payload_and_withdrawals\n" ++
  "  mv a0, s0; la a1, svf_witness; la a2, svf_witness_len\n" ++
  "  jal ra, extract_witness_state_section\n" ++
  "  mv a0, s0; la t0, svf_payload; ld a1, 0(t0)\n" ++
  "  la a2, svf_parent_rlp; la a3, svf_parent_rlp_len; la a4, svf_parent_sr\n" ++
  "  jal ra, extract_parent_header_and_state_root\n" ++
  "  bnez a0, .Lv2_zero\n" ++
  "  la t0, svf_wds_count; ld s1, 0(t0)\n" ++
  "  la t0, svf_wds_ptr;   ld s2, 0(t0)\n" ++
  "  la s3, svf_descriptors\n" ++
  "  la s4, svf_rlp_arena\n" ++
  "  li s5, 0\n" ++
  ".Lv2_wl:\n" ++
  "  bge s5, s1, .Lv2_wd\n" ++
  "  mv a0, s2; mv a1, s4; la a2, svf_wd_len\n" ++
  "  jal ra, ssz_withdrawal_to_rlp\n" ++
  "  sd s4, 0(s3); la t0, svf_wd_len; ld t1, 0(t0); sd t1, 8(s3)\n" ++
  "  addi s2, s2, 44; addi s4, s4, 72; addi s3, s3, 16; addi s5, s5, 1; j .Lv2_wl\n" ++
  ".Lv2_wd:\n" ++
  "  la t1, sv_params\n" ++
  "  la t0, svf_payload;        ld t0, 0(t0); sd t0, 0(t1)\n" ++
  "  la t0, svf_parent_rlp;     ld t0, 0(t0); sd t0, 8(t1)\n" ++
  "  la t0, svf_parent_rlp_len; ld t0, 0(t0); sd t0, 16(t1)\n" ++
  "  la t0, svf_parent_sr;      sd t0, 24(t1)\n" ++
  "  la t0, svf_zero32;         sd t0, 32(t1)\n" ++
  "  la t0, svf_zero32;         sd t0, 40(t1)\n" ++
  "  addi t0, s0, 24;           sd t0, 48(t1)\n" ++
  "  la t0, svf_zero32;         sd t0, 56(t1)\n" ++
  "  la t0, svf_descriptors;    sd t0, 64(t1)\n" ++
  "  la t0, svf_wds_count;      ld t0, 0(t0); sd t0, 72(t1)\n" ++
  "  la t0, svf_witness;        ld t0, 0(t0); sd t0, 80(t1)\n" ++
  "  la t0, svf_witness_len;    ld t0, 0(t0); sd t0, 88(t1)\n" ++
  "  la a0, sv_params; mv a1, s0\n" ++
  "  jal ra, block_verdict\n" ++
  "  j .Lv2_ret\n" ++
  ".Lv2_zero:\n" ++
  "  li a0, 0\n" ++
  ".Lv2_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_stateless_verdict_v2`: probe. Fed the SAME `-i` input as the guest.
    Output OUTPUT+0 = verdict bit (system writes + withdrawals modeled). -/
def ziskStatelessVerdictV2Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  jal ra, stateless_verdict_v2\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)            # OUTPUT+0 = verdict bit\n" ++
  "  j .Lv2_pdone\n" ++
  -- the full stateless_verdict closure (verbatim):
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256DivU64BeFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  u256EqFunction ++ "\n" ++
  withdrawalDecodeFunction ++ "\n" ++
  withdrawalToPathDeltaFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  accountAddBalanceFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  nodeDbAppendFunction ++ "\n" ++
  nodeDbLookupFunction ++ "\n" ++
  mptNodeResolveFunction ++ "\n" ++
  mptSetRecordWalkDbFunction ++ "\n" ++
  mptSetAccFunction ++ "\n" ++
  mptStateRootFunction ++ "\n" ++
  withdrawalsStateRootFunction ++ "\n" ++
  validateHeaderBasicFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  headerValidatePostMergeFunction ++ "\n" ++
  headerValidateExtraDataLengthFunction ++ "\n" ++
  eip1559CalcBaseFeePerGasFunction ++ "\n" ++
  headerValidateBaseFeeFunction ++ "\n" ++
  validateHeaderFullFunction ++ "\n" ++
  headerExtendedDecodeFunction ++ "\n" ++
  headersParentHashFunction ++ "\n" ++
  headerValidateParentHashFunction ++ "\n" ++
  validateHeaderRlpPairFunction ++ "\n" ++
  bhrRevLeBeFunction ++ "\n" ++
  blockHeaderSszToRlpFunction ++ "\n" ++
  step2VerdictFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  ephU32leFunction ++ "\n" ++
  extractParentHeaderAndStateRootFunction ++ "\n" ++
  spwU32leFunction ++ "\n" ++
  extractPayloadAndWithdrawalsFunction ++ "\n" ++
  swsU32leFunction ++ "\n" ++
  extractWitnessStateSectionFunction ++ "\n" ++
  swrRevLeBeFunction ++ "\n" ++
  sszWithdrawalToRlpFunction ++ "\n" ++
  statelessVerdictFromSszFunction ++ "\n" ++
  -- NEW: single_leaf + storage + system + block verdict:
  singleLeafTrieRootFunction ++ "\n" ++
  storageRootSingleSlotFunction ++ "\n" ++
  accountSetStorageRootFunction ++ "\n" ++
  accountApplyStorageSlotFunction ++ "\n" ++
  swdReadU64leFunction ++ "\n" ++
  swdWriteBe32U64Function ++ "\n" ++
  swdWriteBe8Function ++ "\n" ++
  swdMinimalCopyFunction ++ "\n" ++
  systemWriteDescriptorsFunction ++ "\n" ++
  bsrSysChangeFunction ++ "\n" ++
  blockStateRootFunction ++ "\n" ++
  blockVerdictFunction ++ "\n" ++
  statelessVerdictV2Function ++ "\n" ++
  ".Lv2_pdone:"

def ziskStatelessVerdictV2DataSection : String :=
  ziskStatelessVerdictDataSection ++ "\n" ++
  -- single_leaf scratch:
  ".balign 8\n" ++
  "sltr_field_len:\n  .zero 8\n" ++
  "sltr_nibble_count:\n  .zero 8\n" ++
  "sltr_hp_len:\n  .zero 8\n" ++
  "sltr_cursor:\n  .zero 8\n" ++
  "sltr_total_payload:\n  .zero 8\n" ++
  "sltr_nibbles:\n  .zero 2048\n" ++
  "sltr_hp_buf:\n  .zero 1024\n" ++
  "sltr_payload_buf:\n  .zero 16384\n" ++
  "sltr_node_buf:\n  .zero 16384\n" ++
  ".balign 32\n" ++
  "srss_key:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "srss_rlpval:\n  .zero 40\n" ++
  "srss_rlpval_len:\n  .zero 8\n" ++
  "asr_ref:\n  .zero 40\n" ++
  "aps_off:\n  .zero 8\n" ++
  "aps_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "aps_newsroot:\n  .zero 32\n" ++
  "aps_empty_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21\n" ++
  -- system_write_descriptors output:
  ".balign 32\n" ++
  "swd_2935_slot:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_2935_val:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_4788_slot:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_4788_val:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "swd_2935_vlen:\n  .zero 8\n" ++
  "swd_4788_vlen:\n  .zero 8\n" ++
  "swd_ts_be8:\n  .zero 8\n" ++
  -- block_state_root scratch:
  ".balign 8\n" ++
  "bsr_root_p:\n  .zero 8\n" ++
  "bsr_wit_p:\n  .zero 8\n" ++
  "bsr_wl_v:\n  .zero 8\n" ++
  "bsr_pathp:\n  .zero 8\n" ++
  "bsr_acct_len:\n  .zero 8\n" ++
  "bsr_tmplen:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bsr_kbuf:\n  .zero 32\n" ++
  "bsr_delta:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bsr_acct:\n  .zero 256\n" ++
  "bsr_paths:\n  .zero 1152\n" ++
  "bsr_newaccts:\n  .zero 2304\n" ++
  "bsr_changes:\n  .zero 576\n" ++
  ".balign 32\n" ++
  "bsr_addr_2935:\n" ++
  "  .byte 0x00, 0x00, 0xF9, 0x08, 0x27, 0xF1, 0xC5, 0x3a\n" ++
  "  .byte 0x10, 0xcb, 0x7A, 0x02, 0x33, 0x5B, 0x17, 0x53\n" ++
  "  .byte 0x20, 0x00, 0x29, 0x35\n" ++
  ".balign 32\n" ++
  "bsr_addr_4788:\n" ++
  "  .byte 0x00, 0x0F, 0x3d, 0xf6, 0xD7, 0x32, 0x80, 0x7E\n" ++
  "  .byte 0xf1, 0x31, 0x9f, 0xB7, 0xB8, 0xbB, 0x85, 0x22\n" ++
  "  .byte 0xd0, 0xBe, 0xac, 0x02"

def ziskStatelessVerdictV2ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskStatelessVerdictV2Prologue
  dataAsm     := ziskStatelessVerdictV2DataSection
}

end EvmAsm.Codegen
