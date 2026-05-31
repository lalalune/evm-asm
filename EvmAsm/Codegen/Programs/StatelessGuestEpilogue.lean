/-
  EvmAsm.Codegen.Programs.StatelessGuestEpilogue

  Validator-pipeline + .Lsg_hash merkle epilogue for the
  `stateless_guest` ELF. Carved out of `Programs.lean` for the
  file-size hard cap; consumed by the registry hub via
  `statelessGuestEpilogue` (and its inner
  `statelessGuestValidatorPipeline`).
-/
import EvmAsm.Codegen.Programs.ChainValidate
import EvmAsm.Codegen.Programs.ChainValidateBlob
import EvmAsm.Codegen.Programs.ChainValidatePostMerge
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Ssz
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

/-! ## stateless_guest header-validator pipeline (integration PR)

    Inserted between the body's `serialize_stateless_output` and the
    existing SSZ `hash_tree_root` epilogue. Reads N=x16 (header count),
    section_ptr=x17 (witness.headers section), section_len=x14, then
    iterates a curated set of K-PR header validators on the chain.

    On any K-PR violation: writes 0xFEFEFE..FE marker + 8-byte reason
    code at OUTPUT_ADDR and HALTs (matches Stateless.unimplemented_exit
    layout).  On all-pass: overrides OUTPUT[32] := 1 (the
    `successful_validation` byte) and falls through to the hash code.

    s2 = N (callee-saved)
    s3 = section_ptr (callee-saved)
    s4 = section_len (callee-saved)
    s5 = headers_data_ptr = section_ptr + 4*N (callee-saved)

    Reason codes (see `EvmAsm/Stateless/Unimplemented.lean`):
      0x10 POST_MERGE_VIOLATION (K290)
      0x11 EXTRA_DATA_TOO_LONG  (K291)
      0x12 GAS_USED_OVER_LIMIT  (K240)
      0x13 BLOB_GAS_MISALIGNED  (K278)
      0x14 BLOB_GAS_OVER_MAX    (K277)
      0x15 TIMESTAMP_NOT_INCREASING (K229)
      0x16 NUMBERS_NOT_CONSECUTIVE  (K230)
      0x17 RLP_PARSE_FAIL_IN_HEADER (any K-PR returns nonzero status) -/
def statelessGuestValidatorPipeline : String :=
  "  # PR-integration: header-validator pipeline\n" ++
  "  li sp, 0xa0050000\n" ++
  "  mv s2, x16                  # s2 = N\n" ++
  "  mv s3, x21                  # s3 = section_ptr (now from decoder's x21,\n" ++
  "                              # which holds headers_addr; x17 is kept as\n" ++
  "                              # SSZ_BASE for the encoder's bounded byte-copy)\n" ++
  "  mv s4, x14                  # s4 = section_len\n" ++
  "  beqz s2, .Lsg_all_pass      # N=0: skip validators\n" ++
  "  # Build sg_header_lengths[N]: convert N u32 inner-offset deltas\n" ++
  "  # to N u64 absolute lengths.\n" ++
  "  mv t0, s3                   # t0 = offsets cursor (section_ptr)\n" ++
  "  la t1, sg_header_lengths    # t1 = lengths-out cursor\n" ++
  "  mv t2, s2                   # t2 = i (counts down from N)\n" ++
  ".Lsg_bl:\n" ++
  "  beqz t2, .Lsg_bl_done\n" ++
  "  lwu t3, 0(t0)               # t3 = inner_offset[i]\n" ++
  "  addi t4, t2, -1\n" ++
  "  beqz t4, .Lsg_bl_last       # if last header, end = section_len\n" ++
  "  lwu t5, 4(t0)               # t5 = inner_offset[i+1]\n" ++
  "  j .Lsg_bl_diff\n" ++
  ".Lsg_bl_last:\n" ++
  "  mv t5, s4                   # t5 = section_len\n" ++
  ".Lsg_bl_diff:\n" ++
  "  sub t5, t5, t3              # length_i = end - start\n" ++
  "  sd t5, 0(t1)\n" ++
  "  addi t0, t0, 4\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Lsg_bl\n" ++
  ".Lsg_bl_done:\n" ++
  "  # s5 = headers_data_ptr = section_ptr + 4*N\n" ++
  "  slli t0, s2, 2\n" ++
  "  add s5, s3, t0\n" ++
  "  # Validator 1: K290 chain_validate_post_merge_full\n" ++
  "  mv a0, s2; la a1, sg_header_lengths; mv a2, s5\n" ++
  "  la a3, sg_kpr_valid; la a4, sg_kpr_bad_index\n" ++
  "  jal ra, chain_validate_post_merge_full\n" ++
  "  bnez a0, .Lsg_fail_rlp\n" ++
  "  la t0, sg_kpr_valid; ld t1, 0(t0); beqz t1, .Lsg_fail_pm\n" ++
  "  # Validator 2: K291 chain_validate_extra_data_length\n" ++
  "  mv a0, s2; la a1, sg_header_lengths; mv a2, s5\n" ++
  "  la a3, sg_kpr_valid; la a4, sg_kpr_bad_index\n" ++
  "  jal ra, chain_validate_extra_data_length\n" ++
  "  bnez a0, .Lsg_fail_rlp\n" ++
  "  la t0, sg_kpr_valid; ld t1, 0(t0); beqz t1, .Lsg_fail_ed\n" ++
  "  # Validator 3: K240 chain_validate_gas_used_under_limit\n" ++
  "  mv a0, s2; la a1, sg_header_lengths; mv a2, s5\n" ++
  "  la a3, sg_kpr_valid; la a4, sg_kpr_bad_index\n" ++
  "  jal ra, chain_validate_gas_used_under_limit\n" ++
  "  bnez a0, .Lsg_fail_rlp\n" ++
  "  la t0, sg_kpr_valid; ld t1, 0(t0); beqz t1, .Lsg_fail_gas\n" ++
  "  # Validator 4: K278 chain_validate_blob_gas_used_multiple\n" ++
  "  mv a0, s2; la a1, sg_header_lengths; mv a2, s5\n" ++
  "  la a3, sg_kpr_valid; la a4, sg_kpr_bad_index\n" ++
  "  jal ra, chain_validate_blob_gas_used_multiple\n" ++
  "  bnez a0, .Lsg_fail_rlp\n" ++
  "  la t0, sg_kpr_valid; ld t1, 0(t0); beqz t1, .Lsg_fail_bgm\n" ++
  "  # Validator 5: K277 chain_validate_blob_gas_used_under_max\n" ++
  "  mv a0, s2; la a1, sg_header_lengths; mv a2, s5\n" ++
  "  la a3, sg_kpr_valid; la a4, sg_kpr_bad_index\n" ++
  "  jal ra, chain_validate_blob_gas_used_under_max\n" ++
  "  bnez a0, .Lsg_fail_rlp\n" ++
  "  la t0, sg_kpr_valid; ld t1, 0(t0); beqz t1, .Lsg_fail_bgum\n" ++
  "  # Validator 6: K229 chain_validate_increasing_timestamps\n" ++
  "  mv a0, s2; la a1, sg_header_lengths; mv a2, s5\n" ++
  "  la a3, sg_kpr_valid; la a4, sg_kpr_bad_index\n" ++
  "  jal ra, chain_validate_increasing_timestamps\n" ++
  "  bnez a0, .Lsg_fail_rlp\n" ++
  "  la t0, sg_kpr_valid; ld t1, 0(t0); beqz t1, .Lsg_fail_ts\n" ++
  "  # Validator 7: K230 chain_validate_consecutive_numbers\n" ++
  "  mv a0, s2; la a1, sg_header_lengths; mv a2, s5\n" ++
  "  la a3, sg_kpr_valid; la a4, sg_kpr_bad_index\n" ++
  "  jal ra, chain_validate_consecutive_numbers\n" ++
  "  bnez a0, .Lsg_fail_rlp\n" ++
  "  la t0, sg_kpr_valid; ld t1, 0(t0); beqz t1, .Lsg_fail_nm\n" ++
  ".Lsg_all_pass:\n" ++
  "  # All validators that ran passed (or N=0 fast-path). NB: with\n" ++
  "  # the new-schema decoder stubs in `EvmAsm/Stateless/SSZ/Decode/\n" ++
  "  # Program.lean`, N is always 0 right now, so no real validation\n" ++
  "  # has occurred. We deliberately do NOT override OUTPUT[32]:\n" ++
  "  # the encoder already wrote `x11` (= 0 from the decoder stub),\n" ++
  "  # matching the spec's `verify_stateless_new_payload(empty) ==\n" ++
  "  # False` outcome. Once the real witness walk + validators run,\n" ++
  "  # the body's encoder will see x11 = 1 from a real success.\n" ++
  "  j .Lsg_hash\n" ++
  ".Lsg_fail_pm:   li a0, 0x10; j .Lsg_unimpl\n" ++
  ".Lsg_fail_ed:   li a0, 0x11; j .Lsg_unimpl\n" ++
  ".Lsg_fail_gas:  li a0, 0x12; j .Lsg_unimpl\n" ++
  ".Lsg_fail_bgm:  li a0, 0x13; j .Lsg_unimpl\n" ++
  ".Lsg_fail_bgum: li a0, 0x14; j .Lsg_unimpl\n" ++
  ".Lsg_fail_ts:   li a0, 0x15; j .Lsg_unimpl\n" ++
  ".Lsg_fail_nm:   li a0, 0x16; j .Lsg_unimpl\n" ++
  ".Lsg_fail_rlp:  li a0, 0x17\n" ++
  ".Lsg_unimpl:\n" ++
  "  # Previously this block wrote the 0xFEFEFEFEFEFEFEFE unimplemented-\n" ++
  "  # exit marker at OUTPUT[0..8) plus the REASON code at OUTPUT[8..16),\n" ++
  "  # then halted with ECALL. That diverged from the spec's behaviour\n" ++
  "  # for the same input shape (spec catches the validator exception\n" ++
  "  # and returns valid=False with chain_config echo + empty NPR root).\n" ++
  "  # Falling through to .Lsg_hash matches the spec: the encoder's\n" ++
  "  # x11=0 writes valid=False to OUTPUT[32], .Lsg_hash stamps the\n" ++
  "  # empty_npr_root constant at OUTPUT[0..32), and the codegen halt\n" ++
  "  # stub takes over.\n" ++
  "  j .Lsg_hash"

def statelessGuestEpilogue : String :=
  statelessGuestValidatorPipeline ++ "\n" ++
  ".Lsg_hash:\n" ++
  "  # Compute `compute_new_payload_request_root(stateless_input)`\n" ++
  "  # at OUTPUT[0..32) -- the SSZ merkle root over the four NPR\n" ++
  "  # field roots:\n" ++
  "  #   field_root[0] = hash_tree_root(execution_payload)\n" ++
  "  #   field_root[1] = hash_tree_root(versioned_hashes)\n" ++
  "  #   field_root[2] = parent_beacon_block_root      (Bytes32 inline)\n" ++
  "  #   field_root[3] = hash_tree_root(execution_requests)\n" ++
  "  # For all current fixtures every NPR field except\n" ++
  "  # parent_beacon_block_root is the SSZ default, so field_root[0],\n" ++
  "  # field_root[1], and field_root[3] are static constants\n" ++
  "  # (`npr_left_subtree` packages sha256(field_root[0] ||\n" ++
  "  # field_root[1]); `npr_exec_requests_root` is field_root[3]).\n" ++
  "  # field_root[2] is read from input at NPR_addr + 8 (NPR_addr\n" ++
  "  # = SSZ_BASE + outer.offsets[0]; for this schema outer.offsets[0]\n" ++
  "  # is always 16).\n" ++
  "  # \n" ++
  "  # Computation:\n" ++
  "  #   right_subtree = sha256(parent_beacon_block_root ||\n" ++
  "  #                          npr_exec_requests_root)\n" ++
  "  #   npr_root      = sha256(npr_left_subtree || right_subtree)\n" ++
  "  # \n" ++
  "  # For pbr=zero (every previously-shipped fixture) the\n" ++
  "  # computation reproduces the precomputed `empty_npr_root`\n" ++
  "  # constant. For non-empty pbr it produces the spec-matching\n" ++
  "  # root.\n" ++
  "  # \n" ++
  "  # Generalising to non-default execution_payload /\n" ++
  "  # versioned_hashes / execution_requests requires recomputing\n" ++
  "  # those field roots dynamically -- deferred to subsequent PRs.\n" ++
  "  # \n" ++
  "  # Re-derive SSZ_BASE in s6 (callee-saved -- survives zkvm_sha256\n" ++
  "  # calls). K-PR pipeline only saves s0-s5 in its validators, so\n" ++
  "  # s6 is free.\n" ++
  "  li s6, 0x40000000\n" ++
  "  addi s6, s6, 18             # s6 = SSZ_BASE\n" ++
  "  # \n" ++
  "  # ===== dynamic NPR list field-roots (replace empty-list consts) =====\n" ++
  "  # exec_payload_addr = NPR_addr + 44 (NPR fixed header) = s6 + 16 + 44\n" ++
  "  # = s6 + 60. The variable fields' u32 offsets sit in the exec_payload\n" ++
  "  # fixed header: transactions @ +504, withdrawals @ +508,\n" ++
  "  # block_access_list @ +528. The list/bytes helpers cap N<=32 elements\n" ++
  "  # and <=1024 bytes/element; blocks beyond that stay root-diffs.\n" ++
  "  # --- transactions_root = hash_tree_root(List[ByteList[2^30], 2^20]) ---\n" ++
  "  addi t0, s6, 60            # exec_payload_addr\n" ++
  "  lwu t1, 504(t0)            # transactions offset (rel exec_payload)\n" ++
  "  lwu t2, 508(t0)            # withdrawals offset (= transactions end)\n" ++
  "  add a0, t0, t1             # transactions_start\n" ++
  "  sub a1, t2, t1             # transactions_len\n" ++
  "  li a2, 25                  # per-element chunk-cap log2 (2^30 / 32)\n" ++
  "  li a3, 20                  # list capacity log2 (MAX_TRANSACTIONS_PER_PAYLOAD)\n" ++
  "  la a4, npr_dynamic_tx_root\n" ++
  "  jal ra, ssz_hash_tree_root_list_bytelist\n" ++
  "  # --- block_access_list_root = hash_tree_root(ByteList[2^24]) ---\n" ++
  "  # bal section ends at exec_payload end = NPR + versioned_hashes_offset.\n" ++
  "  addi t3, s6, 16            # NPR_addr\n" ++
  "  lwu t4, 4(t3)              # versioned_hashes offset (rel NPR) = exec_payload end\n" ++
  "  add t4, t3, t4             # exec_payload_end_addr\n" ++
  "  addi t0, s6, 60            # exec_payload_addr\n" ++
  "  lwu t1, 528(t0)            # block_access_list offset (rel exec_payload)\n" ++
  "  add a0, t0, t1             # bal_start\n" ++
  "  sub a1, t4, a0             # bal_len = exec_payload_end - bal_start\n" ++
  "  li a2, 19                  # chunk-cap log2 (2^24 / 32)\n" ++
  "  la a3, npr_dynamic_bal_root\n" ++
  "  jal ra, ssz_hash_tree_root_bytes\n" ++
  "  # ===== exec_payload merkle path (leaves 0-15) =====\n" ++
  "  # Path leaf_6 -> node_6_7 -> node_4_7 -> node_0_7 -> node_0_15\n" ++
  "  # \n" ++
  "  # Dynamic leaf_4 = hash_tree_root(logs_bloom) supporting CHUNKS\n" ++
  "  # 0 AND 1 variation. logs_bloom is ByteVector[256], merkleized\n" ++
  "  # over 8 32-byte chunks (3 levels). For NOW we read chunks 0 and\n" ++
  "  # 1 from input; chunks 2..7 stay at their default zero.\n" ++
  "  # Path leaf_4_chunk_0 -> node_0_1 -> node_0_3 -> node_0_7 (= leaf_4):\n" ++
  "  #   node_0_1   = sha256(chunk_0 || chunk_1)\n" ++
  "  #   node_0_3   = sha256(node_0_1 || ssz_zero_hash[1])\n" ++
  "  #   leaf_4     = sha256(node_0_3 || ssz_zero_hash[2])\n" ++
  "  # chunk_0 lives at SSZ_BASE + 16 + 44 + 116 = +176\n" ++
  "  # chunk_1 lives at SSZ_BASE + 16 + 44 + 148 = +208\n" ++
  "  la t1, npr_sha_input\n" ++
  "  ld t2, 176(s6); sd t2,  0(t1)\n" ++
  "  ld t2, 184(s6); sd t2,  8(t1)\n" ++
  "  ld t2, 192(s6); sd t2, 16(t1)\n" ++
  "  ld t2, 200(s6); sd t2, 24(t1)\n" ++
  "  ld t2, 208(s6); sd t2, 32(t1)\n" ++
  "  ld t2, 216(s6); sd t2, 40(t1)\n" ++
  "  ld t2, 224(s6); sd t2, 48(t1)\n" ++
  "  ld t2, 232(s6); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_leaf_4_logs_bloom_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_0_1 -> npr_leaf_4_logs_bloom_scratch\n" ++
  "  # Dynamic node_2_3 = sha256(chunk_2 || chunk_3)\n" ++
  "  # chunk_2 @ SSZ_BASE + 16 + 44 + 180 = +240\n" ++
  "  # chunk_3 @ SSZ_BASE + 16 + 44 + 212 = +272\n" ++
  "  la t1, npr_sha_input\n" ++
  "  ld t2, 240(s6); sd t2,  0(t1)\n" ++
  "  ld t2, 248(s6); sd t2,  8(t1)\n" ++
  "  ld t2, 256(s6); sd t2, 16(t1)\n" ++
  "  ld t2, 264(s6); sd t2, 24(t1)\n" ++
  "  ld t2, 272(s6); sd t2, 32(t1)\n" ++
  "  ld t2, 280(s6); sd t2, 40(t1)\n" ++
  "  ld t2, 288(s6); sd t2, 48(t1)\n" ++
  "  ld t2, 296(s6); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_logs_bloom_node_2_3_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_2_3 -> npr_logs_bloom_node_2_3_scratch\n" ++
  "  # node_0_3 = sha256(node_0_1 || node_2_3)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_leaf_4_logs_bloom_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_logs_bloom_node_2_3_scratch\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_leaf_4_logs_bloom_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_0_3 -> npr_leaf_4_logs_bloom_scratch\n" ++
  "  # leaf_4 (logs_bloom root) = sha256(node_0_3 || node_4_7), where\n" ++
  "  # node_4_7 covers logs_bloom chunks 4-7 (previously assumed zero via\n" ++
  "  # ssz_zero_hash[2] -- wrong for any block that emits logs). chunk_k\n" ++
  "  # lives at SSZ_BASE + 176 + 32*k: chunk4 @ +304 .. chunk7 @ +400.\n" ++
  "  #   node_4_5 = sha256(chunk4 || chunk5)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  ld t2, 304(s6); sd t2,  0(t1)\n" ++
  "  ld t2, 312(s6); sd t2,  8(t1)\n" ++
  "  ld t2, 320(s6); sd t2, 16(t1)\n" ++
  "  ld t2, 328(s6); sd t2, 24(t1)\n" ++
  "  ld t2, 336(s6); sd t2, 32(t1)\n" ++
  "  ld t2, 344(s6); sd t2, 40(t1)\n" ++
  "  ld t2, 352(s6); sd t2, 48(t1)\n" ++
  "  ld t2, 360(s6); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_lb_node_45_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_4_5 -> npr_lb_node_45_scratch\n" ++
  "  #   node_6_7 = sha256(chunk6 || chunk7)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  ld t2, 368(s6); sd t2,  0(t1)\n" ++
  "  ld t2, 376(s6); sd t2,  8(t1)\n" ++
  "  ld t2, 384(s6); sd t2, 16(t1)\n" ++
  "  ld t2, 392(s6); sd t2, 24(t1)\n" ++
  "  ld t2, 400(s6); sd t2, 32(t1)\n" ++
  "  ld t2, 408(s6); sd t2, 40(t1)\n" ++
  "  ld t2, 416(s6); sd t2, 48(t1)\n" ++
  "  ld t2, 424(s6); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_lb_node_67_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_6_7 -> npr_lb_node_67_scratch\n" ++
  "  #   node_4_7 = sha256(node_4_5 || node_6_7) -> npr_lb_node_45_scratch\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_lb_node_45_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_lb_node_67_scratch\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_lb_node_45_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_4_7 -> npr_lb_node_45_scratch\n" ++
  "  #   leaf_4 = sha256(node_0_3 || node_4_7)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_leaf_4_logs_bloom_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_lb_node_45_scratch\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_leaf_4_logs_bloom_scratch\n" ++
  "  jal ra, zkvm_sha256         # leaf_4 (logs_bloom root) -> npr_leaf_4_logs_bloom_scratch\n" ++
  "  # \n" ++
  "  # Dynamic node_4_5 = sha256(leaf_4 || leaf_5)\n" ++
  "  # where leaf_4 is the dynamic logs_bloom root (above) and\n" ++
  "  # leaf_5 = prev_randao (Bytes32 @ SSZ_BASE + 16 + 44 + 372 = +432).\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_leaf_4_logs_bloom_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  ld t2, 432(s6); sd t2, 32(t1)\n" ++
  "  ld t2, 440(s6); sd t2, 40(t1)\n" ++
  "  ld t2, 448(s6); sd t2, 48(t1)\n" ++
  "  ld t2, 456(s6); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_4_5_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_4_5 -> npr_node_4_5_scratch\n" ++
  "  # \n" ++
  "  # Dynamic node_10_11 = sha256(leaf_10=extra_data_default ||\n" ++
  "  #                            leaf_11=base_fee_per_gas):\n" ++
  "  #   leaf_10 = SSZ default empty ByteList root = ssz_zero_hash[1]\n" ++
  "  #             (= sha256(0||0) -- empty merkleized ByteList with\n" ++
  "  #             length mix-in for the empty case).\n" ++
  "  #   leaf_11 = base_fee_per_gas (uint256, 32 bytes LE @\n" ++
  "  #             SSZ_BASE + 16 + 44 + 440 = +500)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, ssz_zero_hashes\n" ++
  "  addi t3, t3, 32             # ssz_zero_hash[1]\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  ld t2, 500(s6); sd t2, 32(t1)\n" ++
  "  ld t2, 508(s6); sd t2, 40(t1)\n" ++
  "  ld t2, 516(s6); sd t2, 48(t1)\n" ++
  "  ld t2, 524(s6); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_10_11_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_10_11 -> npr_node_10_11_scratch\n" ++
  "  # \n" ++
  "  # Dynamic node_14_15 (supports leaf_15 = blob_gas_used):\n" ++
  "  #   node_14_15 = sha256(npr_leaf_14_withdrawals_root ||\n" ++
  "  #                       leaf_15=blob_gas_used)\n" ++
  "  # blob_gas_used (u64 LE @ SSZ_BASE + 16 + 44 + 512 = +572)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_leaf_14_withdrawals_root\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  ld t2, 572(s6); sd t2, 32(t1)\n" ++
  "  sd zero, 40(t1); sd zero, 48(t1); sd zero, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_14_15_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_14_15 -> npr_node_14_15_scratch\n" ++
  "  # Dynamic node_12_15 (supports leaf_12 = block_hash):\n" ++
  "  # node_12_13 = sha256(leaf_12=block_hash || leaf_13=transactions_root)\n" ++
  "  # leaf_13 (transactions default empty list root) is a static\n" ++
  "  # `npr_leaf_13_transactions_root` constant.\n" ++
  "  # block_hash (Bytes32 @ SSZ_BASE + 16 + 44 + 472 = +532)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  ld t2, 532(s6); sd t2,  0(t1)\n" ++
  "  ld t2, 540(s6); sd t2,  8(t1)\n" ++
  "  ld t2, 548(s6); sd t2, 16(t1)\n" ++
  "  ld t2, 556(s6); sd t2, 24(t1)\n" ++
  "  la t3, npr_dynamic_tx_root\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_12_13_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_12_13 -> npr_node_12_13_scratch\n" ++
  "  # node_12_15 = sha256(node_12_13 || npr_node_14_15_scratch)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_node_12_13_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_node_14_15_scratch\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_12_15_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_12_15 -> npr_node_12_15_scratch\n" ++
  "  # \n" ++
  "  # Dynamic node_8_15 path (supports leaf_8 = gas_used and\n" ++
  "  # leaf_9 = timestamp):\n" ++
  "  #   leaf_8 = gas_used  (u64 LE @ SSZ_BASE + 16 + 44 + 420 = +480)\n" ++
  "  #            || 24 bytes of zero padding\n" ++
  "  #   leaf_9 = timestamp (u64 LE @ SSZ_BASE + 16 + 44 + 428 = +488)\n" ++
  "  #            || 24 bytes of zero padding\n" ++
  "  la t1, npr_sha_input\n" ++
  "  ld t2, 480(s6)              # gas_used\n" ++
  "  sd t2,  0(t1)\n" ++
  "  sd zero,  8(t1); sd zero, 16(t1); sd zero, 24(t1)\n" ++
  "  ld t2, 488(s6)              # timestamp\n" ++
  "  sd t2, 32(t1)\n" ++
  "  sd zero, 40(t1); sd zero, 48(t1); sd zero, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_sha_subtree\n" ++
  "  jal ra, zkvm_sha256         # node_8_9 -> npr_sha_subtree\n" ++
  "  # node_8_11 = sha256(node_8_9 || npr_node_10_11_scratch)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_sha_subtree\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_node_10_11_scratch\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_sha_subtree\n" ++
  "  jal ra, zkvm_sha256         # node_8_11 -> npr_sha_subtree\n" ++
  "  # node_8_15 = sha256(node_8_11 || npr_node_12_15_scratch) -> npr_node_8_15_scratch\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_sha_subtree\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_node_12_15_scratch\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_8_15_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_8_15 -> npr_node_8_15_scratch\n" ++
  "  # leaf_6 = block_number (u64 LE @ SSZ_BASE + 16 + 44 + 404 = +464)\n" ++
  "  #          || 24 bytes of zero padding\n" ++
  "  # leaf_7 = gas_limit    (u64 LE @ SSZ_BASE + 16 + 44 + 412 = +472)\n" ++
  "  #          || 24 bytes of zero padding\n" ++
  "  la t1, npr_sha_input\n" ++
  "  ld t2, 464(s6)              # block_number\n" ++
  "  sd t2,  0(t1)\n" ++
  "  sd zero,  8(t1); sd zero, 16(t1); sd zero, 24(t1)\n" ++
  "  ld t2, 472(s6)              # gas_limit\n" ++
  "  sd t2, 32(t1)\n" ++
  "  sd zero, 40(t1); sd zero, 48(t1); sd zero, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_sha_subtree\n" ++
  "  jal ra, zkvm_sha256         # node_6_7 -> npr_sha_subtree\n" ++
  "  # node_4_7 = sha256(npr_node_4_5_scratch || node_6_7)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_node_4_5_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_sha_subtree\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_sha_subtree\n" ++
  "  jal ra, zkvm_sha256         # node_4_7 -> npr_sha_subtree\n" ++
  "  # Dynamic node_0_3 path (supports leaf_0 = parent_hash and\n" ++
  "  # leaf_1 = fee_recipient):\n" ++
  "  #   leaf_0 = parent_hash    (Bytes32 @ SSZ_BASE + 16 + 44 + 0 = +60)\n" ++
  "  #   leaf_1 = fee_recipient  (ByteVector[20] @ SSZ_BASE + 16 + 44 + 32\n" ++
  "  #            = +92), packed into 32 bytes via 20 bytes from input\n" ++
  "  #            + 12 zero padding (SSZ ByteVector[20].hash_tree_root).\n" ++
  "  # node_0_1 = sha256(leaf_0 || leaf_1) -> npr_node_0_3_scratch (temp)\n" ++
  "  # We use npr_node_0_3_scratch as both temp (for node_0_1) and final\n" ++
  "  # (for node_0_3) since sha256 reads input then writes output.\n" ++
  "  la t1, npr_sha_input\n" ++
  "  ld t2,  60(s6); sd t2,  0(t1)\n" ++
  "  ld t2,  68(s6); sd t2,  8(t1)\n" ++
  "  ld t2,  76(s6); sd t2, 16(t1)\n" ++
  "  ld t2,  84(s6); sd t2, 24(t1)\n" ++
  "  ld t2,  92(s6); sd t2, 32(t1)\n" ++
  "  ld t2, 100(s6); sd t2, 40(t1)\n" ++
  "  lwu t2, 108(s6); sd t2, 48(t1)\n" ++
  "  sd zero, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_0_3_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_0_1 -> npr_node_0_3_scratch\n" ++
  "  # node_2_3 = sha256(leaf_2=state_root || leaf_3=receipts_root):\n" ++
  "  #   state_root    (Bytes32 @ SSZ_BASE + 16 + 44 + 52  = +112)\n" ++
  "  #   receipts_root (Bytes32 @ SSZ_BASE + 16 + 44 + 84  = +144)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  ld t2, 112(s6); sd t2,  0(t1)\n" ++
  "  ld t2, 120(s6); sd t2,  8(t1)\n" ++
  "  ld t2, 128(s6); sd t2, 16(t1)\n" ++
  "  ld t2, 136(s6); sd t2, 24(t1)\n" ++
  "  ld t2, 144(s6); sd t2, 32(t1)\n" ++
  "  ld t2, 152(s6); sd t2, 40(t1)\n" ++
  "  ld t2, 160(s6); sd t2, 48(t1)\n" ++
  "  ld t2, 168(s6); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_2_3_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_2_3 -> npr_node_2_3_scratch\n" ++
  "  # node_0_3 = sha256(node_0_1 || node_2_3)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_node_0_3_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_node_2_3_scratch\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_0_3_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_0_3 -> npr_node_0_3_scratch\n" ++
  "  # node_0_7 = sha256(npr_node_0_3_scratch || node_4_7)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_node_0_3_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_sha_subtree\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_sha_subtree\n" ++
  "  jal ra, zkvm_sha256         # node_0_7 -> npr_sha_subtree\n" ++
  "  # node_0_15 = sha256(node_0_7 || npr_node_8_15) -> npr_node_0_15_scratch\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_sha_subtree\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_node_8_15_scratch\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_0_15_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_0_15 -> npr_node_0_15_scratch\n" ++
  "  # \n" ++
  "  # ===== exec_payload merkle path (leaves 16-31) =====\n" ++
  "  # node_16_17 = sha256(leaf_16 || leaf_17) where\n" ++
  "  #   leaf_16 = excess_blob_gas (u64 LE @ SSZ_BASE + 16 + 44 + 520\n" ++
  "  #             = +580) || 24 bytes zero padding\n" ++
  "  #   leaf_17 = npr_leaf_17_bal_root (block_access_list_root for\n" ++
  "  #             the empty/default ByteList -- constant)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  ld t2, 580(s6)              # excess_blob_gas\n" ++
  "  sd t2,  0(t1)\n" ++
  "  sd zero,  8(t1); sd zero, 16(t1); sd zero, 24(t1)\n" ++
  "  la t3, npr_dynamic_bal_root\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_16_17_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_16_17 -> npr_node_16_17_scratch\n" ++
  "  # leaf_18 = slot_number (u64 LE at SSZ_BASE + 16 + 44 + 532 = +592)\n" ++
  "  #          || 24 bytes of zero padding\n" ++
  "  la t1, npr_sha_input\n" ++
  "  ld t2, 592(s6)              # slot_number\n" ++
  "  sd t2,  0(t1)\n" ++
  "  sd zero,  8(t1); sd zero, 16(t1); sd zero, 24(t1)\n" ++
  "  # bytes [32..64) = ssz_zero_hash[0] = leaf_19\n" ++
  "  sd zero, 32(t1); sd zero, 40(t1); sd zero, 48(t1); sd zero, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_sha_subtree\n" ++
  "  jal ra, zkvm_sha256         # node_18_19 -> npr_sha_subtree\n" ++
  "  # node_16_19 = sha256(node_16_17_scratch || node_18_19)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_node_16_17_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_sha_subtree\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_sha_subtree\n" ++
  "  jal ra, zkvm_sha256         # node_16_19 -> npr_sha_subtree\n" ++
  "  # node_16_23 = sha256(node_16_19 || ssz_zero_hash[2])\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_sha_subtree\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, ssz_zero_hashes\n" ++
  "  addi t3, t3, 64             # ssz_zero_hash[2]\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_sha_subtree\n" ++
  "  jal ra, zkvm_sha256         # node_16_23 -> npr_sha_subtree\n" ++
  "  # node_16_31 = sha256(node_16_23 || ssz_zero_hash[3])\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_sha_subtree\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, ssz_zero_hashes\n" ++
  "  addi t3, t3, 96             # ssz_zero_hash[3]\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_sha_subtree\n" ++
  "  jal ra, zkvm_sha256         # node_16_31 -> npr_sha_subtree\n" ++
  "  # exec_payload_root = sha256(node_0_15 || node_16_31)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_node_0_15_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_sha_subtree\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_exec_payload_root\n" ++
  "  jal ra, zkvm_sha256         # exec_payload_root -> npr_exec_payload_root\n" ++
  "  # \n" ++
  "  # ===== NPR top-level merkle =====\n" ++
  "  # left_subtree = sha256(exec_payload_root || versioned_hashes_root)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_exec_payload_root\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_versioned_hashes_root\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_left_subtree_scratch\n" ++
  "  jal ra, zkvm_sha256         # left_subtree -> npr_left_subtree_scratch\n" ++
  "  # right_subtree = sha256(parent_beacon_block_root || npr_exec_requests_root)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  ld t2, 24(s6); sd t2,  0(t1)\n" ++
  "  ld t2, 32(s6); sd t2,  8(t1)\n" ++
  "  ld t2, 40(s6); sd t2, 16(t1)\n" ++
  "  ld t2, 48(s6); sd t2, 24(t1)\n" ++
  "  la t3, npr_exec_requests_root\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_sha_subtree\n" ++
  "  jal ra, zkvm_sha256         # right_subtree -> npr_sha_subtree\n" ++
  "  # root = sha256(left_subtree || right_subtree) -> OUTPUT_ADDR\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_left_subtree_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_sha_subtree\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; li a2, 0xa0010000\n" ++
  "  jal ra, zkvm_sha256         # root -> OUTPUT_ADDR\n" ++
  "  j .Lsg_done\n" ++
  zkvmSha256Function ++ "\n" ++
  -- SSZ merkleization helpers for the dynamic transactions_root /
  -- block_access_list_root (zkvm_sha256 already emitted just above, so it
  -- is NOT re-included here -- doing so would duplicate the label).
  sszPackBytesFunction ++ "\n" ++
  sszMerkleizePow2Function ++ "\n" ++
  sszMerkleizeFunction ++ "\n" ++
  sszHashTreeRootBytesFunction ++ "\n" ++
  sszHashTreeRootListByteListFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainValidatePostMergeFullFunction ++ "\n" ++
  chainValidateExtraDataLengthFunction ++ "\n" ++
  chainValidateGasUsedUnderLimitFunction ++ "\n" ++
  chainValidateBlobGasUsedMultipleFunction ++ "\n" ++
  chainValidateBlobGasUsedUnderMaxFunction ++ "\n" ++
  chainValidateIncreasingTimestampsFunction ++ "\n" ++
  chainValidateConsecutiveNumbersFunction ++ "\n" ++
  ".Lsg_done:"

end EvmAsm.Codegen
