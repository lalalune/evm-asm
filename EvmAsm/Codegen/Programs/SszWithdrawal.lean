/-
  EvmAsm.Codegen.Programs.SszWithdrawal

  ssz_withdrawal_to_rlp (bead evm-asm-fhsxz.2.4.2.1): bridge an SSZ Withdrawal
  to the withdrawal RLP that the Step-2 recompute consumes. The guest's
  ExecutionPayload carries withdrawals as fixed-size SSZ containers
    Withdrawal { index: uint64, validator_index: uint64,
                 address: Bytes20, amount: uint64 }   -- 44 bytes
  but `withdrawals_state_root` (via `withdrawal_decode`) consumes withdrawal
  RLP `rlp([index, validator_index, address, amount])`. This is the missing
  glue for wiring the verdict (.2.4.2) to the real SSZ guest input.

  Independent of the MPT engine — composes only the RLP encoders on main. u64
  fields are read byte-wise (LE) and reversed to big-endian (no-misaligned
  invariant: amount sits at offset 36 ≡ 4 mod 8), then encoded minimal via
  rlp_encode_uint_be; the address goes through rlp_encode_bytes.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## swr_rev_le_be -- reverse `len` little-endian bytes to big-endian
    (local copy; a0 = src, a1 = len, a2 = dst; leaf). -/
def swrRevLeBeFunction : String :=
  "swr_rev_le_be:\n" ++
  "  add t0, a0, a1\n" ++
  "  mv t1, a2\n" ++
  "  mv t2, a1\n" ++
  ".Lswrrev_loop:\n" ++
  "  beqz t2, .Lswrrev_done\n" ++
  "  addi t0, t0, -1\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1)\n" ++
  "  addi t1, t1, 1; addi t2, t2, -1\n" ++
  "  j .Lswrrev_loop\n" ++
  ".Lswrrev_done:\n" ++
  "  ret"

/-- `ssz_withdrawal_to_rlp`.
    a0 = SSZ Withdrawal ptr (44 bytes), a1 = out RLP buffer ptr,
    a2 = u64 out length ptr.  a0 (output) = 0. -/
def sszWithdrawalToRlpFunction : String :=
  "ssz_withdrawal_to_rlp:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # ssz withdrawal\n" ++
  "  mv s1, a1                   # out\n" ++
  "  mv s2, a2                   # out_len\n" ++
  "  li s3, 0                    # payload cursor\n" ++
  "  # field 0: index (u64 LE @0)\n" ++
  "  addi a0, s0, 0; li a1, 8; la a2, swr_be\n" ++
  "  jal ra, swr_rev_le_be\n" ++
  "  la a0, swr_be; li a1, 8; la a2, swr_payload; add a2, a2, s3\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  add s3, s3, a0\n" ++
  "  # field 1: validator_index (u64 LE @8)\n" ++
  "  addi a0, s0, 8; li a1, 8; la a2, swr_be\n" ++
  "  jal ra, swr_rev_le_be\n" ++
  "  la a0, swr_be; li a1, 8; la a2, swr_payload; add a2, a2, s3\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  add s3, s3, a0\n" ++
  "  # field 2: address (20 B @16)\n" ++
  "  addi a0, s0, 16; li a1, 20\n" ++
  "  la a2, swr_payload; add a2, a2, s3; la a3, swr_flen\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, swr_flen; ld t1, 0(t0); add s3, s3, t1\n" ++
  "  # field 3: amount (u64 LE @36)\n" ++
  "  addi a0, s0, 36; li a1, 8; la a2, swr_be\n" ++
  "  jal ra, swr_rev_le_be\n" ++
  "  la a0, swr_be; li a1, 8; la a2, swr_payload; add a2, a2, s3\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  add s3, s3, a0\n" ++
  "  # list prefix + copy payload after it\n" ++
  "  mv a0, s3; mv a1, s1; la a2, swr_prefix_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  la t0, swr_prefix_len; ld t1, 0(t0)\n" ++
  "  add t2, s1, t1; la t3, swr_payload; mv t4, s3\n" ++
  ".Lswr_cp:\n" ++
  "  beqz t4, .Lswr_cpd\n" ++
  "  lbu t5, 0(t3); sb t5, 0(t2)\n" ++
  "  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1\n" ++
  "  j .Lswr_cp\n" ++
  ".Lswr_cpd:\n" ++
  "  add t1, t1, s3; sd t1, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_ssz_withdrawal_to_rlp`: probe.
    Input: bytes 8.. = the 44-byte SSZ Withdrawal.
    Output: OUTPUT+0 = RLP length (u64); OUTPUT+8 = withdrawal RLP bytes. -/
def ziskSszWithdrawalToRlpPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  addi a0, t0, 8              # SSZ withdrawal ptr\n" ++
  "  li a1, 0xa0010008           # out at OUTPUT+8\n" ++
  "  li a2, 0xa0010000           # out_len at OUTPUT+0\n" ++
  "  jal ra, ssz_withdrawal_to_rlp\n" ++
  "  j .Lswr_pdone\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  swrRevLeBeFunction ++ "\n" ++
  sszWithdrawalToRlpFunction ++ "\n" ++
  ".Lswr_pdone:"

def ziskSszWithdrawalToRlpDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "swr_flen:\n  .zero 8\n" ++
  "swr_prefix_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "swr_be:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "swr_payload:\n  .zero 128"

def ziskSszWithdrawalToRlpProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszWithdrawalToRlpPrologue
  dataAsm     := ziskSszWithdrawalToRlpDataSection
}

end EvmAsm.Codegen
