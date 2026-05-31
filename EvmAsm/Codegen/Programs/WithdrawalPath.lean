/-
  EvmAsm.Codegen.Programs.WithdrawalPath

  withdrawal_to_path_delta (bead evm-asm-fhsxz.2.2.1): the non-engine
  preprocessing half of the withdrawal-driven post-state-root recompute
  (.2.2). Given a Shanghai+ withdrawal RLP `rlp([index, validator_index,
  address, amount])`, produce the two things the state-trie update needs:

    * path  = bytes_to_nibbles(keccak256(address))   -- 64 nibbles, the
              account's key path in the world-state trie;
    * delta = amount_gwei * 1e9                       -- 32-byte big-endian
              wei credit to add to the account balance.

  Composes only already-merged, tested helpers: withdrawal_decode
  (Programs/Withdrawal.lean), zkvm_keccak256 (HashBridge), bytes_to_nibbles
  (Programs/Mpt.lean), u256_from_u64_be + u256_mul_u64_be (Programs/U256.lean).

  The full .2.2 then loops: withdrawal_to_path_delta -> mpt_walk (read the
  current account) -> account_add_balance(delta) -> change list -> mpt_state_root
  (those parts wait on the MPT-engine PRs #7743/#7744). This piece is
  independent and verified now. All multi-byte work is on 8-aligned scratch;
  address/hash bytes are read byte-wise (no-misaligned invariant).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.Withdrawal

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## withdrawal_to_path_delta -- withdrawal RLP -> (trie path, wei delta)

    a0 = withdrawal RLP ptr        a1 = withdrawal RLP length
    a2 = out path ptr (64 bytes, one nibble each)
    a3 = out delta ptr (32 bytes, big-endian wei)
    a0 (output) = 0 (ok) / 1 (parse fail or amount*1e9 overflow)

    path  = bytes_to_nibbles(keccak256(address))
    delta = amount_gwei * 1_000_000_000 -/
def withdrawalToPathDeltaFunction : String :=
  "withdrawal_to_path_delta:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a2                   # out path ptr\n" ++
  "  mv s1, a3                   # out delta ptr\n" ++
  "  # decode the withdrawal RLP into wtpd_struct (a0/a1 already set).\n" ++
  "  la a2, wtpd_struct\n" ++
  "  jal ra, withdrawal_decode\n" ++
  "  bnez a0, .Lwtpd_fail\n" ++
  "  # keccak256(address @ struct+16, 20 bytes) -> wtpd_hash.\n" ++
  "  la a0, wtpd_struct; addi a0, a0, 16\n" ++
  "  li a1, 20\n" ++
  "  la a2, wtpd_hash\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # path = bytes_to_nibbles(wtpd_hash, 32) -> out path (64 nibbles).\n" ++
  "  la a0, wtpd_hash; li a1, 32; mv a2, s0\n" ++
  "  jal ra, bytes_to_nibbles\n" ++
  "  # delta = amount (Gwei, struct+40) zero-extended to u256 BE...\n" ++
  "  la t0, wtpd_struct; ld a0, 40(t0)\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, u256_from_u64_be\n" ++
  "  # ... times 1e9 (Gwei -> wei), in place.\n" ++
  "  mv a0, s1; li a1, 1000000000; mv a2, s1\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lwtpd_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lwtpd_ret\n" ++
  ".Lwtpd_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lwtpd_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_withdrawal_to_path_delta`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  withdrawal RLP length (u64)
      +16 withdrawal RLP bytes
    Output layout:
      OUTPUT+0  : status (0 ok / 1 fail)
      OUTPUT+8  : path (64 nibble bytes)
      OUTPUT+72 : delta (32-byte big-endian wei) -/
def ziskWithdrawalToPathDeltaPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # withdrawal RLP length\n" ++
  "  addi a0, t0, 16             # withdrawal RLP ptr\n" ++
  "  li a2, 0xa0010008           # out path at OUTPUT+8\n" ++
  "  li a3, 0xa0010048           # out delta at OUTPUT+72\n" ++
  "  jal ra, withdrawal_to_path_delta\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)   # status at OUTPUT+0\n" ++
  "  j .Lwtpd_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  withdrawalDecodeFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  withdrawalToPathDeltaFunction ++ "\n" ++
  ".Lwtpd_pdone:"

def ziskWithdrawalToPathDeltaDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n  .zero 200\n" ++
  "rfu_offset:\n  .zero 8\n" ++
  "rfu_length:\n  .zero 8\n" ++
  "wd_offset:\n  .zero 8\n" ++
  "wd_length:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n  .zero 40\n" ++
  ".balign 8\n" ++
  "wtpd_struct:\n  .zero 48\n" ++
  ".balign 32\n" ++
  "wtpd_hash:\n  .zero 32"

def ziskWithdrawalToPathDeltaProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWithdrawalToPathDeltaPrologue
  dataAsm     := ziskWithdrawalToPathDeltaDataSection
}

end EvmAsm.Codegen
