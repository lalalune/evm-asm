/-
  EvmAsm.Codegen.Programs.Withdrawal

  EIP-4895 Withdrawal helpers extracted from `EvmAsm.Codegen.Programs`
  per the file-size hard cap. Hosts the canonical Withdrawal record
  encoder and its keccak-hash shortcut:

    K130  withdrawal_rlp_encode
    K132  withdrawal_compute_hash

  Both helpers are referenced by the withdrawal pipeline (K49 / K65 /
  K77 / K78) in `Programs/Block.lean` and by the withdrawals-MPT-root
  validators in `Programs/Mpt.lean`.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## withdrawal_rlp_encode -- PR-K130

    RLP-encode an EIP-4895 `Withdrawal`:

      Withdrawal = [index, validator_index, address, amount]

    Field types:
    - index           : u64 (RLP uint, canonical form)
    - validator_index : u64 (RLP uint, canonical form)
    - address         : 20-byte bytestring (0x94 prefix + 20 bytes)
    - amount          : u64 in Gwei (RLP uint, canonical form)

    Output is the full `rlp.encode(withdrawal)` bytes — a short
    list (payload always < 56 bytes), so the outer prefix is the
    1-byte `0xc0 + payload_len` form.

    Used by:
    - the withdrawals MPT root computation (value field of each
      `[rlp(i), rlp(withdrawal)]` leaf)
    - PR-K77 `process_withdrawal`'s receipt-log path
    - block-body re-serialization

    Composes:
      - PR-K30 `rlp_encode_uint_be` — for u64 uint fields
      - hardcoded `0x94 || address` — for the 20-byte string field
      - 1-byte list prefix — computed inline

    Calling convention:
      a0 (input)  : index (u64)
      a1 (input)  : validator_index (u64)
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : amount (u64, Gwei)
      a4 (input)  : output bytes ptr (caller supplies ≥ 56 bytes)
      a5 (input)  : u64 out ptr (output byte length)
      ra (input)  : return
      a0 (output) : 0 (always succeeds — total function). -/
def withdrawalRlpEncodeFunction : String :=
  "withdrawal_rlp_encode:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # index\n" ++
  "  mv s1, a1                   # validator_index\n" ++
  "  mv s2, a2                   # address ptr\n" ++
  "  mv s3, a3                   # amount\n" ++
  "  mv s4, a4                   # output bytes ptr\n" ++
  "  mv s5, a5                   # output length out\n" ++
  "  # Write index as 8 BE bytes to wre_idx_be, then RLP-encode.\n" ++
  "  la t0, wre_idx_be\n" ++
  "  srli t1, s0, 56; sb t1, 0(t0)\n" ++
  "  srli t1, s0, 48; sb t1, 1(t0)\n" ++
  "  srli t1, s0, 40; sb t1, 2(t0)\n" ++
  "  srli t1, s0, 32; sb t1, 3(t0)\n" ++
  "  srli t1, s0, 24; sb t1, 4(t0)\n" ++
  "  srli t1, s0, 16; sb t1, 5(t0)\n" ++
  "  srli t1, s0,  8; sb t1, 6(t0)\n" ++
  "  sb s0, 7(t0)\n" ++
  "  mv a0, t0\n" ++
  "  li a1, 8\n" ++
  "  la a2, wre_idx_rlp\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  la t0, wre_idx_len\n" ++
  "  sd a0, 0(t0)                # save returned length\n" ++
  "  # Write validator_index as 8 BE bytes.\n" ++
  "  la t0, wre_val_be\n" ++
  "  srli t1, s1, 56; sb t1, 0(t0)\n" ++
  "  srli t1, s1, 48; sb t1, 1(t0)\n" ++
  "  srli t1, s1, 40; sb t1, 2(t0)\n" ++
  "  srli t1, s1, 32; sb t1, 3(t0)\n" ++
  "  srli t1, s1, 24; sb t1, 4(t0)\n" ++
  "  srli t1, s1, 16; sb t1, 5(t0)\n" ++
  "  srli t1, s1,  8; sb t1, 6(t0)\n" ++
  "  sb s1, 7(t0)\n" ++
  "  mv a0, t0\n" ++
  "  li a1, 8\n" ++
  "  la a2, wre_val_rlp\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  la t0, wre_val_len\n" ++
  "  sd a0, 0(t0)\n" ++
  "  # Write amount as 8 BE bytes.\n" ++
  "  la t0, wre_amt_be\n" ++
  "  srli t1, s3, 56; sb t1, 0(t0)\n" ++
  "  srli t1, s3, 48; sb t1, 1(t0)\n" ++
  "  srli t1, s3, 40; sb t1, 2(t0)\n" ++
  "  srli t1, s3, 32; sb t1, 3(t0)\n" ++
  "  srli t1, s3, 24; sb t1, 4(t0)\n" ++
  "  srli t1, s3, 16; sb t1, 5(t0)\n" ++
  "  srli t1, s3,  8; sb t1, 6(t0)\n" ++
  "  sb s3, 7(t0)\n" ++
  "  mv a0, t0\n" ++
  "  li a1, 8\n" ++
  "  la a2, wre_amt_rlp\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  la t0, wre_amt_len\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t0, wre_idx_len; ld t1, 0(t0)\n" ++
  "  la t0, wre_val_len; ld t2, 0(t0)\n" ++
  "  la t0, wre_amt_len; ld t3, 0(t0)\n" ++
  "  add t4, t1, t2\n" ++
  "  addi t4, t4, 21\n" ++
  "  add t4, t4, t3\n" ++
  "  mv s6, t4\n" ++
  "  addi t5, t4, 0xc0\n" ++
  "  sb t5, 0(s4)\n" ++
  "  addi t6, s4, 1\n" ++
  "  la t5, wre_idx_rlp\n" ++
  "  mv t4, t1\n" ++
  ".Lwre_copy_idx:\n" ++
  "  beqz t4, .Lwre_idx_done\n" ++
  "  lbu t0, 0(t5)\n" ++
  "  sb t0, 0(t6)\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t6, t6, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lwre_copy_idx\n" ++
  ".Lwre_idx_done:\n" ++
  "  la t5, wre_val_rlp\n" ++
  "  mv t4, t2\n" ++
  ".Lwre_copy_val:\n" ++
  "  beqz t4, .Lwre_val_done\n" ++
  "  lbu t0, 0(t5)\n" ++
  "  sb t0, 0(t6)\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t6, t6, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lwre_copy_val\n" ++
  ".Lwre_val_done:\n" ++
  "  li t0, 0x94\n" ++
  "  sb t0, 0(t6)\n" ++
  "  addi t6, t6, 1\n" ++
  "  ld t0,  0(s2); sd t0,  0(t6)\n" ++
  "  ld t0,  8(s2); sd t0,  8(t6)\n" ++
  "  lwu t0, 16(s2); sw t0, 16(t6)\n" ++
  "  addi t6, t6, 20\n" ++
  "  la t5, wre_amt_rlp\n" ++
  "  mv t4, t3\n" ++
  ".Lwre_copy_amt:\n" ++
  "  beqz t4, .Lwre_amt_done\n" ++
  "  lbu t0, 0(t5)\n" ++
  "  sb t0, 0(t6)\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t6, t6, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lwre_copy_amt\n" ++
  ".Lwre_amt_done:\n" ++
  "  addi t0, s6, 1\n" ++
  "  sd t0, 0(s5)\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_withdrawal_rlp_encode`: probe BuildUnit. Reads
    (index, validator_index, amount, address_20B) from host input,
    writes (status, out_len, rlp_bytes...) to OUTPUT.
    Input layout:
      bytes  0.. 8 : index
      bytes  8..16 : validator_index
      bytes 16..24 : amount
      bytes 24..44 : address (20 bytes)
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : out_len
      bytes 16..   : withdrawal_rlp bytes -/
def ziskWithdrawalRlpEncodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a0, 8(a6)                # index\n" ++
  "  ld a1, 16(a6)               # validator_index\n" ++
  "  ld a3, 24(a6)               # amount\n" ++
  "  addi a2, a6, 40             # address ptr (INPUT + 40)\n" ++
  "  li a4, 0xa0010010           # out bytes\n" ++
  "  li a5, 0xa0010008           # out_len out\n" ++
  "  jal ra, withdrawal_rlp_encode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwre_pdone\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  withdrawalRlpEncodeFunction ++ "\n" ++
  ".Lwre_pdone:"

def ziskWithdrawalRlpEncodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "wre_idx_be:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wre_idx_rlp:\n" ++
  "  .zero 16\n" ++
  ".balign 8\n" ++
  "wre_idx_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wre_val_be:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wre_val_rlp:\n" ++
  "  .zero 16\n" ++
  ".balign 8\n" ++
  "wre_val_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wre_amt_be:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wre_amt_rlp:\n" ++
  "  .zero 16\n" ++
  ".balign 8\n" ++
  "wre_amt_len:\n" ++
  "  .zero 8"

def ziskWithdrawalRlpEncodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWithdrawalRlpEncodePrologue
  dataAsm     := ziskWithdrawalRlpEncodeDataSection
}

/-! ## withdrawal_compute_hash -- PR-K132

    Compute the keccak256 hash of an EIP-4895 Withdrawal record:

      hash = keccak256(rlp.encode([index, validator_index, address, amount]))

    Used as the leaf value when building/walking the withdrawals
    trie, and for receipt-side `process_withdrawal` bookkeeping.
    Direct composition of:

      - PR-K130 `withdrawal_rlp_encode` — produce the RLP bytes
      - PR-K3   `zkvm_keccak256`        — hash them

    Calling convention:
      a0 (input)  : index (u64)
      a1 (input)  : validator_index (u64)
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : amount (u64, Gwei)
      a4 (input)  : 32-byte output ptr (hash)
      ra (input)  : return
      a0 (output) : 0 (always succeeds — both legs are total).

    Uses 64 bytes of `.data` scratch (`wch_rlp_buf` for the encoded
    withdrawal, ≤ 49 bytes max; `wch_rlp_len` for the length). -/
def withdrawalComputeHashFunction : String :=
  "withdrawal_compute_hash:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  mv s0, a4                   # output ptr (stash)\n" ++
  "  # Call withdrawal_rlp_encode(index, validator_idx, addr, amt,\n" ++
  "  #                           wch_rlp_buf, wch_rlp_len)\n" ++
  "  # a0, a1, a2, a3 already hold the four input fields.\n" ++
  "  la a4, wch_rlp_buf\n" ++
  "  la a5, wch_rlp_len\n" ++
  "  jal ra, withdrawal_rlp_encode\n" ++
  "  # Call zkvm_keccak256(wch_rlp_buf, wch_rlp_len, s0)\n" ++
  "  la a0, wch_rlp_buf\n" ++
  "  la t0, wch_rlp_len; ld a1, 0(t0)\n" ++
  "  mv a2, s0\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_withdrawal_compute_hash`: probe BuildUnit. Reads
    (index, validator_index, amount, address_20B) from host input,
    writes (status, hash[32]) to OUTPUT (40 bytes total). -/
def ziskWithdrawalComputeHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a0, 8(a6)                # index\n" ++
  "  ld a1, 16(a6)               # validator_index\n" ++
  "  ld a3, 24(a6)               # amount\n" ++
  "  addi a2, a6, 40             # address ptr (INPUT + 40)\n" ++
  "  li a4, 0xa0010008           # 32B hash output\n" ++
  "  jal ra, withdrawal_compute_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwch_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  withdrawalRlpEncodeFunction ++ "\n" ++
  withdrawalComputeHashFunction ++ "\n" ++
  ".Lwch_pdone:"

def ziskWithdrawalComputeHashDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "wre_idx_be:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wre_idx_rlp:\n" ++
  "  .zero 16\n" ++
  ".balign 8\n" ++
  "wre_idx_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wre_val_be:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wre_val_rlp:\n" ++
  "  .zero 16\n" ++
  ".balign 8\n" ++
  "wre_val_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wre_amt_be:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wre_amt_rlp:\n" ++
  "  .zero 16\n" ++
  ".balign 8\n" ++
  "wre_amt_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wch_rlp_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "wch_rlp_len:\n" ++
  "  .zero 8"

def ziskWithdrawalComputeHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWithdrawalComputeHashPrologue
  dataAsm     := ziskWithdrawalComputeHashDataSection
}

end EvmAsm.Codegen
