/-
  EvmAsm.Codegen.Programs.Account

  Ethereum-account RLP accessors and predicates carved out of
  `EvmAsm.Codegen.Programs.Tx` per the file-size hard cap. Hosts:

    K121  account_extract_nonce    (field 0, u64)
    K120  account_extract_balance  (field 1, u256 BE)
    K123  account_is_empty         (EIP-161 emptiness)

  All three compose `rlp_field_to_u64` (K34), `rlp_field_to_u256_be`
  (K35), and `rlp_list_nth_item` (K20) — which remain in
  `Programs/Tx.lean` and `Programs/RlpRead.lean`.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## account_extract_nonce -- PR-K121

    Extract the u64 `nonce` field (RLP field 0) from a fully
    RLP-encoded Ethereum account:

      account = [nonce, balance, storage_root, code_hash]

    The nonce counts the number of outbound transactions an EOA
    has issued (or contract creations for a contract). EIP-2681
    caps it at `2^64 - 1` so a u64 fits.

    K27 `account_decode` already extracts the full account record;
    this narrower accessor avoids the 96-byte struct when only the
    nonce is needed (e.g., the tx-replay-protection check inside
    `check_transaction`, or to thread the nonce-mismatch error path
    without unpacking balance / storage_root / code_hash).

    Composes the existing `rlp_field_to_u64` helper (which in turn
    uses PR-K20 `rlp_list_nth_item`).

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : u64 output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 0 missing / > 64 bits -/
def accountExtractNonceFunction : String :=
  "account_extract_nonce:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  mv s0, a2                   # u64 out ptr (stash)\n" ++
  "  sd zero, 0(s0)\n" ++
  "  # a0, a1 still hold (account_ptr, account_len).\n" ++
  "  li a2, 0\n" ++
  "  mv a3, s0\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  beqz a0, .Laen_ret\n" ++
  "  sd zero, 0(s0)\n" ++
  "  li a0, 1\n" ++
  ".Laen_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_account_extract_nonce`: probe BuildUnit. Reads
    (account_len, account_bytes), writes (status, nonce u64) to
    OUTPUT (16 bytes). -/
def ziskAccountExtractNoncePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # account_rlp_len\n" ++
  "  addi a0, a3, 16             # account_rlp ptr\n" ++
  "  li a2, 0xa0010008           # nonce out\n" ++
  "  jal ra, account_extract_nonce\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Laen_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  accountExtractNonceFunction ++ "\n" ++
  ".Laen_pdone:"

def ziskAccountExtractNonceDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskAccountExtractNonceProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountExtractNoncePrologue
  dataAsm     := ziskAccountExtractNonceDataSection
}

/-! ## account_extract_balance -- PR-K120

    Extract the u256 BE `balance` field (RLP field 1) from a fully
    RLP-encoded Ethereum account:

      account = [nonce, balance, storage_root, code_hash]

    The balance is the account's wei holdings, ranged in
    `[0, 2^256)`. Direct input to balance-check predicates
    (`balance >= value + gas_cost`), priority-fee credit, and
    the trie-rebuild path after value transfers.

    K27 `account_decode` already extracts the full account record;
    K120 (with PR-K119 `account_extract_storage_root`) is the
    narrower accessor for callers that only need a single field.

    Composes the existing `rlp_field_to_u256_be` helper (which in
    turn uses PR-K20 `rlp_list_nth_item`).

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : 32-byte output ptr (u256 BE)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 1 missing / > 256 bits -/
def accountExtractBalanceFunction : String :=
  "account_extract_balance:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  mv s0, a2                   # output 32B ptr (stash)\n" ++
  "  sd zero,  0(s0); sd zero,  8(s0); sd zero, 16(s0); sd zero, 24(s0)\n" ++
  "  # a0, a1 still hold (account_ptr, account_len).\n" ++
  "  li a2, 1\n" ++
  "  mv a3, s0\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  beqz a0, .Laeb_ret\n" ++
  "  sd zero,  0(s0); sd zero,  8(s0); sd zero, 16(s0); sd zero, 24(s0)\n" ++
  "  li a0, 1\n" ++
  ".Laeb_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_account_extract_balance`: probe BuildUnit. Reads
    (account_len, account_bytes), writes (status, 32-byte balance
    BE) to OUTPUT (40 bytes). -/
def ziskAccountExtractBalancePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # account_rlp_len\n" ++
  "  addi a0, a3, 16             # account_rlp ptr\n" ++
  "  li a2, 0xa0010008           # 32B u256 output\n" ++
  "  jal ra, account_extract_balance\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Laeb_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  accountExtractBalanceFunction ++ "\n" ++
  ".Laeb_pdone:"

def ziskAccountExtractBalanceDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t48_offset:\n" ++
  "  .zero 8\n" ++
  "t48_length:\n" ++
  "  .zero 8"

def ziskAccountExtractBalanceProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountExtractBalancePrologue
  dataAsm     := ziskAccountExtractBalanceDataSection
}

/-! ## account_is_empty -- PR-K123

    EIP-161 "empty" predicate. An account is empty iff all three:
    - `nonce == 0`
    - `balance == 0`
    - `code_hash == EMPTY_CODE_HASH`

    The `storage_root` field is **not** part of the empty check —
    storage that's unreachable due to empty code is considered to
    not exist for this purpose. (Compare against `EMPTY_TRIE_ROOT`
    is a stricter invariant maintained by the state machine, not
    by this predicate.)

    Used by:
    - state-cleanup pass post-tx (delete-empty rule from EIP-161)
    - `account_exists_and_is_empty` in
      `forks/amsterdam/state_tracker.py`
    - beneficiary credit (a coinbase with no priority fee &
      previously empty becomes alive again only if balance > 0)

    EMPTY_CODE_HASH (keccak256(b'')) is hard-coded as a 32-byte
    constant in `.data`:

      0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

    Composes:
      - PR-K20 `rlp_list_nth_item`         — field bounds
      - existing `rlp_field_to_u64`        — nonce
      - existing `rlp_field_to_u256_be`    — balance

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : u64 out ptr (1 if empty, 0 if non-empty)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written to *out
        1 : RLP parse failure / field missing / wrong width

    Uses 8 + 32 + 8 + 8 + 32 = 88 bytes of `.data` scratch
    (`aie_nonce` u64, `aie_balance` 32 B, `aie_offset` + `aie_length`,
    `aie_empty_code_hash` constant). -/
def accountIsEmptyFunction : String :=
  "account_is_empty:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # account_ptr\n" ++
  "  mv s1, a1                   # account_len\n" ++
  "  mv s2, a2                   # out u64 ptr\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # Step 1: nonce (field 0) → aie_nonce.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  li a2, 0\n" ++
  "  la a3, aie_nonce\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Laie_parse_fail\n" ++
  "  la t0, aie_nonce; ld t1, 0(t0)\n" ++
  "  bnez t1, .Laie_not_empty\n" ++
  "  # Step 2: balance (field 1, u256 BE) → aie_balance.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  li a2, 1\n" ++
  "  la a3, aie_balance\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Laie_parse_fail\n" ++
  "  la t0, aie_balance\n" ++
  "  ld t1,  0(t0); bnez t1, .Laie_not_empty\n" ++
  "  ld t1,  8(t0); bnez t1, .Laie_not_empty\n" ++
  "  ld t1, 16(t0); bnez t1, .Laie_not_empty\n" ++
  "  ld t1, 24(t0); bnez t1, .Laie_not_empty\n" ++
  "  # Step 3: code_hash (field 3) compared against EMPTY_CODE_HASH.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  li a2, 3\n" ++
  "  la a3, aie_offset; la a4, aie_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Laie_parse_fail\n" ++
  "  la t0, aie_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Laie_parse_fail\n" ++
  "  la t0, aie_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  la t4, aie_empty_code_hash\n" ++
  "  ld t5,  0(t3); ld t6,  0(t4); bne t5, t6, .Laie_not_empty\n" ++
  "  ld t5,  8(t3); ld t6,  8(t4); bne t5, t6, .Laie_not_empty\n" ++
  "  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Laie_not_empty\n" ++
  "  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Laie_not_empty\n" ++
  "  # Empty.\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Laie_ret\n" ++
  ".Laie_not_empty:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Laie_ret\n" ++
  ".Laie_parse_fail:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 1\n" ++
  ".Laie_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_account_is_empty`: probe BuildUnit. Reads
    (account_len, account_bytes), writes (status, is_empty) to
    OUTPUT (16 bytes). -/
def ziskAccountIsEmptyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # account_rlp_len\n" ++
  "  addi a0, a3, 16             # account_rlp ptr\n" ++
  "  li a2, 0xa0010008           # is_empty out\n" ++
  "  jal ra, account_is_empty\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Laie_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  accountIsEmptyFunction ++ "\n" ++
  ".Laie_pdone:"

def ziskAccountIsEmptyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t48_offset:\n" ++
  "  .zero 8\n" ++
  "t48_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aie_nonce:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aie_balance:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "aie_offset:\n" ++
  "  .zero 8\n" ++
  "aie_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aie_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"

def ziskAccountIsEmptyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountIsEmptyPrologue
  dataAsm     := ziskAccountIsEmptyDataSection
}

end EvmAsm.Codegen
