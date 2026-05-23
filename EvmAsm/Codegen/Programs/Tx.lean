/-
  EvmAsm.Codegen.Programs.Tx

  Tx-decoding stack lifted out of `EvmAsm.Codegen.Programs` to
  keep the registry hub manageable (file-size hard cap, see
  `Programs.lean` bottom).

  Contains three contiguous slabs as they appeared in
  `Programs.lean`:

  1. **rlp-field shims + account extractors + legacy-tx
     decoders / signature extractors** (PR-K34 / K121 / K35 /
     K120 / K123 / K36 / K37 / K138 / K139).

  2. **u256-BE arithmetic / comparison / pricing helpers**
     (PR-K51 / K52 / K56 / K58 / K59 / K60 / K61 / K62 / K70 /
     K53 / K54) used pervasively by tx validation and fee
     computation.

  3. **u256-BE truncation + tx type / extract / EIP-decode
     family + intrinsic-gas + validate-transaction**
     (PR-K57 / K40 / K102 / K101 / K103 / K104 / K108 / K41 /
     K42 / K44 / K45 / K87 / K88 / K92 / K46 / K66 / K76 / K80
     and adjacent helpers).

  The module is named after the dominant cluster (tx) even
  though slabs (2) and a couple of cross-cutting helpers
  (`rlp_field_to_u*`, account extractors, u256 arithmetic) live
  here alongside it. Grouping them in one submodule reflects
  the fact that the verifier's tx-validation pipeline pulls in
  exactly this collection of helpers; splitting them further is
  a future refactor when this file in turn becomes too large.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## rlp_field_to_u64 -- PR-K34 RLP field → u64 wrapper

    Extract the N-th field of an RLP list and decode its
    big-endian byte string as a u64. Used by future
    transaction-decode and header-decode steps for fields like
    nonce, gas_limit, block_number, v.

    Calling convention:
      a0 (input)  : container RLP bytes ptr (e.g. tx_rlp)
      a1 (input)  : container RLP byte length
      a2 (input)  : field index (0-based)
      a3 (input)  : u64 output ptr (LE-stored u64)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse failure /
                    2 field too long (> 8 bytes)

    Composes PR-K20 `rlp_list_nth_item` + per-byte BE decode.
    The output is stored as a native LE u64 at *a3. -/
def rlpFieldToU64Function : String :=
  "rlp_field_to_u64:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0                  # container ptr\n" ++
  "  mv s1, a3                  # u64 out ptr\n" ++
  "  la a3, rfu_offset\n" ++
  "  la a4, rfu_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lrfu_fail\n" ++
  "  la t0, rfu_length; ld t1, 0(t0)\n" ++
  "  li t2, 8\n" ++
  "  bgtu t1, t2, .Lrfu_too_long\n" ++
  "  la t0, rfu_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  li t2, 0                   # accumulator\n" ++
  ".Lrfu_loop:\n" ++
  "  beqz t1, .Lrfu_done\n" ++
  "  slli t2, t2, 8\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  or t2, t2, t4\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lrfu_loop\n" ++
  ".Lrfu_done:\n" ++
  "  sd t2, 0(s1)               # *out = u64 LE\n" ++
  "  li a0, 0\n" ++
  "  j .Lrfu_ret\n" ++
  ".Lrfu_too_long:\n" ++
  "  sd zero, 0(s1)\n" ++
  "  li a0, 2\n" ++
  "  j .Lrfu_ret\n" ++
  ".Lrfu_fail:\n" ++
  "  sd zero, 0(s1)\n" ++
  "  li a0, 1\n" ++
  ".Lrfu_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_rlp_field_to_u64`: probe BuildUnit. Reads
    (container_len, field_index, container_bytes) from host
    input, writes (status, u64) to OUTPUT. -/
def ziskRlpFieldToU64Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # container_len\n" ++
  "  ld a2, 16(a4)               # field_index\n" ++
  "  addi a0, a4, 24             # container ptr\n" ++
  "  li a3, 0xa0010008           # u64 out at OUTPUT + 8\n" ++
  "  sd zero, 0(a3)\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lrfu_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  ".Lrfu_pdone:"

def ziskRlpFieldToU64DataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskRlpFieldToU64ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRlpFieldToU64Prologue
  dataAsm     := ziskRlpFieldToU64DataSection
}

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

/-! ## rlp_field_to_u256_be -- PR-K35

    Extract the N-th field of an RLP list and right-align its
    big-endian byte string into a 32-byte BE u256 buffer.
    Parallel of PR-K34 `rlp_field_to_u64` for u256 fields like
    balance / tx.value / header.difficulty.

    Calling convention:
      a0 (input)  : container RLP bytes ptr
      a1 (input)  : container RLP byte length
      a2 (input)  : field index (0-based)
      a3 (input)  : 32-byte u256 BE output ptr (right-aligned)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail /
                    2 field too long (> 32 bytes)

    Composes PR-K20 `rlp_list_nth_item`; reuses K34's
    `rfu_offset` / `rfu_length` scratch slots. -/
def rlpFieldToU256BeFunction : String :=
  "rlp_field_to_u256_be:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0                  # container ptr\n" ++
  "  mv s1, a3                  # u256 BE out ptr\n" ++
  "  # Zero output up front (also covers fail/too-long paths).\n" ++
  "  sd zero,  0(s1); sd zero,  8(s1); sd zero, 16(s1); sd zero, 24(s1)\n" ++
  "  la a3, rfu_offset\n" ++
  "  la a4, rfu_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lrf256_fail\n" ++
  "  la t0, rfu_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bgtu t1, t2, .Lrf256_too_long\n" ++
  "  la t0, rfu_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  sub t2, t2, t1             # 32 - len\n" ++
  "  add t4, s1, t2             # dst start (right-aligned)\n" ++
  ".Lrf256_copy:\n" ++
  "  beqz t1, .Lrf256_done\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb  t5, 0(t4)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lrf256_copy\n" ++
  ".Lrf256_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lrf256_ret\n" ++
  ".Lrf256_too_long:\n" ++
  "  li a0, 2\n" ++
  "  j .Lrf256_ret\n" ++
  ".Lrf256_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lrf256_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_rlp_field_to_u256_be`: probe BuildUnit. Reads
    (container_len, field_index, container_bytes), writes
    (status, u256 BE) to OUTPUT. -/
def ziskRlpFieldToU256BePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # container_len\n" ++
  "  ld a2, 16(a4)               # field_index\n" ++
  "  addi a0, a4, 24             # container ptr\n" ++
  "  li a3, 0xa0010008           # u256 out at OUTPUT + 8\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lrf256_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  ".Lrf256_pdone:"

def ziskRlpFieldToU256BeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskRlpFieldToU256BeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRlpFieldToU256BePrologue
  dataAsm     := ziskRlpFieldToU256BeDataSection
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

/-! ## tx_legacy_decode -- PR-K36 full 9-field decoder

    Decode an RLP-encoded legacy Ethereum transaction into a
    196-byte flat output struct. Composes the field-decoder
    primitives shipped in PR-K34/K35 plus PR-K20
    `rlp_list_nth_item` for the variable-length `to` and `data`
    fields.

    Output struct (196 bytes):
       0..  8  nonce (u64 LE)
       8.. 40  gas_price (u256 BE)
      40.. 48  gas_limit (u64 LE)
      48.. 68  to (20-byte address; zero on creation)
      68.. 76  to_present (u64; 0 = creation, 1 = call)
      76..108  value (u256 BE)
     108..116  data_offset (within tx_rlp)
     116..124  data_length
     124..132  v (u64 LE)
     132..164  r (u256 BE)
     164..196  s (u256 BE)

    Calling convention:
      a0 (input)  : tx_rlp ptr
      a1 (input)  : tx_rlp byte length
      a2 (input)  : output struct ptr (196 bytes)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail -/
def txLegacyDecodeFunction : String :=
  "tx_legacy_decode:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # tx ptr\n" ++
  "  mv s1, a1                  # tx_len\n" ++
  "  mv s2, a2                  # struct out\n" ++
  "  # Field 0: nonce (u64)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0; mv a3, s2\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Ltxd_fail\n" ++
  "  # Field 1: gas_price (u256 BE at offset 8)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  addi a3, s2, 8\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Ltxd_fail\n" ++
  "  # Field 2: gas_limit (u64 at offset 40)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  addi a3, s2, 40\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Ltxd_fail\n" ++
  "  # Field 3: to (0 or 20 bytes at offset 48; to_present at 68)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  la a3, txd_offset; la a4, txd_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Ltxd_fail\n" ++
  "  la t0, txd_length; ld t1, 0(t0)\n" ++
  "  beqz t1, .Ltxd_to_creation\n" ++
  "  li t2, 20\n" ++
  "  bne t1, t2, .Ltxd_fail\n" ++
  "  la t0, txd_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  addi t4, s2, 48\n" ++
  "  ld t5,  0(t3); sd t5, 0(t4)\n" ++
  "  ld t5,  8(t3); sd t5, 8(t4)\n" ++
  "  lwu t5, 16(t3); sw t5, 16(t4)\n" ++
  "  li t5, 1\n" ++
  "  sd t5, 68(s2)              # to_present = 1\n" ++
  "  j .Ltxd_after_to\n" ++
  ".Ltxd_to_creation:\n" ++
  "  addi t4, s2, 48\n" ++
  "  sd zero, 0(t4); sd zero, 8(t4); sw zero, 16(t4)\n" ++
  "  sd zero, 68(s2)            # to_present = 0\n" ++
  ".Ltxd_after_to:\n" ++
  "  # Field 4: value (u256 BE at offset 76)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 4\n" ++
  "  addi a3, s2, 76\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Ltxd_fail\n" ++
  "  # Field 5: data (arbitrary; store offset+length at 108/116)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 5\n" ++
  "  la a3, txd_offset; la a4, txd_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Ltxd_fail\n" ++
  "  la t0, txd_offset; ld t1, 0(t0); sd t1, 108(s2)\n" ++
  "  la t0, txd_length; ld t1, 0(t0); sd t1, 116(s2)\n" ++
  "  # Field 6: v (u64 at offset 124)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 6\n" ++
  "  addi a3, s2, 124\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Ltxd_fail\n" ++
  "  # Field 7: r (u256 BE at offset 132)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 7\n" ++
  "  addi a3, s2, 132\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Ltxd_fail\n" ++
  "  # Field 8: s (u256 BE at offset 164)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 8\n" ++
  "  addi a3, s2, 164\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Ltxd_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Ltxd_ret\n" ++
  ".Ltxd_fail:\n" ++
  "  li a0, 1\n" ++
  ".Ltxd_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_tx_legacy_decode`: probe BuildUnit. Reads
    (tx_len, tx_bytes) from host input, writes
    (status, 196-byte struct) to OUTPUT.
    Total output = 204 bytes; fits in ziskemu's 256-byte cap. -/
def ziskTxLegacyDecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # tx_len\n" ++
  "  addi a0, a3, 16             # tx ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 196 bytes (24 × 8 + 4 trailing)\n" ++
  "  mv t0, a2\n" ++
  "  li t1, 24\n" ++
  ".Ltxd_zinit:\n" ++
  "  beqz t1, .Ltxd_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Ltxd_zinit\n" ++
  ".Ltxd_zdone:\n" ++
  "  sw zero, 0(t0)\n" ++
  "  jal ra, tx_legacy_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Ltxd_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txLegacyDecodeFunction ++ "\n" ++
  ".Ltxd_pdone:"

def ziskTxLegacyDecodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "txd_offset:\n" ++
  "  .zero 8\n" ++
  "txd_length:\n" ++
  "  .zero 8"

def ziskTxLegacyDecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxLegacyDecodePrologue
  dataAsm     := ziskTxLegacyDecodeDataSection
}

/-! ## derive_chain_id_from_v -- PR-K37 EIP-155 helper

    Split a legacy-transaction `v` signature parity byte into
    `(chain_id, is_eip155)` per EIP-155:

      v == 27 → pre-EIP-155: chain_id = 0, is_eip155 = 0
      v == 28 → pre-EIP-155: chain_id = 0, is_eip155 = 0
      else    → EIP-155: chain_id = (v - 35) / 2, is_eip155 = 1

    This is the routing logic the signing-hash builder uses to
    pick between the 6-field (pre-155) and 9-field (155+
    chain_id, 0, 0) signing payloads.

    Calling convention:
      a0 (input)  : v (u64)
      a1 (input)  : chain_id u64 output ptr
      a2 (input)  : is_eip155 u64 output ptr
      ra (input)  : return
      a0 (output) : 0 (always success; no validation here --
                    invalid v values just produce wrong
                    chain_id; the signing-hash check catches
                    them later) -/
def deriveChainIdFromVFunction : String :=
  "derive_chain_id_from_v:\n" ++
  "  li t0, 27\n" ++
  "  beq a0, t0, .Ldcid_pre155\n" ++
  "  li t0, 28\n" ++
  "  beq a0, t0, .Ldcid_pre155\n" ++
  "  # EIP-155: chain_id = (v - 35) / 2\n" ++
  "  addi t1, a0, -35\n" ++
  "  srli t1, t1, 1\n" ++
  "  sd t1, 0(a1)\n" ++
  "  li t2, 1\n" ++
  "  sd t2, 0(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Ldcid_pre155:\n" ++
  "  sd zero, 0(a1)\n" ++
  "  sd zero, 0(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_derive_chain_id_from_v`: probe BuildUnit. Reads
    (v, padding) from host input, writes (chain_id, is_eip155)
    to OUTPUT. -/
def ziskDeriveChainIdFromVPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a0, 8(a3)                # v\n" ++
  "  li a1, 0xa0010000           # chain_id out\n" ++
  "  li a2, 0xa0010008           # is_eip155 out\n" ++
  "  jal ra, derive_chain_id_from_v\n" ++
  "  j .Ldcid_pdone\n" ++
  deriveChainIdFromVFunction ++ "\n" ++
  ".Ldcid_pdone:"

def ziskDeriveChainIdFromVDataSection : String :=
  ".section .data\n" ++
  "dcid_pad:\n" ++
  "  .zero 8"

def ziskDeriveChainIdFromVProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskDeriveChainIdFromVPrologue
  dataAsm     := ziskDeriveChainIdFromVDataSection
}

/-! ## tx_legacy_extract_signature -- PR-K138

    Extract `(v, r, s)` from a 9-field legacy transaction RLP:

      legacy_tx = rlp([nonce, gas_price, gas_limit, to,
                       value, data, v, r, s])

    Output convention:
      * v: u64 (the on-the-wire v byte; pass through
        `derive_chain_id_from_v` (K37) to split into chain_id /
        is_eip155).
      * r, s: 32-byte right-aligned, zero-padded big-endian
        buffers — the canonical signature scalars.

    Used by the legacy-tx sender-recovery path:
      1. K138 extracts `(v, r, s)`.
      2. K37 `derive_chain_id_from_v` splits v.
      3. tx_signing_hash_legacy (future) computes the message
         digest from fields 0..5 (+ optional EIP-155 tail).
      4. `zkvm_secp256k1_ecrecover` produces a 64-byte pubkey.
      5. K99 `address_from_pubkey` derives the 20-byte sender
         address.

    PR-K36 `tx_legacy_decode` already extracts these three
    fields as part of full-record extraction; K138 is the
    narrower accessor for callers that only need the signature
    (e.g., when the other fields were already extracted by a
    previous pass).

    Composes:
      - PR-K20 `rlp_list_nth_item` on fields 6, 7, 8

    Calling convention:
      a0 (input)  : tx_rlp ptr
      a1 (input)  : tx_rlp byte length
      a2 (input)  : v u64 out ptr
      a3 (input)  : r 32-byte BE out ptr
      a4 (input)  : s 32-byte BE out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / fields 6/7/8 missing
        2 : v > 8 bytes (cannot fit in u64) or r/s > 32 bytes -/
def txLegacyExtractSignatureFunction : String :=
  "tx_legacy_extract_signature:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # tx_rlp ptr\n" ++
  "  mv s1, a1                   # tx_rlp len\n" ++
  "  mv s2, a2                   # v out\n" ++
  "  mv s3, a3                   # r out (32 B)\n" ++
  "  mv s4, a4                   # s out (32 B)\n" ++
  "  # ---- Field 6: v (uint <= 8 bytes) → u64 ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 6\n" ++
  "  la a3, tlxs_offset; la a4, tlxs_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Ltlxs_fail\n" ++
  "  la t0, tlxs_length; ld t1, 0(t0)\n" ++
  "  li t2, 8\n" ++
  "  bgtu t1, t2, .Ltlxs_size\n" ++
  "  la t0, tlxs_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  li t2, 0\n" ++
  ".Ltlxs_vloop:\n" ++
  "  beqz t1, .Ltlxs_vdone\n" ++
  "  slli t2, t2, 8\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  or t2, t2, t4\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Ltlxs_vloop\n" ++
  ".Ltlxs_vdone:\n" ++
  "  sd t2, 0(s2)\n" ++
  "  # ---- Field 7: r (u256 BE <= 32 bytes) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 7\n" ++
  "  la a3, tlxs_offset; la a4, tlxs_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Ltlxs_fail\n" ++
  "  la t0, tlxs_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bgtu t1, t2, .Ltlxs_size\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  sub t2, t2, t1               # 32 - len\n" ++
  "  add t4, s3, t2               # dst (right-aligned)\n" ++
  "  la t0, tlxs_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  ".Ltlxs_rloop:\n" ++
  "  beqz t1, .Ltlxs_rdone\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb  t5, 0(t4)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Ltlxs_rloop\n" ++
  ".Ltlxs_rdone:\n" ++
  "  # ---- Field 8: s (u256 BE <= 32 bytes) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 8\n" ++
  "  la a3, tlxs_offset; la a4, tlxs_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Ltlxs_fail\n" ++
  "  la t0, tlxs_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bgtu t1, t2, .Ltlxs_size\n" ++
  "  sd zero,  0(s4); sd zero,  8(s4); sd zero, 16(s4); sd zero, 24(s4)\n" ++
  "  sub t2, t2, t1\n" ++
  "  add t4, s4, t2\n" ++
  "  la t0, tlxs_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  ".Ltlxs_sloop:\n" ++
  "  beqz t1, .Ltlxs_sdone\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb  t5, 0(t4)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Ltlxs_sloop\n" ++
  ".Ltlxs_sdone:\n" ++
  "  li a0, 0\n" ++
  "  j .Ltlxs_ret\n" ++
  ".Ltlxs_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Ltlxs_ret\n" ++
  ".Ltlxs_size:\n" ++
  "  li a0, 2\n" ++
  ".Ltlxs_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_tx_legacy_extract_signature`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : tx_rlp_len
      bytes  8..   : tx_rlp
    Output layout (72 bytes):
      bytes  0.. 8 : status
      bytes  8..16 : v
      bytes 16..48 : r (32 B BE)
      bytes 48..80 : s (32 B BE) -- truncated at 256 B cap is fine -/
def ziskTxLegacyExtractSignaturePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # tx_rlp_len\n" ++
  "  addi a0, a5, 16             # tx_rlp ptr\n" ++
  "  li a2, 0xa0010008           # v out\n" ++
  "  li a3, 0xa0010010           # r out (32 B)\n" ++
  "  li a4, 0xa0010030           # s out (32 B)\n" ++
  "  jal ra, tx_legacy_extract_signature\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Ltlxs_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  txLegacyExtractSignatureFunction ++ "\n" ++
  ".Ltlxs_pdone:"

def ziskTxLegacyExtractSignatureDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "tlxs_offset:\n" ++
  "  .zero 8\n" ++
  "tlxs_length:\n" ++
  "  .zero 8"

def ziskTxLegacyExtractSignatureProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxLegacyExtractSignaturePrologue
  dataAsm     := ziskTxLegacyExtractSignatureDataSection
}

/-! ## tx_eip1559_extract_signature -- PR-K139

    Extract `(y_parity, r, s)` from the inner RLP of an EIP-1559
    (type-2) transaction:

      inner = rlp([chain_id, nonce,
                   max_priority_fee_per_gas, max_fee_per_gas,
                   gas_limit, to, value, data, access_list,
                   y_parity, r, s])

    The caller is expected to have stripped the leading `0x02`
    type byte (matching PR-K41 `tx_eip1559_decode`'s convention),
    so `a0` points at the inner list's RLP prefix.

    Output convention (mirrors K138 `tx_legacy_extract_signature`):
      * y_parity: u64 (0 or 1; not the legacy `v` byte — no
        EIP-155 split needed because chain_id already lives in
        field 0).
      * r, s: 32-byte right-aligned, zero-padded big-endian
        buffers — the canonical signature scalars consumed by
        `zkvm_secp256k1_ecrecover`.

    Companion in the sender-recovery pipeline to K138
    (legacy), with EIP-2930 / EIP-4844 / EIP-7702 variants
    landing in follow-up PRs (same shape, different field
    indices).

    Composes:
      - PR-K20 `rlp_list_nth_item` on fields 9, 10, 11

    Calling convention:
      a0 (input)  : inner_rlp ptr
      a1 (input)  : inner_rlp byte length
      a2 (input)  : y_parity u64 out ptr
      a3 (input)  : r 32-byte BE out ptr
      a4 (input)  : s 32-byte BE out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / fields 9/10/11 missing
        2 : y_parity > 8 bytes or r/s > 32 bytes -/
def txEip1559ExtractSignatureFunction : String :=
  "tx_eip1559_extract_signature:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # inner_rlp ptr\n" ++
  "  mv s1, a1                   # inner_rlp len\n" ++
  "  mv s2, a2                   # y_parity out\n" ++
  "  mv s3, a3                   # r out (32 B)\n" ++
  "  mv s4, a4                   # s out (32 B)\n" ++
  "  # ---- Field 9: y_parity (uint <= 8 bytes) → u64 ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 9\n" ++
  "  la a3, txes_offset; la a4, txes_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Ltxes_fail\n" ++
  "  la t0, txes_length; ld t1, 0(t0)\n" ++
  "  li t2, 8\n" ++
  "  bgtu t1, t2, .Ltxes_size\n" ++
  "  la t0, txes_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  li t2, 0\n" ++
  ".Ltxes_yloop:\n" ++
  "  beqz t1, .Ltxes_ydone\n" ++
  "  slli t2, t2, 8\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  or t2, t2, t4\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Ltxes_yloop\n" ++
  ".Ltxes_ydone:\n" ++
  "  sd t2, 0(s2)\n" ++
  "  # ---- Field 10: r (u256 BE <= 32 bytes) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 10\n" ++
  "  la a3, txes_offset; la a4, txes_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Ltxes_fail\n" ++
  "  la t0, txes_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bgtu t1, t2, .Ltxes_size\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  sub t2, t2, t1\n" ++
  "  add t4, s3, t2\n" ++
  "  la t0, txes_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  ".Ltxes_rloop:\n" ++
  "  beqz t1, .Ltxes_rdone\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb  t5, 0(t4)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Ltxes_rloop\n" ++
  ".Ltxes_rdone:\n" ++
  "  # ---- Field 11: s (u256 BE <= 32 bytes) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 11\n" ++
  "  la a3, txes_offset; la a4, txes_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Ltxes_fail\n" ++
  "  la t0, txes_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bgtu t1, t2, .Ltxes_size\n" ++
  "  sd zero,  0(s4); sd zero,  8(s4); sd zero, 16(s4); sd zero, 24(s4)\n" ++
  "  sub t2, t2, t1\n" ++
  "  add t4, s4, t2\n" ++
  "  la t0, txes_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  ".Ltxes_sloop:\n" ++
  "  beqz t1, .Ltxes_sdone\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb  t5, 0(t4)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Ltxes_sloop\n" ++
  ".Ltxes_sdone:\n" ++
  "  li a0, 0\n" ++
  "  j .Ltxes_ret\n" ++
  ".Ltxes_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Ltxes_ret\n" ++
  ".Ltxes_size:\n" ++
  "  li a0, 2\n" ++
  ".Ltxes_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_tx_eip1559_extract_signature`: probe BuildUnit.
    Input layout (after the host header):
      bytes  0.. 8 : inner_rlp_len
      bytes  8..   : inner_rlp (no leading 0x02 type byte)
    Output layout (80 bytes):
      bytes  0.. 8 : status
      bytes  8..16 : y_parity (u64)
      bytes 16..48 : r (32 B BE)
      bytes 48..80 : s (32 B BE) -/
def ziskTxEip1559ExtractSignaturePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # inner_rlp_len\n" ++
  "  addi a0, a5, 16             # inner_rlp ptr\n" ++
  "  li a2, 0xa0010008           # y_parity out\n" ++
  "  li a3, 0xa0010010           # r out (32 B)\n" ++
  "  li a4, 0xa0010030           # s out (32 B)\n" ++
  "  jal ra, tx_eip1559_extract_signature\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Ltxes_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  txEip1559ExtractSignatureFunction ++ "\n" ++
  ".Ltxes_pdone:"

def ziskTxEip1559ExtractSignatureDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "txes_offset:\n" ++
  "  .zero 8\n" ++
  "txes_length:\n" ++
  "  .zero 8"

def ziskTxEip1559ExtractSignatureProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxEip1559ExtractSignaturePrologue
  dataAsm     := ziskTxEip1559ExtractSignatureDataSection
}

/-! ## tx_eip2930_extract_signature -- PR-K140

    Extract `(y_parity, r, s)` from the inner RLP body of an
    EIP-2930 (type-1) access-list transaction:

      inner = rlp([chain_id, nonce, gas_price, gas_limit,
                   to, value, data, access_list,
                   y_parity, r, s])

    EIP-2930 is structurally simpler than EIP-1559 (a single
    `gas_price` field instead of the
    `(max_priority_fee_per_gas, max_fee_per_gas)` pair), so the
    signature triple sits at fields 8/9/10 of an 11-field list.

    Caller is expected to have stripped the leading `0x01` type
    byte (matching PR-K42 `tx_eip2930_decode`'s convention), so
    `a0` points at the inner list's RLP prefix.

    Companion in the sender-recovery pipeline to PR-K138
    (legacy) and PR-K139 (EIP-1559); EIP-4844 / EIP-7702 variants
    land in follow-up PRs.

    Composes:
      - PR-K20 `rlp_list_nth_item` on fields 8, 9, 10

    Calling convention:
      a0 (input)  : inner_rlp ptr
      a1 (input)  : inner_rlp byte length
      a2 (input)  : y_parity u64 out ptr
      a3 (input)  : r 32-byte BE out ptr
      a4 (input)  : s 32-byte BE out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / fields 8/9/10 missing
        2 : y_parity > 8 bytes or r/s > 32 bytes -/
def txEip2930ExtractSignatureFunction : String :=
  "tx_eip2930_extract_signature:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # inner_rlp ptr\n" ++
  "  mv s1, a1                   # inner_rlp len\n" ++
  "  mv s2, a2                   # y_parity out\n" ++
  "  mv s3, a3                   # r out (32 B)\n" ++
  "  mv s4, a4                   # s out (32 B)\n" ++
  "  # ---- Field 8: y_parity (uint <= 8 bytes) → u64 ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 8\n" ++
  "  la a3, t29es_offset; la a4, t29es_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt29es_fail\n" ++
  "  la t0, t29es_length; ld t1, 0(t0)\n" ++
  "  li t2, 8\n" ++
  "  bgtu t1, t2, .Lt29es_size\n" ++
  "  la t0, t29es_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  li t2, 0\n" ++
  ".Lt29es_yloop:\n" ++
  "  beqz t1, .Lt29es_ydone\n" ++
  "  slli t2, t2, 8\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  or t2, t2, t4\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt29es_yloop\n" ++
  ".Lt29es_ydone:\n" ++
  "  sd t2, 0(s2)\n" ++
  "  # ---- Field 9: r (u256 BE <= 32 bytes) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 9\n" ++
  "  la a3, t29es_offset; la a4, t29es_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt29es_fail\n" ++
  "  la t0, t29es_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bgtu t1, t2, .Lt29es_size\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  sub t2, t2, t1\n" ++
  "  add t4, s3, t2\n" ++
  "  la t0, t29es_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  ".Lt29es_rloop:\n" ++
  "  beqz t1, .Lt29es_rdone\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb  t5, 0(t4)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt29es_rloop\n" ++
  ".Lt29es_rdone:\n" ++
  "  # ---- Field 10: s (u256 BE <= 32 bytes) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 10\n" ++
  "  la a3, t29es_offset; la a4, t29es_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt29es_fail\n" ++
  "  la t0, t29es_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bgtu t1, t2, .Lt29es_size\n" ++
  "  sd zero,  0(s4); sd zero,  8(s4); sd zero, 16(s4); sd zero, 24(s4)\n" ++
  "  sub t2, t2, t1\n" ++
  "  add t4, s4, t2\n" ++
  "  la t0, t29es_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  ".Lt29es_sloop:\n" ++
  "  beqz t1, .Lt29es_sdone\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb  t5, 0(t4)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt29es_sloop\n" ++
  ".Lt29es_sdone:\n" ++
  "  li a0, 0\n" ++
  "  j .Lt29es_ret\n" ++
  ".Lt29es_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lt29es_ret\n" ++
  ".Lt29es_size:\n" ++
  "  li a0, 2\n" ++
  ".Lt29es_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_tx_eip2930_extract_signature`: probe BuildUnit.
    Input layout (after the host header):
      bytes  0.. 8 : inner_rlp_len
      bytes  8..   : inner_rlp (no leading 0x01 type byte)
    Output layout (80 bytes): status, y_parity, r (32 B), s (32 B). -/
def ziskTxEip2930ExtractSignaturePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # inner_rlp_len\n" ++
  "  addi a0, a5, 16             # inner_rlp ptr\n" ++
  "  li a2, 0xa0010008           # y_parity out\n" ++
  "  li a3, 0xa0010010           # r out (32 B)\n" ++
  "  li a4, 0xa0010030           # s out (32 B)\n" ++
  "  jal ra, tx_eip2930_extract_signature\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lt29es_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  txEip2930ExtractSignatureFunction ++ "\n" ++
  ".Lt29es_pdone:"

def ziskTxEip2930ExtractSignatureDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "t29es_offset:\n" ++
  "  .zero 8\n" ++
  "t29es_length:\n" ++
  "  .zero 8"

def ziskTxEip2930ExtractSignatureProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxEip2930ExtractSignaturePrologue
  dataAsm     := ziskTxEip2930ExtractSignatureDataSection
}

/-! ## tx_eip4844_extract_signature -- PR-K141

    Extract `(y_parity, r, s)` from the inner RLP body of an
    EIP-4844 (type-3) blob transaction:

      inner = rlp([chain_id, nonce,
                   max_priority_fee_per_gas, max_fee_per_gas,
                   gas_limit, to, value, data,
                   access_list,
                   max_fee_per_blob_gas, blob_versioned_hashes,
                   y_parity, r, s])

    Compared to EIP-1559 (12 fields), EIP-4844 inserts
    `max_fee_per_blob_gas` and `blob_versioned_hashes` between
    `access_list` and `y_parity`, so the signature triple sits at
    fields 11/12/13 of a 14-field list.

    Caller is expected to have stripped the leading 0x03 type byte
    (matching PR-K45 `tx_eip4844_decode`'s convention).

    Companion in the sender-recovery pipeline to PR-K138 (legacy),
    PR-K139 (EIP-1559), and PR-K140 (EIP-2930); EIP-7702 variant
    lands in a follow-up PR.

    Composes:
      - PR-K20 `rlp_list_nth_item` on fields 11, 12, 13

    Calling convention:
      a0 (input)  : inner_rlp ptr
      a1 (input)  : inner_rlp byte length
      a2 (input)  : y_parity u64 out ptr
      a3 (input)  : r 32-byte BE out ptr
      a4 (input)  : s 32-byte BE out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / fields 11/12/13 missing
        2 : y_parity > 8 bytes or r/s > 32 bytes -/
def txEip4844ExtractSignatureFunction : String :=
  "tx_eip4844_extract_signature:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # inner_rlp ptr\n" ++
  "  mv s1, a1                   # inner_rlp len\n" ++
  "  mv s2, a2                   # y_parity out\n" ++
  "  mv s3, a3                   # r out (32 B)\n" ++
  "  mv s4, a4                   # s out (32 B)\n" ++
  "  # ---- Field 11: y_parity (uint <= 8 bytes) → u64 ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 11\n" ++
  "  la a3, t44es_offset; la a4, t44es_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt44es_fail\n" ++
  "  la t0, t44es_length; ld t1, 0(t0)\n" ++
  "  li t2, 8\n" ++
  "  bgtu t1, t2, .Lt44es_size\n" ++
  "  la t0, t44es_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  li t2, 0\n" ++
  ".Lt44es_yloop:\n" ++
  "  beqz t1, .Lt44es_ydone\n" ++
  "  slli t2, t2, 8\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  or t2, t2, t4\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt44es_yloop\n" ++
  ".Lt44es_ydone:\n" ++
  "  sd t2, 0(s2)\n" ++
  "  # ---- Field 12: r (u256 BE <= 32 bytes) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 12\n" ++
  "  la a3, t44es_offset; la a4, t44es_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt44es_fail\n" ++
  "  la t0, t44es_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bgtu t1, t2, .Lt44es_size\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  sub t2, t2, t1\n" ++
  "  add t4, s3, t2\n" ++
  "  la t0, t44es_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  ".Lt44es_rloop:\n" ++
  "  beqz t1, .Lt44es_rdone\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb  t5, 0(t4)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt44es_rloop\n" ++
  ".Lt44es_rdone:\n" ++
  "  # ---- Field 13: s (u256 BE <= 32 bytes) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 13\n" ++
  "  la a3, t44es_offset; la a4, t44es_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt44es_fail\n" ++
  "  la t0, t44es_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bgtu t1, t2, .Lt44es_size\n" ++
  "  sd zero,  0(s4); sd zero,  8(s4); sd zero, 16(s4); sd zero, 24(s4)\n" ++
  "  sub t2, t2, t1\n" ++
  "  add t4, s4, t2\n" ++
  "  la t0, t44es_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  ".Lt44es_sloop:\n" ++
  "  beqz t1, .Lt44es_sdone\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb  t5, 0(t4)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt44es_sloop\n" ++
  ".Lt44es_sdone:\n" ++
  "  li a0, 0\n" ++
  "  j .Lt44es_ret\n" ++
  ".Lt44es_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lt44es_ret\n" ++
  ".Lt44es_size:\n" ++
  "  li a0, 2\n" ++
  ".Lt44es_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_tx_eip4844_extract_signature`: probe BuildUnit. -/
def ziskTxEip4844ExtractSignaturePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # inner_rlp_len\n" ++
  "  addi a0, a5, 16             # inner_rlp ptr\n" ++
  "  li a2, 0xa0010008           # y_parity out\n" ++
  "  li a3, 0xa0010010           # r out (32 B)\n" ++
  "  li a4, 0xa0010030           # s out (32 B)\n" ++
  "  jal ra, tx_eip4844_extract_signature\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lt44es_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  txEip4844ExtractSignatureFunction ++ "\n" ++
  ".Lt44es_pdone:"

def ziskTxEip4844ExtractSignatureDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "t44es_offset:\n" ++
  "  .zero 8\n" ++
  "t44es_length:\n" ++
  "  .zero 8"

def ziskTxEip4844ExtractSignatureProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxEip4844ExtractSignaturePrologue
  dataAsm     := ziskTxEip4844ExtractSignatureDataSection
}

/-! ## tx_eip7702_extract_signature -- PR-K142

    Extract `(y_parity, r, s)` from the inner RLP body of an
    EIP-7702 (type-4) set-code transaction:

      inner = rlp([chain_id, nonce,
                   max_priority_fee_per_gas, max_fee_per_gas,
                   gas_limit, to, value, data,
                   access_list, authorization_list,
                   y_parity, r, s])

    Compared to EIP-1559 (12 fields), EIP-7702 inserts a single
    `authorization_list` field between `access_list` and
    `y_parity`, so the outer-transaction signature triple sits at
    fields 10/11/12 of a 13-field list.

    Note: EIP-7702 carries TWO layers of signatures — the outer
    transaction signature (this PR's target) AND a per-entry
    `(y_parity, r, s)` inside each authorization tuple in
    `authorization_list`. K142 only handles the outer triple.
    Sub-extracting per-authorization signatures lands in a
    follow-up PR (one per authorization).

    Caller is expected to have stripped the leading 0x04 type byte
    (matching PR-K44 `tx_eip7702_decode`'s convention).

    Completes the four-EIP sig-extractor family:
      * PR-K138 legacy
      * PR-K139 EIP-1559
      * PR-K140 EIP-2930
      * PR-K141 EIP-4844
      * PR-K142 EIP-7702

    Composes:
      - PR-K20 `rlp_list_nth_item` on fields 10, 11, 12

    Calling convention:
      a0 (input)  : inner_rlp ptr
      a1 (input)  : inner_rlp byte length
      a2 (input)  : y_parity u64 out ptr
      a3 (input)  : r 32-byte BE out ptr
      a4 (input)  : s 32-byte BE out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / fields 10/11/12 missing
        2 : y_parity > 8 bytes or r/s > 32 bytes -/
def txEip7702ExtractSignatureFunction : String :=
  "tx_eip7702_extract_signature:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # inner_rlp ptr\n" ++
  "  mv s1, a1                   # inner_rlp len\n" ++
  "  mv s2, a2                   # y_parity out\n" ++
  "  mv s3, a3                   # r out (32 B)\n" ++
  "  mv s4, a4                   # s out (32 B)\n" ++
  "  # ---- Field 10: y_parity (uint <= 8 bytes) → u64 ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 10\n" ++
  "  la a3, t77es_offset; la a4, t77es_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt77es_fail\n" ++
  "  la t0, t77es_length; ld t1, 0(t0)\n" ++
  "  li t2, 8\n" ++
  "  bgtu t1, t2, .Lt77es_size\n" ++
  "  la t0, t77es_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  li t2, 0\n" ++
  ".Lt77es_yloop:\n" ++
  "  beqz t1, .Lt77es_ydone\n" ++
  "  slli t2, t2, 8\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  or t2, t2, t4\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt77es_yloop\n" ++
  ".Lt77es_ydone:\n" ++
  "  sd t2, 0(s2)\n" ++
  "  # ---- Field 11: r (u256 BE <= 32 bytes) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 11\n" ++
  "  la a3, t77es_offset; la a4, t77es_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt77es_fail\n" ++
  "  la t0, t77es_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bgtu t1, t2, .Lt77es_size\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  sub t2, t2, t1\n" ++
  "  add t4, s3, t2\n" ++
  "  la t0, t77es_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  ".Lt77es_rloop:\n" ++
  "  beqz t1, .Lt77es_rdone\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb  t5, 0(t4)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt77es_rloop\n" ++
  ".Lt77es_rdone:\n" ++
  "  # ---- Field 12: s (u256 BE <= 32 bytes) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 12\n" ++
  "  la a3, t77es_offset; la a4, t77es_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt77es_fail\n" ++
  "  la t0, t77es_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bgtu t1, t2, .Lt77es_size\n" ++
  "  sd zero,  0(s4); sd zero,  8(s4); sd zero, 16(s4); sd zero, 24(s4)\n" ++
  "  sub t2, t2, t1\n" ++
  "  add t4, s4, t2\n" ++
  "  la t0, t77es_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  ".Lt77es_sloop:\n" ++
  "  beqz t1, .Lt77es_sdone\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb  t5, 0(t4)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt77es_sloop\n" ++
  ".Lt77es_sdone:\n" ++
  "  li a0, 0\n" ++
  "  j .Lt77es_ret\n" ++
  ".Lt77es_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lt77es_ret\n" ++
  ".Lt77es_size:\n" ++
  "  li a0, 2\n" ++
  ".Lt77es_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_tx_eip7702_extract_signature`: probe BuildUnit. -/
def ziskTxEip7702ExtractSignaturePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # inner_rlp_len\n" ++
  "  addi a0, a5, 16             # inner_rlp ptr\n" ++
  "  li a2, 0xa0010008           # y_parity out\n" ++
  "  li a3, 0xa0010010           # r out (32 B)\n" ++
  "  li a4, 0xa0010030           # s out (32 B)\n" ++
  "  jal ra, tx_eip7702_extract_signature\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lt77es_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  txEip7702ExtractSignatureFunction ++ "\n" ++
  ".Lt77es_pdone:"

def ziskTxEip7702ExtractSignatureDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "t77es_offset:\n" ++
  "  .zero 8\n" ++
  "t77es_length:\n" ++
  "  .zero 8"

def ziskTxEip7702ExtractSignatureProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxEip7702ExtractSignaturePrologue
  dataAsm     := ziskTxEip7702ExtractSignatureDataSection
}

/-! ## eip7702_authorization_extract_signature -- PR-K143

    Extract `(y_parity, r, s)` from a single EIP-7702
    *authorization tuple*. Each entry inside an EIP-7702
    transaction's `authorization_list` is a 6-field RLP list:

      authorization = rlp([chain_id, address, nonce,
                           y_parity, r, s])

    so the signature triple sits at fields 3/4/5 of a 6-field
    list — one field earlier on each axis than the legacy tx
    layout because there is no `data`, `to`, or `access_list`
    field in an authorization tuple.

    Companion to PR-K142 `tx_eip7702_extract_signature`, which
    extracts the *outer* transaction signature. EIP-7702 carries
    two layers of signatures:

      * Outer transaction sig (K142): authorises the whole tx.
      * Per-authorization sig (K143): authorises a single
        `(chain_id, address, nonce)` delegation to be applied
        before the tx body runs.

    The full sender-recovery pipeline for an EIP-7702 delegation:
      1. K143 extracts (y_parity, r, s) from the authorization
         tuple.
      2. tx_eip7702_authorization_signing_hash (future) =
         keccak256(MAGIC || rlp([chain_id, address, nonce]))
         where `MAGIC = 0x05` per the EIP.
      3. `zkvm_secp256k1_ecrecover` → 64-byte pubkey of the
         **delegator** (not the tx sender).
      4. K99 `address_from_pubkey` → 20-byte delegator address.

    The caller is responsible for first using K20
    `rlp_list_nth_item` to extract the i-th authorization tuple
    from `authorization_list`; K143 operates on the already-
    extracted tuple bytes.

    Composes:
      - PR-K20 `rlp_list_nth_item` on fields 3, 4, 5

    Calling convention:
      a0 (input)  : authorization_tuple_rlp ptr
      a1 (input)  : authorization_tuple_rlp byte length
      a2 (input)  : y_parity u64 out ptr
      a3 (input)  : r 32-byte BE out ptr
      a4 (input)  : s 32-byte BE out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / fields 3/4/5 missing
        2 : y_parity > 8 bytes or r/s > 32 bytes -/
def eip7702AuthorizationExtractSignatureFunction : String :=
  "eip7702_authorization_extract_signature:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # tuple_rlp ptr\n" ++
  "  mv s1, a1                   # tuple_rlp len\n" ++
  "  mv s2, a2                   # y_parity out\n" ++
  "  mv s3, a3                   # r out (32 B)\n" ++
  "  mv s4, a4                   # s out (32 B)\n" ++
  "  # ---- Field 3: y_parity (uint <= 8 bytes) → u64 ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  la a3, ta77es_offset; la a4, ta77es_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lta77es_fail\n" ++
  "  la t0, ta77es_length; ld t1, 0(t0)\n" ++
  "  li t2, 8\n" ++
  "  bgtu t1, t2, .Lta77es_size\n" ++
  "  la t0, ta77es_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  li t2, 0\n" ++
  ".Lta77es_yloop:\n" ++
  "  beqz t1, .Lta77es_ydone\n" ++
  "  slli t2, t2, 8\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  or t2, t2, t4\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lta77es_yloop\n" ++
  ".Lta77es_ydone:\n" ++
  "  sd t2, 0(s2)\n" ++
  "  # ---- Field 4: r (u256 BE <= 32 bytes) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 4\n" ++
  "  la a3, ta77es_offset; la a4, ta77es_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lta77es_fail\n" ++
  "  la t0, ta77es_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bgtu t1, t2, .Lta77es_size\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  sub t2, t2, t1\n" ++
  "  add t4, s3, t2\n" ++
  "  la t0, ta77es_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  ".Lta77es_rloop:\n" ++
  "  beqz t1, .Lta77es_rdone\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb  t5, 0(t4)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lta77es_rloop\n" ++
  ".Lta77es_rdone:\n" ++
  "  # ---- Field 5: s (u256 BE <= 32 bytes) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 5\n" ++
  "  la a3, ta77es_offset; la a4, ta77es_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lta77es_fail\n" ++
  "  la t0, ta77es_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bgtu t1, t2, .Lta77es_size\n" ++
  "  sd zero,  0(s4); sd zero,  8(s4); sd zero, 16(s4); sd zero, 24(s4)\n" ++
  "  sub t2, t2, t1\n" ++
  "  add t4, s4, t2\n" ++
  "  la t0, ta77es_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  ".Lta77es_sloop:\n" ++
  "  beqz t1, .Lta77es_sdone\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb  t5, 0(t4)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lta77es_sloop\n" ++
  ".Lta77es_sdone:\n" ++
  "  li a0, 0\n" ++
  "  j .Lta77es_ret\n" ++
  ".Lta77es_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lta77es_ret\n" ++
  ".Lta77es_size:\n" ++
  "  li a0, 2\n" ++
  ".Lta77es_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_eip7702_authorization_extract_signature`: probe BuildUnit.
    Input layout (after the host header):
      bytes  0.. 8 : tuple_rlp_len
      bytes  8..   : tuple_rlp -/
def ziskEip7702AuthorizationExtractSignaturePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # tuple_rlp_len\n" ++
  "  addi a0, a5, 16             # tuple_rlp ptr\n" ++
  "  li a2, 0xa0010008           # y_parity out\n" ++
  "  li a3, 0xa0010010           # r out (32 B)\n" ++
  "  li a4, 0xa0010030           # s out (32 B)\n" ++
  "  jal ra, eip7702_authorization_extract_signature\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lta77es_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  eip7702AuthorizationExtractSignatureFunction ++ "\n" ++
  ".Lta77es_pdone:"

def ziskEip7702AuthorizationExtractSignatureDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ta77es_offset:\n" ++
  "  .zero 8\n" ++
  "ta77es_length:\n" ++
  "  .zero 8"

def ziskEip7702AuthorizationExtractSignatureProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskEip7702AuthorizationExtractSignaturePrologue
  dataAsm     := ziskEip7702AuthorizationExtractSignatureDataSection
}

/-! ## rlp_list_truncate_to_n_fields -- PR-K144

    Given an RLP-encoded list and a count `n`, write a freshly
    re-encoded RLP list containing only the first `n` fields of
    the input. The child encodings are reused verbatim (RLP is
    context-free at child level); only the outer list prefix is
    re-emitted to reflect the smaller payload.

    Direct building block for transaction signing-hash computation:

      * Legacy pre-EIP-155 signing hash = `keccak256(rlp([nonce,
        gas_price, gas_limit, to, value, data]))` — i.e., the
        legacy tx's 9-field RLP truncated to its first 6 fields
        (dropping `v, r, s`).
      * EIP-1559 signing hash body = first 9 fields of the
        12-field inner list (dropping `y_parity, r, s`).
      * EIP-2930 signing hash body = first 8 fields of 11.
      * EIP-4844 signing hash body = first 11 fields of 14.
      * EIP-7702 signing hash body = first 10 fields of 13.
      * EIP-7702 authorization signing hash body = first 3 fields
        of the 6-field authorization tuple (dropping
        `y_parity, r, s`).

    Composes:
      - PR-K20 `rlp_list_nth_item`     — locate first / last fields
      - PR-K129 `rlp_encode_list_prefix` — new outer prefix

    Calling convention:
      a0 (input)  : input_rlp ptr (encoded list)
      a1 (input)  : input_rlp byte length
      a2 (input)  : n_fields (u64) — keep first n
      a3 (input)  : output buffer ptr (caller supplies
                    >= 9 + len(retained payload) bytes)
      a4 (input)  : u64 out_length ptr (receives total written
                    bytes, prefix + payload)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / input not a list
        2 : input has fewer than `n` fields
    Edge cases:
      * n == 0 → output is `0xc0` (empty list, 1 byte). -/
def rlpListTruncateToNFieldsFunction : String :=
  "rlp_list_truncate_to_n_fields:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # input_rlp ptr\n" ++
  "  mv s1, a1                   # input_rlp len\n" ++
  "  mv s2, a2                   # n_fields\n" ++
  "  mv s3, a3                   # output buffer ptr\n" ++
  "  mv s4, a4                   # out_length ptr\n" ++
  "  beqz s2, .Lrltn_empty       # n == 0 → emit `0xc0`\n" ++
  "  # ---- Parse the outer list prefix to get payload_start ----\n" ++
  "  # NOTE: we cannot use `rlp_list_nth_item(input, 0)` for this:\n" ++
  "  # K20 returns the *content* offset for byte-string items, which\n" ++
  "  # drops the field's RLP prefix byte. The truncation needs the\n" ++
  "  # *item* offset = start of the outer payload = byte after the\n" ++
  "  # outer list prefix.\n" ++
  "  beqz s1, .Lrltn_parse_fail\n" ++
  "  lbu t0, 0(s0)\n" ++
  "  li t1, 0xc0\n" ++
  "  bltu t0, t1, .Lrltn_parse_fail   # not an RLP list\n" ++
  "  li t1, 0xf8\n" ++
  "  bltu t0, t1, .Lrltn_short_list\n" ++
  "  # Long list: payload_start = 1 + (t0 - 0xf7)\n" ++
  "  addi s5, t0, -0xf7\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lrltn_have_start\n" ++
  ".Lrltn_short_list:\n" ++
  "  li s5, 1                          # payload_start = 1\n" ++
  ".Lrltn_have_start:\n" ++
  "  # ---- Locate field (n-1) to get end-of-payload ----\n" ++
  "  addi t0, s2, -1\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, t0\n" ++
  "  la a3, rltn_offset_hi; la a4, rltn_length_hi\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lrltn_too_few\n" ++
  "  la t0, rltn_offset_hi; ld t1, 0(t0)\n" ++
  "  la t0, rltn_length_hi; ld t2, 0(t0)\n" ++
  "  add t1, t1, t2                              # end-of-payload (after item n-1)\n" ++
  "  sub s6, t1, s5                              # new_payload_len\n" ++
  "  # ---- Write new outer list prefix ----\n" ++
  "  mv a0, s6; mv a1, s3\n" ++
  "  la a2, rltn_prefix_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  la t0, rltn_prefix_len; ld t1, 0(t0)        # prefix_len\n" ++
  "  # ---- Copy payload bytes ----\n" ++
  "  add t2, s3, t1                              # dst = output + prefix\n" ++
  "  add t3, s0, s5                              # src = input + payload_start\n" ++
  "  mv t4, s6                                   # remaining bytes\n" ++
  ".Lrltn_cploop:\n" ++
  "  beqz t4, .Lrltn_cpdone\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb t5, 0(t2)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lrltn_cploop\n" ++
  ".Lrltn_cpdone:\n" ++
  "  add t1, t1, s6                              # out_len = prefix + payload\n" ++
  "  sd t1, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lrltn_ret\n" ++
  ".Lrltn_empty:\n" ++
  "  li t0, 0xc0\n" ++
  "  sb t0, 0(s3)\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lrltn_ret\n" ++
  ".Lrltn_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lrltn_ret\n" ++
  ".Lrltn_too_few:\n" ++
  "  li a0, 2\n" ++
  ".Lrltn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_rlp_list_truncate_to_n_fields`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : input_rlp_len
      bytes  8..16 : n_fields (u64 LE)
      bytes 16..   : input_rlp
    Output layout (1 KiB ought to be plenty for fixtures):
      bytes  0.. 8 : status
      bytes  8..16 : out_length
      bytes 16..   : written RLP bytes (truncated to 256-byte
                     ziskemu cap; the fixture script reconstructs
                     the slice from the input and the expected
                     prefix). -/
def ziskRlpListTruncateToNFieldsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # input_rlp_len\n" ++
  "  ld a2, 16(a5)               # n_fields\n" ++
  "  addi a0, a5, 24             # input_rlp ptr\n" ++
  "  li a3, 0xa0010010           # output buffer\n" ++
  "  li a4, 0xa0010008           # out_length\n" ++
  "  jal ra, rlp_list_truncate_to_n_fields\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lrltn_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpListTruncateToNFieldsFunction ++ "\n" ++
  ".Lrltn_pdone:"

def ziskRlpListTruncateToNFieldsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rltn_offset_lo:\n" ++
  "  .zero 8\n" ++
  "rltn_length_lo:\n" ++
  "  .zero 8\n" ++
  "rltn_offset_hi:\n" ++
  "  .zero 8\n" ++
  "rltn_length_hi:\n" ++
  "  .zero 8\n" ++
  "rltn_prefix_len:\n" ++
  "  .zero 8"

def ziskRlpListTruncateToNFieldsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRlpListTruncateToNFieldsPrologue
  dataAsm     := ziskRlpListTruncateToNFieldsDataSection
}

/-! ## tx_signing_hash -- PR-K145

    Unified transaction signing-hash builder. Given a tx inner
    RLP, the number of fields to retain (everything before
    `y_parity, r, s`), and an optional type-prefix byte, compute

      keccak256( [type_prefix?] || rlp([first n fields]) )

    in a single call. This is the digest fed to
    `zkvm_secp256k1_ecrecover` together with the extracted
    `(y_parity, r, s)` to recover the tx sender's pubkey.

    Per-tx-type usage:

      type   | type_prefix | n  | description
      -------|-------------|----|-----------------------------
      legacy | 0           | 6  | pre-EIP-155 signing hash
      EIP-2930 | 0x01      | 8  | type-1 signing hash
      EIP-1559 | 0x02      | 9  | type-2 signing hash
      EIP-4844 | 0x03      | 11 | type-3 signing hash
      EIP-7702 | 0x04      | 10 | type-4 signing hash

    Legacy EIP-155 (chain_id-bearing) signing hash is **not**
    covered by this helper: it appends `(chain_id, 0, 0)` after
    the first 6 fields, which requires building a new 9-field
    list rather than just truncating. That variant lands as
    `tx_signing_hash_legacy_eip155` in a follow-up PR.

    EIP-7702 authorization signing hash is similarly out of scope
    (it computes over `MAGIC=0x05 || rlp([chain_id, address,
    nonce])` where the body is a 3-field list freshly built from
    the authorization tuple, not a truncation); follow-up.

    Composes:
      - PR-K144 `rlp_list_truncate_to_n_fields`  -- truncation
      - `zkvm_keccak256` (HashBridge)            -- hashing

    Calling convention:
      a0 (input)  : tx_inner_rlp ptr (caller has stripped any
                    leading type byte)
      a1 (input)  : tx_inner_rlp byte length
      a2 (input)  : n_fields (u64) -- fields to keep
      a3 (input)  : type_prefix (u8 in low bits; 0 = no prefix)
      a4 (input)  : 32-byte output hash ptr
      ra (input)  : return
      a0 (output) :
        0 : success -- hash written
        1 : truncation parse failure / fewer than n fields

    Uses two `.data` scratch buffers:
      * `tsh_buf` (8 KiB) -- holds `[optional type byte] ||
        rlp([first n fields])` immediately before the keccak
        call.
      * `zk3_state` (200 bytes) -- reused from the existing
        keccak bridge. -/
def txSigningHashFunction : String :=
  "tx_signing_hash:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # inner_rlp ptr\n" ++
  "  mv s1, a1                   # inner_rlp len\n" ++
  "  mv s2, a2                   # n_fields\n" ++
  "  mv s3, a3                   # type_prefix (low byte)\n" ++
  "  mv s4, a4                   # output hash ptr (32 B)\n" ++
  "  # ---- Write optional type prefix at tsh_buf[0] ----\n" ++
  "  la t0, tsh_buf\n" ++
  "  beqz s3, .Ltsh_after_prefix\n" ++
  "  sb s3, 0(t0)\n" ++
  ".Ltsh_after_prefix:\n" ++
  "  # ---- Truncate inner_rlp into tsh_buf[1..] ----\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2\n" ++
  "  la a3, tsh_buf; addi a3, a3, 1\n" ++
  "  la a4, tsh_trunc_len\n" ++
  "  jal ra, rlp_list_truncate_to_n_fields\n" ++
  "  bnez a0, .Ltsh_fail\n" ++
  "  la t0, tsh_trunc_len; ld t1, 0(t0)        # trunc_len\n" ++
  "  # ---- Compute (hash_data_ptr, hash_data_len) ----\n" ++
  "  beqz s3, .Ltsh_no_prefix\n" ++
  "  la a0, tsh_buf                            # start at byte 0 (prefix)\n" ++
  "  addi a1, t1, 1                            # length = trunc_len + 1\n" ++
  "  j .Ltsh_do_hash\n" ++
  ".Ltsh_no_prefix:\n" ++
  "  la a0, tsh_buf; addi a0, a0, 1            # start at byte 1\n" ++
  "  mv a1, t1                                 # length = trunc_len\n" ++
  ".Ltsh_do_hash:\n" ++
  "  mv a2, s4                                 # output ptr\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  j .Ltsh_ret\n" ++
  ".Ltsh_fail:\n" ++
  "  li a0, 1\n" ++
  ".Ltsh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_tx_signing_hash`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : inner_rlp_len
      bytes  8..16 : n_fields (u64 LE)
      bytes 16..24 : type_prefix (u64 LE; low byte is the byte;
                     0 = no prefix)
      bytes 24..   : inner_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..40 : 32-byte signing hash -/
def ziskTxSigningHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # inner_rlp_len\n" ++
  "  ld a2, 16(a5)               # n_fields\n" ++
  "  ld a3, 24(a5)               # type_prefix (u64; low byte)\n" ++
  "  addi a0, a5, 32             # inner_rlp ptr\n" ++
  "  li a4, 0xa0010008           # output hash ptr (32 B)\n" ++
  "  jal ra, tx_signing_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Ltsh_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpListTruncateToNFieldsFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  txSigningHashFunction ++ "\n" ++
  ".Ltsh_pdone:"

def ziskTxSigningHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "tsh_buf:\n" ++
  "  .zero 8192\n" ++
  "tsh_trunc_len:\n" ++
  "  .zero 8\n" ++
  -- Scratch labels owned by `rlp_list_truncate_to_n_fields` (K144);
  -- the truncate function references them at fixed offsets through
  -- `la`, so we re-declare them in this probe's `.data` section.
  "rltn_offset_lo:\n" ++
  "  .zero 8\n" ++
  "rltn_length_lo:\n" ++
  "  .zero 8\n" ++
  "rltn_offset_hi:\n" ++
  "  .zero 8\n" ++
  "rltn_length_hi:\n" ++
  "  .zero 8\n" ++
  "rltn_prefix_len:\n" ++
  "  .zero 8"

def ziskTxSigningHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxSigningHashPrologue
  dataAsm     := ziskTxSigningHashDataSection
}

/-! ## tx_signing_hash_legacy_eip155 -- PR-K146

    Legacy EIP-155 signing hash. Different from the typed-tx and
    pre-EIP-155 cases (PR-K145 `tx_signing_hash`) because the
    EIP-155 spec appends `(chain_id, 0, 0)` after the first six
    fields rather than just truncating:

      signing_hash = keccak256(rlp([nonce, gas_price, gas_limit,
                                    to, value, data,
                                    chain_id, 0, 0]))

    So we splice rather than truncate:

      new_payload = [old payload bytes of fields 0..5]
                 || [RLP-canonical-encoded chain_id]
                 || 0x80
                 || 0x80

      signing_hash = keccak256(new_outer_prefix || new_payload)

    Used by every post-Spurious-Dragon mainnet legacy tx; the
    pre-EIP-155 variant (`v ∈ {27, 28}`) is rare on modern
    chains. PR-K37 `derive_chain_id_from_v` distinguishes the
    two — caller routes here when `is_eip155 == 1`.

    Composes:
      - PR-K20 `rlp_list_nth_item`     -- locate fields 0 / 5
      - PR-K30 `rlp_encode_uint_be`    -- chain_id encoding
      - PR-K129 `rlp_encode_list_prefix` -- new outer prefix
      - `zkvm_keccak256` (HashBridge)  -- hashing

    Calling convention:
      a0 (input)  : legacy_tx_rlp ptr (9-field RLP with v,r,s)
      a1 (input)  : legacy_tx_rlp byte length
      a2 (input)  : chain_id (u64)
      a3 (input)  : 32-byte output hash ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / fewer than 6 fields -/
def txSigningHashLegacyEip155Function : String :=
  "tx_signing_hash_legacy_eip155:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # tx_rlp ptr\n" ++
  "  mv s1, a1                   # tx_rlp len\n" ++
  "  mv s2, a2                   # chain_id\n" ++
  "  mv s3, a3                   # output hash ptr\n" ++
  "  # ---- Parse outer list prefix to get payload_start ----\n" ++
  "  # NOTE: K20 returns content offsets, not item-start offsets.\n" ++
  "  # We need the byte right after the outer list prefix.\n" ++
  "  beqz s1, .Lt155_fail\n" ++
  "  lbu t0, 0(s0)\n" ++
  "  li t1, 0xc0\n" ++
  "  bltu t0, t1, .Lt155_fail\n" ++
  "  li t1, 0xf8\n" ++
  "  bltu t0, t1, .Lt155_short_list\n" ++
  "  addi s4, t0, -0xf7\n" ++
  "  addi s4, s4, 1                              # payload_start\n" ++
  "  j .Lt155_have_start\n" ++
  ".Lt155_short_list:\n" ++
  "  li s4, 1\n" ++
  ".Lt155_have_start:\n" ++
  "  # ---- Locate field 5 to get end-of-body ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 5\n" ++
  "  la a3, t155_offset_hi; la a4, t155_length_hi\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt155_fail\n" ++
  "  la t0, t155_offset_hi; ld t1, 0(t0)\n" ++
  "  la t0, t155_length_hi; ld t2, 0(t0)\n" ++
  "  add t1, t1, t2                              # end-of-body\n" ++
  "  sub s5, t1, s4                              # body_len\n" ++
  "  # ---- Encode chain_id as canonical RLP into t155_chain_be ----\n" ++
  "  # Write chain_id as 8 BE bytes to t155_chain_be\n" ++
  "  la t0, t155_chain_be\n" ++
  "  li t1, 7\n" ++
  ".Lt155_chain_be_loop:\n" ++
  "  bltz t1, .Lt155_chain_be_done\n" ++
  "  slli t2, t1, 3\n" ++
  "  srl t3, s2, t2\n" ++
  "  andi t3, t3, 0xff\n" ++
  "  sb t3, 0(t0)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt155_chain_be_loop\n" ++
  ".Lt155_chain_be_done:\n" ++
  "  la a0, t155_chain_be; li a1, 8\n" ++
  "  la a2, t155_chain_enc\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  mv t3, a0                                   # chain_id_enc_len\n" ++
  "  # tail_len = chain_id_enc_len + 2  (two 0x80 bytes for 0, 0)\n" ++
  "  addi t3, t3, 2\n" ++
  "  # new_payload_len = body_len + tail_len\n" ++
  "  add t4, s5, t3                              # new_payload_len\n" ++
  "  # ---- Write new outer list prefix into t155_buf ----\n" ++
  "  mv a0, t4; la a1, t155_buf\n" ++
  "  la a2, t155_prefix_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  la t0, t155_prefix_len; ld t5, 0(t0)        # prefix_len\n" ++
  "  # ---- Copy body bytes after the prefix ----\n" ++
  "  la t0, t155_buf; add t0, t0, t5             # dst\n" ++
  "  add t1, s0, s4                              # src = input + payload_start\n" ++
  "  mv t2, s5                                   # body bytes remaining\n" ++
  ".Lt155_body_cp:\n" ++
  "  beqz t2, .Lt155_body_done\n" ++
  "  lbu t6, 0(t1)\n" ++
  "  sb t6, 0(t0)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Lt155_body_cp\n" ++
  ".Lt155_body_done:\n" ++
  "  # ---- Append encoded chain_id ----\n" ++
  "  la t1, t155_chain_enc\n" ++
  "  la t6, t155_prefix_len; ld t6, 0(t6)        # reload prefix_len\n" ++
  "  # Reload chain_id_enc_len: re-derive from tail_len-2 ... easier to recompute\n" ++
  "  # Actually we lost t3 above; recompute by saving differently. Use t4 - s5 - 2.\n" ++
  "  sub t2, t4, s5\n" ++
  "  addi t2, t2, -2                             # chain_id_enc_len\n" ++
  ".Lt155_chain_cp:\n" ++
  "  beqz t2, .Lt155_chain_done\n" ++
  "  lbu t6, 0(t1)\n" ++
  "  sb t6, 0(t0)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Lt155_chain_cp\n" ++
  ".Lt155_chain_done:\n" ++
  "  # ---- Append two 0x80 bytes for (0, 0) tail ----\n" ++
  "  li t6, 0x80\n" ++
  "  sb t6, 0(t0)\n" ++
  "  sb t6, 1(t0)\n" ++
  "  # ---- Total hash input length = prefix_len + new_payload_len ----\n" ++
  "  la t0, t155_prefix_len; ld t6, 0(t0)\n" ++
  "  add a1, t6, t4                              # total length\n" ++
  "  la a0, t155_buf                             # data ptr\n" ++
  "  mv a2, s3                                   # output hash ptr\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  j .Lt155_ret\n" ++
  ".Lt155_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lt155_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_tx_signing_hash_legacy_eip155`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : tx_rlp_len
      bytes  8..16 : chain_id (u64 LE)
      bytes 16..   : tx_rlp (full 9-field)
    Output layout:
      bytes  0.. 8 : status
      bytes  8..40 : 32-byte signing hash -/
def ziskTxSigningHashLegacyEip155Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # tx_rlp_len\n" ++
  "  ld a2, 16(a5)               # chain_id\n" ++
  "  addi a0, a5, 24             # tx_rlp ptr\n" ++
  "  li a3, 0xa0010008           # output hash ptr (32 B)\n" ++
  "  jal ra, tx_signing_hash_legacy_eip155\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lt155_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  txSigningHashLegacyEip155Function ++ "\n" ++
  ".Lt155_pdone:"

def ziskTxSigningHashLegacyEip155DataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "t155_buf:\n" ++
  "  .zero 8192\n" ++
  "t155_offset_lo:\n" ++
  "  .zero 8\n" ++
  "t155_length_lo:\n" ++
  "  .zero 8\n" ++
  "t155_offset_hi:\n" ++
  "  .zero 8\n" ++
  "t155_length_hi:\n" ++
  "  .zero 8\n" ++
  "t155_chain_be:\n" ++
  "  .zero 8\n" ++
  "t155_chain_enc:\n" ++
  "  .zero 9\n" ++
  "t155_prefix_len:\n" ++
  "  .zero 8"

def ziskTxSigningHashLegacyEip155ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxSigningHashLegacyEip155Prologue
  dataAsm     := ziskTxSigningHashLegacyEip155DataSection
}

/-! ## blob_gas_used_from_versioned_hashes -- PR-K64

    Compute the EIP-4844 `blob_gas_used` field as:

      blob_gas_used = len(tx.blob_versioned_hashes) × GAS_PER_BLOB

    where `GAS_PER_BLOB = 131072 = 0x20000` per spec. The
    `gas_per_blob` constant is parameterized so the helper works
    across forks that might adjust it.

    Direct use case — validating header.blob_gas_used and
    rejecting blob-fee under-pays:

      header.blob_gas_used  ==  sum(tx.blob_versioned_hashes count
                                    × GAS_PER_BLOB
                                    for tx in block.txs
                                    if tx.is_blob)

    Composes PR-K47 `rlp_list_count_items` (#5532) + a `mul`.
    `rlp_list_count_items` is inlined into the probe BuildUnit.

    Calling convention:
      a0 (input)  : blob_versioned_hashes_rlp ptr (whole encoded
                    sub-list as returned by PR-K45
                    `tx_eip4844_decode` field 10)
      a1 (input)  : blob_versioned_hashes_rlp byte length
      a2 (input)  : gas_per_blob (u64; 131072 on mainnet)
      a3 (input)  : u64 out ptr (receives blob_gas_used)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail (output zeroed).

    Uses 8 bytes of `.data` scratch (`bgvh_count_scratch`). -/
def blobGasUsedFromVersionedHashesFunction : String :=
  "blob_gas_used_from_versioned_hashes:\n" ++
  "  addi sp, sp, -24\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a2                   # gas_per_blob\n" ++
  "  mv s1, a3                   # out ptr\n" ++
  "  la a2, bgvh_count_scratch\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbgvh_fail\n" ++
  "  la t0, bgvh_count_scratch; ld t1, 0(t0)\n" ++
  "  mul t2, t1, s0\n" ++
  "  sd t2, 0(s1)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbgvh_ret\n" ++
  ".Lbgvh_fail:\n" ++
  "  sd zero, 0(s1)\n" ++
  "  li a0, 1\n" ++
  ".Lbgvh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 24\n" ++
  "  ret"

/-- `zisk_blob_gas_used_from_versioned_hashes`: probe BuildUnit.
    Reads (list_len, gas_per_blob, list_bytes) from host input,
    writes (status, blob_gas_used) to OUTPUT (16 bytes total). -/
def ziskBlobGasUsedFromVersionedHashesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # list_len\n" ++
  "  ld a2, 16(a4)               # gas_per_blob\n" ++
  "  addi a0, a4, 24             # list ptr\n" ++
  "  li a3, 0xa0010008           # out at OUTPUT + 8\n" ++
  "  sd zero, 0(a3)\n" ++
  "  jal ra, blob_gas_used_from_versioned_hashes\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbgvh_pdone\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  blobGasUsedFromVersionedHashesFunction ++ "\n" ++
  ".Lbgvh_pdone:"

def ziskBlobGasUsedFromVersionedHashesDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bgvh_count_scratch:\n" ++
  "  .zero 8"

def ziskBlobGasUsedFromVersionedHashesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlobGasUsedFromVersionedHashesPrologue
  dataAsm     := ziskBlobGasUsedFromVersionedHashesDataSection
}

/-! ## tx_validate_against_block -- PR-K69

    Combine three u64 tx-validation invariants into one helper:

      1. tx.chain_id == block.chain_id
      2. tx.gas_limit <= block.gas_limit
      3. tx.nonce == account.nonce

    These are the cheapest tx-validation checks (pre-EVM
    execution); a tx that fails any of them is rejected without
    further work. Mirrors three of the assertions in Python's
    `validate_transaction`:

      assert tx.chain_id == chain.chain_id
      assert tx.gas <= block.gas_limit
      assert tx.nonce == account.nonce

    Pure u64 compares; no scratch memory; leaf-callable.

    Calling convention:
      a0 (input)  : tx.chain_id      (u64)
      a1 (input)  : block.chain_id   (u64)
      a2 (input)  : tx.gas_limit     (u64)
      a3 (input)  : block.gas_limit  (u64)
      a4 (input)  : tx.nonce         (u64)
      a5 (input)  : account.nonce    (u64)
      ra (input)  : return
      a0 (output) :
        0  : all three invariants hold
        1  : chain_id mismatch
        2  : tx.gas_limit > block.gas_limit
        3  : tx.nonce != account.nonce

    Distinct codes let callers pinpoint which check fired
    without re-running individual asserts. -/
def txValidateAgainstBlockFunction : String :=
  "tx_validate_against_block:\n" ++
  "  bne a0, a1, .Ltvab_fail_chain\n" ++
  "  bgtu a2, a3, .Ltvab_fail_gas\n" ++
  "  bne a4, a5, .Ltvab_fail_nonce\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Ltvab_fail_chain:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Ltvab_fail_gas:\n" ++
  "  li a0, 2\n" ++
  "  ret\n" ++
  ".Ltvab_fail_nonce:\n" ++
  "  li a0, 3\n" ++
  "  ret"

/-- `zisk_tx_validate_against_block`: probe BuildUnit. Reads
    (tx_chain, block_chain, tx_gas, block_gas, tx_nonce,
    account_nonce) as 6 u64 LE words from host input, writes
    8-byte status to OUTPUT. -/
def ziskTxValidateAgainstBlockPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a0,  8(t0)               # tx.chain_id\n" ++
  "  ld a1, 16(t0)               # block.chain_id\n" ++
  "  ld a2, 24(t0)               # tx.gas_limit\n" ++
  "  ld a3, 32(t0)               # block.gas_limit\n" ++
  "  ld a4, 40(t0)               # tx.nonce\n" ++
  "  ld a5, 48(t0)               # account.nonce\n" ++
  "  jal ra, tx_validate_against_block\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Ltvab_pdone\n" ++
  txValidateAgainstBlockFunction ++ "\n" ++
  ".Ltvab_pdone:"

def ziskTxValidateAgainstBlockDataSection : String :=
  ".section .data\n" ++
  "tvab_pad:\n" ++
  "  .zero 8"

def ziskTxValidateAgainstBlockProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxValidateAgainstBlockPrologue
  dataAsm     := ziskTxValidateAgainstBlockDataSection
}

/-! ## u256_add_be -- PR-K51 modular addition on BE u256 buffers

    Compute `(a + b) mod 2^256` over two 32-byte big-endian
    `u256` buffers, storing the result in `out` and returning a
    0/1 overflow flag (`1` ⇔ unsigned overflow ⇔ `a + b >= 2^256`).

    BE storage convention: byte 0 = MSB, byte 31 = LSB. Mirrors
    the layout produced by `rlp_field_to_u256_be` and consumed by
    `u256_lt` (PR-K50).

    Building block for `tx_cost = max_fee_per_gas * gas_limit +
    value` in tx validation, and for any subsequent u256
    arithmetic helpers (`u256_sub_be`, `u256_mul_u64`).

    Calling convention:
      a0 (input)  : u256 a ptr (32 bytes, BE)
      a1 (input)  : u256 b ptr (32 bytes, BE)
      a2 (input)  : u256 out ptr (32 bytes, BE; may alias a or b)
      ra (input)  : return
      a0 (output) : 1 on overflow, 0 otherwise.

    Aliasing is safe: `out` may alias `a` or `b`. The
    byte-by-byte loop reads `a[i]` and `b[i]` before writing
    `out[i]` at each step. Pure register arithmetic, no scratch
    memory, leaf-callable. -/
def u256AddBeFunction : String :=
  "u256_add_be:\n" ++
  "  li t0, 31                  # byte index (LSB first)\n" ++
  "  li t1, 0                   # carry\n" ++
  ".Lu256a_loop:\n" ++
  "  add t2, a0, t0\n" ++
  "  add t3, a1, t0\n" ++
  "  add t4, a2, t0\n" ++
  "  lbu t5, 0(t2)\n" ++
  "  lbu t6, 0(t3)\n" ++
  "  add t5, t5, t6\n" ++
  "  add t5, t5, t1             # + carry-in\n" ++
  "  srli t1, t5, 8             # carry-out\n" ++
  "  andi t5, t5, 0xff          # masked sum byte\n" ++
  "  sb t5, 0(t4)\n" ++
  "  beqz t0, .Lu256a_done\n" ++
  "  addi t0, t0, -1\n" ++
  "  j .Lu256a_loop\n" ++
  ".Lu256a_done:\n" ++
  "  mv a0, t1                  # final carry = overflow flag\n" ++
  "  ret"

/-- `zisk_u256_add_be`: probe BuildUnit. Reads (32B a, 32B b) from
    host input, writes (overflow_flag, 32B result) to OUTPUT (40
    bytes total). -/
def ziskU256AddBePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 8              # a ptr\n" ++
  "  addi a1, a3, 40             # b ptr\n" ++
  "  li a2, 0xa0010008           # out ptr at OUTPUT + 8\n" ++
  "  # Pre-zero the 32 output bytes (defensive).\n" ++
  "  mv t0, a2; li t1, 4\n" ++
  ".Lu256a_zinit:\n" ++
  "  beqz t1, .Lu256a_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lu256a_zinit\n" ++
  ".Lu256a_zdone:\n" ++
  "  jal ra, u256_add_be\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # overflow flag\n" ++
  "  j .Lu256a_pdone\n" ++
  u256AddBeFunction ++ "\n" ++
  ".Lu256a_pdone:"

def ziskU256AddBeDataSection : String :=
  ".section .data\n" ++
  "u256a_pad:\n" ++
  "  .zero 8"

def ziskU256AddBeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskU256AddBePrologue
  dataAsm     := ziskU256AddBeDataSection
}

/-! ## u256_sub_be -- PR-K52 modular subtraction on BE u256 buffers

    Compute `(a - b) mod 2^256` over two 32-byte big-endian
    `u256` buffers, storing the result in `out` and returning a
    0/1 borrow flag (`1` ⇔ unsigned underflow ⇔ `a < b`).

    Natural pair to PR-K51 `u256_add_be`. Direct use case:

      new_balance = u256_sub_be(account.balance, tx_cost)
      if borrow: reject tx (insufficient funds)

    BE storage convention: byte 0 = MSB, byte 31 = LSB.

    Calling convention:
      a0 (input)  : u256 a ptr (32 bytes, BE)
      a1 (input)  : u256 b ptr (32 bytes, BE)
      a2 (input)  : u256 out ptr (32 bytes, BE; may alias a or b)
      ra (input)  : return
      a0 (output) : 1 on underflow (a < b), 0 otherwise.

    Aliasing is safe: `out` may alias `a` or `b`. Pure register
    arithmetic, no scratch memory, leaf-callable. -/
def u256SubBeFunction : String :=
  "u256_sub_be:\n" ++
  "  li t0, 31                  # byte index (LSB first)\n" ++
  "  li t1, 0                   # borrow\n" ++
  ".Lu256s_loop:\n" ++
  "  add t2, a0, t0\n" ++
  "  add t3, a1, t0\n" ++
  "  add t4, a2, t0\n" ++
  "  lbu t5, 0(t2)\n" ++
  "  lbu t6, 0(t3)\n" ++
  "  sub t5, t5, t6\n" ++
  "  sub t5, t5, t1             # - borrow-in\n" ++
  "  sltz t1, t5                # borrow-out = (t5 < 0)\n" ++
  "  andi t5, t5, 0xff          # masked diff byte\n" ++
  "  sb t5, 0(t4)\n" ++
  "  beqz t0, .Lu256s_done\n" ++
  "  addi t0, t0, -1\n" ++
  "  j .Lu256s_loop\n" ++
  ".Lu256s_done:\n" ++
  "  mv a0, t1                  # final borrow = underflow flag\n" ++
  "  ret"

/-- `zisk_u256_sub_be`: probe BuildUnit. Reads (32B a, 32B b)
    from host input, writes (borrow_flag, 32B result) to OUTPUT
    (40 bytes total). -/
def ziskU256SubBePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 8              # a ptr\n" ++
  "  addi a1, a3, 40             # b ptr\n" ++
  "  li a2, 0xa0010008           # out ptr at OUTPUT + 8\n" ++
  "  mv t0, a2; li t1, 4\n" ++
  ".Lu256s_zinit:\n" ++
  "  beqz t1, .Lu256s_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lu256s_zinit\n" ++
  ".Lu256s_zdone:\n" ++
  "  jal ra, u256_sub_be\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # borrow flag\n" ++
  "  j .Lu256s_pdone\n" ++
  u256SubBeFunction ++ "\n" ++
  ".Lu256s_pdone:"

def ziskU256SubBeDataSection : String :=
  ".section .data\n" ++
  "u256s_pad:\n" ++
  "  .zero 8"

def ziskU256SubBeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskU256SubBePrologue
  dataAsm     := ziskU256SubBeDataSection
}

/-! ## u256_from_u64_be -- PR-K56 zero-extend u64 → BE u256 buffer

    Materialize a `u64` value as a 32-byte big-endian `u256`
    buffer by zero-extending. Lets callers feed small operands
    (`gas_limit`, `nonce`, `data_length`, etc.) into the u256
    arithmetic and comparison toolkit (`u256_add_be`,
    `u256_sub_be`, `u256_lt`, `u256_eq`, `u256_mul_u64_be`).

    BE storage convention: byte 0 = MSB, byte 31 = LSB. Output:
      bytes 0..24  = 0x00
      bytes 24..32 = u64 value in big-endian order

    Calling convention:
      a0 (input)  : u64 value (in register)
      a1 (input)  : u256 out ptr (32 bytes; will be fully written)
      ra (input)  : return

    Pure register arithmetic except for the 4 zero-stores + 8
    byte-stores; no scratch memory; leaf-callable. Uses RV64 `sb`
    semantics (stores low 8 bits of rs2), so no `andi 0xff`
    masking is needed before each byte write. -/
def u256FromU64BeFunction : String :=
  "u256_from_u64_be:\n" ++
  "  # Zero the high 24 bytes.\n" ++
  "  sd zero,  0(a1)\n" ++
  "  sd zero,  8(a1)\n" ++
  "  sd zero, 16(a1)\n" ++
  "  # Write the u64 in BE order at bytes 24..32.\n" ++
  "  srli t0, a0, 56; sb t0, 24(a1)\n" ++
  "  srli t0, a0, 48; sb t0, 25(a1)\n" ++
  "  srli t0, a0, 40; sb t0, 26(a1)\n" ++
  "  srli t0, a0, 32; sb t0, 27(a1)\n" ++
  "  srli t0, a0, 24; sb t0, 28(a1)\n" ++
  "  srli t0, a0, 16; sb t0, 29(a1)\n" ++
  "  srli t0, a0,  8; sb t0, 30(a1)\n" ++
  "                  sb a0, 31(a1)\n" ++
  "  ret"

/-- `zisk_u256_from_u64_be`: probe BuildUnit. Reads (u64 value)
    from host input, writes the 32-byte BE u256 to OUTPUT. -/
def ziskU256FromU64BePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a2, 0x40000000\n" ++
  "  ld a0, 8(a2)                # value\n" ++
  "  li a1, 0xa0010000           # out ptr at OUTPUT\n" ++
  "  jal ra, u256_from_u64_be\n" ++
  "  j .Lu256f_pdone\n" ++
  u256FromU64BeFunction ++ "\n" ++
  ".Lu256f_pdone:"

def ziskU256FromU64BeDataSection : String :=
  ".section .data\n" ++
  "u256f_pad:\n" ++
  "  .zero 8"

def ziskU256FromU64BeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskU256FromU64BePrologue
  dataAsm     := ziskU256FromU64BeDataSection
}

/-! ## u256_is_zero -- PR-K58 all-zero predicate on BE u256 buffers

    Test whether a 32-byte big-endian `u256` buffer encodes the
    value `0`. Returns `1` if all 32 bytes are zero, else `0`.

    Saves callers from keeping a 32-byte zero buffer around just
    to call `u256_eq` against it. Common pattern in tx
    validation:

      // Reject zero-value txs to a contract creation address
      if not u256_is_zero(tx.value) and tx.is_creation: ...

      // Skip the priority-fee credit if no surplus
      if u256_is_zero(priority_fee_after_cap): goto next

    BE storage convention: byte 0 = MSB, byte 31 = LSB. (For
    is-zero the endian doesn't matter — all-zero bytes mean
    value 0 either way — but kept consistent with the K50/K53
    convention.)

    Calling convention:
      a0 (input)  : u256 ptr (32 bytes)
      ra (input)  : return
      a0 (output) : 1 if all-zero, 0 otherwise.

    Pure register arithmetic: 4 ld + 3 or + 1 seqz. No
    short-circuit (we always read all 32 bytes), keeping
    timing data-independent for any future side-channel
    considerations. Leaf-callable. -/
def u256IsZeroFunction : String :=
  "u256_is_zero:\n" ++
  "  ld t0,  0(a0)\n" ++
  "  ld t1,  8(a0)\n" ++
  "  ld t2, 16(a0)\n" ++
  "  ld t3, 24(a0)\n" ++
  "  or t0, t0, t1\n" ++
  "  or t0, t0, t2\n" ++
  "  or t0, t0, t3\n" ++
  "  seqz a0, t0\n" ++
  "  ret"

/-- `zisk_u256_is_zero`: probe BuildUnit. Reads 32B u256 from host
    input, writes the u64 result. -/
def ziskU256IsZeroPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a1, 0x40000000\n" ++
  "  addi a0, a1, 8              # u256 ptr\n" ++
  "  jal ra, u256_is_zero\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # result\n" ++
  "  j .Lu256z_pdone\n" ++
  u256IsZeroFunction ++ "\n" ++
  ".Lu256z_pdone:"

def ziskU256IsZeroDataSection : String :=
  ".section .data\n" ++
  "u256z_pad:\n" ++
  "  .zero 8"

def ziskU256IsZeroProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskU256IsZeroPrologue
  dataAsm     := ziskU256IsZeroDataSection
}

/-! ## u256_min -- PR-K59 minimum of two BE u256 buffers

    Compare two 32-byte big-endian `u256` buffers and copy the
    smaller (or `a` on equality) into `out`. Standalone — does
    not call `u256_lt` (PR-K50); the byte-walk-and-pick logic
    is inlined to avoid the cross-PR dependency.

    Direct use case — EIP-1559 effective priority fee:

      surplus = u256_sub_be(tx.max_fee_per_gas, base_fee_per_gas)
      priority = u256_min(tx.max_priority_fee_per_gas, surplus)

    Per the Python `transaction_priority_fee_per_gas`:

      def priority_fee(tx, base_fee):
          if tx.type == 0:  # legacy
              return tx.gas_price - base_fee
          else:
              return min(tx.max_priority_fee_per_gas,
                         tx.max_fee_per_gas - base_fee)

    BE storage convention: byte 0 = MSB, byte 31 = LSB.

    Calling convention:
      a0 (input)  : u256 a ptr (32 bytes, BE)
      a1 (input)  : u256 b ptr (32 bytes, BE)
      a2 (input)  : u256 out ptr (may alias a or b)
      ra (input)  : return
      a0 (output) : 0 (the selected pointer is internally chosen).

    The byte-walk pass short-circuits on the first differing
    byte. Then a 4 × (ld + sd) chunk copy emits 32 bytes. Pure
    register arithmetic, no scratch memory, leaf-callable.

    Note on aliasing: if `out` aliases either input, the byte
    walk is read-only over both inputs, and the 4 × (ld + sd)
    copy reads each chunk from one of them and writes to `out`
    in the same step — fine since `ld` happens before `sd`. -/
def u256MinFunction : String :=
  "u256_min:\n" ++
  "  li t0, 0                   # byte index\n" ++
  "  li t6, 32\n" ++
  ".Lumin_lt_loop:\n" ++
  "  beq t0, t6, .Lumin_pick_a  # all bytes equal → return a\n" ++
  "  add t1, a0, t0\n" ++
  "  add t2, a1, t0\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  bltu t3, t4, .Lumin_pick_a # a < b → return a\n" ++
  "  bgtu t3, t4, .Lumin_pick_b # a > b → return b\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lumin_lt_loop\n" ++
  ".Lumin_pick_a:\n" ++
  "  mv t0, a0\n" ++
  "  j .Lumin_copy\n" ++
  ".Lumin_pick_b:\n" ++
  "  mv t0, a1\n" ++
  ".Lumin_copy:\n" ++
  "  ld t1,  0(t0); sd t1,  0(a2)\n" ++
  "  ld t1,  8(t0); sd t1,  8(a2)\n" ++
  "  ld t1, 16(t0); sd t1, 16(a2)\n" ++
  "  ld t1, 24(t0); sd t1, 24(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_u256_min`: probe BuildUnit. Reads (32B a, 32B b) from
    host input, writes the 32B min into OUTPUT. -/
def ziskU256MinPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 8              # a ptr\n" ++
  "  addi a1, a3, 40             # b ptr\n" ++
  "  li a2, 0xa0010000           # out ptr at OUTPUT\n" ++
  "  jal ra, u256_min\n" ++
  "  j .Lumin_pdone\n" ++
  u256MinFunction ++ "\n" ++
  ".Lumin_pdone:"

def ziskU256MinDataSection : String :=
  ".section .data\n" ++
  "umin_pad:\n" ++
  "  .zero 8"

def ziskU256MinProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskU256MinPrologue
  dataAsm     := ziskU256MinDataSection
}

/-! ## u256_max -- PR-K60 maximum of two BE u256 buffers

    Direct companion to PR-K59 `u256_min`. Compares two 32-byte
    big-endian `u256` buffers and copies the larger (or `a` on
    equality) into `out`. Same byte-walk + inline pick logic as
    `u256_min` with inverted selection; no separate `u256_lt`
    dependency.

    Direct use case — EIP-1559 base-fee delta floor:

      base_fee_delta = u256_max(target_fee_delta_div_8,
                                u256_from_u64(1))

    (Per Python `calculate_base_fee_per_gas`'s `max(..., 1)`
    when parent.gas_used > parent_gas_target.)

    BE storage convention: byte 0 = MSB, byte 31 = LSB.

    Calling convention:
      a0 (input)  : u256 a ptr (32 bytes, BE)
      a1 (input)  : u256 b ptr (32 bytes, BE)
      a2 (input)  : u256 out ptr (may alias a or b)
      ra (input)  : return
      a0 (output) : 0.

    Short-circuits on the first differing byte. Pure register
    arithmetic + 4 × (ld + sd) chunk copy. Leaf-callable.
    Aliasing safe. -/
def u256MaxFunction : String :=
  "u256_max:\n" ++
  "  li t0, 0                   # byte index\n" ++
  "  li t6, 32\n" ++
  ".Lumax_loop:\n" ++
  "  beq t0, t6, .Lumax_pick_a  # all bytes equal → return a\n" ++
  "  add t1, a0, t0\n" ++
  "  add t2, a1, t0\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  bgtu t3, t4, .Lumax_pick_a # a > b → return a\n" ++
  "  bltu t3, t4, .Lumax_pick_b # a < b → return b\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lumax_loop\n" ++
  ".Lumax_pick_a:\n" ++
  "  mv t0, a0\n" ++
  "  j .Lumax_copy\n" ++
  ".Lumax_pick_b:\n" ++
  "  mv t0, a1\n" ++
  ".Lumax_copy:\n" ++
  "  ld t1,  0(t0); sd t1,  0(a2)\n" ++
  "  ld t1,  8(t0); sd t1,  8(a2)\n" ++
  "  ld t1, 16(t0); sd t1, 16(a2)\n" ++
  "  ld t1, 24(t0); sd t1, 24(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_u256_max`: probe BuildUnit. Reads (32B a, 32B b) from
    host input, writes the 32B max into OUTPUT. -/
def ziskU256MaxPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 8              # a ptr\n" ++
  "  addi a1, a3, 40             # b ptr\n" ++
  "  li a2, 0xa0010000           # out ptr at OUTPUT\n" ++
  "  jal ra, u256_max\n" ++
  "  j .Lumax_pdone\n" ++
  u256MaxFunction ++ "\n" ++
  ".Lumax_pdone:"

def ziskU256MaxDataSection : String :=
  ".section .data\n" ++
  "umax_pad:\n" ++
  "  .zero 8"

def ziskU256MaxProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskU256MaxPrologue
  dataAsm     := ziskU256MaxDataSection
}

/-! ## u256_div_u64_be -- PR-K61 u256 / u64 byte-by-byte long division

    Compute `(quotient, remainder)` where
    `src = quotient * b + remainder` with `0 <= remainder < b`.
    Stores the 32-byte BE quotient at `out` and returns the
    u64 remainder.

    Direct use case — EIP-1559 base-fee formula:

      parent_gas_target  = parent.gas_limit / 2   (b = 2)
      target_fee_delta   = parent_fee_gas_delta / parent_gas_target  (b ≤ 2^30)
      base_fee_per_gas_delta = target_fee_delta / BASE_FEE_MAX_CHANGE_DENOMINATOR  (b = 8)

    All three divisors fit far inside the safe range.

    ## Precondition: divisor ≤ 2^56

    The byte-by-byte algorithm maintains `carry < b` across
    iterations. Each step computes `num = (carry << 8) | a[i]`.
    For `num` to fit in `u64` we need `carry << 8 < 2^64`, i.e.
    `carry < 2^56`. Since `carry < b`, this is satisfied iff
    `b ≤ 2^56`. The function does NOT check this precondition;
    passing `b > 2^56` produces garbage but no crash.

    The precondition still admits a 56-bit divisor (≈ `7.2e16`),
    which covers every Ethereum-state-related divisor:

      - Gas limits / targets:  < 2^30
      - EIP-1559 denominator:  = 8
      - Withdrawal counts:     < 2^32
      - Per-block tx counts:   < 2^20

    For larger divisors, a future PR can ship a bit-by-bit
    long-division helper supporting `b ≤ 2^63`.

    Also: caller must pass `b > 0`. Passing `b == 0` invokes
    RV64's `divu`-by-zero behavior (quotient = all-1s, remainder
    = dividend) — not a crash, but the output is meaningless.

    BE storage convention: byte 0 = MSB, byte 31 = LSB.

    Calling convention:
      a0 (input)  : u256 src ptr (32 bytes, BE)
      a1 (input)  : u64 b (0 < b ≤ 2^56)
      a2 (input)  : u256 out ptr (32 bytes, BE; may alias src)
      ra (input)  : return
      a0 (output) : u64 remainder.

    Aliasing safe: each iteration reads `src[i]` then writes
    `out[i]`; subsequent iterations advance to `src[i+1]`. -/
def u256DivU64BeFunction : String :=
  "u256_div_u64_be:\n" ++
  "  li t0, 0                   # carry (< b)\n" ++
  "  li t1, 0                   # byte index (MSB → LSB)\n" ++
  ".Lu256d_loop:\n" ++
  "  li t2, 32\n" ++
  "  beq t1, t2, .Lu256d_done\n" ++
  "  add t3, a0, t1\n" ++
  "  lbu t4, 0(t3)              # src[i]\n" ++
  "  slli t5, t0, 8\n" ++
  "  or t5, t5, t4              # num = (carry << 8) | src[i]\n" ++
  "  divu t6, t5, a1            # q_byte = num / b  (< 256)\n" ++
  "  remu t0, t5, a1            # new carry = num mod b\n" ++
  "  add t3, a2, t1\n" ++
  "  sb t6, 0(t3)               # out[i] = q_byte (low 8 bits)\n" ++
  "  addi t1, t1, 1\n" ++
  "  j .Lu256d_loop\n" ++
  ".Lu256d_done:\n" ++
  "  mv a0, t0                  # remainder\n" ++
  "  ret"

/-- `zisk_u256_div_u64_be`: probe BuildUnit. Reads (32B BE src,
    8B LE b) from host input, writes (u64 remainder, 32B BE
    quotient) to OUTPUT (40 bytes total). -/
def ziskU256DivU64BePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 8              # src ptr (32B BE)\n" ++
  "  ld a1, 40(a3)               # b (u64 LE)\n" ++
  "  li a2, 0xa0010008           # out ptr at OUTPUT + 8\n" ++
  "  # Pre-zero 32 output bytes (defensive).\n" ++
  "  mv t0, a2; li t1, 4\n" ++
  ".Lu256d_zout:\n" ++
  "  beqz t1, .Lu256d_zout_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lu256d_zout\n" ++
  ".Lu256d_zout_done:\n" ++
  "  jal ra, u256_div_u64_be\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # remainder\n" ++
  "  j .Lu256d_pdone\n" ++
  u256DivU64BeFunction ++ "\n" ++
  ".Lu256d_pdone:"

def ziskU256DivU64BeDataSection : String :=
  ".section .data\n" ++
  "u256d_pad:\n" ++
  "  .zero 8"

def ziskU256DivU64BeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskU256DivU64BePrologue
  dataAsm     := ziskU256DivU64BeDataSection
}


/-! ## priority_fee_per_gas_eip1559 -- PR-K62

    Compute the effective priority fee per gas for a post-EIP-1559
    transaction. Mirrors Python's
    `transaction_priority_fee_per_gas` from
    `forks/amsterdam/transaction_helpers.py`:

      surplus = tx.max_fee_per_gas - block.base_fee_per_gas
      priority_fee = min(tx.max_priority_fee_per_gas, surplus)

    Where `surplus = max_fee - base_fee` would underflow
    (`max_fee < base_fee`), the tx is invalid; this helper
    returns `1` so the caller can reject without inspecting the
    output. Otherwise returns `0` and the 32-byte priority fee
    is written to `*out` in big-endian.

    First higher-level helper composed on the K-stack's u256
    toolkit: PR-K52 `u256_sub_be` + PR-K59 `u256_min`. Both are
    inlined into the probe BuildUnit so this PR doesn't require
    any new external symbols.

    BE storage convention: byte 0 = MSB, byte 31 = LSB.

    Calling convention:
      a0 (input)  : max_priority_fee_per_gas ptr (32 B BE)
      a1 (input)  : max_fee_per_gas ptr (32 B BE)
      a2 (input)  : base_fee_per_gas ptr (32 B BE)
      a3 (input)  : output ptr (32 B BE; receives priority fee)
      ra (input)  : return
      a0 (output) : 0 success / 1 max_fee < base_fee (reject tx). -/
def priorityFeePerGasEip1559Function : String :=
  "priority_fee_per_gas_eip1559:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # max_priority ptr\n" ++
  "  mv s1, a1                   # max_fee ptr\n" ++
  "  mv s2, a2                   # base_fee ptr\n" ++
  "  mv s3, a3                   # out ptr\n" ++
  "  # surplus = max_fee - base_fee  (store in out)\n" ++
  "  mv a0, s1; mv a1, s2; mv a2, s3\n" ++
  "  jal ra, u256_sub_be\n" ++
  "  bnez a0, .Lpfee_fail        # borrow → max_fee < base_fee\n" ++
  "  # priority_fee = min(max_priority, surplus); aliasing OK\n" ++
  "  mv a0, s0; mv a1, s3; mv a2, s3\n" ++
  "  jal ra, u256_min\n" ++
  "  li a0, 0\n" ++
  "  j .Lpfee_ret\n" ++
  ".Lpfee_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lpfee_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_priority_fee_per_gas_eip1559`: probe BuildUnit. Reads
    (32B max_priority, 32B max_fee, 32B base_fee) from host
    input, writes (status, 32B priority fee BE) to OUTPUT (40
    bytes total). -/
def ziskPriorityFeePerGasEip1559Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  addi a0, a4, 8              # max_priority ptr\n" ++
  "  addi a1, a4, 40             # max_fee ptr\n" ++
  "  addi a2, a4, 72             # base_fee ptr\n" ++
  "  li a3, 0xa0010008           # out ptr\n" ++
  "  mv t0, a3; li t1, 4\n" ++
  ".Lpfee_zout:\n" ++
  "  beqz t1, .Lpfee_zout_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lpfee_zout\n" ++
  ".Lpfee_zout_done:\n" ++
  "  jal ra, priority_fee_per_gas_eip1559\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lpfee_pdone\n" ++
  u256SubBeFunction ++ "\n" ++
  u256MinFunction ++ "\n" ++
  priorityFeePerGasEip1559Function ++ "\n" ++
  ".Lpfee_pdone:"

def ziskPriorityFeePerGasEip1559DataSection : String :=
  ".section .data\n" ++
  "pfee_pad:\n" ++
  "  .zero 8"

def ziskPriorityFeePerGasEip1559ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskPriorityFeePerGasEip1559Prologue
  dataAsm     := ziskPriorityFeePerGasEip1559DataSection
}

/-! ## effective_gas_price_eip1559 -- PR-K70

    Compute the effective gas price for an EIP-1559 transaction:

      effective_gas_price = base_fee
                           + min(max_priority_fee, max_fee - base_fee)

    Equivalent (per Python `transaction_effective_gas_price`):

      effective_gas_price = min(max_fee, base_fee + max_priority_fee)

    The two formulations match because
    `base + min(max_priority, max_fee - base) =
     min(base + max_priority, max_fee)`.

    Composes PR-K62 `priority_fee_per_gas_eip1559` (#5612) with
    PR-K51 `u256_add_be`. The priority-fee step writes its
    result to `out`; the add step folds `base_fee` in place.

    If `max_fee < base_fee` (would-underflow in the priority-fee
    step), this helper returns `1` so the caller can reject the
    tx without inspecting the output.

    Calling convention:
      a0 (input)  : max_priority_fee_per_gas ptr (32 B BE)
      a1 (input)  : max_fee_per_gas ptr (32 B BE)
      a2 (input)  : base_fee_per_gas ptr (32 B BE)
      a3 (input)  : output ptr (32 B BE; receives effective gas price)
      ra (input)  : return
      a0 (output) : 0 success / 1 max_fee < base_fee (reject tx). -/
def effectiveGasPriceEip1559Function : String :=
  "effective_gas_price_eip1559:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a2                   # base_fee ptr\n" ++
  "  mv s1, a3                   # out ptr\n" ++
  "  # Step 1: priority_fee = priority_fee_per_gas_eip1559(...)\n" ++
  "  jal ra, priority_fee_per_gas_eip1559\n" ++
  "  bnez a0, .Legpe_fail\n" ++
  "  # Step 2: effective = base_fee + priority_fee   (out = base + out)\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_add_be         # overflow flag in a0 (always 0 in practice)\n" ++
  "  li a0, 0\n" ++
  "  j .Legpe_ret\n" ++
  ".Legpe_fail:\n" ++
  "  li a0, 1\n" ++
  ".Legpe_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_effective_gas_price_eip1559`: probe BuildUnit. Reads
    (max_priority, max_fee, base_fee) from host input, writes
    (status, effective_gas_price) to OUTPUT (40 bytes). -/
def ziskEffectiveGasPriceEip1559Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  addi a0, a4, 8              # max_priority ptr\n" ++
  "  addi a1, a4, 40             # max_fee ptr\n" ++
  "  addi a2, a4, 72             # base_fee ptr\n" ++
  "  li a3, 0xa0010008           # out ptr\n" ++
  "  mv t0, a3; li t1, 4\n" ++
  ".Legpe_zout:\n" ++
  "  beqz t1, .Legpe_zout_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Legpe_zout\n" ++
  ".Legpe_zout_done:\n" ++
  "  jal ra, effective_gas_price_eip1559\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Legpe_pdone\n" ++
  u256SubBeFunction ++ "\n" ++
  u256MinFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  priorityFeePerGasEip1559Function ++ "\n" ++
  effectiveGasPriceEip1559Function ++ "\n" ++
  ".Legpe_pdone:"

def ziskEffectiveGasPriceEip1559DataSection : String :=
  ".section .data\n" ++
  "egpe_pad:\n" ++
  "  .zero 8"

def ziskEffectiveGasPriceEip1559ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskEffectiveGasPriceEip1559Prologue
  dataAsm     := ziskEffectiveGasPriceEip1559DataSection
}

/-! ## u256_eq -- PR-K53 equality companion to PR-K50 u256_lt

    Equality predicate on two 32-byte big-endian `u256` buffers.
    Returns `1` if `a == b`, else `0`. Pair to PR-K50 `u256_lt`
    so callers can express `a >= b` as `!u256_lt(a, b)` plus
    optionally `u256_eq` for equality discrimination, or `a > b`
    as `u256_lt(b, a)`, etc.

    BE storage convention: byte 0 = MSB, byte 31 = LSB.

    Calling convention:
      a0 (input)  : u256 a ptr (32 bytes, BE)
      a1 (input)  : u256 b ptr (32 bytes, BE)
      ra (input)  : return
      a0 (output) : 1 if a == b, 0 otherwise.

    Pure register arithmetic, no scratch memory, leaf-callable.
    Walks at most 32 bytes; short-circuits on the first
    differing byte. -/
def u256EqFunction : String :=
  "u256_eq:\n" ++
  "  li t0, 0                   # byte index\n" ++
  "  li t6, 32\n" ++
  ".Lu256eq_loop:\n" ++
  "  beq t0, t6, .Lu256eq_yes   # 32 bytes equal → a == b\n" ++
  "  add t1, a0, t0\n" ++
  "  add t2, a1, t0\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  bne t3, t4, .Lu256eq_no\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lu256eq_loop\n" ++
  ".Lu256eq_yes:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Lu256eq_no:\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_u256_eq`: probe BuildUnit. Reads (32B a, 32B b) from
    host input, writes the u64 result. -/
def ziskU256EqPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a2, 0x40000000\n" ++
  "  addi a0, a2, 8              # a ptr\n" ++
  "  addi a1, a2, 40             # b ptr (a + 32)\n" ++
  "  jal ra, u256_eq\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # result\n" ++
  "  j .Lu256eq_pdone\n" ++
  u256EqFunction ++ "\n" ++
  ".Lu256eq_pdone:"

def ziskU256EqDataSection : String :=
  ".section .data\n" ++
  "u256eq_pad:\n" ++
  "  .zero 8"

def ziskU256EqProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskU256EqPrologue
  dataAsm     := ziskU256EqDataSection
}


/-! ## u256_mul_u64_be -- PR-K54 u256 × u64 schoolbook multiply

    Compute `(a * b) mod 2^256` where `a` is a 32-byte big-endian
    `u256` buffer and `b` is a u64 scalar. Stores the low 256 bits
    of the product in `out` (BE) and returns a 0/1 overflow flag.

    Direct use case: `tx_cost = max_fee_per_gas * gas_limit` in
    tx validation (then `+ value` via PR-K51 `u256_add_be`).

    Algorithm: byte-by-byte schoolbook over the u256 operand,
    avoiding any BE↔u64 conversion of `a`. For each byte
    `a[31-p]` (p in 0..31, LSB first):

      1. partial = a[31-p] * b  (u72; mul + mulhu)
      2. add `partial` to an LSB-first 40-byte accumulator at
         byte offset `p`, with carry propagation
      3. After all 32 bytes, accumulator[0..32] = low 256 bits
         (LSB first), accumulator[32..40] holds the high 64 bits

    Final output:
      out[i]   = accumulator[31 - i]  for i in 0..32  (BE)
      overflow = (accumulator[32..40] != 0)

    The accumulator lives in `.data` (`u256m_acc`, 40 bytes), so
    this function is NOT reentrant.

    Calling convention:
      a0 (input)  : u256 a ptr (32 bytes, BE)
      a1 (input)  : u64 b (scalar, in register)
      a2 (input)  : u256 out ptr (32 bytes, BE; out may alias a;
                    must NOT alias `u256m_acc`)
      ra (input)  : return
      a0 (output) : 1 on overflow (a * b >= 2^256), 0 otherwise.

    Uses 40 bytes of `.data` scratch (`u256m_acc`). -/
def u256MulU64BeFunction : String :=
  "u256_mul_u64_be:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                  # a ptr\n" ++
  "  mv s1, a1                  # b\n" ++
  "  mv s2, a2                  # out ptr\n" ++
  "  # Zero 40-byte accumulator.\n" ++
  "  la s3, u256m_acc\n" ++
  "  mv t0, s3\n" ++
  "  li t1, 5\n" ++
  ".Lmul_zinit:\n" ++
  "  beqz t1, .Lmul_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lmul_zinit\n" ++
  ".Lmul_zdone:\n" ++
  "  # Outer loop: p in 0..32 (byte position from LSB).\n" ++
  "  li s4, 0\n" ++
  ".Lmul_outer:\n" ++
  "  li t0, 32\n" ++
  "  beq s4, t0, .Lmul_post\n" ++
  "  # byte_a = a[31 - p]\n" ++
  "  li t0, 31\n" ++
  "  sub t0, t0, s4\n" ++
  "  add t0, s0, t0\n" ++
  "  lbu t0, 0(t0)\n" ++
  "  beqz t0, .Lmul_step        # skip zero bytes (optimization)\n" ++
  "  # partial = byte_a * b: low 64 in t1, high ≤ 0xff in t2.\n" ++
  "  mul   t1, t0, s1\n" ++
  "  mulhu t2, t0, s1\n" ++
  "  # Add to acc[p..p+9] with carry.\n" ++
  "  add t3, s3, s4             # &acc[p]\n" ++
  "  li t4, 8                   # 8 low bytes\n" ++
  "  li t5, 0                   # carry\n" ++
  ".Lmul_addlo:\n" ++
  "  lbu t6, 0(t3)\n" ++
  "  andi a3, t1, 0xff\n" ++
  "  add  t6, t6, a3\n" ++
  "  add  t6, t6, t5\n" ++
  "  andi a3, t6, 0xff\n" ++
  "  sb   a3, 0(t3)\n" ++
  "  srli t5, t6, 8\n" ++
  "  srli t1, t1, 8\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lmul_addlo\n" ++
  "  # Add p_hi (t2; ≤ 1 byte) + carry at acc[p+8].\n" ++
  "  lbu t6, 0(t3)\n" ++
  "  add t6, t6, t2\n" ++
  "  add t6, t6, t5\n" ++
  "  andi a3, t6, 0xff\n" ++
  "  sb   a3, 0(t3)\n" ++
  "  srli t5, t6, 8\n" ++
  "  addi t3, t3, 1\n" ++
  "  # Propagate remaining carry through higher bytes.\n" ++
  ".Lmul_carry:\n" ++
  "  beqz t5, .Lmul_step\n" ++
  "  lbu t6, 0(t3)\n" ++
  "  add t6, t6, t5\n" ++
  "  andi a3, t6, 0xff\n" ++
  "  sb   a3, 0(t3)\n" ++
  "  srli t5, t6, 8\n" ++
  "  addi t3, t3, 1\n" ++
  "  j .Lmul_carry\n" ++
  ".Lmul_step:\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lmul_outer\n" ++
  ".Lmul_post:\n" ++
  "  # Copy acc[0..32] (LSB first) into out (BE, MSB first).\n" ++
  "  mv t0, s3                  # acc cursor (LSB)\n" ++
  "  addi t1, s2, 32            # out end (exclusive)\n" ++
  "  li t2, 32\n" ++
  ".Lmul_copy:\n" ++
  "  beqz t2, .Lmul_overflow_check\n" ++
  "  addi t1, t1, -1\n" ++
  "  lbu t3, 0(t0)\n" ++
  "  sb t3, 0(t1)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Lmul_copy\n" ++
  ".Lmul_overflow_check:\n" ++
  "  # t0 now points to acc[32]; any nonzero in acc[32..40] → overflow.\n" ++
  "  li t1, 8\n" ++
  "  li a0, 0\n" ++
  ".Lmul_of_loop:\n" ++
  "  beqz t1, .Lmul_done\n" ++
  "  lbu t3, 0(t0)\n" ++
  "  beqz t3, .Lmul_of_next\n" ++
  "  li a0, 1\n" ++
  "  j .Lmul_done\n" ++
  ".Lmul_of_next:\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lmul_of_loop\n" ++
  ".Lmul_done:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_u256_mul_u64_be`: probe BuildUnit. Reads (32B a BE,
    8B b LE) from host input, writes (overflow_flag, 32B result
    BE) to OUTPUT (40 bytes total). -/
def ziskU256MulU64BePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 8              # a ptr (32B BE)\n" ++
  "  ld a1, 40(a3)               # b (u64 LE)\n" ++
  "  li a2, 0xa0010008           # out ptr at OUTPUT + 8\n" ++
  "  # Pre-zero the 32 output bytes (defensive).\n" ++
  "  mv t0, a2; li t1, 4\n" ++
  ".Lmul_zout:\n" ++
  "  beqz t1, .Lmul_zout_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lmul_zout\n" ++
  ".Lmul_zout_done:\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # overflow flag\n" ++
  "  j .Lmul_pdone\n" ++
  u256MulU64BeFunction ++ "\n" ++
  ".Lmul_pdone:"

def ziskU256MulU64BeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40"

def ziskU256MulU64BeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskU256MulU64BePrologue
  dataAsm     := ziskU256MulU64BeDataSection
}

/-! ## tx_cost_compute -- PR-K71

    Compute the full upfront cost of a transaction:

      tx_cost = gas_limit × effective_gas_price + value

    This is the value that must not exceed `account.balance` for
    the tx to be valid. Mirrors the Python check in
    `validate_transaction` / `process_transaction`:

      max_gas_fee = tx.gas * effective_gas_price
      if sender.balance < max_gas_fee + tx.value:
          raise InsufficientBalance

    Composes:
      - PR-K54 `u256_mul_u64_be` for the multiplication step
      - PR-K51 `u256_add_be` for adding `value`

    Reports overflow on either step via `status=1`. In practice
    `effective_gas_price ≤ max_fee_per_gas` is u128-sized at
    most, so the multiplicand fits comfortably; overflow is a
    "garbage input" safety net.

    BE storage convention: byte 0 = MSB, byte 31 = LSB.

    Calling convention:
      a0 (input)  : effective_gas_price ptr (32 B BE)
      a1 (input)  : gas_limit (u64)
      a2 (input)  : value ptr (32 B BE)
      a3 (input)  : out ptr (32 B BE; receives tx_cost)
      ra (input)  : return
      a0 (output) : 0 success / 1 overflow on mul or add. -/
def txCostComputeFunction : String :=
  "tx_cost_compute:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a2                   # value ptr\n" ++
  "  mv s1, a3                   # out ptr\n" ++
  "  # Step 1: out = effective_gas_price × gas_limit.\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Ltcc_fail\n" ++
  "  # Step 2: out = out + value.\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s0\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Ltcc_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Ltcc_ret\n" ++
  ".Ltcc_fail:\n" ++
  "  li a0, 1\n" ++
  ".Ltcc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_tx_cost_compute`: probe BuildUnit. Reads (32B egp, 8B
    gas_limit LE, 32B value) from host input, writes (status,
    32B tx_cost BE) to OUTPUT (40 bytes total). -/
def ziskTxCostComputePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  addi a0, a4, 8              # egp ptr\n" ++
  "  ld a1, 40(a4)               # gas_limit (u64)\n" ++
  "  addi a2, a4, 48             # value ptr\n" ++
  "  li a3, 0xa0010008           # out ptr\n" ++
  "  mv t0, a3; li t1, 4\n" ++
  ".Ltcc_zout:\n" ++
  "  beqz t1, .Ltcc_zout_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Ltcc_zout\n" ++
  ".Ltcc_zout_done:\n" ++
  "  jal ra, tx_cost_compute\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Ltcc_pdone\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  txCostComputeFunction ++ "\n" ++
  ".Ltcc_pdone:"

def ziskTxCostComputeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40"

def ziskTxCostComputeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxCostComputePrologue
  dataAsm     := ziskTxCostComputeDataSection
}

/-! ## validate_transaction_balance -- PR-K79

    Verify that the sender's account balance covers the
    worst-case (pre-execution) tx cost:

      tx_cost = tx.max_fee_per_gas × tx.gas_limit + tx.value
      assert sender.balance >= tx_cost

    This is the pre-flight check from Python's
    `validate_transaction`:

      max_gas_fee = tx.gas * tx.max_fee_per_gas
      if sender.balance < max_gas_fee + tx.value:
          raise InsufficientBalance

    Note: this uses `max_fee_per_gas` (the absolute cap), not
    `effective_gas_price` — the worst-case cost the sender could
    incur. Post-execution, the actual cost uses the lower
    effective_gas_price.

    Composes PR-K71 `tx_cost_compute` (#5723) + an inline
    byte-walk `>=` comparison (no dependency on still-pending
    PR-K50 `u256_lt`).

    Calling convention:
      a0 (input)  : max_fee_per_gas ptr (32 B BE)
      a1 (input)  : gas_limit (u64)
      a2 (input)  : value ptr (32 B BE)
      a3 (input)  : sender.balance ptr (32 B BE)
      ra (input)  : return
      a0 (output) :
        0  : balance >= tx_cost (ok)
        1  : tx_cost computation overflowed u256
        2  : balance < tx_cost (insufficient funds)

    Uses 32 bytes of `.data` scratch (`vtbal_cost_scratch`). -/
def validateTransactionBalanceFunction : String :=
  "validate_transaction_balance:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  mv s0, a3                   # save balance ptr\n" ++
  "  # tx_cost = tx_cost_compute(max_fee, gas_limit, value, vtbal_cost_scratch)\n" ++
  "  la a3, vtbal_cost_scratch\n" ++
  "  jal ra, tx_cost_compute\n" ++
  "  bnez a0, .Lvtbal_overflow\n" ++
  "  # Inline byte-walk: balance >= cost (MSB→LSB).\n" ++
  "  la t0, vtbal_cost_scratch   # cost ptr\n" ++
  "  mv t1, s0                   # balance ptr\n" ++
  "  li t2, 0\n" ++
  "  li t3, 32\n" ++
  ".Lvtbal_cmp:\n" ++
  "  beq t2, t3, .Lvtbal_ok      # all 32 bytes equal → balance == cost → ok\n" ++
  "  add t4, t1, t2\n" ++
  "  add t5, t0, t2\n" ++
  "  lbu t6, 0(t4)\n" ++
  "  lbu a7, 0(t5)\n" ++
  "  bltu t6, a7, .Lvtbal_lt\n" ++
  "  bgtu t6, a7, .Lvtbal_ok\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lvtbal_cmp\n" ++
  ".Lvtbal_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Lvtbal_ret\n" ++
  ".Lvtbal_lt:\n" ++
  "  li a0, 2\n" ++
  "  j .Lvtbal_ret\n" ++
  ".Lvtbal_overflow:\n" ++
  "  li a0, 1\n" ++
  ".Lvtbal_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_validate_transaction_balance`: probe BuildUnit. Reads
    (32B max_fee, 8B gas_limit LE, 32B value, 32B balance) from
    host input, writes 8-byte status to OUTPUT. -/
def ziskValidateTransactionBalancePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  addi a0, a4, 8              # max_fee ptr\n" ++
  "  ld a1, 40(a4)               # gas_limit (u64)\n" ++
  "  addi a2, a4, 48             # value ptr\n" ++
  "  addi a3, a4, 80             # balance ptr\n" ++
  "  jal ra, validate_transaction_balance\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lvtbal_pdone\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  txCostComputeFunction ++ "\n" ++
  validateTransactionBalanceFunction ++ "\n" ++
  ".Lvtbal_pdone:"

def ziskValidateTransactionBalanceDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40\n" ++
  ".balign 32\n" ++
  "vtbal_cost_scratch:\n" ++
  "  .zero 32"

def ziskValidateTransactionBalanceProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateTransactionBalancePrologue
  dataAsm     := ziskValidateTransactionBalanceDataSection
}

/-! ## u256_to_u64_be -- PR-K57 truncate BE u256 → u64 with overflow flag

    Truncate a 32-byte big-endian `u256` buffer down to its
    low 64 bits, storing them at `*out`. Returns a 0/1 overflow
    flag: `1` if any of the high 192 bits are nonzero, `0`
    otherwise.

    Natural inverse of PR-K56 `u256_from_u64_be`. Together they
    let callers move values between the u256 BE byte-buffer
    representation and the u64 register-resident form.

    Direct use cases:
      - `gas_left = u256_to_u64_be(account.balance / gas_price)`
      - Tx validation: check `intrinsic_gas <= tx.gas_limit`
        after computing intrinsic gas as a u64
      - Compact a small u256 result for further u64-domain work

    BE storage convention: byte 0 = MSB, byte 31 = LSB.

    Calling convention:
      a0 (input)  : u256 src ptr (32 bytes, BE)
      a1 (input)  : u64 out ptr
      ra (input)  : return
      a0 (output) : 1 on overflow (high 192 bits nonzero), 0 otherwise.

    Pure register arithmetic, no scratch memory, leaf-callable.
    Always writes the low-64-bit value to `*out`, even on
    overflow (so callers don't need to branch on the flag to
    read a defined value). -/
def u256ToU64BeFunction : String :=
  "u256_to_u64_be:\n" ++
  "  # Check high 24 bytes (positions 0..24) are all zero.\n" ++
  "  ld t0,  0(a0)\n" ++
  "  ld t1,  8(a0)\n" ++
  "  ld t2, 16(a0)\n" ++
  "  or t0, t0, t1\n" ++
  "  or t0, t0, t2\n" ++
  "  # Assemble low u64 from BE bytes at positions 24..32.\n" ++
  "  lbu t1, 24(a0); slli t1, t1, 56\n" ++
  "  lbu t2, 25(a0); slli t2, t2, 48; or t1, t1, t2\n" ++
  "  lbu t2, 26(a0); slli t2, t2, 40; or t1, t1, t2\n" ++
  "  lbu t2, 27(a0); slli t2, t2, 32; or t1, t1, t2\n" ++
  "  lbu t2, 28(a0); slli t2, t2, 24; or t1, t1, t2\n" ++
  "  lbu t2, 29(a0); slli t2, t2, 16; or t1, t1, t2\n" ++
  "  lbu t2, 30(a0); slli t2, t2,  8; or t1, t1, t2\n" ++
  "  lbu t2, 31(a0);                  or t1, t1, t2\n" ++
  "  sd t1, 0(a1)\n" ++
  "  snez a0, t0                      # overflow = (high bits != 0)\n" ++
  "  ret"

/-- `zisk_u256_to_u64_be`: probe BuildUnit. Reads 32B BE u256
    from host input, writes (overflow_flag, u64 result LE) to
    OUTPUT (16 bytes total). -/
def ziskU256ToU64BePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a2, 0x40000000\n" ++
  "  addi a0, a2, 8              # src ptr\n" ++
  "  li a1, 0xa0010008           # u64 out\n" ++
  "  jal ra, u256_to_u64_be\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # overflow flag\n" ++
  "  j .Lu256t_pdone\n" ++
  u256ToU64BeFunction ++ "\n" ++
  ".Lu256t_pdone:"

def ziskU256ToU64BeDataSection : String :=
  ".section .data\n" ++
  "u256t_pad:\n" ++
  "  .zero 8"

def ziskU256ToU64BeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskU256ToU64BePrologue
  dataAsm     := ziskU256ToU64BeDataSection
}


/-! ## tx_type_dispatch -- PR-K40 typed-tx prefix detector

    Read the first byte of an RLP/typed-tx-encoded transaction
    and return the type code + inner-RLP offset:

      byte 0 ≥ 0xc0     → legacy (type=0, inner_offset=0)
      byte 0 == 0x01    → EIP-2930 access list (type=1, inner_offset=1)
      byte 0 == 0x02    → EIP-1559 dynamic fee  (type=2, inner_offset=1)
      byte 0 == 0x03    → EIP-4844 blob         (type=3, inner_offset=1)
      byte 0 == 0x04    → EIP-7702 set code     (type=4, inner_offset=1)
      else              → invalid (status=1)

    Callers consume `inner_offset` to skip the type prefix
    before passing the remaining bytes to the type-specific
    decoder.

    Calling convention:
      a0 (input)  : tx_bytes ptr
      a1 (input)  : tx_bytes byte length
      a2 (input)  : u64 type code out
      a3 (input)  : u64 inner_offset out
      ra (input)  : return
      a0 (output) : 0 success / 1 unknown / empty input

    Leaf-callable, no scratch. -/
def txTypeDispatchFunction : String :=
  "tx_type_dispatch:\n" ++
  "  beqz a1, .Ltd_fail\n" ++
  "  lbu t0, 0(a0)\n" ++
  "  li t1, 0xc0\n" ++
  "  bgeu t0, t1, .Ltd_legacy\n" ++
  "  li t1, 1\n" ++
  "  beq t0, t1, .Ltd_t1\n" ++
  "  li t1, 2\n" ++
  "  beq t0, t1, .Ltd_t2\n" ++
  "  li t1, 3\n" ++
  "  beq t0, t1, .Ltd_t3\n" ++
  "  li t1, 4\n" ++
  "  beq t0, t1, .Ltd_t4\n" ++
  "  j .Ltd_fail\n" ++
  ".Ltd_legacy:\n" ++
  "  sd zero, 0(a2)\n" ++
  "  sd zero, 0(a3)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Ltd_t1:\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(a2)\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(a3)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Ltd_t2:\n" ++
  "  li t0, 2\n" ++
  "  sd t0, 0(a2)\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(a3)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Ltd_t3:\n" ++
  "  li t0, 3\n" ++
  "  sd t0, 0(a2)\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(a3)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Ltd_t4:\n" ++
  "  li t0, 4\n" ++
  "  sd t0, 0(a2)\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(a3)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Ltd_fail:\n" ++
  "  sd zero, 0(a2)\n" ++
  "  sd zero, 0(a3)\n" ++
  "  li a0, 1\n" ++
  "  ret"

/-- `zisk_tx_type_dispatch`: probe BuildUnit. -/
def ziskTxTypeDispatchPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # tx_len\n" ++
  "  addi a0, a4, 16             # tx ptr\n" ++
  "  li a2, 0xa0010008           # type out\n" ++
  "  li a3, 0xa0010010           # inner_offset out\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Ltd_pdone\n" ++
  txTypeDispatchFunction ++ "\n" ++
  ".Ltd_pdone:"

def ziskTxTypeDispatchDataSection : String :=
  ".section .data\n" ++
  "td_pad:\n" ++
  "  .zero 8"

def ziskTxTypeDispatchProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxTypeDispatchPrologue
  dataAsm     := ziskTxTypeDispatchDataSection
}

/-! ## tx_extract_nonce_and_gas -- PR-K102

    Extract the (`nonce`, `gas_limit`) pair from any encoded tx
    type. Both are u64-bounded by EIP-2681 / EIP-1559 / EIP-4844.

    Per-type field indices (post type-byte stripping):

      type 0 legacy   : nonce = 0,  gas_limit = 2
      type 1 EIP-2930 : nonce = 1,  gas_limit = 3
      type 2 EIP-1559 : nonce = 1,  gas_limit = 4
      type 3 EIP-4844 : nonce = 1,  gas_limit = 4
      type 4 EIP-7702 : nonce = 1,  gas_limit = 4

    Composes:
      - PR-K40 `tx_type_dispatch`  — typed-tx detector
      - PR-K53 `rlp_field_to_u64`  — u64 field extraction

    Useful as a fast prelude to `check_transaction` (nonce
    ordering + gas-availability) without a full per-type decode.

    Calling convention:
      a0 (input)  : tx_bytes ptr (encoded form)
      a1 (input)  : tx_bytes byte length
      a2 (input)  : u64 nonce out ptr
      a3 (input)  : u64 gas_limit out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : tx_type_dispatch failed
        2 : nonce field extraction failed
        3 : gas_limit field extraction failed

    Both outputs are zeroed on failure. Uses two 8-byte `.data`
    scratch slots (`teng_type`, `teng_inner_off`). -/
def txExtractNonceAndGasFunction : String :=
  "tx_extract_nonce_and_gas:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # tx_ptr\n" ++
  "  mv s1, a1                   # tx_len\n" ++
  "  mv s2, a2                   # nonce out\n" ++
  "  mv s3, a3                   # gas out\n" ++
  "  sd zero, 0(s2); sd zero, 0(s3)\n" ++
  "  # Step 1: tx_type_dispatch\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, teng_type\n" ++
  "  la a3, teng_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  beqz a0, .Lteng_after_dispatch\n" ++
  "  li a0, 1\n" ++
  "  j .Lteng_ret\n" ++
  ".Lteng_after_dispatch:\n" ++
  "  la t0, teng_type;      ld s4, 0(t0)    # type → s4\n" ++
  "  la t0, teng_inner_off; ld t5, 0(t0)\n" ++
  "  add s5, s0, t5                          # inner_ptr → s5\n" ++
  "  sub s6, s1, t5                          # inner_len → s6\n" ++
  "  # Step 2: extract nonce.\n" ++
  "  li t0, 0\n" ++
  "  beq s4, t0, .Lteng_n_legacy\n" ++
  "  li t1, 1                              # typed: nonce index = 1\n" ++
  "  j .Lteng_n_have\n" ++
  ".Lteng_n_legacy:\n" ++
  "  li t1, 0                              # legacy: nonce index = 0\n" ++
  ".Lteng_n_have:\n" ++
  "  mv a0, s5\n" ++
  "  mv a1, s6\n" ++
  "  mv a2, t1\n" ++
  "  mv a3, s2\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  beqz a0, .Lteng_step3\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 2\n" ++
  "  j .Lteng_ret\n" ++
  ".Lteng_step3:\n" ++
  "  # Step 3: extract gas_limit.\n" ++
  "  li t0, 0\n" ++
  "  beq s4, t0, .Lteng_g_legacy\n" ++
  "  li t0, 1\n" ++
  "  beq s4, t0, .Lteng_g_2930\n" ++
  "  li t1, 4                              # type 2/3/4: gas index = 4\n" ++
  "  j .Lteng_g_have\n" ++
  ".Lteng_g_legacy:\n" ++
  "  li t1, 2                              # legacy: gas index = 2\n" ++
  "  j .Lteng_g_have\n" ++
  ".Lteng_g_2930:\n" ++
  "  li t1, 3                              # 2930: gas index = 3\n" ++
  ".Lteng_g_have:\n" ++
  "  mv a0, s5\n" ++
  "  mv a1, s6\n" ++
  "  mv a2, t1\n" ++
  "  mv a3, s3\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  beqz a0, .Lteng_ok\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li a0, 3\n" ++
  "  j .Lteng_ret\n" ++
  ".Lteng_ok:\n" ++
  "  li a0, 0\n" ++
  ".Lteng_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_tx_extract_nonce_and_gas`: probe BuildUnit. Reads
    (tx_len, tx_bytes) from host input, writes (status, nonce u64,
    gas u64) to OUTPUT (24 bytes total). -/
def ziskTxExtractNonceAndGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # tx_len\n" ++
  "  addi a0, a4, 16             # tx_ptr\n" ++
  "  li a2, 0xa0010008           # nonce out\n" ++
  "  li a3, 0xa0010010           # gas out\n" ++
  "  jal ra, tx_extract_nonce_and_gas\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lteng_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txExtractNonceAndGasFunction ++ "\n" ++
  ".Lteng_pdone:"

def ziskTxExtractNonceAndGasDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "teng_type:\n" ++
  "  .zero 8\n" ++
  "teng_inner_off:\n" ++
  "  .zero 8"

def ziskTxExtractNonceAndGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxExtractNonceAndGasPrologue
  dataAsm     := ziskTxExtractNonceAndGasDataSection
}

/-! ## tx_extract_to_address -- PR-K101

    For any encoded tx (legacy or typed), extract the `to`
    (recipient) field and a contract-creation flag:

      is_creation = (to_field_length == 0)
      to_bytes    = 20 raw bytes when not creation, zeros otherwise

    Per-type RLP layout — the field index of `to`:

      type 0 legacy   : field 3 of the outer list
      type 1 EIP-2930 : field 4 of the inner RLP
      type 2 EIP-1559 : field 5 of the inner RLP
      type 3 EIP-4844 : field 5 of the inner RLP
      type 4 EIP-7702 : field 5 of the inner RLP

    Composes:
      - PR-K40 `tx_type_dispatch`   — typed-tx detector
      - PR-K20 `rlp_list_nth_item`  — field extractor

    Useful for `apply_body` (CREATE vs CALL routing) and for any
    pre-EVM check that needs the recipient without doing a full
    per-type decode.

    Calling convention:
      a0 (input)  : tx_bytes ptr (encoded form)
      a1 (input)  : tx_bytes byte length
      a2 (input)  : 20-byte output ptr (zeros on creation / fail)
      a3 (input)  : u64 out ptr (is_creation flag, 0 or 1)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : tx_type_dispatch failed
        2 : `to` field extraction failed (not 0 or 20 B)

    Uses two 8-byte `.data` scratch slots
    (`tea_type` + `tea_inner_off`) plus K20's offset/length pair. -/
def txExtractToAddressFunction : String :=
  "tx_extract_to_address:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # tx_bytes ptr\n" ++
  "  mv s1, a1                   # tx_len\n" ++
  "  mv s2, a2                   # 20B out ptr\n" ++
  "  mv s3, a3                   # is_creation out ptr\n" ++
  "  # Pre-zero outputs in case of failure.\n" ++
  "  sd zero,  0(s2); sd zero,  8(s2); sw zero, 16(s2)\n" ++
  "  sd zero,  0(s3)\n" ++
  "  # Step 1: tx_type_dispatch(tx, len, &type, &inner_off)\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, tea_type\n" ++
  "  la a3, tea_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  beqz a0, .Ltea_after_dispatch\n" ++
  "  li a0, 1\n" ++
  "  j .Ltea_ret\n" ++
  ".Ltea_after_dispatch:\n" ++
  "  la t0, tea_type;      ld t4, 0(t0)    # type\n" ++
  "  la t0, tea_inner_off; ld t5, 0(t0)    # inner_off\n" ++
  "  add t6, s0, t5                         # inner_ptr\n" ++
  "  sub t3, s1, t5                         # inner_len\n" ++
  "  # Determine field index based on type.\n" ++
  "  # type 0 → 3, type 1 → 4, type 2/3/4 → 5.\n" ++
  "  li t0, 0\n" ++
  "  beq t4, t0, .Ltea_legacy_idx\n" ++
  "  li t0, 1\n" ++
  "  beq t4, t0, .Ltea_t1_idx\n" ++
  "  li t1, 5                              # type 2,3,4\n" ++
  "  j .Ltea_have_idx\n" ++
  ".Ltea_legacy_idx:\n" ++
  "  li t1, 3\n" ++
  "  j .Ltea_have_idx\n" ++
  ".Ltea_t1_idx:\n" ++
  "  li t1, 4\n" ++
  ".Ltea_have_idx:\n" ++
  "  # rlp_list_nth_item(inner_ptr, inner_len, idx, &off, &len)\n" ++
  "  mv a0, t6\n" ++
  "  mv a1, t3\n" ++
  "  mv a2, t1\n" ++
  "  la a3, tea_field_off\n" ++
  "  la a4, tea_field_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Ltea_field_fail\n" ++
  "  la t0, tea_field_len; ld t2, 0(t0)\n" ++
  "  beqz t2, .Ltea_creation\n" ++
  "  li t1, 20\n" ++
  "  bne t2, t1, .Ltea_field_fail\n" ++
  "  # Copy 20 bytes from (inner_ptr + field_off) to s2.\n" ++
  "  # We lost inner_ptr (t6); recompute from s0 + tea_inner_off.\n" ++
  "  la t0, tea_inner_off; ld t5, 0(t0)\n" ++
  "  add t6, s0, t5\n" ++
  "  la t0, tea_field_off; ld t4, 0(t0)\n" ++
  "  add t6, t6, t4\n" ++
  "  ld t0,  0(t6); sd t0,  0(s2)\n" ++
  "  ld t0,  8(t6); sd t0,  8(s2)\n" ++
  "  lwu t0, 16(t6); sw t0, 16(s2)\n" ++
  "  sd zero, 0(s3)              # is_creation = 0\n" ++
  "  li a0, 0\n" ++
  "  j .Ltea_ret\n" ++
  ".Ltea_creation:\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3)                # is_creation = 1\n" ++
  "  li a0, 0\n" ++
  "  j .Ltea_ret\n" ++
  ".Ltea_field_fail:\n" ++
  "  li a0, 2\n" ++
  ".Ltea_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_tx_extract_to_address`: probe BuildUnit. Reads
    (tx_len, tx_bytes) from host input, writes (status, 20-byte
    address, is_creation u64) to OUTPUT (40 bytes total).
    Output layout:
      bytes  0.. 8 : status
      bytes  8..28 : 20-byte to address (zeros on creation/fail)
      bytes 28..32 : padding
      bytes 32..40 : is_creation u64 -/
def ziskTxExtractToAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # tx_len\n" ++
  "  addi a0, a4, 16             # tx ptr\n" ++
  "  li a2, 0xa0010008           # 20B output\n" ++
  "  li a3, 0xa0010020           # is_creation u64 (OUTPUT + 32)\n" ++
  "  jal ra, tx_extract_to_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Ltea_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txExtractToAddressFunction ++ "\n" ++
  ".Ltea_pdone:"

def ziskTxExtractToAddressDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "tea_type:\n" ++
  "  .zero 8\n" ++
  "tea_inner_off:\n" ++
  "  .zero 8\n" ++
  "tea_field_off:\n" ++
  "  .zero 8\n" ++
  "tea_field_len:\n" ++
  "  .zero 8"

def ziskTxExtractToAddressProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxExtractToAddressPrologue
  dataAsm     := ziskTxExtractToAddressDataSection
}

/-! ## tx_extract_value -- PR-K103

    Extract the `value` field (u256 BE) from any encoded tx type.
    `value` is the amount of wei the tx transfers to its `to`
    recipient (or contributes to the new account's balance on
    CREATE).

    Per-type RLP layout — the field index of `value`:

      type 0 legacy   : field 4 of the outer list
      type 1 EIP-2930 : field 5 of the inner RLP
      type 2 EIP-1559 : field 6 of the inner RLP
      type 3 EIP-4844 : field 6 of the inner RLP
      type 4 EIP-7702 : field 6 of the inner RLP

    Composes:
      - PR-K40 `tx_type_dispatch`        — typed-tx detector
      - PR-K-rlp_field_to_u256_be helper — u256 BE field extraction

    Useful for balance checks (`sender_balance >= value + gas_cost`)
    and for the priority-fee credit path. Together with PR-K101
    (`to` address) and PR-K102 (nonce + gas), this covers the
    fields `check_transaction` and `process_transaction` need from
    a tx without doing a full per-type decode.

    Calling convention:
      a0 (input)  : tx_bytes ptr (encoded form)
      a1 (input)  : tx_bytes byte length
      a2 (input)  : 32-byte output ptr (u256 BE)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : tx_type_dispatch failed (unknown / empty input)
        2 : value field extraction failed (parse error or > 256 bits)

    Output zeroed on failure. Uses two 8-byte `.data` scratch
    slots (`tev_type`, `tev_inner_off`). -/
def txExtractValueFunction : String :=
  "tx_extract_value:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # tx_ptr\n" ++
  "  mv s1, a1                   # tx_len\n" ++
  "  mv s2, a2                   # 32B out ptr\n" ++
  "  # Pre-zero output.\n" ++
  "  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)\n" ++
  "  # Step 1: tx_type_dispatch.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, tev_type\n" ++
  "  la a3, tev_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  beqz a0, .Ltev_after_dispatch\n" ++
  "  li a0, 1\n" ++
  "  j .Ltev_ret\n" ++
  ".Ltev_after_dispatch:\n" ++
  "  la t0, tev_type;      ld s3, 0(t0)    # type → s3\n" ++
  "  la t0, tev_inner_off; ld t5, 0(t0)\n" ++
  "  add t6, s0, t5                          # inner_ptr\n" ++
  "  sub t4, s1, t5                          # inner_len\n" ++
  "  # Determine field index.\n" ++
  "  li t0, 0\n" ++
  "  beq s3, t0, .Ltev_legacy_idx\n" ++
  "  li t0, 1\n" ++
  "  beq s3, t0, .Ltev_t1_idx\n" ++
  "  li t1, 6                              # type 2/3/4: value = 6\n" ++
  "  j .Ltev_have_idx\n" ++
  ".Ltev_legacy_idx:\n" ++
  "  li t1, 4                              # legacy: value = 4\n" ++
  "  j .Ltev_have_idx\n" ++
  ".Ltev_t1_idx:\n" ++
  "  li t1, 5                              # EIP-2930: value = 5\n" ++
  ".Ltev_have_idx:\n" ++
  "  mv a0, t6\n" ++
  "  mv a1, t4\n" ++
  "  mv a2, t1\n" ++
  "  mv a3, s2\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  beqz a0, .Ltev_ok\n" ++
  "  # Re-zero output on failure (rlp_field_to_u256_be may have\n" ++
  "  # partially written).\n" ++
  "  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)\n" ++
  "  li a0, 2\n" ++
  "  j .Ltev_ret\n" ++
  ".Ltev_ok:\n" ++
  "  li a0, 0\n" ++
  ".Ltev_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_tx_extract_value`: probe BuildUnit. Reads (tx_len,
    tx_bytes) from host input, writes (status, 32-byte value BE)
    to OUTPUT (40 bytes total). -/
def ziskTxExtractValuePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # tx_len\n" ++
  "  addi a0, a4, 16             # tx_ptr\n" ++
  "  li a2, 0xa0010008           # 32B u256 output\n" ++
  "  jal ra, tx_extract_value\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Ltev_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txExtractValueFunction ++ "\n" ++
  ".Ltev_pdone:"

def ziskTxExtractValueDataSection : String :=
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
  "tev_type:\n" ++
  "  .zero 8\n" ++
  "tev_inner_off:\n" ++
  "  .zero 8"

def ziskTxExtractValueProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxExtractValuePrologue
  dataAsm     := ziskTxExtractValueDataSection
}

/-! ## tx_extract_data_section -- PR-K104

    Extract the `data` (calldata / init-code) field's absolute
    pointer and byte length from any encoded tx type. The data
    field is variable-length: 0 bytes for value transfers, up to
    `MAX_INIT_CODE_SIZE` bytes for contract creations, longer for
    `CALL`-style payloads.

    Per-type RLP layout — the field index of `data`:

      type 0 legacy   : field 5 of the outer list
      type 1 EIP-2930 : field 6 of the inner RLP
      type 2 EIP-1559 : field 7 of the inner RLP
      type 3 EIP-4844 : field 7 of the inner RLP
      type 4 EIP-7702 : field 7 of the inner RLP

    Composes:
      - PR-K40 `tx_type_dispatch`   — typed-tx detector
      - PR-K20 `rlp_list_nth_item`  — byte-string content bounds

    Useful for:
    - intrinsic-gas pricing (zero/non-zero byte counts)
    - EIP-3860 init-code size check (CREATE / CREATE2)
    - feeding the EVM's `calldata` region pre-execution

    Calling convention:
      a0 (input)  : tx_bytes ptr (encoded form)
      a1 (input)  : tx_bytes byte length
      a2 (input)  : u64 out ptr (data_ptr — absolute address)
      a3 (input)  : u64 out ptr (data_len)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : tx_type_dispatch failed
        2 : data field extraction failed (parse error)

    Both outputs zeroed on failure. Uses two 8-byte `.data`
    scratch slots (`teds_type`, `teds_inner_off`). -/
def txExtractDataSectionFunction : String :=
  "tx_extract_data_section:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # tx_ptr\n" ++
  "  mv s1, a1                   # tx_len\n" ++
  "  mv s2, a2                   # data_ptr out\n" ++
  "  mv s3, a3                   # data_len out\n" ++
  "  sd zero, 0(s2); sd zero, 0(s3)\n" ++
  "  # Step 1: tx_type_dispatch.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, teds_type\n" ++
  "  la a3, teds_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  beqz a0, .Lteds_after_dispatch\n" ++
  "  li a0, 1\n" ++
  "  j .Lteds_ret\n" ++
  ".Lteds_after_dispatch:\n" ++
  "  la t0, teds_type;      ld t4, 0(t0)     # type\n" ++
  "  la t0, teds_inner_off; ld t5, 0(t0)\n" ++
  "  add t6, s0, t5                           # inner_ptr\n" ++
  "  sub t3, s1, t5                           # inner_len\n" ++
  "  # Determine field index.\n" ++
  "  li t0, 0\n" ++
  "  beq t4, t0, .Lteds_legacy_idx\n" ++
  "  li t0, 1\n" ++
  "  beq t4, t0, .Lteds_t1_idx\n" ++
  "  li t1, 7                                # type 2/3/4: data = 7\n" ++
  "  j .Lteds_have_idx\n" ++
  ".Lteds_legacy_idx:\n" ++
  "  li t1, 5                                # legacy: data = 5\n" ++
  "  j .Lteds_have_idx\n" ++
  ".Lteds_t1_idx:\n" ++
  "  li t1, 6                                # EIP-2930: data = 6\n" ++
  ".Lteds_have_idx:\n" ++
  "  mv a0, t6\n" ++
  "  mv a1, t3\n" ++
  "  mv a2, t1\n" ++
  "  la a3, teds_field_off\n" ++
  "  la a4, teds_field_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lteds_field_fail\n" ++
  "  # data_ptr = inner_ptr + field_off; data_len = field_len.\n" ++
  "  la t0, teds_inner_off; ld t5, 0(t0)\n" ++
  "  add t6, s0, t5\n" ++
  "  la t0, teds_field_off; ld t4, 0(t0)\n" ++
  "  add t6, t6, t4\n" ++
  "  sd t6, 0(s2)\n" ++
  "  la t0, teds_field_len; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lteds_ret\n" ++
  ".Lteds_field_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lteds_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_tx_extract_data_section`: probe BuildUnit. Reads
    (tx_len, tx_bytes), writes (status, data_ptr, data_len) to
    OUTPUT (24 bytes total). The data_ptr is an absolute address
    in the guest's memory space (inside the INPUT region for this
    probe). -/
def ziskTxExtractDataSectionPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # tx_len\n" ++
  "  addi a0, a4, 16             # tx_ptr\n" ++
  "  li a2, 0xa0010008           # data_ptr out\n" ++
  "  li a3, 0xa0010010           # data_len out\n" ++
  "  jal ra, tx_extract_data_section\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lteds_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txExtractDataSectionFunction ++ "\n" ++
  ".Lteds_pdone:"

def ziskTxExtractDataSectionDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "teds_type:\n" ++
  "  .zero 8\n" ++
  "teds_inner_off:\n" ++
  "  .zero 8\n" ++
  "teds_field_off:\n" ++
  "  .zero 8\n" ++
  "teds_field_len:\n" ++
  "  .zero 8"

def ziskTxExtractDataSectionProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxExtractDataSectionPrologue
  dataAsm     := ziskTxExtractDataSectionDataSection
}

/-! ## tx_extract_gas_pricing -- PR-K108

    Extract a tx's gas-pricing fields, normalised to the EIP-1559
    `(max_priority_fee, max_fee)` shape. For pre-EIP-1559 tx types
    that carry a single `gas_price`, both outputs receive the same
    value.

    Per-type RLP layout:

      type 0 legacy   : gas_price = field 1 → fill both outputs
      type 1 EIP-2930 : gas_price = field 2 → fill both outputs
      type 2 EIP-1559 : max_priority_fee = field 2, max_fee = field 3
      type 3 EIP-4844 : max_priority_fee = field 2, max_fee = field 3
      type 4 EIP-7702 : max_priority_fee = field 2, max_fee = field 3

    Both outputs are 32-byte big-endian (u256). Useful for
    `priority_fee_per_gas` (K62), `effective_gas_price` (K70),
    and `tx_cost_compute` (K71) which take this pair as input.

    Composes:
      - PR-K40 `tx_type_dispatch`        — typed-tx detector
      - `rlp_field_to_u256_be` helper    — u256 field extractor

    Calling convention:
      a0 (input)  : tx_bytes ptr (encoded form)
      a1 (input)  : tx_bytes byte length
      a2 (input)  : 32-byte out (max_priority_fee BE)
      a3 (input)  : 32-byte out (max_fee BE)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : tx_type_dispatch failed
        2 : first u256 field extraction failed
        3 : max_fee field extraction failed (typed only)

    Both outputs zeroed on failure. Uses two 8-byte `.data`
    scratch slots (`tegp_type`, `tegp_inner_off`). -/
def txExtractGasPricingFunction : String :=
  "tx_extract_gas_pricing:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # tx_ptr\n" ++
  "  mv s1, a1                   # tx_len\n" ++
  "  mv s2, a2                   # max_priority_fee out (32B)\n" ++
  "  mv s3, a3                   # max_fee out (32B)\n" ++
  "  # Pre-zero both outputs.\n" ++
  "  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  # Step 1: tx_type_dispatch.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, tegp_type\n" ++
  "  la a3, tegp_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  beqz a0, .Ltegp_after_dispatch\n" ++
  "  li a0, 1\n" ++
  "  j .Ltegp_ret\n" ++
  ".Ltegp_after_dispatch:\n" ++
  "  la t0, tegp_type;      ld s4, 0(t0)    # type → s4\n" ++
  "  la t0, tegp_inner_off; ld t5, 0(t0)\n" ++
  "  add s5, s0, t5                          # inner_ptr → s5\n" ++
  "  sub s6, s1, t5                          # inner_len → s6\n" ++
  "  # Determine first u256 field index.\n" ++
  "  # Legacy: gas_price=1. 2930: gas_price=2. 1559/4844/7702: max_priority=2.\n" ++
  "  li t0, 0\n" ++
  "  beq s4, t0, .Ltegp_p_legacy\n" ++
  "  li t1, 2                              # typed: index 2\n" ++
  "  j .Ltegp_p_have\n" ++
  ".Ltegp_p_legacy:\n" ++
  "  li t1, 1                              # legacy: index 1\n" ++
  ".Ltegp_p_have:\n" ++
  "  mv a0, s5\n" ++
  "  mv a1, s6\n" ++
  "  mv a2, t1\n" ++
  "  mv a3, s2\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  beqz a0, .Ltegp_after_p\n" ++
  "  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)\n" ++
  "  li a0, 2\n" ++
  "  j .Ltegp_ret\n" ++
  ".Ltegp_after_p:\n" ++
  "  # If legacy or 2930, copy max_priority_fee → max_fee.\n" ++
  "  li t0, 2\n" ++
  "  bgeu s4, t0, .Ltegp_typed_fee\n" ++
  "  ld t0,  0(s2); sd t0,  0(s3)\n" ++
  "  ld t0,  8(s2); sd t0,  8(s3)\n" ++
  "  ld t0, 16(s2); sd t0, 16(s3)\n" ++
  "  ld t0, 24(s2); sd t0, 24(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Ltegp_ret\n" ++
  ".Ltegp_typed_fee:\n" ++
  "  # Type 2/3/4: max_fee = field 3.\n" ++
  "  mv a0, s5\n" ++
  "  mv a1, s6\n" ++
  "  li a2, 3\n" ++
  "  mv a3, s3\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  beqz a0, .Ltegp_ok\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  li a0, 3\n" ++
  "  j .Ltegp_ret\n" ++
  ".Ltegp_ok:\n" ++
  "  li a0, 0\n" ++
  ".Ltegp_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_tx_extract_gas_pricing`: probe BuildUnit. Reads (tx_len,
    tx_bytes), writes (status, max_priority_fee BE, max_fee BE) to
    OUTPUT (72 bytes total). -/
def ziskTxExtractGasPricingPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # tx_len\n" ++
  "  addi a0, a4, 16             # tx_ptr\n" ++
  "  li a2, 0xa0010008           # max_priority_fee out\n" ++
  "  li a3, 0xa0010028           # max_fee out (OUTPUT + 0x28)\n" ++
  "  jal ra, tx_extract_gas_pricing\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Ltegp_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txExtractGasPricingFunction ++ "\n" ++
  ".Ltegp_pdone:"

def ziskTxExtractGasPricingDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "tegp_type:\n" ++
  "  .zero 8\n" ++
  "tegp_inner_off:\n" ++
  "  .zero 8"

def ziskTxExtractGasPricingProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxExtractGasPricingPrologue
  dataAsm     := ziskTxExtractGasPricingDataSection
}

/-! ## tx_eip1559_decode -- PR-K41 full 12-field EIP-1559 decoder

    Decode the inner (post-type-byte) RLP body of an EIP-1559
    (type-2) transaction into a flat 248-byte output struct.
    Inner RLP shape (12 fields):

      rlp([
        chain_id, nonce,
        max_priority_fee_per_gas, max_fee_per_gas,
        gas_limit, to, value, data, access_list,
        y_parity, r, s
      ])

    Output struct (248 bytes):
       0..  8  chain_id              (u64 LE)
       8.. 16  nonce                 (u64 LE)
      16.. 48  max_priority_fee_per_gas (u256 BE)
      48.. 80  max_fee_per_gas       (u256 BE)
      80.. 88  gas_limit             (u64 LE)
      88..108  to (20-byte address; zero for creation)
     108..112  to_present (u32; 0 = creation, 1 = call)
     112..144  value                 (u256 BE)
     144..152  data_offset           (u64 within inner RLP)
     152..160  data_length           (u64)
     160..168  access_list_offset    (u64; whole encoded item incl. prefix)
     168..176  access_list_length    (u64; whole encoded item incl. prefix)
     176..184  y_parity              (u64; 0 or 1)
     184..216  r                     (u256 BE)
     216..248  s                     (u256 BE)

    Caller passes the inner RLP body -- after stripping the 0x02
    type byte that PR-K40 `tx_type_dispatch` reports via
    `inner_offset`.

    access_list semantics: per `rlp_list_nth_item`'s contract for
    list items, the returned (offset, length) span the *full*
    encoded sub-list including its RLP prefix, so the caller can
    recurse into it with another `rlp_list_nth_item` call.

    Calling convention:
      a0 (input)  : inner_rlp ptr
      a1 (input)  : inner_rlp byte length
      a2 (input)  : output struct ptr (248 bytes)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail -/
def txEip1559DecodeFunction : String :=
  "tx_eip1559_decode:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # inner_rlp ptr\n" ++
  "  mv s1, a1                  # inner_rlp_len\n" ++
  "  mv s2, a2                  # struct out\n" ++
  "  # Field 0: chain_id (u64 at offset 0)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0; mv a3, s2\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  # Field 1: nonce (u64 at offset 8)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  addi a3, s2, 8\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  # Field 2: max_priority_fee_per_gas (u256 at offset 16)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  addi a3, s2, 16\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  # Field 3: max_fee_per_gas (u256 at offset 48)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  addi a3, s2, 48\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  # Field 4: gas_limit (u64 at offset 80)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 4\n" ++
  "  addi a3, s2, 80\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  # Field 5: to (0 or 20 bytes at offset 88; to_present u32 at 108)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 5\n" ++
  "  la a3, t1d_offset; la a4, t1d_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  la t0, t1d_length; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lt1d_to_creation\n" ++
  "  li t2, 20\n" ++
  "  bne t1, t2, .Lt1d_fail\n" ++
  "  la t0, t1d_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  addi t4, s2, 88\n" ++
  "  ld t5,  0(t3); sd t5, 0(t4)\n" ++
  "  ld t5,  8(t3); sd t5, 8(t4)\n" ++
  "  lwu t5, 16(t3); sw t5, 16(t4)\n" ++
  "  li t5, 1\n" ++
  "  sw t5, 108(s2)             # to_present = 1\n" ++
  "  j .Lt1d_after_to\n" ++
  ".Lt1d_to_creation:\n" ++
  "  addi t4, s2, 88\n" ++
  "  sd zero, 0(t4); sd zero, 8(t4); sw zero, 16(t4)\n" ++
  "  sw zero, 108(s2)           # to_present = 0\n" ++
  ".Lt1d_after_to:\n" ++
  "  # Field 6: value (u256 at offset 112)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 6\n" ++
  "  addi a3, s2, 112\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  # Field 7: data (offset+length stored at 144/152)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 7\n" ++
  "  la a3, t1d_offset; la a4, t1d_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  la t0, t1d_offset; ld t1, 0(t0); sd t1, 144(s2)\n" ++
  "  la t0, t1d_length; ld t1, 0(t0); sd t1, 152(s2)\n" ++
  "  # Field 8: access_list (offset+length at 160/168; full encoded item)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 8\n" ++
  "  la a3, t1d_offset; la a4, t1d_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  la t0, t1d_offset; ld t1, 0(t0); sd t1, 160(s2)\n" ++
  "  la t0, t1d_length; ld t1, 0(t0); sd t1, 168(s2)\n" ++
  "  # Field 9: y_parity (u64 at offset 176)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 9\n" ++
  "  addi a3, s2, 176\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  # Field 10: r (u256 at offset 184)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 10\n" ++
  "  addi a3, s2, 184\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  # Field 11: s (u256 at offset 216)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 11\n" ++
  "  addi a3, s2, 216\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lt1d_ret\n" ++
  ".Lt1d_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lt1d_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_tx_eip1559_decode`: probe BuildUnit. Reads (inner_len,
    inner_bytes) from host input -- caller is expected to have
    stripped the 0x02 type byte. Writes (status, 248-byte struct)
    to OUTPUT (256 bytes total, matching ziskemu's output cap). -/
def ziskTxEip1559DecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # inner_len\n" ++
  "  addi a0, a3, 16             # inner ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 248 bytes (31 × 8 dwords).\n" ++
  "  mv t0, a2\n" ++
  "  li t1, 31\n" ++
  ".Lt1d_zinit:\n" ++
  "  beqz t1, .Lt1d_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt1d_zinit\n" ++
  ".Lt1d_zdone:\n" ++
  "  jal ra, tx_eip1559_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lt1d_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txEip1559DecodeFunction ++ "\n" ++
  ".Lt1d_pdone:"

def ziskTxEip1559DecodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t1d_offset:\n" ++
  "  .zero 8\n" ++
  "t1d_length:\n" ++
  "  .zero 8"

def ziskTxEip1559DecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxEip1559DecodePrologue
  dataAsm     := ziskTxEip1559DecodeDataSection
}

/-! ## tx_eip2930_decode -- PR-K42 full 11-field EIP-2930 decoder

    Decode the inner (post-type-byte) RLP body of an EIP-2930
    (type-1) access-list transaction into a flat 216-byte output
    struct. Inner RLP shape (11 fields):

      rlp([
        chain_id, nonce, gas_price, gas_limit,
        to, value, data, access_list,
        y_parity, r, s
      ])

    EIP-2930 is structurally simpler than EIP-1559: a single
    `gas_price` field (legacy-style) instead of the
    `(max_priority_fee_per_gas, max_fee_per_gas)` pair.

    Output struct (216 bytes):
       0..  8  chain_id              (u64 LE)
       8.. 16  nonce                 (u64 LE)
      16.. 48  gas_price             (u256 BE)
      48.. 56  gas_limit             (u64 LE)
      56.. 76  to (20-byte address; zero for creation)
      76.. 80  to_present (u32; 0 = creation, 1 = call)
      80..112  value                 (u256 BE)
     112..120  data_offset           (u64 within inner RLP)
     120..128  data_length           (u64)
     128..136  access_list_offset    (u64; whole encoded item incl. prefix)
     136..144  access_list_length    (u64; whole encoded item incl. prefix)
     144..152  y_parity              (u64; 0 or 1)
     152..184  r                     (u256 BE)
     184..216  s                     (u256 BE)

    Caller passes the inner RLP body -- after stripping the 0x01
    type byte that PR-K40 `tx_type_dispatch` reports via
    `inner_offset`. access_list semantics mirror PR-K41
    `tx_eip1559_decode`: the returned (offset, length) span the
    *full* encoded sub-list including its RLP prefix, so the
    caller can recurse into it.

    Calling convention:
      a0 (input)  : inner_rlp ptr
      a1 (input)  : inner_rlp byte length
      a2 (input)  : output struct ptr (216 bytes)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail -/
def txEip2930DecodeFunction : String :=
  "tx_eip2930_decode:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # inner_rlp ptr\n" ++
  "  mv s1, a1                  # inner_rlp_len\n" ++
  "  mv s2, a2                  # struct out\n" ++
  "  # Field 0: chain_id (u64 at offset 0)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0; mv a3, s2\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  # Field 1: nonce (u64 at offset 8)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  addi a3, s2, 8\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  # Field 2: gas_price (u256 at offset 16)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  addi a3, s2, 16\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  # Field 3: gas_limit (u64 at offset 48)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  addi a3, s2, 48\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  # Field 4: to (0 or 20 bytes at offset 56; to_present u32 at 76)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 4\n" ++
  "  la a3, t29_offset; la a4, t29_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  la t0, t29_length; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lt29_to_creation\n" ++
  "  li t2, 20\n" ++
  "  bne t1, t2, .Lt29_fail\n" ++
  "  la t0, t29_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  addi t4, s2, 56\n" ++
  "  ld t5,  0(t3); sd t5, 0(t4)\n" ++
  "  ld t5,  8(t3); sd t5, 8(t4)\n" ++
  "  lwu t5, 16(t3); sw t5, 16(t4)\n" ++
  "  li t5, 1\n" ++
  "  sw t5, 76(s2)              # to_present = 1\n" ++
  "  j .Lt29_after_to\n" ++
  ".Lt29_to_creation:\n" ++
  "  addi t4, s2, 56\n" ++
  "  sd zero, 0(t4); sd zero, 8(t4); sw zero, 16(t4)\n" ++
  "  sw zero, 76(s2)            # to_present = 0\n" ++
  ".Lt29_after_to:\n" ++
  "  # Field 5: value (u256 at offset 80)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 5\n" ++
  "  addi a3, s2, 80\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  # Field 6: data (offset+length at 112/120)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 6\n" ++
  "  la a3, t29_offset; la a4, t29_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  la t0, t29_offset; ld t1, 0(t0); sd t1, 112(s2)\n" ++
  "  la t0, t29_length; ld t1, 0(t0); sd t1, 120(s2)\n" ++
  "  # Field 7: access_list (offset+length at 128/136; full encoded item)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 7\n" ++
  "  la a3, t29_offset; la a4, t29_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  la t0, t29_offset; ld t1, 0(t0); sd t1, 128(s2)\n" ++
  "  la t0, t29_length; ld t1, 0(t0); sd t1, 136(s2)\n" ++
  "  # Field 8: y_parity (u64 at offset 144)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 8\n" ++
  "  addi a3, s2, 144\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  # Field 9: r (u256 at offset 152)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 9\n" ++
  "  addi a3, s2, 152\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  # Field 10: s (u256 at offset 184)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 10\n" ++
  "  addi a3, s2, 184\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lt29_ret\n" ++
  ".Lt29_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lt29_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_tx_eip2930_decode`: probe BuildUnit. Reads (inner_len,
    inner_bytes) from host input -- caller is expected to have
    stripped the 0x01 type byte. Writes (status, 216-byte struct)
    to OUTPUT (224 bytes total). -/
def ziskTxEip2930DecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # inner_len\n" ++
  "  addi a0, a3, 16             # inner ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 216 bytes (27 × 8 dwords).\n" ++
  "  mv t0, a2\n" ++
  "  li t1, 27\n" ++
  ".Lt29_zinit:\n" ++
  "  beqz t1, .Lt29_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt29_zinit\n" ++
  ".Lt29_zdone:\n" ++
  "  jal ra, tx_eip2930_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lt29_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txEip2930DecodeFunction ++ "\n" ++
  ".Lt29_pdone:"

def ziskTxEip2930DecodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t29_offset:\n" ++
  "  .zero 8\n" ++
  "t29_length:\n" ++
  "  .zero 8"

def ziskTxEip2930DecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxEip2930DecodePrologue
  dataAsm     := ziskTxEip2930DecodeDataSection
}

/-! ## tx_eip7702_decode -- PR-K44 full 13-field EIP-7702 decoder

    Decode the inner (post-type-byte) RLP body of an EIP-7702
    (type-4) set-code transaction into a flat 240-byte output
    struct. Inner RLP shape (13 fields):

      rlp([
        chain_id, nonce,
        max_priority_fee_per_gas, max_fee_per_gas,
        gas_limit, to, value, data,
        access_list, authorization_list,
        y_parity, r, s
      ])

    Compared to PR-K41 EIP-1559 (12 fields), EIP-7702 inserts an
    `authorization_list` after `access_list` -- a list of
    (chain_id, address, nonce, y_parity, r, s) authorization
    tuples. The decoder records only its outer (offset, length)
    bounds; sub-decoding into individual authorization entries
    lands in a follow-up PR.

    Output struct (240 bytes; u32 offsets/lengths to fit the
    256-byte ziskemu output cap):

       0..  8  chain_id              (u64 LE)
       8.. 16  nonce                 (u64 LE)
      16.. 48  max_priority_fee_per_gas (u256 BE)
      48.. 80  max_fee_per_gas       (u256 BE)
      80.. 88  gas_limit             (u64 LE)
      88..108  to (20-byte address; zero for creation -- but
                  EIP-7702 spec requires `to` so empty paths
                  are still reported as creation status=1)
     108..112  to_present (u32; 0 = creation, 1 = call)
     112..144  value                 (u256 BE)
     144..148  data_offset           (u32)
     148..152  data_length           (u32)
     152..156  access_list_offset    (u32; whole encoded item)
     156..160  access_list_length    (u32; whole encoded item)
     160..164  auth_list_offset      (u32; whole encoded item)
     164..168  auth_list_length      (u32; whole encoded item)
     168..176  y_parity              (u64; 0 or 1)
     176..208  r                     (u256 BE)
     208..240  s                     (u256 BE)

    Calling convention:
      a0 (input)  : inner_rlp ptr
      a1 (input)  : inner_rlp byte length
      a2 (input)  : output struct ptr (240 bytes)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail -/
def txEip7702DecodeFunction : String :=
  "tx_eip7702_decode:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # inner_rlp ptr\n" ++
  "  mv s1, a1                  # inner_rlp_len\n" ++
  "  mv s2, a2                  # struct out\n" ++
  "  # Field 0: chain_id (u64 at offset 0)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0; mv a3, s2\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  # Field 1: nonce (u64 at offset 8)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  addi a3, s2, 8\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  # Field 2: max_priority_fee_per_gas (u256 at offset 16)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  addi a3, s2, 16\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  # Field 3: max_fee_per_gas (u256 at offset 48)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  addi a3, s2, 48\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  # Field 4: gas_limit (u64 at offset 80)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 4\n" ++
  "  addi a3, s2, 80\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  # Field 5: to (0 or 20 bytes at offset 88; to_present u32 at 108)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 5\n" ++
  "  la a3, t77_offset; la a4, t77_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  la t0, t77_length; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lt77_to_creation\n" ++
  "  li t2, 20\n" ++
  "  bne t1, t2, .Lt77_fail\n" ++
  "  la t0, t77_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  addi t4, s2, 88\n" ++
  "  ld t5,  0(t3); sd t5, 0(t4)\n" ++
  "  ld t5,  8(t3); sd t5, 8(t4)\n" ++
  "  lwu t5, 16(t3); sw t5, 16(t4)\n" ++
  "  li t5, 1\n" ++
  "  sw t5, 108(s2)             # to_present = 1\n" ++
  "  j .Lt77_after_to\n" ++
  ".Lt77_to_creation:\n" ++
  "  addi t4, s2, 88\n" ++
  "  sd zero, 0(t4); sd zero, 8(t4); sw zero, 16(t4)\n" ++
  "  sw zero, 108(s2)           # to_present = 0\n" ++
  ".Lt77_after_to:\n" ++
  "  # Field 6: value (u256 at offset 112)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 6\n" ++
  "  addi a3, s2, 112\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  # Field 7: data (offset+length u32 at 144/148)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 7\n" ++
  "  la a3, t77_offset; la a4, t77_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  la t0, t77_offset; ld t1, 0(t0); sw t1, 144(s2)\n" ++
  "  la t0, t77_length; ld t1, 0(t0); sw t1, 148(s2)\n" ++
  "  # Field 8: access_list (offset+length u32 at 152/156)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 8\n" ++
  "  la a3, t77_offset; la a4, t77_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  la t0, t77_offset; ld t1, 0(t0); sw t1, 152(s2)\n" ++
  "  la t0, t77_length; ld t1, 0(t0); sw t1, 156(s2)\n" ++
  "  # Field 9: authorization_list (offset+length u32 at 160/164)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 9\n" ++
  "  la a3, t77_offset; la a4, t77_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  la t0, t77_offset; ld t1, 0(t0); sw t1, 160(s2)\n" ++
  "  la t0, t77_length; ld t1, 0(t0); sw t1, 164(s2)\n" ++
  "  # Field 10: y_parity (u64 at offset 168)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 10\n" ++
  "  addi a3, s2, 168\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  # Field 11: r (u256 at offset 176)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 11\n" ++
  "  addi a3, s2, 176\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  # Field 12: s (u256 at offset 208)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 12\n" ++
  "  addi a3, s2, 208\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lt77_ret\n" ++
  ".Lt77_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lt77_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_tx_eip7702_decode`: probe BuildUnit. Reads (inner_len,
    inner_bytes) from host input -- caller is expected to have
    stripped the 0x04 type byte. Writes (status, 240-byte struct)
    to OUTPUT (248 bytes total). -/
def ziskTxEip7702DecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # inner_len\n" ++
  "  addi a0, a3, 16             # inner ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 240 bytes (30 × 8 dwords).\n" ++
  "  mv t0, a2\n" ++
  "  li t1, 30\n" ++
  ".Lt77_zinit:\n" ++
  "  beqz t1, .Lt77_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt77_zinit\n" ++
  ".Lt77_zdone:\n" ++
  "  jal ra, tx_eip7702_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lt77_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txEip7702DecodeFunction ++ "\n" ++
  ".Lt77_pdone:"

def ziskTxEip7702DecodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t77_offset:\n" ++
  "  .zero 8\n" ++
  "t77_length:\n" ++
  "  .zero 8"

def ziskTxEip7702DecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxEip7702DecodePrologue
  dataAsm     := ziskTxEip7702DecodeDataSection
}

/-! ## tx_eip4844_decode -- PR-K45 full 14-field EIP-4844 decoder

    Decode the inner (post-type-byte) RLP body of an EIP-4844
    (type-3) blob transaction into a flat 248-byte output struct.
    Inner RLP shape (14 fields):

      rlp([
        chain_id, nonce,
        max_priority_fee_per_gas, max_fee_per_gas,
        gas_limit, to, value, data,
        access_list,
        max_fee_per_blob_gas, blob_versioned_hashes,
        y_parity, r, s
      ])

    Compared to PR-K41 EIP-1559 (12 fields), EIP-4844 inserts
    `max_fee_per_blob_gas` (u256) and `blob_versioned_hashes`
    (list of 32-byte hashes) between `access_list` and `y_parity`.

    NOTE on max_fee_per_blob_gas: the spec type is u256, but
    real-world blob fees fit comfortably in u64 (mainnet typical
    range is 1 wei .. low gwei). To keep the struct within
    ziskemu's 256-byte output cap, this decoder stores the
    field as `u64` and rejects (status=1) any encoded value
    longer than 8 bytes. Callers needing the full u256 can
    re-extract via `rlp_field_to_u256_be` at field index 9.

    Output struct (248 bytes; u32 offsets/lengths):

       0..  8  chain_id                  (u64 LE)
       8.. 16  nonce                     (u64 LE)
      16.. 48  max_priority_fee_per_gas  (u256 BE)
      48.. 80  max_fee_per_gas           (u256 BE)
      80.. 88  gas_limit                 (u64 LE)
      88..108  to (20-byte address; zero for creation -- but
                  EIP-4844 spec disallows creation, so empty
                  to is just reported via to_present=0)
     108..112  to_present (u32; 0 = creation, 1 = call)
     112..144  value                     (u256 BE)
     144..148  data_offset               (u32)
     148..152  data_length               (u32)
     152..156  access_list_offset        (u32; whole encoded item)
     156..160  access_list_length        (u32; whole encoded item)
     160..168  max_fee_per_blob_gas      (u64 LE; rejects > 8 B BE)
     168..172  blob_versioned_hashes_off (u32; whole encoded item)
     172..176  blob_versioned_hashes_len (u32; whole encoded item)
     176..184  y_parity                  (u64; 0 or 1)
     184..216  r                         (u256 BE)
     216..248  s                         (u256 BE)

    Calling convention:
      a0 (input)  : inner_rlp ptr
      a1 (input)  : inner_rlp byte length
      a2 (input)  : output struct ptr (248 bytes)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail (incl. blob fee > u64) -/
def txEip4844DecodeFunction : String :=
  "tx_eip4844_decode:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # inner_rlp ptr\n" ++
  "  mv s1, a1                  # inner_rlp_len\n" ++
  "  mv s2, a2                  # struct out\n" ++
  "  # Field 0: chain_id\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0; mv a3, s2\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  # Field 1: nonce\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  addi a3, s2, 8\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  # Field 2: max_priority_fee_per_gas\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  addi a3, s2, 16\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  # Field 3: max_fee_per_gas\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  addi a3, s2, 48\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  # Field 4: gas_limit\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 4\n" ++
  "  addi a3, s2, 80\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  # Field 5: to (0 or 20 B at 88; to_present u32 at 108)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 5\n" ++
  "  la a3, t48_offset; la a4, t48_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  la t0, t48_length; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lt48_to_creation\n" ++
  "  li t2, 20\n" ++
  "  bne t1, t2, .Lt48_fail\n" ++
  "  la t0, t48_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  addi t4, s2, 88\n" ++
  "  ld t5,  0(t3); sd t5, 0(t4)\n" ++
  "  ld t5,  8(t3); sd t5, 8(t4)\n" ++
  "  lwu t5, 16(t3); sw t5, 16(t4)\n" ++
  "  li t5, 1\n" ++
  "  sw t5, 108(s2)             # to_present = 1\n" ++
  "  j .Lt48_after_to\n" ++
  ".Lt48_to_creation:\n" ++
  "  addi t4, s2, 88\n" ++
  "  sd zero, 0(t4); sd zero, 8(t4); sw zero, 16(t4)\n" ++
  "  sw zero, 108(s2)           # to_present = 0\n" ++
  ".Lt48_after_to:\n" ++
  "  # Field 6: value\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 6\n" ++
  "  addi a3, s2, 112\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  # Field 7: data (u32 off+len at 144/148)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 7\n" ++
  "  la a3, t48_offset; la a4, t48_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  la t0, t48_offset; ld t1, 0(t0); sw t1, 144(s2)\n" ++
  "  la t0, t48_length; ld t1, 0(t0); sw t1, 148(s2)\n" ++
  "  # Field 8: access_list (u32 off+len at 152/156)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 8\n" ++
  "  la a3, t48_offset; la a4, t48_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  la t0, t48_offset; ld t1, 0(t0); sw t1, 152(s2)\n" ++
  "  la t0, t48_length; ld t1, 0(t0); sw t1, 156(s2)\n" ++
  "  # Field 9: max_fee_per_blob_gas (u64 at 160; rejects > 8B BE)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 9\n" ++
  "  addi a3, s2, 160\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  # Field 10: blob_versioned_hashes (u32 off+len at 168/172)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 10\n" ++
  "  la a3, t48_offset; la a4, t48_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  la t0, t48_offset; ld t1, 0(t0); sw t1, 168(s2)\n" ++
  "  la t0, t48_length; ld t1, 0(t0); sw t1, 172(s2)\n" ++
  "  # Field 11: y_parity (u64 at 176)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 11\n" ++
  "  addi a3, s2, 176\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  # Field 12: r (u256 at 184)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 12\n" ++
  "  addi a3, s2, 184\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  # Field 13: s (u256 at 216)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 13\n" ++
  "  addi a3, s2, 216\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lt48_ret\n" ++
  ".Lt48_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lt48_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_tx_eip4844_decode`: probe BuildUnit. Reads (inner_len,
    inner_bytes) from host input -- caller is expected to have
    stripped the 0x03 type byte. Writes (status, 248-byte struct)
    to OUTPUT (256 bytes total). -/
def ziskTxEip4844DecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # inner_len\n" ++
  "  addi a0, a3, 16             # inner ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 248 bytes (31 × 8 dwords).\n" ++
  "  mv t0, a2\n" ++
  "  li t1, 31\n" ++
  ".Lt48_zinit:\n" ++
  "  beqz t1, .Lt48_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt48_zinit\n" ++
  ".Lt48_zdone:\n" ++
  "  jal ra, tx_eip4844_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lt48_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  ".Lt48_pdone:"

def ziskTxEip4844DecodeDataSection : String :=
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

def ziskTxEip4844DecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxEip4844DecodePrologue
  dataAsm     := ziskTxEip4844DecodeDataSection
}

/-! ## tx_decode_dispatch -- PR-K87 unified tx decoder

    Dispatch on a tx envelope's type byte and route to the
    appropriate inner decoder. Mirrors Python's
    `decode_transaction`:

      byte 0 ≥ 0xc0     → legacy        → tx_legacy_decode    (K36)
      byte 0 == 0x01    → EIP-2930      → tx_eip2930_decode   (K42)
      byte 0 == 0x02    → EIP-1559      → tx_eip1559_decode   (K41)
      byte 0 == 0x03    → EIP-4844      → tx_eip4844_decode   (K45)
      byte 0 == 0x04    → EIP-7702      → tx_eip7702_decode   (K44)
      else              → status = type-unrecognized

    The decoded struct's size depends on the tx type:
      type 0 (legacy)   : 196 B
      type 1 (EIP-2930) : 216 B
      type 2 (EIP-1559) : 248 B
      type 3 (EIP-4844) : 248 B
      type 4 (EIP-7702) : 240 B

    Status encoding packs both the tx_type and sub-status:

      status = (tx_type << 8) | sub_status

      sub_status 0  : success
      sub_status 1  : type unrecognized (used with tx_type=0)
      sub_status 2  : sub-decoder returned non-zero

    Caller responsibilities:
      - Pre-zero the 248-byte struct_out buffer.
      - After success, infer struct_size from `tx_type` extracted
        as `(status >> 8) & 0xff`.

    Composes PR-K40 + each of K36, K41, K42, K44, K45.

    Calling convention:
      a0 (input)  : envelope ptr
      a1 (input)  : envelope_len
      a2 (input)  : struct_out ptr (must be ≥ 248 bytes, pre-zeroed)
      ra (input)  : return
      a0 (output) : packed status (see encoding above).

    Uses 8 bytes of `.data` scratch (`tdd_inner_off`) plus the
    inner-decoder scratches (rfu_offset/rfu_length etc.). -/
def txDecodeDispatchFunction : String :=
  "tx_decode_dispatch:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # envelope ptr\n" ++
  "  mv s1, a1                   # envelope_len\n" ++
  "  mv s2, a2                   # struct_out ptr\n" ++
  "  # tx_type_dispatch(envelope, len, type_out=tdd_type, inner_offset_out=tdd_inner_off)\n" ++
  "  la a2, tdd_type\n" ++
  "  la a3, tdd_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Ltdd_unrec\n" ++
  "  la t0, tdd_type; ld t1, 0(t0)\n" ++
  "  la t0, tdd_inner_off; ld t2, 0(t0)\n" ++
  "  add t3, s0, t2              # inner_ptr\n" ++
  "  sub t4, s1, t2              # inner_len\n" ++
  "  # Dispatch on tx_type (t1)\n" ++
  "  beqz t1, .Ltdd_legacy\n" ++
  "  li t5, 1\n" ++
  "  beq t1, t5, .Ltdd_2930\n" ++
  "  li t5, 2\n" ++
  "  beq t1, t5, .Ltdd_1559\n" ++
  "  li t5, 3\n" ++
  "  beq t1, t5, .Ltdd_4844\n" ++
  "  li t5, 4\n" ++
  "  beq t1, t5, .Ltdd_7702\n" ++
  "  j .Ltdd_unrec\n" ++
  ".Ltdd_legacy:\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2\n" ++
  "  jal ra, tx_legacy_decode\n" ++
  "  bnez a0, .Ltdd_decode_fail_legacy\n" ++
  "  li a0, 0\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_2930:\n" ++
  "  mv a0, t3; mv a1, t4; mv a2, s2\n" ++
  "  jal ra, tx_eip2930_decode\n" ++
  "  bnez a0, .Ltdd_decode_fail_2930\n" ++
  "  li a0, 0x0100\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_1559:\n" ++
  "  mv a0, t3; mv a1, t4; mv a2, s2\n" ++
  "  jal ra, tx_eip1559_decode\n" ++
  "  bnez a0, .Ltdd_decode_fail_1559\n" ++
  "  li a0, 0x0200\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_4844:\n" ++
  "  mv a0, t3; mv a1, t4; mv a2, s2\n" ++
  "  jal ra, tx_eip4844_decode\n" ++
  "  bnez a0, .Ltdd_decode_fail_4844\n" ++
  "  li a0, 0x0300\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_7702:\n" ++
  "  mv a0, t3; mv a1, t4; mv a2, s2\n" ++
  "  jal ra, tx_eip7702_decode\n" ++
  "  bnez a0, .Ltdd_decode_fail_7702\n" ++
  "  li a0, 0x0400\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_unrec:\n" ++
  "  li a0, 0x0001\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_decode_fail_legacy:\n" ++
  "  li a0, 0x0002\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_decode_fail_2930:\n" ++
  "  li a0, 0x0102\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_decode_fail_1559:\n" ++
  "  li a0, 0x0202\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_decode_fail_4844:\n" ++
  "  li a0, 0x0302\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_decode_fail_7702:\n" ++
  "  li a0, 0x0402\n" ++
  ".Ltdd_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_tx_decode_dispatch`: probe BuildUnit. Reads (env_len,
    env_bytes) from host input; pre-zeros 248-byte struct slot
    at OUTPUT+8; calls helper; writes (packed status, struct)
    to OUTPUT (256 bytes total). -/
def ziskTxDecodeDispatchPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # env_len\n" ++
  "  addi a0, a3, 16             # env ptr\n" ++
  "  li a2, 0xa0010008           # struct slot at OUTPUT + 8\n" ++
  "  # Pre-zero 248 bytes (31 dwords).\n" ++
  "  mv t0, a2; li t1, 31\n" ++
  ".Ltdd_zout:\n" ++
  "  beqz t1, .Ltdd_zout_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Ltdd_zout\n" ++
  ".Ltdd_zout_done:\n" ++
  "  jal ra, tx_decode_dispatch\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # packed status\n" ++
  "  j .Ltdd_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txLegacyDecodeFunction ++ "\n" ++
  txEip2930DecodeFunction ++ "\n" ++
  txEip1559DecodeFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  txEip7702DecodeFunction ++ "\n" ++
  txDecodeDispatchFunction ++ "\n" ++
  ".Ltdd_pdone:"

def ziskTxDecodeDispatchDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "txd_offset:\n" ++
  "  .zero 8\n" ++
  "txd_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t1d_offset:\n" ++
  "  .zero 8\n" ++
  "t1d_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t29_offset:\n" ++
  "  .zero 8\n" ++
  "t29_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t48_offset:\n" ++
  "  .zero 8\n" ++
  "t48_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t77_offset:\n" ++
  "  .zero 8\n" ++
  "t77_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "tdd_type:\n" ++
  "  .zero 8\n" ++
  "tdd_inner_off:\n" ++
  "  .zero 8"

def ziskTxDecodeDispatchProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxDecodeDispatchPrologue
  dataAsm     := ziskTxDecodeDispatchDataSection
}

/-! ## tx_eip4844_compute_blob_gas -- PR-K88

    Given an EIP-4844 (type 3) tx inner RLP body, decode it and
    compute the per-tx `blob_gas_used` field:

      blob_gas_used = len(tx.blob_versioned_hashes) × GAS_PER_BLOB

    Where `GAS_PER_BLOB = 131072` (mainnet Cancun); parameterized
    so the helper works across forks that adjust it.

    Composes:
      - PR-K45 `tx_eip4844_decode` — decode inner body → 248 B struct
      - PR-K64 `blob_gas_used_from_versioned_hashes` — count × gas_per_blob

    Useful for verifying that
    `header.blob_gas_used == sum(tx.blob_gas_used for tx in block)`.

    The K45 struct at offsets 168..172 (u32 LE) holds
    `blob_versioned_hashes_offset` (relative to `inner_ptr`), and
    offsets 172..176 hold `blob_versioned_hashes_length`. This
    helper reads those, computes the absolute pointer, and
    invokes K64.

    Calling convention:
      a0 (input)  : inner_rlp ptr (post-0x03 type byte)
      a1 (input)  : inner_rlp byte length
      a2 (input)  : gas_per_blob (u64; 131072 on mainnet)
      a3 (input)  : u64 out ptr (receives blob_gas_used)
      ra (input)  : return
      a0 (output) :
        0  : success
        1  : tx_eip4844_decode failed (parse error)
        2  : blob_gas_used_from_versioned_hashes failed (parse error)

    Uses 248 + 8 bytes of `.data` scratch (`tcbg_struct` for the
    decoded EIP-4844 struct, plus an inherited count scratch). -/
def txEip4844ComputeBlobGasFunction : String :=
  "tx_eip4844_compute_blob_gas:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # inner_rlp ptr\n" ++
  "  mv s1, a2                   # gas_per_blob\n" ++
  "  mv s2, a3                   # out ptr\n" ++
  "  # Step 1: K45 tx_eip4844_decode(inner, len, tcbg_struct)\n" ++
  "  la a2, tcbg_struct\n" ++
  "  # Pre-zero 248 bytes (31 dwords)\n" ++
  "  mv t0, a2; li t1, 31\n" ++
  ".Ltcbg_zinit:\n" ++
  "  beqz t1, .Ltcbg_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Ltcbg_zinit\n" ++
  ".Ltcbg_zdone:\n" ++
  "  jal ra, tx_eip4844_decode\n" ++
  "  bnez a0, .Ltcbg_decode_fail\n" ++
  "  # Step 2: K64 blob_gas_used_from_versioned_hashes(...)\n" ++
  "  la t0, tcbg_struct\n" ++
  "  lwu t1, 168(t0)             # blob_versioned_hashes_offset (u32)\n" ++
  "  lwu t2, 172(t0)             # blob_versioned_hashes_length (u32)\n" ++
  "  add a0, s0, t1              # absolute blob_list ptr\n" ++
  "  mv a1, t2                   # blob_list length\n" ++
  "  mv a2, s1                   # gas_per_blob\n" ++
  "  mv a3, s2                   # out ptr\n" ++
  "  jal ra, blob_gas_used_from_versioned_hashes\n" ++
  "  beqz a0, .Ltcbg_ret\n" ++
  "  li a0, 2\n" ++
  "  j .Ltcbg_ret\n" ++
  ".Ltcbg_decode_fail:\n" ++
  "  li a0, 1\n" ++
  ".Ltcbg_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_tx_eip4844_compute_blob_gas`: probe BuildUnit. Reads
    (inner_len, gas_per_blob, inner_bytes) from host input,
    writes (status, blob_gas_used) to OUTPUT (16 bytes). -/
def ziskTxEip4844ComputeBlobGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # inner_len\n" ++
  "  ld a2, 16(a4)               # gas_per_blob\n" ++
  "  addi a0, a4, 24             # inner_ptr\n" ++
  "  li a3, 0xa0010008           # out u64 ptr\n" ++
  "  sd zero, 0(a3)\n" ++
  "  jal ra, tx_eip4844_compute_blob_gas\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Ltcbg_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  blobGasUsedFromVersionedHashesFunction ++ "\n" ++
  txEip4844ComputeBlobGasFunction ++ "\n" ++
  ".Ltcbg_pdone:"

def ziskTxEip4844ComputeBlobGasDataSection : String :=
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
  "bgvh_count_scratch:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "tcbg_struct:\n" ++
  "  .zero 248"

def ziskTxEip4844ComputeBlobGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxEip4844ComputeBlobGasPrologue
  dataAsm     := ziskTxEip4844ComputeBlobGasDataSection
}

/-! ## tx_calculate_total_blob_gas -- PR-K92

    Python reference (`forks/amsterdam/vm/gas.py`):

      def calculate_total_blob_gas(tx) -> U64:
          if isinstance(tx, BlobTransaction):
              return GAS_PER_BLOB * U64(len(tx.blob_versioned_hashes))
          else:
              return U64(0)

    Accepts a transaction in its encoded form (legacy RLP list,
    or typed `[type_byte || rlp(inner)]`) and returns the per-tx
    blob_gas_used: 0 for any non-EIP-4844 type, otherwise the
    blob-count × gas-per-blob product computed by PR-K88.

    Composes:
      - PR-K40 `tx_type_dispatch`           — typed-tx detector
      - PR-K88 `tx_eip4844_compute_blob_gas` — count × gas_per_blob

    Useful per-tx primitive for `apply_body` and for receipt-side
    bookkeeping that needs the same number on every tx without
    branching on type in the caller.

    Calling convention:
      a0 (input)  : tx_bytes ptr (encoded form)
      a1 (input)  : tx_bytes byte length
      a2 (input)  : gas_per_blob (u64; 131072 on mainnet Cancun)
      a3 (input)  : u64 out ptr (receives total blob gas)
      ra (input)  : return
      a0 (output) : composite status code

    Status decade encoding (floor(status/100) identifies the
    failing step):

      0          : success
      1          : tx_type_dispatch failed (unknown tx type / empty)
      101..102   : tx_eip4844_compute_blob_gas forwarded
                   (101 = K45 decode, 102 = K64 sum)

    Uses two 8-byte `.data` scratch slots (`tctbg_type`,
    `tctbg_inner_off`) plus the buffers inherited from K88. -/
def txCalculateTotalBlobGasFunction : String :=
  "tx_calculate_total_blob_gas:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # tx ptr\n" ++
  "  mv s1, a1                   # tx_len\n" ++
  "  mv s3, a2                   # gas_per_blob (stash)\n" ++
  "  mv s2, a3                   # out ptr\n" ++
  "  # Default zero in case of early non-type-3 exit.\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # Step 1: tx_type_dispatch(tx, len, &type, &inner_off)\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, tctbg_type\n" ++
  "  la a3, tctbg_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  beqz a0, .Lctbg_after_dispatch\n" ++
  "  li a0, 1\n" ++
  "  j .Lctbg_ret\n" ++
  ".Lctbg_after_dispatch:\n" ++
  "  la t0, tctbg_type\n" ++
  "  ld t1, 0(t0)\n" ++
  "  li t2, 3\n" ++
  "  bne t1, t2, .Lctbg_zero_ok\n" ++
  "  # type 3: compute blob gas via K88.\n" ++
  "  la t0, tctbg_inner_off\n" ++
  "  ld t3, 0(t0)\n" ++
  "  add a0, s0, t3              # inner_ptr\n" ++
  "  sub a1, s1, t3              # inner_len\n" ++
  "  mv a2, s3                   # gas_per_blob\n" ++
  "  mv a3, s2                   # out ptr\n" ++
  "  jal ra, tx_eip4844_compute_blob_gas\n" ++
  "  beqz a0, .Lctbg_ok\n" ++
  "  li t0, 100\n" ++
  "  add a0, a0, t0              # 1 → 101, 2 → 102\n" ++
  "  j .Lctbg_ret\n" ++
  ".Lctbg_zero_ok:\n" ++
  "  # *out already 0.\n" ++
  ".Lctbg_ok:\n" ++
  "  li a0, 0\n" ++
  ".Lctbg_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_tx_calculate_total_blob_gas`: probe BuildUnit. Reads
    (tx_len, gas_per_blob, tx_bytes) from host input, writes
    (status, total_blob_gas) to OUTPUT (16 bytes). -/
def ziskTxCalculateTotalBlobGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # tx_len\n" ++
  "  ld a2, 16(a4)               # gas_per_blob\n" ++
  "  addi a0, a4, 24             # tx_ptr\n" ++
  "  li a3, 0xa0010008           # out u64 ptr\n" ++
  "  sd zero, 0(a3)\n" ++
  "  jal ra, tx_calculate_total_blob_gas\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lctbg_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  blobGasUsedFromVersionedHashesFunction ++ "\n" ++
  txEip4844ComputeBlobGasFunction ++ "\n" ++
  txCalculateTotalBlobGasFunction ++ "\n" ++
  ".Lctbg_pdone:"

def ziskTxCalculateTotalBlobGasDataSection : String :=
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
  "bgvh_count_scratch:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "tcbg_struct:\n" ++
  "  .zero 248\n" ++
  ".balign 8\n" ++
  "tctbg_type:\n" ++
  "  .zero 8\n" ++
  "tctbg_inner_off:\n" ++
  "  .zero 8"

def ziskTxCalculateTotalBlobGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxCalculateTotalBlobGasPrologue
  dataAsm     := ziskTxCalculateTotalBlobGasDataSection
}


/-! ## intrinsic_gas_legacy -- PR-K46 base + creation + data gas

    Compute the intrinsic gas cost portion of a legacy /
    EIP-2930 / EIP-1559 transaction that depends only on the
    `data` payload and the creation flag. Higher-fork-specific
    extras (access-list address/slot costs, EIP-7702 auth
    entries, EIP-7623 floor data cost) are NOT included here --
    callers compose them.

    Formula (EIP-2028 / EIP-2 base):

      gas = 21000
          + (32000 if creation else 0)
          + sum(4 if b == 0 else 16 for b in data)

    Calling convention:
      a0 (input)  : data ptr
      a1 (input)  : data byte length
      a2 (input)  : is_creation (0 = call, 1 = creation)
      ra (input)  : return
      a0 (output) : u64 intrinsic gas

    Pure register arithmetic, no scratch memory, leaf-callable.
    Cannot overflow u64 in practice: even at max gas_limit ~30M,
    data length << 2^59, so 16 * data_len is well within u64. -/
def intrinsicGasLegacyFunction : String :=
  "intrinsic_gas_legacy:\n" ++
  "  li t0, 21000               # base\n" ++
  "  beqz a2, .Ligl_skip_creation\n" ++
  "  li t1, 32000\n" ++
  "  add t0, t0, t1\n" ++
  ".Ligl_skip_creation:\n" ++
  "  mv t2, a0                  # data cursor\n" ++
  "  add t3, a0, a1             # data end\n" ++
  ".Ligl_loop:\n" ++
  "  bgeu t2, t3, .Ligl_done\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  beqz t4, .Ligl_zero\n" ++
  "  addi t0, t0, 16\n" ++
  "  j .Ligl_step\n" ++
  ".Ligl_zero:\n" ++
  "  addi t0, t0, 4\n" ++
  ".Ligl_step:\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Ligl_loop\n" ++
  ".Ligl_done:\n" ++
  "  mv a0, t0\n" ++
  "  ret"

/-- `zisk_intrinsic_gas_legacy`: probe BuildUnit. Reads
    (data_len, is_creation, data_bytes) from host input, writes
    the u64 intrinsic gas to OUTPUT. -/
def ziskIntrinsicGasLegacyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # data_len\n" ++
  "  ld a2, 16(a3)               # is_creation\n" ++
  "  addi a0, a3, 24             # data ptr\n" ++
  "  jal ra, intrinsic_gas_legacy\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # gas\n" ++
  "  j .Ligl_pdone\n" ++
  intrinsicGasLegacyFunction ++ "\n" ++
  ".Ligl_pdone:"

def ziskIntrinsicGasLegacyDataSection : String :=
  ".section .data\n" ++
  "igl_pad:\n" ++
  "  .zero 8"

def ziskIntrinsicGasLegacyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskIntrinsicGasLegacyPrologue
  dataAsm     := ziskIntrinsicGasLegacyDataSection
}

/-! ## tx_validate_intrinsic_gas_legacy -- PR-K66

    Compose PR-K46 `intrinsic_gas_legacy` with the standard tx
    validation check `intrinsic_gas <= tx.gas_limit`. Mirrors
    Python's check in `validate_transaction`:

      if tx.gas < calculate_intrinsic_gas(tx):
          raise InvalidTransaction

    Returns the actual intrinsic-gas value via an out pointer so
    callers don't have to re-call PR-K46; this lets downstream
    `process_transaction` deduct it from the tx's gas allowance.

    Calling convention:
      a0 (input)  : data ptr
      a1 (input)  : data byte length
      a2 (input)  : is_creation (0 or 1)
      a3 (input)  : tx.gas_limit (u64)
      a4 (input)  : u64 out ptr (receives intrinsic_gas)
      ra (input)  : return
      a0 (output) : 0 ok / 1 intrinsic_gas > tx.gas_limit (reject)

    The `out` pointer always receives the computed intrinsic gas,
    even on reject — callers can record it for receipt purposes
    or further analysis. -/
def txValidateIntrinsicGasLegacyFunction : String :=
  "tx_validate_intrinsic_gas_legacy:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a3                   # tx.gas_limit\n" ++
  "  mv s1, a4                   # out ptr\n" ++
  "  jal ra, intrinsic_gas_legacy # a0 = intrinsic_gas\n" ++
  "  sd a0, 0(s1)                # write to out, regardless of reject\n" ++
  "  bltu s0, a0, .Ltvil_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Ltvil_ret\n" ++
  ".Ltvil_fail:\n" ++
  "  li a0, 1\n" ++
  ".Ltvil_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_tx_validate_intrinsic_gas_legacy`: probe BuildUnit.
    Reads (data_len, is_creation, gas_limit, data_bytes) from
    host input, writes (status, intrinsic_gas) to OUTPUT (16
    bytes total). -/
def ziskTxValidateIntrinsicGasLegacyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # data_len\n" ++
  "  ld a2, 16(a5)               # is_creation\n" ++
  "  ld a3, 24(a5)               # tx.gas_limit\n" ++
  "  addi a0, a5, 32             # data ptr\n" ++
  "  li a4, 0xa0010008           # out ptr for intrinsic_gas\n" ++
  "  sd zero, 0(a4)\n" ++
  "  jal ra, tx_validate_intrinsic_gas_legacy\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Ltvil_pdone\n" ++
  intrinsicGasLegacyFunction ++ "\n" ++
  txValidateIntrinsicGasLegacyFunction ++ "\n" ++
  ".Ltvil_pdone:"

def ziskTxValidateIntrinsicGasLegacyDataSection : String :=
  ".section .data\n" ++
  "tvil_pad:\n" ++
  "  .zero 8"

def ziskTxValidateIntrinsicGasLegacyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxValidateIntrinsicGasLegacyPrologue
  dataAsm     := ziskTxValidateIntrinsicGasLegacyDataSection
}

/-! ## validate_transaction_basic -- PR-K76 cheap pre-EVM tx validation

    Run the two cheap u64-level transaction validation checks in
    sequence and return a composite status:

      1. PR-K69 `tx_validate_against_block`        — chain_id, gas_limit, nonce
      2. PR-K66 `tx_validate_intrinsic_gas_legacy` — intrinsic_gas ≤ tx.gas_limit

    These are the cheapest pre-EVM checks; a tx that fails any
    of them is rejected without invoking the EVM. Mirrors the
    `chain_id == ...`, `tx.gas <= block.gas_limit`, `tx.nonce ==
    account.nonce`, and `intrinsic_gas <= tx.gas` assertions in
    Python's `validate_transaction`.

    The intrinsic_gas check applies to legacy / EIP-2930 / EIP-1559
    txs sharing the base + creation + per-byte data formula.
    EIP-2930+ access-list and EIP-7702 authorization-list gas
    additions land in follow-up PRs that compose this helper
    with K48 + future authorization counters.

    Status encoding (analogous to PR-K75 validate_header_full):

      0          : all checks pass
      101..103   : step 1 (K69) failed (chain_id / gas_limit / nonce)
      201        : step 2 (K66) failed (intrinsic_gas > tx.gas_limit)

    The intrinsic_gas value is also written to an out pointer
    regardless of the verdict — callers can deduct it from
    tx.gas_limit on the success path or record it for analysis.

    Calling convention:
      a0 (input)  : tx.chain_id (u64)
      a1 (input)  : block.chain_id (u64)
      a2 (input)  : tx.gas_limit (u64)
      a3 (input)  : block.gas_limit (u64)
      a4 (input)  : tx.nonce (u64)
      a5 (input)  : account.nonce (u64)
      a6 (input)  : data ptr
      a7 (input)  : packed input: low bits = data_len, bit 63 = is_creation
      ra (input)  : return
      a0 (output) : composite status code

    The `a7` packing avoids needing an 8th and 9th register
    (RV64 has only 8 arg regs). data_len in the low 32 bits is
    plenty (mainnet caps tx data well below 4 GiB), and
    is_creation is one bit.

    Note: this helper does NOT take an intrinsic_gas out
    pointer — the cost of forwarding through the stack adds
    register pressure. Callers that need the intrinsic gas can
    call PR-K46 `intrinsic_gas_legacy` directly. -/
def validateTransactionBasicFunction : String :=
  "validate_transaction_basic:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  # Save data ptr, gas_limit, and a7 for step 2.\n" ++
  "  mv s0, a6                   # data ptr\n" ++
  "  mv s1, a2                   # tx.gas_limit\n" ++
  "  mv s2, a7                   # packed: low 32 = data_len, bit 63 = is_creation\n" ++
  "  # Step 1: K69 tx_validate_against_block(chain, block_chain, gas, block_gas, nonce, acct_nonce)\n" ++
  "  jal ra, tx_validate_against_block\n" ++
  "  beqz a0, .Lvtb_s2\n" ++
  "  li t0, 100\n" ++
  "  add a0, a0, t0\n" ++
  "  j .Lvtb_ret\n" ++
  ".Lvtb_s2:\n" ++
  "  # Step 2: K66 tx_validate_intrinsic_gas_legacy(data, len, is_creation, gas_limit, gas_out)\n" ++
  "  mv a0, s0\n" ++
  "  li t0, 0xffffffff           # mask for low 32 bits (data_len)\n" ++
  "  and a1, s2, t0\n" ++
  "  srli a2, s2, 63             # is_creation = high bit\n" ++
  "  mv a3, s1                   # tx.gas_limit\n" ++
  "  la a4, vtb_gas_scratch      # intrinsic_gas out (scratch, unused by caller)\n" ++
  "  jal ra, tx_validate_intrinsic_gas_legacy\n" ++
  "  beqz a0, .Lvtb_ret\n" ++
  "  li t0, 200\n" ++
  "  add a0, a0, t0\n" ++
  ".Lvtb_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_validate_transaction_basic`: probe BuildUnit. Reads
    (tx_chain, block_chain, tx_gas, block_gas, tx_nonce,
    account_nonce, is_creation, data_len, data_bytes) from host
    input, writes 8-byte composite status to OUTPUT. -/
def ziskValidateTransactionBasicPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a0,  8(t0)               # tx.chain_id\n" ++
  "  ld a1, 16(t0)               # block.chain_id\n" ++
  "  ld a2, 24(t0)               # tx.gas_limit\n" ++
  "  ld a3, 32(t0)               # block.gas_limit\n" ++
  "  ld a4, 40(t0)               # tx.nonce\n" ++
  "  ld a5, 48(t0)               # account.nonce\n" ++
  "  ld t1, 56(t0)               # is_creation (u64)\n" ++
  "  ld t2, 64(t0)               # data_len (u64; low 32 used)\n" ++
  "  addi a6, t0, 72             # data ptr\n" ++
  "  # Pack t1 (is_creation, 0 or 1) and t2 (data_len) into a7.\n" ++
  "  slli t1, t1, 63\n" ++
  "  li t3, 0xffffffff\n" ++
  "  and t2, t2, t3\n" ++
  "  or  a7, t1, t2\n" ++
  "  jal ra, validate_transaction_basic\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lvtb_pdone\n" ++
  txValidateAgainstBlockFunction ++ "\n" ++
  intrinsicGasLegacyFunction ++ "\n" ++
  txValidateIntrinsicGasLegacyFunction ++ "\n" ++
  validateTransactionBasicFunction ++ "\n" ++
  ".Lvtb_pdone:"

def ziskValidateTransactionBasicDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "vtb_gas_scratch:\n" ++
  "  .zero 8"

def ziskValidateTransactionBasicProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateTransactionBasicPrologue
  dataAsm     := ziskValidateTransactionBasicDataSection
}

/-! ## validate_transaction_full -- PR-K80

    Top-level pre-EVM tx validator: compose all the cheap u64
    checks with the u256-arithmetic balance check.

      1. PR-K76 `validate_transaction_basic`   — chain_id / gas_limit /
                                                  nonce / intrinsic_gas
      2. PR-K79 `validate_transaction_balance` — balance >= max_fee * gas + value

    If any sub-step fails, this helper returns immediately with
    a composite status code (analogous to PR-K75 and K76):

      0          : all checks pass — tx ready for EVM dispatch
      101..103   : K76 step 1 (chain_id / gas_limit / nonce)
      201        : K76 step 2 (intrinsic_gas > gas_limit)
      301        : K79 step 1 (tx_cost overflow)
      302        : K79 step 2 (balance < tx_cost)

    Distinct decades let callers `floor(status/100)` to identify
    the failing layer.

    The argument packing follows K76 (a7 = (is_creation << 63) |
    data_len) and inserts a `max_fee_per_gas ptr` / `value ptr` /
    `balance ptr` triple in saved registers since RV64 has only
    8 arg regs.

    Calling convention:
      a0 (input)  : tx.chain_id (u64)
      a1 (input)  : block.chain_id (u64)
      a2 (input)  : tx.gas_limit (u64)
      a3 (input)  : block.gas_limit (u64)
      a4 (input)  : tx.nonce (u64)
      a5 (input)  : account.nonce (u64)
      a6 (input)  : data ptr
      a7 (input)  : packed input: low 32 = data_len, bit 63 = is_creation
      ra (input)  : return

    The three 32-byte pointers (max_fee_per_gas, value, balance)
    are passed through fixed `.data` slots that the caller
    populates BEFORE invoking this helper:
      vtf_max_fee  : 32 B u256 BE
      vtf_value    : 32 B u256 BE
      vtf_balance  : 32 B u256 BE

    a0 (output) : composite status code (see encoding above). -/
def validateTransactionFullFunction : String :=
  "validate_transaction_full:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  # Save tx.gas_limit (a2) for step 2 — K76 will not preserve\n" ++
  "  # caller's args, and step 2 needs it as a1 input.\n" ++
  "  mv s0, a2                   # tx.gas_limit\n" ++
  "  # Step 1: K76 validate_transaction_basic — args already in a0..a7.\n" ++
  "  jal ra, validate_transaction_basic\n" ++
  "  beqz a0, .Lvtf_s2\n" ++
  "  # Forward K76's code (100..201) directly — it's already in the\n" ++
  "  # K80 status table since K76 and K80 share the same decades.\n" ++
  "  j .Lvtf_ret\n" ++
  ".Lvtf_s2:\n" ++
  "  # Step 2: K79 validate_transaction_balance(max_fee, gas_limit,\n" ++
  "  #                                         value, balance)\n" ++
  "  la a0, vtf_max_fee\n" ++
  "  mv a1, s0                   # restored tx.gas_limit\n" ++
  "  la a2, vtf_value\n" ++
  "  la a3, vtf_balance\n" ++
  "  jal ra, validate_transaction_balance\n" ++
  "  beqz a0, .Lvtf_ret\n" ++
  "  li t0, 300\n" ++
  "  add a0, a0, t0\n" ++
  ".Lvtf_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_validate_transaction_full`: probe BuildUnit. Reads
    (tx_chain, block_chain, tx_gas, block_gas, tx_nonce,
    account_nonce, is_creation, data_len, max_fee, value,
    balance, data_bytes) from host input; sets up the .data
    slots and a-regs; writes 8-byte composite status. -/
def ziskValidateTransactionFullPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a0,  8(t0)               # tx.chain_id\n" ++
  "  ld a1, 16(t0)               # block.chain_id\n" ++
  "  ld a2, 24(t0)               # tx.gas_limit\n" ++
  "  ld a3, 32(t0)               # block.gas_limit\n" ++
  "  ld a4, 40(t0)               # tx.nonce\n" ++
  "  ld a5, 48(t0)               # account.nonce\n" ++
  "  ld t1, 56(t0)               # is_creation\n" ++
  "  ld t2, 64(t0)               # data_len\n" ++
  "  # Copy max_fee (offset 72..104) → vtf_max_fee\n" ++
  "  la t3, vtf_max_fee\n" ++
  "  addi t4, t0, 72\n" ++
  "  ld t5,  0(t4); sd t5,  0(t3)\n" ++
  "  ld t5,  8(t4); sd t5,  8(t3)\n" ++
  "  ld t5, 16(t4); sd t5, 16(t3)\n" ++
  "  ld t5, 24(t4); sd t5, 24(t3)\n" ++
  "  # Copy value (offset 104..136) → vtf_value\n" ++
  "  la t3, vtf_value\n" ++
  "  addi t4, t0, 104\n" ++
  "  ld t5,  0(t4); sd t5,  0(t3)\n" ++
  "  ld t5,  8(t4); sd t5,  8(t3)\n" ++
  "  ld t5, 16(t4); sd t5, 16(t3)\n" ++
  "  ld t5, 24(t4); sd t5, 24(t3)\n" ++
  "  # Copy balance (offset 136..168) → vtf_balance\n" ++
  "  la t3, vtf_balance\n" ++
  "  addi t4, t0, 136\n" ++
  "  ld t5,  0(t4); sd t5,  0(t3)\n" ++
  "  ld t5,  8(t4); sd t5,  8(t3)\n" ++
  "  ld t5, 16(t4); sd t5, 16(t3)\n" ++
  "  ld t5, 24(t4); sd t5, 24(t3)\n" ++
  "  addi a6, t0, 168            # data ptr (after balance)\n" ++
  "  # Pack a7\n" ++
  "  slli t1, t1, 63\n" ++
  "  li t6, 0xffffffff\n" ++
  "  and t2, t2, t6\n" ++
  "  or  a7, t1, t2\n" ++
  "  jal ra, validate_transaction_full\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lvtf_pdone\n" ++
  txValidateAgainstBlockFunction ++ "\n" ++
  intrinsicGasLegacyFunction ++ "\n" ++
  txValidateIntrinsicGasLegacyFunction ++ "\n" ++
  validateTransactionBasicFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  txCostComputeFunction ++ "\n" ++
  validateTransactionBalanceFunction ++ "\n" ++
  validateTransactionFullFunction ++ "\n" ++
  ".Lvtf_pdone:"

def ziskValidateTransactionFullDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40\n" ++
  ".balign 32\n" ++
  "vtbal_cost_scratch:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "vtb_gas_scratch:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "vtf_max_fee:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "vtf_value:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "vtf_balance:\n" ++
  "  .zero 32"

def ziskValidateTransactionFullProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateTransactionFullPrologue
  dataAsm     := ziskValidateTransactionFullDataSection
}


end EvmAsm.Codegen
