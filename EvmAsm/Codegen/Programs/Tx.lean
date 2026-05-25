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
import EvmAsm.Codegen.Programs.U256

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

/-! ## eip7702_authorization_signing_hash -- PR-K147

    EIP-7702 per-authorization signing hash:

      signing_hash =
        keccak256(MAGIC || rlp([chain_id, address, nonce]))

    where `MAGIC = 0x05`. This is the digest a delegator signs to
    authorise their account to delegate execution to a target
    address at a specific nonce.

    Companion to PR-K143
    `eip7702_authorization_extract_signature` (which extracts the
    `(y_parity, r, s)` triple). Together, K143 + K147 + the
    upcoming `zkvm_secp256k1_ecrecover` wiring + K99
    `address_from_pubkey` recover the **delegator** address from
    an authorization tuple.

    The body operation is structurally identical to K145
    `tx_signing_hash` with `n = 3` and `type_prefix = 0x05`:
    truncate the 6-field authorization tuple to its first 3
    fields and keccak the prefix-extended result. K147 is a
    typed convenience wrapper -- callers don't need to remember
    the MAGIC byte or the field count -- and delegates to
    `tx_signing_hash` for the body.

    Composes:
      - PR-K145 `tx_signing_hash` (truncate + keccak)
        which in turn composes K144 + K129 + K20 + Keccak.

    Calling convention:
      a0 (input)  : authorization_tuple_rlp ptr
      a1 (input)  : authorization_tuple_rlp byte length
      a2 (input)  : 32-byte output hash ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / fewer than 3 fields -/
def eip7702AuthorizationSigningHashFunction : String :=
  "eip7702_authorization_signing_hash:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra,  0(sp)\n" ++
  "  # Forward to tx_signing_hash with n=3, type_prefix=0x05.\n" ++
  "  # a0 = inner_rlp ptr      (unchanged)\n" ++
  "  # a1 = inner_rlp byte len (unchanged)\n" ++
  "  # a2 = 32-byte output ptr (move to a4 per K145 ABI)\n" ++
  "  mv a4, a2\n" ++
  "  li a2, 3                  # n_fields\n" ++
  "  li a3, 0x05               # MAGIC type prefix\n" ++
  "  jal ra, tx_signing_hash\n" ++
  "  ld ra,  0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_eip7702_authorization_signing_hash`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : tuple_rlp_len
      bytes  8..   : tuple_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..40 : 32-byte signing hash -/
def ziskEip7702AuthorizationSigningHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # tuple_rlp_len\n" ++
  "  addi a0, a4, 16             # tuple_rlp ptr\n" ++
  "  li a2, 0xa0010008           # output hash ptr (32 B)\n" ++
  "  jal ra, eip7702_authorization_signing_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Ltash_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpListTruncateToNFieldsFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  txSigningHashFunction ++ "\n" ++
  eip7702AuthorizationSigningHashFunction ++ "\n" ++
  ".Ltash_pdone:"

/-- Reuse the same scratch labels as `ziskTxSigningHashDataSection`
    (`tsh_buf`, `tsh_trunc_len`, `rltn_*`, `zk3_state`). -/
def ziskEip7702AuthorizationSigningHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "tsh_buf:\n" ++
  "  .zero 8192\n" ++
  "tsh_trunc_len:\n" ++
  "  .zero 8\n" ++
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

def ziskEip7702AuthorizationSigningHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskEip7702AuthorizationSigningHashPrologue
  dataAsm     := ziskEip7702AuthorizationSigningHashDataSection
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

/-! ## u256-BE arithmetic + pricing helpers (K51/K52/K56/K58/K59/K60/K61/K62/K70/K53/K54/K57/K160) — moved to `Programs/U256.lean` (file-size hard cap). -/

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
