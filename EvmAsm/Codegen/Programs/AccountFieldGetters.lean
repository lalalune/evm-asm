/-
  EvmAsm.Codegen.Programs.AccountFieldGetters

  Account-field getters layered over the K201 + K28 trie walk.
  Each function returns a single field of `account_at_address`'s
  104-byte struct (with a spec-defining default value for absent
  accounts) and applies the "missing-anything → zero-or-canonical"
  flattening from the EVM spec.

  Family overview (siblings of distinct return shapes):

    BALANCE        : u256;       missing -> 0
    NONCE          : u64;        missing -> 0
    storage_root   : Bytes32;    missing -> EMPTY_TRIE_ROOT
    code_hash      : Bytes32;    missing -> EMPTY_CODE_HASH

  This module hosts `code_hash_at_header_state_root`; the other
  three currently live in `EvmAsm.Codegen.Programs.EvmOpcodes`.
  Once that file approaches its hard-cap line limit, the
  remaining getters will migrate here.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.State

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## code_hash_at_header_state_root

    Witness-side getter for `account.code_hash` as a 32-byte
    hash. Sibling of `storage_root_at_header_state_root`
    (raw-field getter with a canonical default for absent
    accounts), but with the spec default being EMPTY_CODE_HASH
    instead of EMPTY_TRIE_ROOT:

      EMPTY_CODE_HASH = keccak("") = 0xc5d2460186f7233c...

    Distinct from PR-K? `extcodehash_at_header_state_root` (EIP-1052),
    which applies the EIP-161 empty-account rule (an account
    with nonce=0 AND balance=0 AND code_hash=EMPTY_CODE_HASH
    returns 0 even when present in the trie). This primitive is
    the raw field accessor: it returns whatever `account.code_hash`
    holds, with EMPTY_CODE_HASH for missing accounts (per the
    "missing account is conceptually an account with no code"
    convention).

    The spec-divergence test: an account in the trie with
    nonce=0, balance=0, code_hash=EMPTY_CODE_HASH:

      | primitive          | returns |
      |--------------------|---------|
      | code_hash (this PR)| EMPTY_CODE_HASH |
      | extcodehash (#7150)| 0 (EIP-1052) |

    Composes K201 `header_extract_state_root` + K28
    `account_at_address`, then copies the 32-byte code_hash
    field (struct + 72 .. + 104) OR writes EMPTY_CODE_HASH when
    the account is absent.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      a5 (input)  : 32-byte output ptr
      ra (input)  : return

      a0 (output) :
        0 = success (code_hash written; EMPTY_CODE_HASH on absent)
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail

      (Code 1 is intentionally absent: missing accounts map to
      `status=0, output=EMPTY_CODE_HASH`.)
-/
def codeHashAtHeaderStateRootFunction : String :=
  "code_hash_at_header_state_root:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_rlp_len\n" ++
  "  mv s2, a2                  # address ptr\n" ++
  "  mv s3, a3                  # witness.state ptr\n" ++
  "  mv s4, a4                  # witness.state len\n" ++
  "  mv s5, a5                  # 32-byte output ptr\n" ++
  "  # Pre-fill output with EMPTY_CODE_HASH (spec default for absent).\n" ++
  "  la t0, chahsr_empty_code_hash\n" ++
  "  ld t1,  0(t0); sd t1,  0(s5)\n" ++
  "  ld t1,  8(t0); sd t1,  8(s5)\n" ++
  "  ld t1, 16(t0); sd t1, 16(s5)\n" ++
  "  ld t1, 24(t0); sd t1, 24(s5)\n" ++
  "  # Step 1: header.state_root -> chahsr_state_root.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, chahsr_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lchahsr_step2\n" ++
  "  # Header parse fail: zero output for unambiguous error reporting.\n" ++
  "  sd zero,  0(s5); sd zero,  8(s5); sd zero, 16(s5); sd zero, 24(s5)\n" ++
  "  li a0, 4\n" ++
  "  j .Lchahsr_ret\n" ++
  ".Lchahsr_step2:\n" ++
  "  mv a0, s2\n" ++
  "  li a1, 20\n" ++
  "  la a2, chahsr_state_root\n" ++
  "  mv a3, s3\n" ++
  "  mv a4, s4\n" ++
  "  la s6, chahsr_acct_struct\n" ++
  "  mv a5, s6\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lchahsr_copy\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lchahsr_absent  # 1 -> output stays EMPTY_CODE_HASH\n" ++
  "  # 2/3 propagate; zero output for unambiguous error.\n" ++
  "  sd zero,  0(s5); sd zero,  8(s5); sd zero, 16(s5); sd zero, 24(s5)\n" ++
  "  j .Lchahsr_ret\n" ++
  ".Lchahsr_absent:\n" ++
  "  li a0, 0\n" ++
  "  j .Lchahsr_ret\n" ++
  ".Lchahsr_copy:\n" ++
  "  # Copy code_hash (struct + 72 .. + 104) to output.\n" ++
  "  ld t1, 72(s6); sd t1,  0(s5)\n" ++
  "  ld t1, 80(s6); sd t1,  8(s5)\n" ++
  "  ld t1, 88(s6); sd t1, 16(s5)\n" ++
  "  ld t1, 96(s6); sd t1, 24(s5)\n" ++
  "  li a0, 0\n" ++
  ".Lchahsr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_code_hash_at_header_state_root`: probe BuildUnit.

    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len    (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..44 : address (20 bytes)
      bytes 44..44+H              : header_rlp
      bytes 44+H..44+H+WS         : witness.state
    Output layout:
      bytes  0.. 8 : status (0 / 2 / 3 / 4)
      bytes  8..40 : code_hash (32 bytes; EMPTY_CODE_HASH on
                     absent; zeros on error) -/
def ziskCodeHashAtHeaderStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000\n" ++
  "  ld t2, 8(t1)                # header_rlp_len\n" ++
  "  ld t3, 16(t1)               # witness_state_len\n" ++
  "  addi a2, t1, 24             # address ptr\n" ++
  "  addi a0, t1, 44             # header_rlp ptr\n" ++
  "  mv a1, t2                   # header_rlp_len\n" ++
  "  add a3, a0, t2              # witness.state ptr\n" ++
  "  mv a4, t3                   # witness_state_len\n" ++
  "  li a5, 0xa0010008           # 32 B output\n" ++
  "  jal ra, code_hash_at_header_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lchahsr_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  accountDecodeFunction ++ "\n" ++
  accountAtAddressFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  codeHashAtHeaderStateRootFunction ++ "\n" ++
  ".Lchahsr_pdone:"

def ziskCodeHashAtHeaderStateRootDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8\n" ++
  "mbc_offset:\n" ++
  "  .zero 8\n" ++
  "mbc_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_lookup_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_lookup_offset:\n" ++
  "  .zero 8\n" ++
  "mw_lookup_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_child_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_path_offset:\n" ++
  "  .zero 8\n" ++
  "mw_path_length:\n" ++
  "  .zero 8\n" ++
  "mw_child_offset:\n" ++
  "  .zero 8\n" ++
  "mw_child_length:\n" ++
  "  .zero 8\n" ++
  "mw_value_offset:\n" ++
  "  .zero 8\n" ++
  "mw_value_length:\n" ++
  "  .zero 8\n" ++
  "mw_nibble_count:\n" ++
  "  .zero 8\n" ++
  "mw_is_leaf:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_nibble_buf:\n" ++
  "  .zero 128\n" ++
  ".balign 32\n" ++
  "mlk_keccak_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "mlk_nibble_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "ad_offset:\n" ++
  "  .zero 8\n" ++
  "ad_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aa_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aa_value_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "chahsr_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "chahsr_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "chahsr_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"

def ziskCodeHashAtHeaderStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCodeHashAtHeaderStateRootPrologue
  dataAsm     := ziskCodeHashAtHeaderStateRootDataSection
}

end EvmAsm.Codegen
