/-
  EvmAsm.Codegen.Programs.RlpRead

  Standalone Lean strings for the RLP primitives -- read side
  (`rlp_list_nth_item` PR-K20, `rlp_list_count_items` PR-K47) and
  write side (`rlp_encode_uint_be` PR-K30, `rlp_encode_bytes`
  PR-K128, `rlp_encode_list_prefix` PR-K129).

  Lifted out of `EvmAsm.Codegen.Programs` so MPT / tx / header /
  block consumers can import them without pulling the full
  registry hub.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## rlp_list_nth_item -- PR-K20 walk RLP list to extract
    the N-th item's content bounds.

    Foundation for MPT node decoding. Handles all RLP item
    forms: single bytes, short strings (0x80..0xb7), long
    strings (0xb8..0xbf), short lists (0xc0..0xf7), long lists
    (0xf8..0xff with length-of-length in [1..8]).

    Calling convention:
      a0 (input)  : list bytes ptr (start of outer RLP list
                    prefix)
      a1 (input)  : total list byte length
      a2 (input)  : index N (0-based)
      a3 (input)  : u64 out ptr (content offset within list bytes)
      a4 (input)  : u64 out ptr (content byte length)
      ra (input)  : return
      a0 (output) : 0 on hit, 1 on parse error / OOB.

    Content interpretation:
      * Single byte (0x00..0x7f)   : offset = item_start; len = 1
      * Short string (0x80..0xb7)  : offset = item_start+1; len = b - 0x80
      * Long string (0xb8..0xbf)   : offset = item_start+1+lol; len = decoded
      * Short list (0xc0..0xf7)    : offset = item_start; len = full encoded length
      * Long list (0xf8..0xff)     : offset = item_start; len = full encoded length

    Byte-string items have their RLP prefix stripped; sub-list
    items are returned in full (so callers can recurse with
    another call to `rlp_list_nth_item`).

    Pure register arithmetic, no scratch memory, leaf-callable. -/
def rlpListNthItemFunction : String :=
  "rlp_list_nth_item:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # s0 = list_ptr\n" ++
  "  add s1, a0, a1             # s1 = list_end\n" ++
  "  mv s2, a2                  # s2 = N\n" ++
  "  mv s3, a3                  # s3 = out_offset_ptr\n" ++
  "  mv s4, a4                  # s4 = out_length_ptr\n" ++
  "  # Parse outer list prefix.\n" ++
  "  bgeu s0, s1, .Lrln_fail\n" ++
  "  lbu t0, 0(s0)\n" ++
  "  li t1, 0xc0\n" ++
  "  bltu t0, t1, .Lrln_fail    # not an RLP list\n" ++
  "  li t1, 0xf8\n" ++
  "  bltu t0, t1, .Lrln_short_outer\n" ++
  "  # Long outer: prefix bytes = 1 + (t0 - 0xf7)\n" ++
  "  li t1, 0xf7\n" ++
  "  sub t2, t0, t1             # lol\n" ++
  "  addi t2, t2, 1             # prefix bytes\n" ++
  "  add s5, s0, t2             # s5 = cursor at first item\n" ++
  "  j .Lrln_walk\n" ++
  ".Lrln_short_outer:\n" ++
  "  addi s5, s0, 1\n" ++
  ".Lrln_walk:\n" ++
  "  li s6, 0                   # i\n" ++
  ".Lrln_loop:\n" ++
  "  beq s6, s2, .Lrln_at_target\n" ++
  "  bgeu s5, s1, .Lrln_fail    # walked past end of list\n" ++
  "  # Compute size of item at s5; advance s5 by it.\n" ++
  "  lbu t0, 0(s5)\n" ++
  "  li t1, 0x80\n" ++
  "  bltu t0, t1, .Lrln_skip_single\n" ++
  "  li t1, 0xb8\n" ++
  "  bltu t0, t1, .Lrln_skip_short_string\n" ++
  "  li t1, 0xc0\n" ++
  "  bltu t0, t1, .Lrln_skip_long_string\n" ++
  "  li t1, 0xf8\n" ++
  "  bltu t0, t1, .Lrln_skip_short_list\n" ++
  "  # Long list: lol = t0 - 0xf7\n" ++
  "  li t1, 0xf7\n" ++
  "  sub t2, t0, t1             # lol\n" ++
  "  li t3, 0                   # decoded length accumulator\n" ++
  "  mv t4, t2                  # remaining length bytes\n" ++
  "  addi t5, s5, 1\n" ++
  ".Lrln_skll_be:\n" ++
  "  beqz t4, .Lrln_skll_done\n" ++
  "  slli t3, t3, 8\n" ++
  "  lbu t6, 0(t5)\n" ++
  "  or t3, t3, t6\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lrln_skll_be\n" ++
  ".Lrln_skll_done:\n" ++
  "  addi t6, t2, 1\n" ++
  "  add t6, t6, t3             # 1 + lol + decoded\n" ++
  "  add s5, s5, t6\n" ++
  "  j .Lrln_step\n" ++
  ".Lrln_skip_short_list:\n" ++
  "  li t1, 0xc0\n" ++
  "  sub t6, t0, t1\n" ++
  "  addi t6, t6, 1             # 1 + (t0 - 0xc0)\n" ++
  "  add s5, s5, t6\n" ++
  "  j .Lrln_step\n" ++
  ".Lrln_skip_long_string:\n" ++
  "  li t1, 0xb7\n" ++
  "  sub t2, t0, t1             # lol\n" ++
  "  li t3, 0\n" ++
  "  mv t4, t2\n" ++
  "  addi t5, s5, 1\n" ++
  ".Lrln_skls_be:\n" ++
  "  beqz t4, .Lrln_skls_done\n" ++
  "  slli t3, t3, 8\n" ++
  "  lbu t6, 0(t5)\n" ++
  "  or t3, t3, t6\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lrln_skls_be\n" ++
  ".Lrln_skls_done:\n" ++
  "  addi t6, t2, 1\n" ++
  "  add t6, t6, t3\n" ++
  "  add s5, s5, t6\n" ++
  "  j .Lrln_step\n" ++
  ".Lrln_skip_short_string:\n" ++
  "  li t1, 0x80\n" ++
  "  sub t6, t0, t1\n" ++
  "  addi t6, t6, 1\n" ++
  "  add s5, s5, t6\n" ++
  "  j .Lrln_step\n" ++
  ".Lrln_skip_single:\n" ++
  "  addi s5, s5, 1\n" ++
  ".Lrln_step:\n" ++
  "  addi s6, s6, 1\n" ++
  "  j .Lrln_loop\n" ++
  ".Lrln_at_target:\n" ++
  "  bgeu s5, s1, .Lrln_fail    # target index past last item\n" ++
  "  lbu t0, 0(s5)\n" ++
  "  li t1, 0x80\n" ++
  "  bltu t0, t1, .Lrln_t_single\n" ++
  "  li t1, 0xb8\n" ++
  "  bltu t0, t1, .Lrln_t_short_string\n" ++
  "  li t1, 0xc0\n" ++
  "  bltu t0, t1, .Lrln_t_long_string\n" ++
  "  li t1, 0xf8\n" ++
  "  bltu t0, t1, .Lrln_t_short_list\n" ++
  "  # Long list (full encoded form)\n" ++
  "  li t1, 0xf7\n" ++
  "  sub t2, t0, t1\n" ++
  "  li t3, 0\n" ++
  "  mv t4, t2\n" ++
  "  addi t5, s5, 1\n" ++
  ".Lrln_tll_be:\n" ++
  "  beqz t4, .Lrln_tll_done\n" ++
  "  slli t3, t3, 8\n" ++
  "  lbu t6, 0(t5)\n" ++
  "  or t3, t3, t6\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lrln_tll_be\n" ++
  ".Lrln_tll_done:\n" ++
  "  addi t6, t2, 1\n" ++
  "  add t6, t6, t3             # full encoded size\n" ++
  "  sub t1, s5, s0\n" ++
  "  sd t1, 0(s3)\n" ++
  "  sd t6, 0(s4)\n" ++
  "  j .Lrln_ok\n" ++
  ".Lrln_t_short_list:\n" ++
  "  li t1, 0xc0\n" ++
  "  sub t6, t0, t1\n" ++
  "  addi t6, t6, 1\n" ++
  "  sub t1, s5, s0\n" ++
  "  sd t1, 0(s3)\n" ++
  "  sd t6, 0(s4)\n" ++
  "  j .Lrln_ok\n" ++
  ".Lrln_t_long_string:\n" ++
  "  li t1, 0xb7\n" ++
  "  sub t2, t0, t1\n" ++
  "  li t3, 0\n" ++
  "  mv t4, t2\n" ++
  "  addi t5, s5, 1\n" ++
  ".Lrln_tls_be:\n" ++
  "  beqz t4, .Lrln_tls_done\n" ++
  "  slli t3, t3, 8\n" ++
  "  lbu t6, 0(t5)\n" ++
  "  or t3, t3, t6\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lrln_tls_be\n" ++
  ".Lrln_tls_done:\n" ++
  "  # content offset = s5 + 1 + lol - s0\n" ++
  "  addi t6, t2, 1\n" ++
  "  add t6, t6, s5\n" ++
  "  sub t6, t6, s0\n" ++
  "  sd t6, 0(s3)\n" ++
  "  sd t3, 0(s4)               # content length = decoded\n" ++
  "  j .Lrln_ok\n" ++
  ".Lrln_t_short_string:\n" ++
  "  # content offset = s5 + 1 - s0; length = t0 - 0x80\n" ++
  "  addi t6, s5, 1\n" ++
  "  sub t6, t6, s0\n" ++
  "  sd t6, 0(s3)\n" ++
  "  li t1, 0x80\n" ++
  "  sub t1, t0, t1\n" ++
  "  sd t1, 0(s4)\n" ++
  "  j .Lrln_ok\n" ++
  ".Lrln_t_single:\n" ++
  "  # content offset = s5 - s0; length = 1\n" ++
  "  sub t1, s5, s0\n" ++
  "  sd t1, 0(s3)\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s4)\n" ++
  ".Lrln_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Lrln_ret\n" ++
  ".Lrln_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lrln_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-! ## rlp_list_count_items -- PR-K47 top-level item counter

    Walk an RLP-encoded list once and return the number of
    top-level items it contains. Building block for callers
    that need cardinality but not the items themselves:
    `access_list_count`, `authorization_list_count`,
    `blob_versioned_hashes_count`, `tx_count_per_block`.

    Mirrors the item-skip logic in PR-K20 `rlp_list_nth_item`
    but doesn't track a target index; counts every item it
    can walk past until the list payload ends.

    Calling convention:
      a0 (input)  : list bytes ptr (start of outer RLP list
                    prefix, byte 0xc0..0xff)
      a1 (input)  : total list byte length (full encoded item
                    incl. prefix)
      a2 (input)  : u64 out ptr (receives count on success)
      ra (input)  : return
      a0 (output) : 0 on success, 1 on parse error
                    (not a list, truncated, item runs past end)

    Pure register arithmetic except for the count store; no
    scratch memory; leaf-callable. -/
def rlpListCountItemsFunction : String :=
  "rlp_list_count_items:\n" ++
  "  beqz a1, .Lrlc_fail        # empty input cannot encode a list\n" ++
  "  lbu t0, 0(a0)\n" ++
  "  li t1, 0xc0\n" ++
  "  bltu t0, t1, .Lrlc_fail    # not an RLP list\n" ++
  "  li t1, 0xf8\n" ++
  "  bltu t0, t1, .Lrlc_short_outer\n" ++
  "  # Long outer list: prefix bytes = 1 + (t0 - 0xf7)\n" ++
  "  li t1, 0xf7\n" ++
  "  sub t2, t0, t1             # lol\n" ++
  "  addi t2, t2, 1             # total prefix bytes\n" ++
  "  add t3, a0, t2             # cursor at first item\n" ++
  "  j .Lrlc_walk\n" ++
  ".Lrlc_short_outer:\n" ++
  "  addi t3, a0, 1\n" ++
  ".Lrlc_walk:\n" ++
  "  add t4, a0, a1             # end-of-list cursor (exclusive)\n" ++
  "  li t5, 0                   # count\n" ++
  ".Lrlc_loop:\n" ++
  "  beq t3, t4, .Lrlc_done\n" ++
  "  bgtu t3, t4, .Lrlc_fail    # cursor walked past end → malformed\n" ++
  "  lbu t0, 0(t3)\n" ++
  "  li t1, 0x80\n" ++
  "  bltu t0, t1, .Lrlc_skip_single\n" ++
  "  li t1, 0xb8\n" ++
  "  bltu t0, t1, .Lrlc_skip_short_str\n" ++
  "  li t1, 0xc0\n" ++
  "  bltu t0, t1, .Lrlc_skip_long_str\n" ++
  "  li t1, 0xf8\n" ++
  "  bltu t0, t1, .Lrlc_skip_short_list\n" ++
  "  # Long list at t3: lol = t0 - 0xf7\n" ++
  "  li t1, 0xf7\n" ++
  "  sub t2, t0, t1             # lol\n" ++
  "  li a3, 0                   # decoded length accumulator\n" ++
  "  mv a4, t2                  # remaining length bytes\n" ++
  "  addi a5, t3, 1\n" ++
  ".Lrlc_skll_be:\n" ++
  "  beqz a4, .Lrlc_skll_done\n" ++
  "  slli a3, a3, 8\n" ++
  "  lbu a6, 0(a5)\n" ++
  "  or  a3, a3, a6\n" ++
  "  addi a5, a5, 1\n" ++
  "  addi a4, a4, -1\n" ++
  "  j .Lrlc_skll_be\n" ++
  ".Lrlc_skll_done:\n" ++
  "  addi a6, t2, 1\n" ++
  "  add  a6, a6, a3            # 1 + lol + decoded\n" ++
  "  add  t3, t3, a6\n" ++
  "  j .Lrlc_step\n" ++
  ".Lrlc_skip_short_list:\n" ++
  "  li t1, 0xc0\n" ++
  "  sub a6, t0, t1\n" ++
  "  addi a6, a6, 1             # 1 + (t0 - 0xc0)\n" ++
  "  add  t3, t3, a6\n" ++
  "  j .Lrlc_step\n" ++
  ".Lrlc_skip_long_str:\n" ++
  "  li t1, 0xb7\n" ++
  "  sub t2, t0, t1             # lol\n" ++
  "  li a3, 0\n" ++
  "  mv a4, t2\n" ++
  "  addi a5, t3, 1\n" ++
  ".Lrlc_skls_be:\n" ++
  "  beqz a4, .Lrlc_skls_done\n" ++
  "  slli a3, a3, 8\n" ++
  "  lbu a6, 0(a5)\n" ++
  "  or  a3, a3, a6\n" ++
  "  addi a5, a5, 1\n" ++
  "  addi a4, a4, -1\n" ++
  "  j .Lrlc_skls_be\n" ++
  ".Lrlc_skls_done:\n" ++
  "  addi a6, t2, 1\n" ++
  "  add  a6, a6, a3\n" ++
  "  add  t3, t3, a6\n" ++
  "  j .Lrlc_step\n" ++
  ".Lrlc_skip_short_str:\n" ++
  "  li t1, 0x80\n" ++
  "  sub a6, t0, t1\n" ++
  "  addi a6, a6, 1\n" ++
  "  add  t3, t3, a6\n" ++
  "  j .Lrlc_step\n" ++
  ".Lrlc_skip_single:\n" ++
  "  addi t3, t3, 1\n" ++
  ".Lrlc_step:\n" ++
  "  addi t5, t5, 1\n" ++
  "  j .Lrlc_loop\n" ++
  ".Lrlc_done:\n" ++
  "  sd t5, 0(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lrlc_fail:\n" ++
  "  sd zero, 0(a2)\n" ++
  "  li a0, 1\n" ++
  "  ret"


/-! ## rlp_encode_list_prefix -- PR-K129

    Write the RLP list-header prefix bytes for a list whose total
    pre-encoded payload size is `payload_length`. Matches the yellow
    paper §B "list" rule:

      payload_length < 56  → 0xc0 + payload_length   (1 byte)
      else                 → 0xf7 + bc, then `bc`-byte BE length
                             (`bc` = effective byte count of
                             `payload_length`, 1..8)

    Companion to PR-K128 `rlp_encode_bytes` (the string version)
    and PR-K30 `rlp_encode_uint_be` (the uint version). Together
    these three primitives cover the encoder side of the trie /
    node / header / tx serialisation pipeline.

    Calling convention:
      a0 (input)  : payload_length (u64)
      a1 (input)  : output bytes ptr (caller supplies ≥ 9 bytes)
      a2 (input)  : u64 out ptr (prefix byte length)
      ra (input)  : return
      a0 (output) : 0 (always succeeds — total function).

    Pure-leaf semantics: no scratch memory, no transitive calls. -/
def rlpEncodeListPrefixFunction : String :=
  "rlp_encode_list_prefix:\n" ++
  "  li t0, 56\n" ++
  "  bgeu a0, t0, .Lrelp_long\n" ++
  "  # Short list: prefix = 0xc0 + payload_length (1 byte).\n" ++
  "  addi t1, a0, 0xc0\n" ++
  "  sb t1, 0(a1)\n" ++
  "  li t2, 1\n" ++
  "  sd t2, 0(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lrelp_long:\n" ++
  "  # Long list: prefix = 0xf7 + bc, then bc-byte BE length.\n" ++
  "  li t3, 1\n" ++
  "  li t4, 0x100\n" ++
  "  bltu a0, t4, .Lrelp_have_bc\n" ++
  "  li t3, 2\n" ++
  "  slli t4, t4, 8\n" ++
  "  bltu a0, t4, .Lrelp_have_bc\n" ++
  "  li t3, 3\n" ++
  "  slli t4, t4, 8\n" ++
  "  bltu a0, t4, .Lrelp_have_bc\n" ++
  "  li t3, 4\n" ++
  "  slli t4, t4, 8\n" ++
  "  bltu a0, t4, .Lrelp_have_bc\n" ++
  "  li t3, 5\n" ++
  "  slli t4, t4, 8\n" ++
  "  bltu a0, t4, .Lrelp_have_bc\n" ++
  "  li t3, 6\n" ++
  "  slli t4, t4, 8\n" ++
  "  bltu a0, t4, .Lrelp_have_bc\n" ++
  "  li t3, 7\n" ++
  "  slli t4, t4, 8\n" ++
  "  bltu a0, t4, .Lrelp_have_bc\n" ++
  "  li t3, 8\n" ++
  ".Lrelp_have_bc:\n" ++
  "  addi t4, t3, 0xf7\n" ++
  "  sb t4, 0(a1)\n" ++
  "  mv t5, a1\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t4, t3, -1\n" ++
  ".Lrelp_emit_be:\n" ++
  "  bltz t4, .Lrelp_be_done\n" ++
  "  slli t6, t4, 3\n" ++
  "  srl t0, a0, t6\n" ++
  "  sb t0, 0(t5)\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lrelp_emit_be\n" ++
  ".Lrelp_be_done:\n" ++
  "  addi t5, t3, 1\n" ++
  "  sd t5, 0(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret"


/-! ## rlp_encode_uint_be -- PR-K30 RLP canonical-form encoder

    Strip leading zeros from a big-endian byte array and emit
    the canonical RLP encoding:

      value == 0       → 0x80 (1 byte; RLP empty bytes)
      value < 0x80     → single byte = value
      else (1..32 B)   → 0x80 + len  +  stripped BE bytes

    Building block for `account_encode` (PR-K31+), which calls
    this for the nonce / balance fields, and for state-root
    recompute after MPT mutation.

    Calling convention:
      a0 (input)  : src bytes ptr (BE, possibly with leading zeros)
      a1 (input)  : src byte length (any; typical: 8 for u64,
                    32 for u256)
      a2 (input)  : output buffer ptr (≥ a1 + 1 bytes capacity)
      ra (input)  : return
      a0 (output) : number of bytes written

    Pure register arithmetic, no scratch, leaf-callable. -/
def rlpEncodeUintBeFunction : String :=
  "rlp_encode_uint_be:\n" ++
  "  # Find first non-zero byte; stripped_len = src_len - leading_zeros.\n" ++
  "  mv t0, a0\n" ++
  "  mv t1, a1\n" ++
  ".Lreu_skip_zero:\n" ++
  "  beqz t1, .Lreu_all_zero\n" ++
  "  lbu t3, 0(t0)\n" ++
  "  bnez t3, .Lreu_have\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lreu_skip_zero\n" ++
  ".Lreu_all_zero:\n" ++
  "  li t3, 0x80\n" ++
  "  sb t3, 0(a2)\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Lreu_have:\n" ++
  "  # t0 = ptr to first non-zero byte; t1 = stripped_len.\n" ++
  "  mv t6, t1\n" ++
  "  li t3, 1\n" ++
  "  bne t1, t3, .Lreu_multi\n" ++
  "  lbu t4, 0(t0)\n" ++
  "  li t5, 0x80\n" ++
  "  bgeu t4, t5, .Lreu_multi\n" ++
  "  # Single-byte form.\n" ++
  "  sb t4, 0(a2)\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Lreu_multi:\n" ++
  "  # Short-string form: 0x80 + stripped_len, then stripped bytes.\n" ++
  "  li t3, 0x80\n" ++
  "  add t3, t3, t6\n" ++
  "  sb t3, 0(a2)\n" ++
  "  addi t4, a2, 1\n" ++
  "  mv t1, t6\n" ++
  ".Lreu_copy:\n" ++
  "  beqz t1, .Lreu_done\n" ++
  "  lbu t5, 0(t0)\n" ++
  "  sb  t5, 0(t4)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lreu_copy\n" ++
  ".Lreu_done:\n" ++
  "  addi a0, t6, 1               # 1 + stripped_len\n" ++
  "  ret"


/-! ## rlp_encode_bytes -- PR-K128

    Generic RLP encoder for a raw byte string. Matches the
    `rlp.encode(bytes)` reference (Ethereum yellow-paper §B):

      len == 1 AND byte < 0x80   → single byte (no prefix)
      len < 56                   → 0x80 + len, then `len` bytes
      else                       → 0xb7 + bc, then `bc`-byte BE
                                   length, then `len` bytes
                                   (`bc` = effective byte count of
                                    `len`, no leading zeros, 1..8)

    PR-K30 `rlp_encode_uint_be` covers the *uint* shape (BE bytes
    + canonical-form leading-zero stripping); K128 covers the
    *arbitrary bytes* shape, which doesn't strip leading zeros and
    handles the single-byte-no-prefix short-cut. Together they're
    the two RLP-string primitives needed for trie / node /
    header / tx re-encoding.

    Calling convention:
      a0 (input)  : data ptr
      a1 (input)  : data byte length
      a2 (input)  : output bytes ptr
                    (caller must have space for `9 + len` bytes)
      a3 (input)  : u64 out ptr (output byte length)
      ra (input)  : return
      a0 (output) : 0 (always succeeds — total function).

    Pure-leaf semantics: no scratch memory, no transitive calls. -/
def rlpEncodeBytesFunction : String :=
  "rlp_encode_bytes:\n" ++
  "  # t0 = data cursor; t1 = remaining; t2 = out cursor.\n" ++
  "  mv t0, a0\n" ++
  "  mv t1, a1\n" ++
  "  mv t2, a2\n" ++
  "  # Single-byte short-cut: len == 1 AND byte < 0x80.\n" ++
  "  li t3, 1\n" ++
  "  bne t1, t3, .Lreb_check_short\n" ++
  "  lbu t4, 0(t0)\n" ++
  "  li t5, 0x80\n" ++
  "  bgeu t4, t5, .Lreb_check_short\n" ++
  "  sb t4, 0(t2)\n" ++
  "  li t6, 1\n" ++
  "  sd t6, 0(a3)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lreb_check_short:\n" ++
  "  li t3, 56\n" ++
  "  bgeu t1, t3, .Lreb_long\n" ++
  "  # Short string: prefix = 0x80 + len, then data.\n" ++
  "  addi t3, t1, 0x80\n" ++
  "  sb t3, 0(t2)\n" ++
  "  addi t2, t2, 1\n" ++
  "  mv t4, t1                   # bytes to copy\n" ++
  ".Lreb_short_copy:\n" ++
  "  beqz t4, .Lreb_short_done\n" ++
  "  lbu t3, 0(t0)\n" ++
  "  sb t3, 0(t2)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lreb_short_copy\n" ++
  ".Lreb_short_done:\n" ++
  "  addi t6, t1, 1              # out_len = 1 + len\n" ++
  "  sd t6, 0(a3)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lreb_long:\n" ++
  "  # Long string: prefix = 0xb7 + bc, then bc-byte BE len, then data.\n" ++
  "  # Compute bc = effective byte count of t1 (1..8).\n" ++
  "  # Write t1 as 8 BE bytes to a small scratch on the stack (or use\n" ++
  "  # shifts directly into the out buffer). Use direct write approach:\n" ++
  "  # determine bc, then write bc BE bytes from t1 by shifting right.\n" ++
  "  li t3, 1\n" ++
  "  li t4, 0x100                # 2^8\n" ++
  "  bltu t1, t4, .Lreb_have_bc\n" ++
  "  li t3, 2\n" ++
  "  slli t4, t4, 8              # 2^16\n" ++
  "  bltu t1, t4, .Lreb_have_bc\n" ++
  "  li t3, 3\n" ++
  "  slli t4, t4, 8              # 2^24\n" ++
  "  bltu t1, t4, .Lreb_have_bc\n" ++
  "  li t3, 4\n" ++
  "  slli t4, t4, 8              # 2^32\n" ++
  "  bltu t1, t4, .Lreb_have_bc\n" ++
  "  li t3, 5\n" ++
  "  slli t4, t4, 8              # 2^40\n" ++
  "  bltu t1, t4, .Lreb_have_bc\n" ++
  "  li t3, 6\n" ++
  "  slli t4, t4, 8              # 2^48\n" ++
  "  bltu t1, t4, .Lreb_have_bc\n" ++
  "  li t3, 7\n" ++
  "  slli t4, t4, 8              # 2^56\n" ++
  "  bltu t1, t4, .Lreb_have_bc\n" ++
  "  li t3, 8\n" ++
  ".Lreb_have_bc:\n" ++
  "  # t3 = bc. Write prefix 0xb7 + bc.\n" ++
  "  addi t4, t3, 0xb7\n" ++
  "  sb t4, 0(t2)\n" ++
  "  addi t2, t2, 1\n" ++
  "  # Write bc bytes of t1 in BE order. Use a counter i = bc-1..0,\n" ++
  "  # shift t1 right by 8*i, store low byte.\n" ++
  "  addi t4, t3, -1             # i = bc-1\n" ++
  ".Lreb_emit_be:\n" ++
  "  bltz t4, .Lreb_be_done\n" ++
  "  slli t5, t4, 3              # 8 * i\n" ++
  "  srl t6, t1, t5\n" ++
  "  sb t6, 0(t2)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lreb_emit_be\n" ++
  ".Lreb_be_done:\n" ++
  "  # Copy data bytes.\n" ++
  "  mv t4, t1\n" ++
  ".Lreb_long_copy:\n" ++
  "  beqz t4, .Lreb_long_done\n" ++
  "  lbu t5, 0(t0)\n" ++
  "  sb t5, 0(t2)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lreb_long_copy\n" ++
  ".Lreb_long_done:\n" ++
  "  # out_len = 1 + bc + len\n" ++
  "  addi t5, t3, 1\n" ++
  "  add t5, t5, t1\n" ++
  "  sd t5, 0(a3)\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_rlp_encode_bytes`: probe BuildUnit. Reads (data_len,
    data_bytes) from host input, writes (status, out_len,
    out_bytes...) to OUTPUT. -/
def ziskRlpEncodeBytesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # data length\n" ++
  "  addi a0, a4, 16             # data ptr\n" ++
  "  li a2, 0xa0010010           # out bytes\n" ++
  "  li a3, 0xa0010008           # out_len out\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lreb_pdone\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  ".Lreb_pdone:"

def ziskRlpEncodeBytesDataSection : String :=
  ".section .data\n" ++
  "reb_scratch:\n" ++
  "  .zero 8"

def ziskRlpEncodeBytesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRlpEncodeBytesPrologue
  dataAsm     := ziskRlpEncodeBytesDataSection
}

/-! ## rlp_item_size / rlp_item_span (PR: full byte-span of an RLP item)

    `rlp_list_nth_item` returns the item's CONTENT offset/length for string
    items (e.g. a `0xa0||hash` ref -> offset after `0xa0`, length 32) but the
    FULL span for embedded-list items -- inconsistent, so it can't be used to
    copy a branch slot verbatim. `rlp_item_span` returns the FULL encoded span
    (start offset incl. prefix, total size) of list item `i` for EVERY item
    type, which is what mpt_set's branch-slot reconstruction needs. -/

/-- `rlp_item_size`: a0 = ptr to one RLP item -> a0 = its full encoded size.
    Leaf; clobbers t0..t6 only (preserves all s-registers and ra). -/
def rlpItemSizeFunction : String :=
  "rlp_item_size:\n" ++
  "  lbu t0, 0(a0)\n" ++
  "  li t1, 0x80\n" ++
  "  bgeu t0, t1, .Lris2_a\n" ++
  "  li a0, 1\n" ++                          -- single byte < 0x80
  "  ret\n" ++
  ".Lris2_a:\n" ++
  "  li t1, 0xb8\n" ++
  "  bgeu t0, t1, .Lris2_b\n" ++
  "  addi a0, t0, -128\n" ++                  -- short string: len = t0 - 0x80
  "  addi a0, a0, 1\n" ++                     -- + 1 prefix byte
  "  ret\n" ++
  ".Lris2_b:\n" ++
  "  li t1, 0xc0\n" ++
  "  bgeu t0, t1, .Lris2_c\n" ++
  "  li t1, 0xb7\n" ++
  "  sub t2, t0, t1\n" ++                     -- long string: lol = t0 - 0xb7
  "  j .Lris2_long\n" ++
  ".Lris2_c:\n" ++
  "  li t1, 0xf8\n" ++
  "  bgeu t0, t1, .Lris2_d\n" ++
  "  addi a0, t0, -192\n" ++                  -- short list: len = t0 - 0xc0
  "  addi a0, a0, 1\n" ++
  "  ret\n" ++
  ".Lris2_d:\n" ++
  "  li t1, 0xf7\n" ++
  "  sub t2, t0, t1\n" ++                     -- long list: lol = t0 - 0xf7
  ".Lris2_long:\n" ++
  "  li t3, 0\n" ++                           -- decoded length accumulator
  "  addi t4, a0, 1\n" ++                     -- BE length bytes start at item+1
  "  mv t5, t2\n" ++                          -- remaining lol bytes
  ".Lris2_be:\n" ++
  "  beqz t5, .Lris2_done\n" ++
  "  slli t3, t3, 8\n" ++
  "  lbu t6, 0(t4)\n" ++
  "  or t3, t3, t6\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t5, t5, -1\n" ++
  "  j .Lris2_be\n" ++
  ".Lris2_done:\n" ++
  "  addi a0, t2, 1\n" ++                     -- 1 (tag) + lol
  "  add a0, a0, t3\n" ++                     -- + decoded payload length
  "  ret"

/-- `rlp_item_span`: a0 = list ptr, a1 = list len, a2 = item index i,
    a3 = out_start_ptr (u64, item start offset incl. its prefix, relative to
    list ptr), a4 = out_size_ptr (u64, full encoded size). Returns a0 = 0 on
    success, 1 on parse failure / i out of range. The cursor is kept in a
    callee-saved register because `rlp_item_size` clobbers the temporaries. -/
def rlpItemSpanFunction : String :=
  "rlp_item_span:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; add s1, a0, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  bgeu s0, s1, .Lrisp_fail\n" ++
  "  lbu t0, 0(s0)\n" ++
  "  li t1, 0xc0; bltu t0, t1, .Lrisp_fail\n" ++   -- outer must be a list
  "  li t1, 0xf8; bltu t0, t1, .Lrisp_short_outer\n" ++
  "  li t1, 0xf7; sub t2, t0, t1; addi t2, t2, 1\n" ++
  "  add s5, s0, t2; j .Lrisp_walk\n" ++
  ".Lrisp_short_outer:\n" ++
  "  addi s5, s0, 1\n" ++                          -- cursor at first item
  ".Lrisp_walk:\n" ++
  "  li s6, 0\n" ++                                -- index
  ".Lrisp_loop:\n" ++
  "  beq s6, s2, .Lrisp_target\n" ++
  "  bgeu s5, s1, .Lrisp_fail\n" ++
  "  mv a0, s5; jal ra, rlp_item_size\n" ++
  "  add s5, s5, a0; addi s6, s6, 1; j .Lrisp_loop\n" ++
  ".Lrisp_target:\n" ++
  "  bgeu s5, s1, .Lrisp_fail\n" ++
  "  mv a0, s5; jal ra, rlp_item_size\n" ++
  "  sub t1, s5, s0; sd t1, 0(s3); sd a0, 0(s4)\n" ++
  "  li a0, 0; j .Lrisp_ret\n" ++
  ".Lrisp_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lrisp_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64; ret"

/-- `zisk_rlp_item_span`: probe. Input: bytes 0..8 list_len, 8..16 index i,
    16.. list bytes. Output: 0..8 status, 8..16 item start offset, 16..24
    item full size. -/
def ziskRlpItemSpanPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # list_len\n" ++
  "  ld a2, 16(a5)               # index i\n" ++
  "  addi a0, a5, 24             # list ptr\n" ++
  "  li a3, 0xa0010008           # out_start\n" ++
  "  li a4, 0xa0010010           # out_size\n" ++
  "  jal ra, rlp_item_span\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)\n" ++
  "  j .Lrisp_pdone\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  ".Lrisp_pdone:"

def ziskRlpItemSpanDataSection : String :=
  ".section .data\n" ++
  "ris_scratch:\n" ++
  "  .zero 8"

def ziskRlpItemSpanProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRlpItemSpanPrologue
  dataAsm     := ziskRlpItemSpanDataSection
}


end EvmAsm.Codegen
