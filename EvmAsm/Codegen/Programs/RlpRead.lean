/-
  EvmAsm.Codegen.Programs.RlpRead

  Standalone Lean strings for the two RLP-list reader primitives:
  - `rlp_list_nth_item` (PR-K20) — walk an RLP list and return the
    i-th item's content bounds
  - `rlp_list_count_items` (PR-K47) — count top-level items in an
    RLP list

  Lifted out of `EvmAsm.Codegen.Programs` so MPT / tx / header /
  block consumers can import them without pulling the full
  registry hub.
-/

namespace EvmAsm.Codegen

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

end EvmAsm.Codegen
