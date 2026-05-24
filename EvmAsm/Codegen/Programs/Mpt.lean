/-
  EvmAsm.Codegen.Programs.Mpt

  MPT codec primitives (PR-K109..K116):
  - K109 `mpt_nibbles_to_compact`     — encoder side of HP
  - K110 `mpt_compact_to_nibbles`     — decoder side of HP
  - K111 `mpt_node_classify`          — branch / leaf / extension
  - K112 `mpt_encode_internal_node`   — embed-or-hash node reference
  - K113 `mpt_leaf_extract`           — leaf node → (nibbles, value)
  - K114 `mpt_extension_extract`      — ext node → (nibbles, child_ref)
  - K115 `mpt_branch_get_child`       — i-th child of a branch
  - K116 `mpt_branch_get_value`       — field 16 of a branch

  Lifted out of `EvmAsm.Codegen.Programs` to keep the registry hub
  manageable.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## witness_lookup_by_hash -- PR-K19 (linear-scan flavour)

    Find the entry in an SSZ list section whose keccak256 digest
    matches a caller-supplied target hash. Returns the matched
    entry's (offset, length) within the section, or status=1 on
    miss.

    Calling convention:
      a0 (input)  : SSZ list section ptr (witness.state /
                    witness.codes shape)
      a1 (input)  : section_len (0 ⇒ guaranteed miss)
      a2 (input)  : 32-byte target hash ptr
      a3 (input)  : u64 out ptr (matched entry's byte offset
                    within the section; meaningful only on hit)
      a4 (input)  : u64 out ptr (matched entry's byte length;
                    meaningful only on hit)
      ra (input)  : return
      a0 (output) : 0 on hit, 1 on miss

    Walks every element computing `keccak256(element_bytes)`
    until either a match is found or the list is exhausted.
    O(N) per call; PR-K20+ will replace with a pre-built bucket
    table for O(1) average lookups. -/
def witnessLookupByHashFunction : String :=
  "witness_lookup_by_hash:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # section ptr\n" ++
  "  mv s1, a1                  # section_len\n" ++
  "  mv s2, a2                  # target_hash ptr\n" ++
  "  mv s3, a3                  # out_offset ptr\n" ++
  "  mv s4, a4                  # out_length ptr\n" ++
  "  beqz s1, .Lwlh_miss        # empty section ⇒ miss\n" ++
  "  lwu t0, 0(s0)              # first inner offset = 4 * N\n" ++
  "  srli s5, t0, 2             # s5 = N\n" ++
  "  li s6, 0                   # s6 = i\n" ++
  ".Lwlh_loop:\n" ++
  "  beq s6, s5, .Lwlh_miss\n" ++
  "  # Compute element i bounds.\n" ++
  "  slli t0, s6, 2             # 4*i\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  add a0, s0, t2             # el_i_start\n" ++
  "  addi t3, s6, 1\n" ++
  "  beq t3, s5, .Lwlh_use_end\n" ++
  "  slli t3, t3, 2             # 4*(i+1)\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # el_i_end\n" ++
  "  j .Lwlh_have_end\n" ++
  ".Lwlh_use_end:\n" ++
  "  add t4, s0, s1             # el_i_end = section_end\n" ++
  ".Lwlh_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  la a2, wlh_scratch_hash\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # Compare scratch_hash vs target_hash.\n" ++
  "  la t0, wlh_scratch_hash\n" ++
  "  mv t1, s2\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lwlh_no_match\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lwlh_no_match\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lwlh_no_match\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lwlh_no_match\n" ++
  "  # Match. Recompute (offset, length) from i (clobbered above).\n" ++
  "  slli t0, s6, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  sd t2, 0(s3)               # *out_offset = inner_off_i\n" ++
  "  addi t3, s6, 1\n" ++
  "  beq t3, s5, .Lwlh_last_len\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  sub t4, t4, t2             # length = inner_off_{i+1} - inner_off_i\n" ++
  "  j .Lwlh_store_len\n" ++
  ".Lwlh_last_len:\n" ++
  "  sub t4, s1, t2             # length = section_len - inner_off_i\n" ++
  ".Lwlh_store_len:\n" ++
  "  sd t4, 0(s4)\n" ++
  "  li a0, 0                   # hit\n" ++
  "  j .Lwlh_ret\n" ++
  ".Lwlh_no_match:\n" ++
  "  addi s6, s6, 1\n" ++
  "  j .Lwlh_loop\n" ++
  ".Lwlh_miss:\n" ++
  "  li a0, 1                   # miss\n" ++
  ".Lwlh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_witness_lookup_by_hash`: probe BuildUnit. Reads
    (section_len, target_hash, section_bytes) from host input,
    writes (status, offset, length) to OUTPUT.
    Input layout:
      bytes  0.. 8 : section_len (u64)
      bytes  8..40 : target_hash (32 bytes)
      bytes 40..   : SSZ list section bytes
    Output layout:
      bytes  0.. 8 : status (u64; 0 hit, 1 miss)
      bytes  8..16 : matched entry offset within section (u64)
      bytes 16..24 : matched entry length (u64) -/
def ziskWitnessLookupByHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # section_len\n" ++
  "  addi a2, a5, 16             # target_hash ptr\n" ++
  "  addi a0, a5, 48             # section ptr\n" ++
  "  li a3, 0xa0010008           # out_offset (OUTPUT + 8)\n" ++
  "  li a4, 0xa0010010           # out_length (OUTPUT + 16)\n" ++
  "  # Pre-zero offset/length so a miss surfaces as zeros.\n" ++
  "  sd zero, 0(a3)\n" ++
  "  sd zero, 0(a4)\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Lwlh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  ".Lwlh_pdone:"

def ziskWitnessLookupByHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32"

def ziskWitnessLookupByHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessLookupByHashPrologue
  dataAsm     := ziskWitnessLookupByHashDataSection
}

/-! ## mpt_nibbles_to_compact -- PR-K109

    Pack a nibble-list into the MPT compact (hex-prefix) encoding
    used in leaf and extension node first fields.

    Matches `nibble_list_to_compact(nibbles, is_leaf)` in
    `forks/amsterdam/trie.py`.

    The output's first byte has its high nibble structured as:

        +---+---+----------+--------+
        | _ | _ | is_leaf | parity |
        +---+---+----------+--------+
          3   2      1         0

    The low nibble of the prefix is either:
    - 0 when the input has even length
    - the first nibble of the input when odd length

    Remaining nibbles are then packed two-per-byte, high nibble
    first.

    Output length = `nibble_count / 2 + 1`, regardless of parity:
    - `nibble_count=0` → 1 byte (prefix only)
    - `nibble_count=1` → 1 byte (prefix carries the lone nibble)
    - `nibble_count=2` → 2 bytes
    - `nibble_count=3` → 2 bytes
    - …

    Calling convention:
      a0 (input)  : nibbles ptr (each byte 0..15)
      a1 (input)  : nibble count
      a2 (input)  : is_leaf flag (0 or 1)
      a3 (input)  : output bytes ptr (caller supplies space)
      a4 (input)  : u64 out ptr (writes output byte length)
      ra (input)  : return
      a0 (output) : 0 (always succeeds — total function).

    Pure-leaf semantics: no scratch memory, no transitive calls.
    Callers are responsible for ensuring each input byte is in
    `[0, 15]`; out-of-range bytes get truncated to their low
    nibble. -/
def mptNibblesToCompactFunction : String :=
  "mpt_nibbles_to_compact:\n" ++
  "  # parity = count & 1\n" ++
  "  andi t0, a1, 1\n" ++
  "  # high_nibble = (is_leaf << 1) | parity\n" ++
  "  slli t1, a2, 1\n" ++
  "  or t1, t1, t0\n" ++
  "  beqz t0, .Lmnc_even\n" ++
  "  # Odd: prefix = (high_nibble << 4) | nibbles[0]\n" ++
  "  lbu t3, 0(a0)\n" ++
  "  slli t2, t1, 4\n" ++
  "  andi t3, t3, 0xf\n" ++
  "  or t2, t2, t3\n" ++
  "  addi t4, a0, 1               # cursor at nibble[1]\n" ++
  "  addi t5, a1, -1              # remaining (even)\n" ++
  "  j .Lmnc_pack\n" ++
  ".Lmnc_even:\n" ++
  "  slli t2, t1, 4               # prefix byte (low nibble 0)\n" ++
  "  mv t4, a0\n" ++
  "  mv t5, a1\n" ++
  ".Lmnc_pack:\n" ++
  "  sb t2, 0(a3)\n" ++
  "  addi t6, a3, 1\n" ++
  ".Lmnc_loop:\n" ++
  "  beqz t5, .Lmnc_done\n" ++
  "  lbu t0, 0(t4)\n" ++
  "  lbu t1, 1(t4)\n" ++
  "  andi t0, t0, 0xf\n" ++
  "  andi t1, t1, 0xf\n" ++
  "  slli t0, t0, 4\n" ++
  "  or t0, t0, t1\n" ++
  "  sb t0, 0(t6)\n" ++
  "  addi t6, t6, 1\n" ++
  "  addi t4, t4, 2\n" ++
  "  addi t5, t5, -2\n" ++
  "  j .Lmnc_loop\n" ++
  ".Lmnc_done:\n" ++
  "  srli t0, a1, 1\n" ++
  "  addi t0, t0, 1\n" ++
  "  sd t0, 0(a4)\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_mpt_nibbles_to_compact`: probe BuildUnit. Reads
    (nibble_count, is_leaf, nibble_bytes) from host input, writes
    (status, output_len, compact_bytes...) to OUTPUT.
    Input layout:
      bytes  0.. 8 : nibble count
      bytes  8..16 : is_leaf flag (0/1)
      bytes 16..   : nibble bytes (one nibble per byte)
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : output_len
      bytes 16..   : compact-encoded bytes -/
def ziskMptNibblesToCompactPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # nibble count\n" ++
  "  ld a2, 16(a5)               # is_leaf\n" ++
  "  addi a0, a5, 24             # nibbles ptr\n" ++
  "  li a3, 0xa0010010           # output bytes\n" ++
  "  li a4, 0xa0010008           # output_len out\n" ++
  "  jal ra, mpt_nibbles_to_compact\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmnc_pdone\n" ++
  mptNibblesToCompactFunction ++ "\n" ++
  ".Lmnc_pdone:"

def ziskMptNibblesToCompactDataSection : String :=
  ".section .data\n" ++
  "mnc_scratch:\n" ++
  "  .zero 8"

def ziskMptNibblesToCompactProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptNibblesToCompactPrologue
  dataAsm     := ziskMptNibblesToCompactDataSection
}

/-! ## mpt_compact_to_nibbles -- PR-K110

    Decode the MPT compact (hex-prefix) encoding back to a nibble
    list and an `is_leaf` flag. The inverse of PR-K109
    `mpt_nibbles_to_compact`.

    Matches `compact_to_nibbles` in
    `forks/amsterdam/incremental_mpt.py`.

    The compact form's first byte high nibble structure:

        +---+---+----------+--------+
        | _ | _ | is_leaf | parity |
        +---+---+----------+--------+
          3   2      1         0

    Parity = 1 → first nibble of the path lives in the low nibble
    of the prefix byte; parity = 0 → prefix's low nibble is 0 and
    the path is fully packed in bytes 1..end.

    Output nibble count:
    - even-parity input of byte-length L → 2 × (L - 1) nibbles
    - odd-parity input of byte-length L → 2 × L - 1 nibbles

    Calling convention:
      a0 (input)  : compact bytes ptr
      a1 (input)  : compact byte length
      a2 (input)  : nibbles output ptr (≥ 2×L bytes of space)
      a3 (input)  : u64 out ptr (nibble count)
      a4 (input)  : u64 out ptr (is_leaf flag: 0 or 1)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty input (L = 0; no prefix byte to read)

    Pure-leaf semantics: no scratch memory, no transitive calls.
    Counter and flag outputs are zeroed on failure. -/
def mptCompactToNibblesFunction : String :=
  "mpt_compact_to_nibbles:\n" ++
  "  sd zero, 0(a3)              # default count = 0\n" ++
  "  sd zero, 0(a4)              # default is_leaf = 0\n" ++
  "  beqz a1, .Lmctn_fail\n" ++
  "  lbu t0, 0(a0)               # prefix byte\n" ++
  "  srli t1, t0, 4              # high nibble\n" ++
  "  andi t2, t1, 2              # is_leaf bit\n" ++
  "  srli t2, t2, 1\n" ++
  "  sd t2, 0(a4)\n" ++
  "  andi t3, t1, 1              # parity bit\n" ++
  "  mv t4, a2                   # nibbles cursor\n" ++
  "  li t5, 0                    # nibble count\n" ++
  "  beqz t3, .Lmctn_even\n" ++
  "  # Odd: first nibble = low nibble of prefix\n" ++
  "  andi t6, t0, 0xf\n" ++
  "  sb t6, 0(t4)\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t5, t5, 1\n" ++
  ".Lmctn_even:\n" ++
  "  addi t6, a0, 1              # cursor over packed bytes\n" ++
  "  addi t1, a1, -1             # remaining packed bytes\n" ++
  ".Lmctn_loop:\n" ++
  "  beqz t1, .Lmctn_done\n" ++
  "  lbu t0, 0(t6)\n" ++
  "  srli t2, t0, 4              # high nibble\n" ++
  "  andi t3, t0, 0xf            # low nibble\n" ++
  "  sb t2, 0(t4)\n" ++
  "  sb t3, 1(t4)\n" ++
  "  addi t4, t4, 2\n" ++
  "  addi t5, t5, 2\n" ++
  "  addi t6, t6, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lmctn_loop\n" ++
  ".Lmctn_done:\n" ++
  "  sd t5, 0(a3)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lmctn_fail:\n" ++
  "  li a0, 1\n" ++
  "  ret"

/-- `zisk_mpt_compact_to_nibbles`: probe BuildUnit. Reads
    (compact_len, compact_bytes) from host input, writes
    (status, nibble_count, is_leaf, nibbles...) to OUTPUT.
    Input layout:
      bytes  0.. 8 : compact byte length
      bytes  8..   : compact-encoded bytes
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : nibble count
      bytes 16..24 : is_leaf flag
      bytes 24..   : N nibble bytes -/
def ziskMptCompactToNibblesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # compact length\n" ++
  "  addi a0, a5, 16             # compact bytes\n" ++
  "  li a2, 0xa0010018           # nibbles output (OUTPUT + 0x18)\n" ++
  "  li a3, 0xa0010008           # nibble count out\n" ++
  "  li a4, 0xa0010010           # is_leaf out\n" ++
  "  jal ra, mpt_compact_to_nibbles\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmctn_pdone\n" ++
  mptCompactToNibblesFunction ++ "\n" ++
  ".Lmctn_pdone:"

def ziskMptCompactToNibblesDataSection : String :=
  ".section .data\n" ++
  "mctn_scratch:\n" ++
  "  .zero 8"

def ziskMptCompactToNibblesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptCompactToNibblesPrologue
  dataAsm     := ziskMptCompactToNibblesDataSection
}

/-! ## mpt_node_classify -- PR-K111

    Classify an MPT node from its RLP-encoded bytes.

    An MPT node is one of three shapes:
    - 17-item list → **branch** (16 children + value)
    - 2-item list with leaf-flagged compact path → **leaf**
    - 2-item list with extension-flagged compact path → **extension**

    PR-K23/K24 already walk MPT trees; this primitive lets callers
    introspect a single node's kind cheaply without a full decode,
    so dispatch tables (`branch_get_child` vs `leaf_decode` vs
    `extension_skip`) can pick the right path.

    Composes:
      - PR-K47 `rlp_list_count_items` — top-level item count
      - PR-K20 `rlp_list_nth_item`    — field 0 bounds (for 2-item)

    The MPT compact-encoded path's first byte high nibble carries
    `(is_leaf, parity)` flags (see PR-K109/K110): bit 1 → is_leaf.

    Calling convention:
      a0 (input)  : node_rlp ptr
      a1 (input)  : node_rlp byte length
      a2 (input)  : u64 out ptr (kind)
      ra (input)  : return
      a0 (output) :
        0 : success — kind in {0,1,2}
        1 : invalid (not a 2- or 17-item list, or path missing)

    Kind encoding:
      0 : branch (17 items)
      1 : extension (2 items, compact prefix indicates not-leaf)
      2 : leaf (2 items, compact prefix indicates leaf) -/
def mptNodeClassifyFunction : String :=
  "mpt_node_classify:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # node ptr\n" ++
  "  mv s1, a1                   # node len\n" ++
  "  mv s2, a2                   # kind out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # Count items.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, mnodc_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lmnodc_fail\n" ++
  "  la t0, mnodc_count; ld t1, 0(t0)\n" ++
  "  li t2, 17\n" ++
  "  beq t1, t2, .Lmnodc_branch\n" ++
  "  li t2, 2\n" ++
  "  bne t1, t2, .Lmnodc_fail\n" ++
  "  # 2-item: read first byte of compact-encoded path.\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0\n" ++
  "  la a3, mnodc_path_off; la a4, mnodc_path_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmnodc_fail\n" ++
  "  la t0, mnodc_path_len; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lmnodc_fail\n" ++
  "  la t0, mnodc_path_off; ld t2, 0(t0)\n" ++
  "  add t3, s0, t2\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  srli t5, t4, 5\n" ++
  "  andi t5, t5, 1\n" ++
  "  addi t5, t5, 1              # 1 = ext, 2 = leaf\n" ++
  "  sd t5, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmnodc_ret\n" ++
  ".Lmnodc_branch:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmnodc_ret\n" ++
  ".Lmnodc_fail:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 1\n" ++
  ".Lmnodc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_mpt_node_classify`: probe BuildUnit. Reads
    (node_len, node_bytes) from host input, writes (status, kind)
    to OUTPUT (16 bytes total). -/
def ziskMptNodeClassifyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # node_len\n" ++
  "  addi a0, a3, 16             # node ptr\n" ++
  "  li a2, 0xa0010008           # kind out\n" ++
  "  jal ra, mpt_node_classify\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmnodc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  mptNodeClassifyFunction ++ "\n" ++
  ".Lmnodc_pdone:"

def ziskMptNodeClassifyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mnodc_count:\n" ++
  "  .zero 8\n" ++
  "mnodc_path_off:\n" ++
  "  .zero 8\n" ++
  "mnodc_path_len:\n" ++
  "  .zero 8"

def ziskMptNodeClassifyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptNodeClassifyPrologue
  dataAsm     := ziskMptNodeClassifyDataSection
}

/-! ## mpt_encode_internal_node -- PR-K112

    Compute the canonical MPT "node reference" used by parent
    nodes to point at this node. Matches
    `encode_internal_node(node)` in `forks/amsterdam/trie.py`:

      encoded = rlp.encode(node)
      if len(encoded) < 32:
          return encoded            # embedded RLP (in-place ref)
      else:
          return keccak256(encoded) # 32-byte hash ref

    Callers pass in the already-RLP-encoded node bytes. The helper
    returns either the same bytes verbatim (when short enough to
    embed) or their keccak256 digest (when ≥ 32 bytes).

    Used by:
    - MPT walk when descending into a branch's child: the slot's
      stored bytes are this encoding, and the walker decides
      whether to dereference via the node DB hash table or to
      recurse on the embedded RLP directly.
    - MPT root recomputation, which propagates this encoding up
      the tree.

    Composes PR-K3 `zkvm_keccak256`. Uses 200 bytes of `.data`
    scratch (`zk3_state`, the keccak sponge state).

    Calling convention:
      a0 (input)  : node_rlp ptr
      a1 (input)  : node_rlp byte length
      a2 (input)  : output bytes ptr (caller supplies max(32, len) B)
      a3 (input)  : u64 out ptr (output length: 32 hashed, len embedded)
      a4 (input)  : u64 out ptr (is_hashed flag: 1 hashed, 0 embedded)
      ra (input)  : return
      a0 (output) : 0 (always succeeds — total function). -/
def mptEncodeInternalNodeFunction : String :=
  "mpt_encode_internal_node:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a2                   # out_bytes ptr\n" ++
  "  mv s1, a3                   # out_len ptr\n" ++
  "  mv s2, a4                   # is_hashed out\n" ++
  "  li t0, 32\n" ++
  "  bltu a1, t0, .Lmein_embed\n" ++
  "  # Hash path: keccak256(node_rlp, len) → out.\n" ++
  "  mv a2, s0\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li t0, 32\n" ++
  "  sd t0, 0(s1)\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmein_ret\n" ++
  ".Lmein_embed:\n" ++
  "  # Embedded path: copy node_rlp bytes to out_bytes.\n" ++
  "  mv t0, a0                   # src cursor\n" ++
  "  mv t1, s0                   # dst cursor\n" ++
  "  mv t2, a1                   # remaining\n" ++
  ".Lmein_copy:\n" ++
  "  beqz t2, .Lmein_copy_done\n" ++
  "  lbu t3, 0(t0)\n" ++
  "  sb t3, 0(t1)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Lmein_copy\n" ++
  ".Lmein_copy_done:\n" ++
  "  sd a1, 0(s1)\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 0\n" ++
  ".Lmein_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_mpt_encode_internal_node`: probe BuildUnit. Reads
    (node_len, node_bytes), writes (status, output_len, is_hashed,
    output_bytes...) to OUTPUT.
    Input layout:
      bytes  0.. 8 : node byte length
      bytes  8..   : node RLP bytes
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : output_len
      bytes 16..24 : is_hashed flag
      bytes 24..   : output bytes (32 if hashed, node_len if embedded) -/
def ziskMptEncodeInternalNodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # node length\n" ++
  "  addi a0, a5, 16             # node ptr\n" ++
  "  li a2, 0xa0010018           # output bytes\n" ++
  "  li a3, 0xa0010008           # output_len out\n" ++
  "  li a4, 0xa0010010           # is_hashed out\n" ++
  "  jal ra, mpt_encode_internal_node\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmein_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  mptEncodeInternalNodeFunction ++ "\n" ++
  ".Lmein_pdone:"

def ziskMptEncodeInternalNodeDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskMptEncodeInternalNodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptEncodeInternalNodePrologue
  dataAsm     := ziskMptEncodeInternalNodeDataSection
}

/-! ## mpt_branch_get_child -- PR-K115

    Extract the i-th child reference of an MPT branch node.

    A branch node is a 17-item RLP list: `[c0, c1, …, c15, value]`.
    Each child slot `ci` (i in 0..15) holds the i-th child's node
    reference — either a 32-byte keccak digest or an embedded RLP
    blob (see PR-K112 `encode_internal_node`). An empty child slot
    is encoded as the empty RLP string (length 0).

    Pairs with PR-K113 `mpt_leaf_extract` and PR-K114
    `mpt_extension_extract` to cover the three MPT node shapes
    (leaf / extension / branch). Used by the MPT walker
    (PR-K24 `mpt_walk`) every time it descends through a branch
    along the path's current nibble.

    Composes:
      - PR-K47 `rlp_list_count_items` — sanity-check 17 items
      - PR-K20 `rlp_list_nth_item`    — i-th field bounds

    Calling convention:
      a0 (input)  : branch_rlp ptr
      a1 (input)  : branch_rlp byte length
      a2 (input)  : nibble index (0..15)
      a3 (input)  : u64 out ptr (child_ptr — absolute)
      a4 (input)  : u64 out ptr (child_len)
      ra (input)  : return
      a0 (output) :
        0 : success — child slot extracted (may be empty / 32 B / embedded)
        1 : not a 17-item list (or RLP parse failure)
        2 : invalid index (> 15)
        3 : i-th field extraction failed (mid-list parse error)

    Uses two 8-byte `.data` scratch slots
    (`mbc_count`, `mbc_off` + `mbc_len`). -/
def mptBranchGetChildFunction : String :=
  "mpt_branch_get_child:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # branch ptr\n" ++
  "  mv s1, a1                   # branch len\n" ++
  "  mv s2, a2                   # index\n" ++
  "  mv s3, a3                   # child_ptr out\n" ++
  "  mv s4, a4                   # child_len out\n" ++
  "  sd zero, 0(s3); sd zero, 0(s4)\n" ++
  "  # Bounds-check index.\n" ++
  "  li t0, 16\n" ++
  "  bgeu s2, t0, .Lmbc_bad_idx\n" ++
  "  # Verify 17-item list.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, mbc_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lmbc_not_branch\n" ++
  "  la t0, mbc_count; ld t1, 0(t0)\n" ++
  "  li t2, 17\n" ++
  "  bne t1, t2, .Lmbc_not_branch\n" ++
  "  # Extract i-th field.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  mv a2, s2\n" ++
  "  la a3, mbc_off; la a4, mbc_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmbc_nth_fail\n" ++
  "  la t0, mbc_off; ld t1, 0(t0)\n" ++
  "  add t2, s0, t1\n" ++
  "  sd t2, 0(s3)\n" ++
  "  la t0, mbc_len; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmbc_ret\n" ++
  ".Lmbc_bad_idx:\n" ++
  "  li a0, 2\n" ++
  "  j .Lmbc_ret\n" ++
  ".Lmbc_not_branch:\n" ++
  "  li a0, 1\n" ++
  "  j .Lmbc_ret\n" ++
  ".Lmbc_nth_fail:\n" ++
  "  li a0, 3\n" ++
  ".Lmbc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_mpt_branch_get_child`: probe BuildUnit. Reads
    (branch_len, index, branch_bytes), writes
    (status, child_offset, child_len, child_bytes...) to OUTPUT.
    Probe converts the absolute `child_ptr` to a relative offset
    within `branch_rlp` so the test harness can rehydrate. -/
def ziskMptBranchGetChildPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # branch length\n" ++
  "  ld a2, 16(a5)               # index\n" ++
  "  addi a0, a5, 24             # branch ptr\n" ++
  "  li a3, 0xa0010008           # child_ptr (absolute) out\n" ++
  "  li a4, 0xa0010010           # child_len out\n" ++
  "  jal ra, mpt_branch_get_child\n" ++
  "  li t0, 0xa0010008\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beqz t1, .Lmbc_skip_rel\n" ++
  "  addi t2, a5, 24\n" ++
  "  sub t1, t1, t2\n" ++
  "  sd t1, 0(t0)\n" ++
  ".Lmbc_skip_rel:\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmbc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  mptBranchGetChildFunction ++ "\n" ++
  ".Lmbc_pdone:"

def ziskMptBranchGetChildDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mbc_count:\n" ++
  "  .zero 8\n" ++
  "mbc_off:\n" ++
  "  .zero 8\n" ++
  "mbc_len:\n" ++
  "  .zero 8"

def ziskMptBranchGetChildProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptBranchGetChildPrologue
  dataAsm     := ziskMptBranchGetChildDataSection
}

/-! ## mpt_branch_get_value -- PR-K116

    Extract the value field (item 16) of an MPT branch node.

    A branch node is a 17-item RLP list: `[c0, c1, …, c15, value]`.
    The trailing `value` slot holds the leaf payload when the
    walked key terminates exactly at this branch level (i.e., when
    the path's remaining nibble count equals zero on arrival). It
    is the empty RLP string when no key terminates at this branch.

    Sister to PR-K115 `mpt_branch_get_child` — same node, different
    field. Pairs cleanly with the leaf/extension/branch decode
    trio (K113/K114/K115) for full MPT walking.

    Composes:
      - PR-K47 `rlp_list_count_items` — sanity-check 17 items
      - PR-K20 `rlp_list_nth_item`    — field 16 bounds

    Calling convention:
      a0 (input)  : branch_rlp ptr
      a1 (input)  : branch_rlp byte length
      a2 (input)  : u64 out ptr (value_ptr — absolute)
      a3 (input)  : u64 out ptr (value_len)
      ra (input)  : return
      a0 (output) :
        0 : success — value slot extracted (may be empty)
        1 : not a 17-item list (or RLP parse failure)
        2 : field 16 extraction failed (parse error)

    Uses three 8-byte `.data` scratch slots
    (`mbv_count`, `mbv_off`, `mbv_len`). -/
def mptBranchGetValueFunction : String :=
  "mpt_branch_get_value:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # branch ptr\n" ++
  "  mv s1, a1                   # branch len\n" ++
  "  mv s2, a2                   # value_ptr out\n" ++
  "  mv s3, a3                   # value_len out\n" ++
  "  sd zero, 0(s2); sd zero, 0(s3)\n" ++
  "  # Verify 17-item list.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, mbv_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lmbv_not_branch\n" ++
  "  la t0, mbv_count; ld t1, 0(t0)\n" ++
  "  li t2, 17\n" ++
  "  bne t1, t2, .Lmbv_not_branch\n" ++
  "  # Extract field 16 (value).\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  li a2, 16\n" ++
  "  la a3, mbv_off; la a4, mbv_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmbv_nth_fail\n" ++
  "  la t0, mbv_off; ld t1, 0(t0)\n" ++
  "  add t2, s0, t1\n" ++
  "  sd t2, 0(s2)\n" ++
  "  la t0, mbv_len; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmbv_ret\n" ++
  ".Lmbv_not_branch:\n" ++
  "  li a0, 1\n" ++
  "  j .Lmbv_ret\n" ++
  ".Lmbv_nth_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lmbv_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_mpt_branch_get_value`: probe BuildUnit. Reads
    (branch_len, branch_bytes), writes (status, value_offset,
    value_len, value_bytes...) to OUTPUT. The probe rewrites the
    absolute `value_ptr` to a relative offset within `branch_rlp`. -/
def ziskMptBranchGetValuePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # branch length\n" ++
  "  addi a0, a4, 16             # branch ptr\n" ++
  "  li a2, 0xa0010008           # value_ptr (absolute) out\n" ++
  "  li a3, 0xa0010010           # value_len out\n" ++
  "  jal ra, mpt_branch_get_value\n" ++
  "  li t0, 0xa0010008\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beqz t1, .Lmbv_skip_rel\n" ++
  "  li t2, 0x40000010           # branch_rlp ptr (INPUT_ADDR + 16)\n" ++
  "  sub t1, t1, t2\n" ++
  "  sd t1, 0(t0)\n" ++
  ".Lmbv_skip_rel:\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmbv_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  mptBranchGetValueFunction ++ "\n" ++
  ".Lmbv_pdone:"

def ziskMptBranchGetValueDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mbv_count:\n" ++
  "  .zero 8\n" ++
  "mbv_off:\n" ++
  "  .zero 8\n" ++
  "mbv_len:\n" ++
  "  .zero 8"

def ziskMptBranchGetValueProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptBranchGetValuePrologue
  dataAsm     := ziskMptBranchGetValueDataSection
}

/-! ## mpt_leaf_extract -- PR-K113

    Fully decode an MPT leaf node RLP:

      node = [compact_path, value]

    into:
    - path nibbles (decompressed from compact form)
    - absolute pointer to the value bytes (inside `node_rlp`)
    - value byte length

    Rejects branch (17-item), extension (2-item with non-leaf
    prefix), and malformed RLP inputs.

    Composes:
      - PR-K20 `rlp_list_nth_item` — field extractor
      - PR-K110 (compact_to_nibbles, inlined here) — path decode

    Callers chain this with PR-K27 `account_decode` to walk the
    state trie's leaves into structured account fields, or with
    storage-slot decoders to read slot values straight out of
    leaves.

    Calling convention:
      a0 (input)  : node_rlp ptr
      a1 (input)  : node_rlp byte length
      a2 (input)  : 64-byte nibbles output ptr
      a3 (input)  : u64 out ptr (nibble count)
      a4 (input)  : u64 out ptr (value_ptr — absolute)
      a5 (input)  : u64 out ptr (value_len)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse / not 2-item list / missing path
        2 : compact prefix says extension, not leaf

    Uses two 8-byte `.data` scratch slots (`mle_path_off`,
    `mle_path_len`). -/
def mptLeafExtractFunction : String :=
  "mpt_leaf_extract:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # node ptr\n" ++
  "  mv s1, a1                   # node len\n" ++
  "  mv s2, a2                   # nibbles out\n" ++
  "  mv s3, a3                   # nibble_count out\n" ++
  "  mv s4, a4                   # value_ptr out\n" ++
  "  mv s5, a5                   # value_len out\n" ++
  "  sd zero, 0(s3); sd zero, 0(s4); sd zero, 0(s5)\n" ++
  "  # Field 0: compact path bytes.\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0\n" ++
  "  la a3, mle_path_off; la a4, mle_path_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmle_parse_fail\n" ++
  "  la t0, mle_path_len; ld t6, 0(t0)\n" ++
  "  beqz t6, .Lmle_parse_fail\n" ++
  "  la t0, mle_path_off; ld t5, 0(t0)\n" ++
  "  add s6, s0, t5\n" ++
  "  # Inline compact_to_nibbles: read prefix byte.\n" ++
  "  lbu t0, 0(s6)\n" ++
  "  srli t1, t0, 4\n" ++
  "  andi t2, t1, 2\n" ++
  "  beqz t2, .Lmle_not_leaf\n" ++
  "  andi t3, t1, 1\n" ++
  "  mv t4, s2\n" ++
  "  li t5, 0\n" ++
  "  beqz t3, .Lmle_path_even\n" ++
  "  andi t6, t0, 0xf\n" ++
  "  sb t6, 0(t4)\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t5, t5, 1\n" ++
  ".Lmle_path_even:\n" ++
  "  la t0, mle_path_len; ld t1, 0(t0)\n" ++
  "  addi t1, t1, -1\n" ++
  "  addi t6, s6, 1\n" ++
  ".Lmle_path_loop:\n" ++
  "  beqz t1, .Lmle_path_done\n" ++
  "  lbu t0, 0(t6)\n" ++
  "  srli t2, t0, 4\n" ++
  "  andi t3, t0, 0xf\n" ++
  "  sb t2, 0(t4)\n" ++
  "  sb t3, 1(t4)\n" ++
  "  addi t4, t4, 2\n" ++
  "  addi t5, t5, 2\n" ++
  "  addi t6, t6, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lmle_path_loop\n" ++
  ".Lmle_path_done:\n" ++
  "  sd t5, 0(s3)\n" ++
  "  # Field 1: value bytes.\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  la a3, mle_path_off; la a4, mle_path_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmle_parse_fail\n" ++
  "  la t0, mle_path_off; ld t1, 0(t0)\n" ++
  "  add t2, s0, t1\n" ++
  "  sd t2, 0(s4)\n" ++
  "  la t0, mle_path_len; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s5)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmle_ret\n" ++
  ".Lmle_not_leaf:\n" ++
  "  li a0, 2\n" ++
  "  j .Lmle_ret\n" ++
  ".Lmle_parse_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lmle_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_mpt_leaf_extract`: probe BuildUnit. Reads
    (node_len, node_bytes), writes (status, nibble_count,
    value_offset_in_node, value_len, nibbles...) to OUTPUT.
    The probe rewrites the returned absolute `value_ptr` to a
    relative offset within `node_rlp` so the test harness can
    rehydrate the value from the host `-i` file. -/
def ziskMptLeafExtractPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # node length\n" ++
  "  addi a0, a6, 16             # node ptr\n" ++
  "  li a2, 0xa0010020           # nibbles output\n" ++
  "  li a3, 0xa0010008           # nibble_count out\n" ++
  "  li a4, 0xa0010010           # value_ptr (absolute) out\n" ++
  "  li a5, 0xa0010018           # value_len out\n" ++
  "  jal ra, mpt_leaf_extract\n" ++
  "  # Convert absolute value_ptr to relative offset within node_rlp.\n" ++
  "  li t0, 0xa0010010\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beqz t1, .Lmle_skip_rel\n" ++
  "  addi t2, a6, 16\n" ++
  "  sub t1, t1, t2\n" ++
  "  sd t1, 0(t0)\n" ++
  ".Lmle_skip_rel:\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmle_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptLeafExtractFunction ++ "\n" ++
  ".Lmle_pdone:"

def ziskMptLeafExtractDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mle_path_off:\n" ++
  "  .zero 8\n" ++
  "mle_path_len:\n" ++
  "  .zero 8"

def ziskMptLeafExtractProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptLeafExtractPrologue
  dataAsm     := ziskMptLeafExtractDataSection
}

/-! ## mpt_extension_extract -- PR-K114

    Fully decode an MPT extension node RLP:

      node = [compact_path, child_ref]

    into:
    - path nibbles (decompressed from compact form)
    - absolute pointer to the child reference bytes (inside `node_rlp`)
    - child reference byte length

    The child reference is either a 32-byte keccak digest (when the
    referenced node's RLP encoding is ≥ 32 B) or an embedded RLP
    blob (when shorter); see PR-K112 `encode_internal_node`.

    Rejects leaf (2-item with leaf-flagged prefix), branch
    (17-item), and malformed RLP inputs.

    Sister to PR-K113 `mpt_leaf_extract`. Same shape and field
    layout; the only behavioural difference is the prefix-bit
    polarity (rejects when `is_leaf` is set rather than when
    cleared).

    Composes:
      - PR-K20 `rlp_list_nth_item`     — field extractor
      - PR-K110 `compact_to_nibbles` (inlined) — path decode

    Calling convention:
      a0 (input)  : node_rlp ptr
      a1 (input)  : node_rlp byte length
      a2 (input)  : 64-byte nibbles output ptr
      a3 (input)  : u64 out ptr (nibble count)
      a4 (input)  : u64 out ptr (child_ref_ptr — absolute)
      a5 (input)  : u64 out ptr (child_ref_len)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse / not 2-item list / missing path
        2 : compact prefix says leaf, not extension

    Uses two 8-byte `.data` scratch slots (`mee_path_off`,
    `mee_path_len`). -/
def mptExtensionExtractFunction : String :=
  "mpt_extension_extract:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # node ptr\n" ++
  "  mv s1, a1                   # node len\n" ++
  "  mv s2, a2                   # nibbles out\n" ++
  "  mv s3, a3                   # nibble_count out\n" ++
  "  mv s4, a4                   # child_ref_ptr out\n" ++
  "  mv s5, a5                   # child_ref_len out\n" ++
  "  sd zero, 0(s3); sd zero, 0(s4); sd zero, 0(s5)\n" ++
  "  # Field 0: compact path bytes.\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0\n" ++
  "  la a3, mee_path_off; la a4, mee_path_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmee_parse_fail\n" ++
  "  la t0, mee_path_len; ld t6, 0(t0)\n" ++
  "  beqz t6, .Lmee_parse_fail\n" ++
  "  la t0, mee_path_off; ld t5, 0(t0)\n" ++
  "  add s6, s0, t5\n" ++
  "  # Read prefix; reject if is_leaf bit set.\n" ++
  "  lbu t0, 0(s6)\n" ++
  "  srli t1, t0, 4\n" ++
  "  andi t2, t1, 2\n" ++
  "  bnez t2, .Lmee_not_extension\n" ++
  "  andi t3, t1, 1\n" ++
  "  mv t4, s2\n" ++
  "  li t5, 0\n" ++
  "  beqz t3, .Lmee_path_even\n" ++
  "  andi t6, t0, 0xf\n" ++
  "  sb t6, 0(t4)\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t5, t5, 1\n" ++
  ".Lmee_path_even:\n" ++
  "  la t0, mee_path_len; ld t1, 0(t0)\n" ++
  "  addi t1, t1, -1\n" ++
  "  addi t6, s6, 1\n" ++
  ".Lmee_path_loop:\n" ++
  "  beqz t1, .Lmee_path_done\n" ++
  "  lbu t0, 0(t6)\n" ++
  "  srli t2, t0, 4\n" ++
  "  andi t3, t0, 0xf\n" ++
  "  sb t2, 0(t4)\n" ++
  "  sb t3, 1(t4)\n" ++
  "  addi t4, t4, 2\n" ++
  "  addi t5, t5, 2\n" ++
  "  addi t6, t6, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lmee_path_loop\n" ++
  ".Lmee_path_done:\n" ++
  "  sd t5, 0(s3)\n" ++
  "  # Field 1: child_ref bytes.\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  la a3, mee_path_off; la a4, mee_path_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmee_parse_fail\n" ++
  "  la t0, mee_path_off; ld t1, 0(t0)\n" ++
  "  add t2, s0, t1\n" ++
  "  sd t2, 0(s4)\n" ++
  "  la t0, mee_path_len; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s5)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmee_ret\n" ++
  ".Lmee_not_extension:\n" ++
  "  li a0, 2\n" ++
  "  j .Lmee_ret\n" ++
  ".Lmee_parse_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lmee_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_mpt_extension_extract`: probe BuildUnit. Reads
    (node_len, node_bytes), writes (status, nibble_count,
    child_ref_offset_in_node, child_ref_len, nibbles...) to OUTPUT.
    The probe rewrites the absolute `child_ref_ptr` to a relative
    offset within `node_rlp` so the test harness can rehydrate the
    bytes from the host `-i` file. -/
def ziskMptExtensionExtractPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # node length\n" ++
  "  addi a0, a6, 16             # node ptr\n" ++
  "  li a2, 0xa0010020           # nibbles output\n" ++
  "  li a3, 0xa0010008           # nibble_count out\n" ++
  "  li a4, 0xa0010010           # child_ref_ptr (absolute) out\n" ++
  "  li a5, 0xa0010018           # child_ref_len out\n" ++
  "  jal ra, mpt_extension_extract\n" ++
  "  li t0, 0xa0010010\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beqz t1, .Lmee_skip_rel\n" ++
  "  addi t2, a6, 16\n" ++
  "  sub t1, t1, t2\n" ++
  "  sd t1, 0(t0)\n" ++
  ".Lmee_skip_rel:\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmee_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptExtensionExtractFunction ++ "\n" ++
  ".Lmee_pdone:"

def ziskMptExtensionExtractDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mee_path_off:\n" ++
  "  .zero 8\n" ++
  "mee_path_len:\n" ++
  "  .zero 8"

def ziskMptExtensionExtractProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptExtensionExtractPrologue
  dataAsm     := ziskMptExtensionExtractDataSection
}


/-! ## mpt_account_path_nibbles -- PR-K100

    Compute the state trie's path for a given 20-byte address:

      digest   = keccak256(address)         # 32 bytes
      nibbles  = unpack_high_low(digest)    # 64 nibbles

    The MPT walks paths in nibble units (each byte = two
    consecutive nibbles, high first). Account lookups in the state
    trie use `keccak256(address)` as the path key, expressed as 64
    nibbles. PR-K24 `mpt_walk` consumes such a nibble array; this
    helper produces it from an address in one call.

    Storage slots use the analogous `keccak256(slot_key_BE)` path;
    K100 also handles that case directly when callers feed in a
    32-byte slot key (see calling convention).

    Composes PR-K3 `zkvm_keccak256`. Uses 32 bytes of `.data`
    scratch (`mapn_digest`).

    Calling convention:
      a0 (input)  : address (or slot key) ptr
      a1 (input)  : input length (20 for address, 32 for slot key)
      a2 (input)  : 64-byte nibble output ptr
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def mptAccountPathNibblesFunction : String :=
  "mpt_account_path_nibbles:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  mv s0, a2                   # nibble output ptr (stash)\n" ++
  "  # keccak256(input, len) → mapn_digest\n" ++
  "  la a2, mapn_digest\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # Unpack 32 bytes → 64 nibbles.\n" ++
  "  la t0, mapn_digest\n" ++
  "  mv t1, s0                   # cursor over output\n" ++
  "  li t2, 32                   # remaining bytes\n" ++
  ".Lmapn_loop:\n" ++
  "  beqz t2, .Lmapn_done\n" ++
  "  lbu t3, 0(t0)\n" ++
  "  srli t4, t3, 4              # high nibble\n" ++
  "  andi t5, t3, 15             # low nibble\n" ++
  "  sb t4, 0(t1)\n" ++
  "  sb t5, 1(t1)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 2\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Lmapn_loop\n" ++
  ".Lmapn_done:\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_mpt_account_path_nibbles`: probe BuildUnit. Reads
    (input_len, input_bytes) from host input, writes (status, 64
    nibbles) to OUTPUT (72 bytes total). -/
def ziskMptAccountPathNibblesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # input length\n" ++
  "  addi a0, a3, 16             # input ptr\n" ++
  "  li a2, 0xa0010008           # 64-byte nibble output\n" ++
  "  jal ra, mpt_account_path_nibbles\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmapn_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  mptAccountPathNibblesFunction ++ "\n" ++
  ".Lmapn_pdone:"

def ziskMptAccountPathNibblesDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "mapn_digest:\n" ++
  "  .zero 32"

def ziskMptAccountPathNibblesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptAccountPathNibblesPrologue
  dataAsm     := ziskMptAccountPathNibblesDataSection
}

/-! ## mpt_node_kind -- PR-K21 classifier

    Determines whether an RLP-encoded MPT node is a leaf,
    extension, or branch by:
      1. Probing whether item 2 exists (presence = 17-item
         branch list).
      2. If absent, reading item 0's first byte and inspecting
         the high nibble (HP encoding flag: 0/1 → extension,
         2/3 → leaf).

    Calling convention:
      a0 (input)  : node bytes ptr
      a1 (input)  : node byte length
      ra (input)  : return
      a0 (output) : 0 branch / 1 extension / 2 leaf / 3 parse fail

    Calls `rlp_list_nth_item` twice. Uses four 8-byte `.data`
    scratches (`mnk_dummy_offset`, `mnk_dummy_length`,
    `mnk_path_offset`, `mnk_path_length`) for the temporary
    returns. -/
def mptNodeKindFunction : String :=
  "mpt_node_kind:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0                  # node ptr\n" ++
  "  mv s1, a1                  # node_len\n" ++
  "  # Probe item 2 (index 2). If found ⇒ 17-item branch list.\n" ++
  "  li a2, 2\n" ++
  "  la a3, mnk_dummy_offset\n" ++
  "  la a4, mnk_dummy_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  beqz a0, .Lmnk_branch\n" ++
  "  # Item 2 absent ⇒ 2-item list (leaf or extension).\n" ++
  "  # Get item 0 to read path's first byte.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  li a2, 0\n" ++
  "  la a3, mnk_path_offset\n" ++
  "  la a4, mnk_path_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmnk_fail        # item 0 missing ⇒ parse fail\n" ++
  "  la t0, mnk_path_offset\n" ++
  "  ld t1, 0(t0)               # path content offset\n" ++
  "  la t0, mnk_path_length\n" ++
  "  ld t2, 0(t0)               # path content length\n" ++
  "  beqz t2, .Lmnk_fail        # empty path ⇒ malformed HP\n" ++
  "  add t3, s0, t1             # path byte ptr\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  srli t4, t4, 4             # high nibble\n" ++
  "  li t5, 2\n" ++
  "  bltu t4, t5, .Lmnk_extension  # 0,1 → extension\n" ++
  "  li t5, 4\n" ++
  "  bltu t4, t5, .Lmnk_leaf       # 2,3 → leaf\n" ++
  "  j .Lmnk_fail                   # ≥ 4 → invalid HP\n" ++
  ".Lmnk_branch:\n" ++
  "  li a0, 0\n" ++
  "  j .Lmnk_ret\n" ++
  ".Lmnk_extension:\n" ++
  "  li a0, 1\n" ++
  "  j .Lmnk_ret\n" ++
  ".Lmnk_leaf:\n" ++
  "  li a0, 2\n" ++
  "  j .Lmnk_ret\n" ++
  ".Lmnk_fail:\n" ++
  "  li a0, 3\n" ++
  ".Lmnk_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_mpt_node_kind`: probe BuildUnit. Reads
    (node_len, node_bytes) from host input, writes
    classification result to OUTPUT.
    Input layout:
      bytes  0.. 8 : node_len (u64)
      bytes  8..   : node bytes
    Output layout:
      bytes  0.. 8 : kind (u64; 0 branch / 1 ext / 2 leaf / 3 fail) -/
def ziskMptNodeKindPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # node_len\n" ++
  "  addi a0, a3, 16             # node ptr\n" ++
  "  jal ra, mpt_node_kind\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # write kind\n" ++
  "  j .Lmnk_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  ".Lmnk_pdone:"

def ziskMptNodeKindDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8"

def ziskMptNodeKindProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptNodeKindPrologue
  dataAsm     := ziskMptNodeKindDataSection
}

/-! ## mpt_branch_child -- PR-K22 extract i-th child of a branch

    Wraps `rlp_list_nth_item` with a branch-shape-aware
    interpretation of the returned content. Ethereum MPT branch
    nodes have items 0..15 each being one of:

      * 32-byte hash       (Bytes32: 0xa0 + 32 raw bytes)
      * empty bytes        (RLP 0x80)
      * inlined RLP node   (variable bytes, < 32 bytes total)

    Calling convention:
      a0 (input)  : branch node bytes ptr
      a1 (input)  : node byte length
      a2 (input)  : nibble (0..15)
      a3 (input)  : 32-byte output buffer ptr
      ra (input)  : return
      a0 (output) :
        0 = hash slot (32 bytes copied to *a3)
        1 = empty slot (output buffer zeroed)
        2 = inlined RLP node (output buffer holds first ≤ 32
            bytes of the inlined form, zero-padded)
        3 = parse failure (nibble out of range or node
            malformed)

    Does NOT verify the caller has actually given a branch
    node; if applied to a 2-item leaf/extension, items 0 and 1
    are returned according to the same length-driven rules but
    the semantics aren't branch-children. -/
def mptBranchChildFunction : String :=
  "mpt_branch_child:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                  # node ptr\n" ++
  "  mv s1, a1                  # node_len\n" ++
  "  mv s2, a2                  # nibble\n" ++
  "  mv s3, a3                  # out ptr\n" ++
  "  li t0, 16\n" ++
  "  bgeu s2, t0, .Lmbc_fail    # nibble ≥ 16 → out of range\n" ++
  "  # Call rlp_list_nth_item(node, len, nibble, &mbc_offset, &mbc_length).\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2\n" ++
  "  la a3, mbc_offset\n" ++
  "  la a4, mbc_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmbc_fail\n" ++
  "  la t0, mbc_length\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beqz t1, .Lmbc_empty       # length 0 ⇒ empty slot\n" ++
  "  li t0, 32\n" ++
  "  bne t1, t0, .Lmbc_inlined  # length != 32 ⇒ inlined\n" ++
  "  # Hash slot: copy 32 bytes from node + offset to out.\n" ++
  "  la t0, mbc_offset\n" ++
  "  ld t2, 0(t0)\n" ++
  "  add t2, s0, t2             # src\n" ++
  "  ld t3,  0(t2); sd t3,  0(s3)\n" ++
  "  ld t3,  8(t2); sd t3,  8(s3)\n" ++
  "  ld t3, 16(t2); sd t3, 16(s3)\n" ++
  "  ld t3, 24(t2); sd t3, 24(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmbc_ret\n" ++
  ".Lmbc_empty:\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3)\n" ++
  "  sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  li a0, 1\n" ++
  "  j .Lmbc_ret\n" ++
  ".Lmbc_inlined:\n" ++
  "  # Length 1..31. Zero the output, then byte-copy `length` bytes.\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3)\n" ++
  "  sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  la t0, mbc_offset\n" ++
  "  ld t2, 0(t0)\n" ++
  "  add t2, s0, t2             # src cursor\n" ++
  "  mv t3, s3                  # dst cursor\n" ++
  ".Lmbc_inline_cp:\n" ++
  "  beqz t1, .Lmbc_inline_done\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  sb  t4, 0(t3)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lmbc_inline_cp\n" ++
  ".Lmbc_inline_done:\n" ++
  "  li a0, 2\n" ++
  "  j .Lmbc_ret\n" ++
  ".Lmbc_fail:\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3)\n" ++
  "  sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  li a0, 3\n" ++
  ".Lmbc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_mpt_branch_child`: probe BuildUnit. Reads
    (node_len, nibble, node_bytes) from host input, writes
    (status, 32-byte content) to OUTPUT.
    Input layout:
      bytes  0.. 8 : node_len (u64)
      bytes  8..16 : nibble (u64)
      bytes 16..   : node bytes
    Output layout:
      bytes  0.. 8 : status (0 hash / 1 empty / 2 inlined / 3 fail)
      bytes  8..40 : 32-byte content (hash, zeros, or inlined bytes) -/
def ziskMptBranchChildPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # node_len\n" ++
  "  ld a2, 16(a4)               # nibble\n" ++
  "  addi a0, a4, 24             # node ptr\n" ++
  "  li a3, 0xa0010008           # 32-byte out at OUTPUT + 8\n" ++
  "  jal ra, mpt_branch_child\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lmbc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  ".Lmbc_pdone:"

def ziskMptBranchChildDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mbc_offset:\n" ++
  "  .zero 8\n" ++
  "mbc_length:\n" ++
  "  .zero 8"

def ziskMptBranchChildProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptBranchChildPrologue
  dataAsm     := ziskMptBranchChildDataSection
}

/-! ## hp_decode_nibbles -- PR-K23 HP-encoded path → nibble array

    Decode the HP-encoded first item of a leaf/extension MPT
    node into an array of one-nibble bytes (each ∈ [0..15]).
    Also returns whether the node is a leaf or extension.

    HP encoding cheat-sheet (input byte 0):
      high nibble  meaning
      ----------   -------
         0         extension, even path length (low nibble must be 0)
         1         extension, odd path length (low nibble is first path nibble)
         2         leaf, even path length (low nibble must be 0)
         3         leaf, odd path length (low nibble is first path nibble)
      anything else → invalid

    Remaining input bytes hold 2 nibbles each (high, then low),
    contributing to the output starting at the next slot.

    Calling convention:
      a0 (input)  : HP-encoded path bytes ptr
      a1 (input)  : path byte length
      a2 (input)  : output nibble buffer (caller-allocated;
                    holds up to 2 * (a1 - 1) + 1 bytes,
                    one byte per nibble)
      a3 (input)  : u64 out ptr (number of nibbles emitted)
      a4 (input)  : u64 out ptr (is_leaf flag: 0 = ext, 1 = leaf)
      ra (input)  : return
      a0 (output) : 0 success, 1 parse failure (empty input,
                    high nibble ≥ 4, or even path with non-zero
                    low nibble of byte 0).

    Each output byte holds one nibble in its low 4 bits; the
    high 4 bits are zero. This is the format consumed by future
    `mpt_walk` (PR-K24) which compares one byte per nibble. -/
def hpDecodeNibblesFunction : String :=
  "hp_decode_nibbles:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                  # path_bytes ptr\n" ++
  "  mv s1, a1                  # len\n" ++
  "  mv s2, a2                  # out nibble buf\n" ++
  "  mv s3, a3                  # out count ptr\n" ++
  "  mv s4, a4                  # out is_leaf ptr\n" ++
  "  beqz s1, .Lhp_fail\n" ++
  "  lbu t0, 0(s0)              # b0\n" ++
  "  srli t1, t0, 4             # high nibble\n" ++
  "  andi t2, t0, 0xf           # low nibble\n" ++
  "  li t3, 4\n" ++
  "  bgeu t1, t3, .Lhp_fail     # high ≥ 4 → invalid\n" ++
  "  # is_leaf = (high & 2) >> 1\n" ++
  "  andi t3, t1, 2\n" ++
  "  srli t3, t3, 1\n" ++
  "  sd t3, 0(s4)\n" ++
  "  # is_odd = high & 1\n" ++
  "  andi t1, t1, 1\n" ++
  "  beqz t1, .Lhp_even\n" ++
  "  # Odd: write low as first output nibble.\n" ++
  "  sb t2, 0(s2)\n" ++
  "  li t5, 1                   # nibble count so far\n" ++
  "  addi t6, s2, 1             # output cursor\n" ++
  "  j .Lhp_loop_init\n" ++
  ".Lhp_even:\n" ++
  "  bnez t2, .Lhp_fail         # even but low nibble != 0\n" ++
  "  li t5, 0\n" ++
  "  mv t6, s2\n" ++
  ".Lhp_loop_init:\n" ++
  "  li t0, 1                   # i = 1\n" ++
  ".Lhp_loop:\n" ++
  "  bgeu t0, s1, .Lhp_done\n" ++
  "  add t1, s0, t0\n" ++
  "  lbu t2, 0(t1)\n" ++
  "  srli t3, t2, 4\n" ++
  "  andi t4, t2, 0xf\n" ++
  "  sb t3, 0(t6)\n" ++
  "  sb t4, 1(t6)\n" ++
  "  addi t6, t6, 2\n" ++
  "  addi t5, t5, 2\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lhp_loop\n" ++
  ".Lhp_done:\n" ++
  "  sd t5, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhp_ret\n" ++
  ".Lhp_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lhp_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_hp_decode_nibbles`: probe BuildUnit. Reads
    (path_len, path_bytes) from host input, writes
    (status, count, is_leaf, nibbles...) to OUTPUT.
    Input layout:
      bytes  0.. 8 : path_len (u64)
      bytes  8..   : HP-encoded path bytes
    Output layout:
      bytes  0.. 8 : status (u64; 0 ok, 1 fail)
      bytes  8..16 : nibble count (u64)
      bytes 16..24 : is_leaf (u64)
      bytes 24..   : nibble bytes (count bytes; each in [0..15]) -/
def ziskHpDecodeNibblesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # path_len\n" ++
  "  addi a0, a4, 16             # path bytes ptr\n" ++
  "  li a2, 0xa0010018           # nibble buf at OUTPUT + 24\n" ++
  "  li a3, 0xa0010008           # count ptr at OUTPUT + 8\n" ++
  "  li a4, 0xa0010010           # is_leaf ptr at OUTPUT + 16\n" ++
  "  jal ra, hp_decode_nibbles\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Lhp_pdone\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  ".Lhp_pdone:"

def ziskHpDecodeNibblesDataSection : String :=
  ".section .data\n" ++
  "hp_pad:\n" ++
  "  .zero 8"

def ziskHpDecodeNibblesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHpDecodeNibblesPrologue
  dataAsm     := ziskHpDecodeNibblesDataSection
}

/-! ## mpt_walk -- PR-K24 end-to-end MPT lookup

    Compose every K-stack primitive into a single
    `mpt_walk(root, witness, path) → value` entry. Walks the
    branch / extension / leaf chain following nibble path
    elements.

    Calling convention:
      a0 (input)  : root_hash ptr (32 bytes)
      a1 (input)  : witness.state SSZ list section ptr
      a2 (input)  : witness section_len
      a3 (input)  : path_nibbles ptr (one byte per nibble)
      a4 (input)  : path_nibbles_len
      a5 (input)  : value output buffer ptr (256 bytes)
      a6 (input)  : u64 out ptr (matched value byte length)
      ra (input)  : return
      a0 (output) : 0 (found) / 1 (not found) / 2 (parse error)

    Calls itself transitively via PR-K19..K23 primitives.
    Uses a 256-byte mw_value_buf for the output and ~200 B of
    additional scratch state. -/
def mptWalkFunction : String :=
  "mpt_walk:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a1                   # s0 = witness ptr\n" ++
  "  mv s1, a2                   # s1 = witness_len\n" ++
  "  mv s2, a3                   # s2 = path_nibbles ptr\n" ++
  "  mv s3, a4                   # s3 = path_nibbles_len\n" ++
  "  mv s4, a5                   # s4 = value out buf\n" ++
  "  mv s5, a6                   # s5 = value_len out ptr\n" ++
  "  # Copy root_hash to mw_lookup_hash for the first lookup.\n" ++
  "  la t0, mw_lookup_hash\n" ++
  "  ld t1,  0(a0); sd t1,  0(t0)\n" ++
  "  ld t1,  8(a0); sd t1,  8(t0)\n" ++
  "  ld t1, 16(a0); sd t1, 16(t0)\n" ++
  "  ld t1, 24(a0); sd t1, 24(t0)\n" ++
  "  # First lookup of root_hash in witness.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, mw_lookup_hash\n" ++
  "  la a3, mw_lookup_offset\n" ++
  "  la a4, mw_lookup_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lmw_not_found\n" ++
  "  # s7 = current node ptr; s8 = current node len; s6 = consumed nibbles.\n" ++
  "  la t0, mw_lookup_offset; ld t1, 0(t0); add s7, s0, t1\n" ++
  "  la t0, mw_lookup_length; ld s8, 0(t0)\n" ++
  "  li s6, 0\n" ++
  ".Lmw_loop:\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  jal ra, mpt_node_kind\n" ++
  "  beqz a0, .Lmw_branch\n" ++
  "  li t0, 1; beq a0, t0, .Lmw_extension\n" ++
  "  li t0, 2; beq a0, t0, .Lmw_leaf\n" ++
  "  j .Lmw_parse_fail\n" ++
  ".Lmw_branch:\n" ++
  "  beq s6, s3, .Lmw_branch_end\n" ++
  "  # Get child slot via rlp_list_nth_item (bypass mpt_branch_child so we\n" ++
  "  # can keep the actual inlined byte count, not zero-padded to 32).\n" ++
  "  add t0, s2, s6              # &path[consumed]\n" ++
  "  lbu t1, 0(t0)\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  mv a2, t1                   # nibble (item index)\n" ++
  "  la a3, mw_child_offset\n" ++
  "  la a4, mw_child_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  addi s6, s6, 1\n" ++
  "  bnez a0, .Lmw_parse_fail\n" ++
  "  la t0, mw_child_length; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lmw_not_found      # empty slot\n" ++
  "  li t2, 32\n" ++
  "  beq t1, t2, .Lmw_branch_hash\n" ++
  "  # Inlined (length 1..31): set node to (s7 + child_offset, child_length).\n" ++
  "  la t0, mw_child_offset; ld t2, 0(t0)\n" ++
  "  add s7, s7, t2\n" ++
  "  mv s8, t1\n" ++
  "  j .Lmw_loop\n" ++
  ".Lmw_branch_hash:\n" ++
  "  # 32-byte hash: copy to mw_lookup_hash then lookup.\n" ++
  "  la t0, mw_child_offset; ld t1, 0(t0)\n" ++
  "  add t2, s7, t1\n" ++
  "  la t3, mw_lookup_hash\n" ++
  "  ld t4,  0(t2); sd t4,  0(t3)\n" ++
  "  ld t4,  8(t2); sd t4,  8(t3)\n" ++
  "  ld t4, 16(t2); sd t4, 16(t3)\n" ++
  "  ld t4, 24(t2); sd t4, 24(t3)\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, mw_lookup_hash\n" ++
  "  la a3, mw_lookup_offset\n" ++
  "  la a4, mw_lookup_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lmw_not_found\n" ++
  "  la t0, mw_lookup_offset; ld t1, 0(t0); add s7, s0, t1\n" ++
  "  la t0, mw_lookup_length; ld s8, 0(t0)\n" ++
  "  j .Lmw_loop\n" ++
  ".Lmw_branch_end:\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  li a2, 16\n" ++
  "  la a3, mw_value_offset\n" ++
  "  la a4, mw_value_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmw_parse_fail\n" ++
  "  la t0, mw_value_length; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lmw_not_found     # empty value slot\n" ++
  "  j .Lmw_copy_value\n" ++
  ".Lmw_extension:\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  li a2, 0\n" ++
  "  la a3, mw_path_offset\n" ++
  "  la a4, mw_path_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmw_parse_fail\n" ++
  "  la t0, mw_path_offset; ld t1, 0(t0); add a0, s7, t1\n" ++
  "  la t0, mw_path_length; ld a1, 0(t0)\n" ++
  "  la a2, mw_nibble_buf\n" ++
  "  la a3, mw_nibble_count\n" ++
  "  la a4, mw_is_leaf\n" ++
  "  jal ra, hp_decode_nibbles\n" ++
  "  bnez a0, .Lmw_parse_fail\n" ++
  "  la t0, mw_is_leaf; ld t1, 0(t0)\n" ++
  "  bnez t1, .Lmw_parse_fail    # node kind said extension; HP says leaf\n" ++
  "  la t0, mw_nibble_count; ld t1, 0(t0)\n" ++
  "  add t2, s6, t1\n" ++
  "  bgtu t2, s3, .Lmw_not_found # consumed + nib_count > path_len\n" ++
  "  # Compare nibbles\n" ++
  "  la t2, mw_nibble_buf\n" ++
  "  add t3, s2, s6\n" ++
  "  mv t4, t1\n" ++
  ".Lmw_ext_cmp:\n" ++
  "  beqz t4, .Lmw_ext_cmp_done\n" ++
  "  lbu t5, 0(t2)\n" ++
  "  lbu t6, 0(t3)\n" ++
  "  bne t5, t6, .Lmw_not_found\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lmw_ext_cmp\n" ++
  ".Lmw_ext_cmp_done:\n" ++
  "  add s6, s6, t1\n" ++
  "  # Get item 1 (child ref).\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  li a2, 1\n" ++
  "  la a3, mw_child_offset\n" ++
  "  la a4, mw_child_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmw_parse_fail\n" ++
  "  la t0, mw_child_length; ld t1, 0(t0)\n" ++
  "  la t0, mw_child_offset; ld t2, 0(t0)\n" ++
  "  add t3, s7, t2\n" ++
  "  li t4, 32\n" ++
  "  beq t1, t4, .Lmw_ext_hash\n" ++
  "  # Inline child: t3 is its ptr, t1 is its length.\n" ++
  "  mv s7, t3\n" ++
  "  mv s8, t1\n" ++
  "  j .Lmw_loop\n" ++
  ".Lmw_ext_hash:\n" ++
  "  la t4, mw_lookup_hash\n" ++
  "  ld t5,  0(t3); sd t5,  0(t4)\n" ++
  "  ld t5,  8(t3); sd t5,  8(t4)\n" ++
  "  ld t5, 16(t3); sd t5, 16(t4)\n" ++
  "  ld t5, 24(t3); sd t5, 24(t4)\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, mw_lookup_hash\n" ++
  "  la a3, mw_lookup_offset\n" ++
  "  la a4, mw_lookup_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lmw_not_found\n" ++
  "  la t0, mw_lookup_offset; ld t1, 0(t0); add s7, s0, t1\n" ++
  "  la t0, mw_lookup_length; ld s8, 0(t0)\n" ++
  "  j .Lmw_loop\n" ++
  ".Lmw_leaf:\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  li a2, 0\n" ++
  "  la a3, mw_path_offset\n" ++
  "  la a4, mw_path_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmw_parse_fail\n" ++
  "  la t0, mw_path_offset; ld t1, 0(t0); add a0, s7, t1\n" ++
  "  la t0, mw_path_length; ld a1, 0(t0)\n" ++
  "  la a2, mw_nibble_buf\n" ++
  "  la a3, mw_nibble_count\n" ++
  "  la a4, mw_is_leaf\n" ++
  "  jal ra, hp_decode_nibbles\n" ++
  "  bnez a0, .Lmw_parse_fail\n" ++
  "  la t0, mw_is_leaf; ld t1, 0(t0)\n" ++
  "  li t2, 1\n" ++
  "  bne t1, t2, .Lmw_parse_fail\n" ++
  "  la t0, mw_nibble_count; ld t1, 0(t0)\n" ++
  "  sub t2, s3, s6              # remaining nibbles\n" ++
  "  bne t1, t2, .Lmw_not_found  # length mismatch\n" ++
  "  la t2, mw_nibble_buf\n" ++
  "  add t3, s2, s6\n" ++
  "  mv t4, t1\n" ++
  ".Lmw_leaf_cmp:\n" ++
  "  beqz t4, .Lmw_leaf_match\n" ++
  "  lbu t5, 0(t2)\n" ++
  "  lbu t6, 0(t3)\n" ++
  "  bne t5, t6, .Lmw_not_found\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lmw_leaf_cmp\n" ++
  ".Lmw_leaf_match:\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  li a2, 1\n" ++
  "  la a3, mw_value_offset\n" ++
  "  la a4, mw_value_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmw_parse_fail\n" ++
  ".Lmw_copy_value:\n" ++
  "  # Write value_len, then byte-copy at most 256 bytes from\n" ++
  "  # (s7 + mw_value_offset) to s4.\n" ++
  "  la t0, mw_value_length; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s5)\n" ++
  "  la t0, mw_value_offset; ld t2, 0(t0); add t2, s7, t2\n" ++
  "  mv t3, s4                   # dst\n" ++
  "  li t4, 256\n" ++
  "  bgtu t1, t4, .Lmw_copy_set_cap\n" ++
  "  j .Lmw_copy_loop\n" ++
  ".Lmw_copy_set_cap:\n" ++
  "  mv t1, t4\n" ++
  ".Lmw_copy_loop:\n" ++
  "  beqz t1, .Lmw_found\n" ++
  "  lbu t0, 0(t2)\n" ++
  "  sb  t0, 0(t3)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lmw_copy_loop\n" ++
  ".Lmw_found:\n" ++
  "  li a0, 0\n" ++
  "  j .Lmw_ret\n" ++
  ".Lmw_not_found:\n" ++
  "  li a0, 1\n" ++
  "  sd zero, 0(s5)              # value_len = 0\n" ++
  "  j .Lmw_ret\n" ++
  ".Lmw_parse_fail:\n" ++
  "  li a0, 2\n" ++
  "  sd zero, 0(s5)\n" ++
  ".Lmw_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_mpt_walk`: probe BuildUnit. Reads
    (witness_len, path_len, root_hash, path_nibbles,
     witness_bytes) from host input, writes
    (status, value_len, value_bytes) to OUTPUT.
    Input layout:
      bytes   0..  8 : witness_len (u64)
      bytes   8.. 16 : path_len (u64)
      bytes  16.. 48 : root_hash (32 bytes)
      bytes  48..   : path_nibbles bytes (path_len of them)
      bytes  48 + path_len .. : witness section bytes
    Output layout:
      bytes   0.. 8 : status (0 found / 1 not / 2 fail)
      bytes   8..16 : value_len
      bytes  16..   : value bytes (up to 256 - 16 = 240) -/
def ziskMptWalkPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld t6, 8(a7)                # witness_len\n" ++
  "  ld t5, 16(a7)               # path_len\n" ++
  "  addi a0, a7, 24             # root_hash ptr (offset 16 from start of file)\n" ++
  "  addi a3, a7, 56             # path_nibbles ptr (offset 48)\n" ++
  "  # witness ptr = path_nibbles + path_len.\n" ++
  "  add a1, a3, t5\n" ++
  "  mv a2, t6                   # witness_len\n" ++
  "  mv a4, t5                   # path_len\n" ++
  "  li a5, 0xa0010010           # value buf at OUTPUT + 16\n" ++
  "  li a6, 0xa0010008           # value_len ptr at OUTPUT + 8\n" ++
  "  jal ra, mpt_walk\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Lmw_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  ".Lmw_pdone:"

def ziskMptWalkDataSection : String :=
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
  ".balign 8\n" ++
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
  ".balign 8\n" ++
  "mw_child_offset:\n" ++
  "  .zero 8\n" ++
  "mw_child_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "mw_value_offset:\n" ++
  "  .zero 8\n" ++
  "mw_value_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "mw_nibble_count:\n" ++
  "  .zero 8\n" ++
  "mw_is_leaf:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_nibble_buf:\n" ++
  "  .zero 128"

def ziskMptWalkProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptWalkPrologue
  dataAsm     := ziskMptWalkDataSection
}

/-! ## bytes_to_nibbles -- PR-K25 byte → nibble array expansion

    Convert N bytes into 2N nibbles (one byte per nibble, in
    [0..15]). Each input byte writes 2 output bytes: high nibble
    then low nibble. The output format matches what `mpt_walk`
    (PR-K24) consumes as its path argument.

    Composes with `zkvm_keccak256` to derive the standard MPT
    path from a state-trie or storage-trie key:

        keccak256(address)   -- 32 bytes
        bytes_to_nibbles     -- 64 nibbles
        mpt_walk(...)        -- account / slot lookup

    Calling convention:
      a0 (input)  : src bytes ptr
      a1 (input)  : src byte length
      a2 (input)  : dst nibble buf ptr (2 * a1 bytes)
      ra (input)  : return
      a0 (output) : 2 * a1 (number of nibbles emitted)

    Pure register arithmetic, no scratch memory, leaf-callable. -/
def bytesToNibblesFunction : String :=
  "bytes_to_nibbles:\n" ++
  "  mv t0, a0                  # src cursor\n" ++
  "  mv t1, a2                  # dst cursor\n" ++
  "  mv t2, a1                  # remaining\n" ++
  "  li t6, 0                   # emitted count\n" ++
  ".Lbtn_loop:\n" ++
  "  beqz t2, .Lbtn_done\n" ++
  "  lbu t3, 0(t0)\n" ++
  "  srli t4, t3, 4\n" ++
  "  andi t5, t3, 0xf\n" ++
  "  sb t4, 0(t1)\n" ++
  "  sb t5, 1(t1)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 2\n" ++
  "  addi t2, t2, -1\n" ++
  "  addi t6, t6, 2\n" ++
  "  j .Lbtn_loop\n" ++
  ".Lbtn_done:\n" ++
  "  mv a0, t6\n" ++
  "  ret"

/-- `zisk_bytes_to_nibbles`: probe BuildUnit. Reads
    (src_len, src_bytes) from host input, writes
    (nibble_count, nibbles) to OUTPUT.
    Input layout:
      bytes  0.. 8 : src_len (u64)
      bytes  8..   : src bytes
    Output layout:
      bytes  0.. 8 : nibble_count (u64 = 2 * src_len)
      bytes  8..   : nibble bytes -/
def ziskBytesToNibblesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # src_len\n" ++
  "  addi a0, a3, 16             # src bytes ptr\n" ++
  "  li a2, 0xa0010008           # nibble buf at OUTPUT + 8\n" ++
  "  jal ra, bytes_to_nibbles\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # nibble_count at OUTPUT + 0\n" ++
  "  j .Lbtn_pdone\n" ++
  bytesToNibblesFunction ++ "\n" ++
  ".Lbtn_pdone:"

def ziskBytesToNibblesDataSection : String :=
  ".section .data\n" ++
  "btn_pad:\n" ++
  "  .zero 8"

def ziskBytesToNibblesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBytesToNibblesPrologue
  dataAsm     := ziskBytesToNibblesDataSection
}

/-! ## mpt_lookup_by_key -- PR-K26 keccak + nibbles + mpt_walk

    Compose the lookup chain that turns a raw key (address or
    storage slot index) into a value via Ethereum's standard
    `keccak256(key) -> path -> mpt_walk(...)` shape.

    Both Ethereum state and storage tries use this same shape;
    only the value semantics differ (account RLP vs 32-byte
    storage word).

    Calling convention:
      a0 (input)  : key bytes ptr (20-byte address or 32-byte
                    storage slot index, big-endian)
      a1 (input)  : key byte length
      a2 (input)  : root_hash ptr (32 bytes)
      a3 (input)  : witness section ptr
      a4 (input)  : witness section_len
      a5 (input)  : value output buffer ptr (256 bytes)
      a6 (input)  : u64 out ptr (matched value byte length)
      ra (input)  : return
      a0 (output) : 0 found / 1 not found / 2 parse error
                    (mirrors mpt_walk return codes).

    Internal scratch buffers:
      mlk_keccak_buf : 32 bytes (keccak256 output)
      mlk_nibble_buf : 64 bytes (one nibble per byte) -/
def mptLookupByKeyFunction : String :=
  "mpt_lookup_by_key:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a2                   # s0 = root_hash ptr\n" ++
  "  mv s1, a3                   # s1 = witness ptr\n" ++
  "  mv s2, a4                   # s2 = witness_len\n" ++
  "  mv s3, a5                   # s3 = value out\n" ++
  "  mv s4, a6                   # s4 = value_len out\n" ++
  "  # Step 1: keccak(key) -> mlk_keccak_buf.\n" ++
  "  la a2, mlk_keccak_buf\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # Step 2: bytes_to_nibbles(mlk_keccak_buf, 32, mlk_nibble_buf).\n" ++
  "  la a0, mlk_keccak_buf\n" ++
  "  li a1, 32\n" ++
  "  la a2, mlk_nibble_buf\n" ++
  "  jal ra, bytes_to_nibbles\n" ++
  "  # Step 3: mpt_walk(root, witness, witness_len, path, 64, val_out, val_len).\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s2\n" ++
  "  la a3, mlk_nibble_buf\n" ++
  "  li a4, 64\n" ++
  "  mv a5, s3\n" ++
  "  mv a6, s4\n" ++
  "  jal ra, mpt_walk\n" ++
  "  # a0 already holds mpt_walk's status.\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_mpt_lookup_by_key`: probe BuildUnit. Reads
    (witness_len, key_len, root_hash, key, witness) from host
    input and writes (status, value_len, value_bytes) to OUTPUT.
    Input layout:
      bytes   0.. 8 : witness_len (u64)
      bytes   8..16 : key_len (u64)
      bytes  16..48 : root_hash (32 bytes)
      bytes  48..   : key bytes (key_len)
      bytes  48+key_len.. : witness section bytes
    Output: same as PR-K24 mpt_walk. -/
def ziskMptLookupByKeyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld t6, 8(a7)                # witness_len\n" ++
  "  ld t5, 16(a7)               # key_len\n" ++
  "  addi a2, a7, 24             # root_hash ptr (input offset 16)\n" ++
  "  addi a0, a7, 56             # key ptr (input offset 48)\n" ++
  "  mv a1, t5                   # key_len\n" ++
  "  add a3, a0, t5              # witness ptr = key + key_len\n" ++
  "  mv a4, t6                   # witness_len\n" ++
  "  li a5, 0xa0010010           # value buf at OUTPUT + 16\n" ++
  "  li a6, 0xa0010008           # value_len at OUTPUT + 8\n" ++
  "  jal ra, mpt_lookup_by_key\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Lmlk_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  ".Lmlk_pdone:"

def ziskMptLookupByKeyDataSection : String :=
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
  "  .zero 64"

def ziskMptLookupByKeyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptLookupByKeyPrologue
  dataAsm     := ziskMptLookupByKeyDataSection
}


/-! ## mpt_branch_used_count -- PR-K117

    Count the number of non-empty child slots in an MPT branch
    node's `[c0, c1, …, c15, value]` head. A child slot is
    "non-empty" iff its RLP byte-length is > 0 (empty children
    serialise as the empty RLP string `0x80`, len 0).

    Used by state-root recomputation to detect *single-child*
    branches that can collapse into an extension after a delete
    operation: the trie invariant says a branch must always have
    ≥ 2 children or be replaced by an extension/leaf.

    The `value` field (item 16) is **not** counted; only the 16
    nibble-indexed children. A branch where the value slot is the
    only non-empty entry still returns 0 here (and is itself a
    consensus violation under the standard trie invariants).
-/
/-! ## mpt_branch_first_used_index -- PR-K118

    Find the lowest-indexed non-empty child slot in an MPT branch
    node's `[c0, c1, …, c15, value]` head. Returns the index in
    `[0, 15]` of the first child whose RLP byte-length is > 0, or
    `16` (sentinel "none") when every child slot is empty.

    Used by state-root recomputation in the *trie-collapse* path:
    when PR-K117 `mpt_branch_used_count` reports exactly one
    surviving child, this helper tells the rewriter *which* child
    to inline into the parent's path.

    The `value` field (item 16) is **not** scanned. A branch where
    the value slot is the only non-empty entry still returns the
    `16` sentinel.

    Composes:
      - PR-K47 `rlp_list_count_items` — sanity-check 17 items
      - PR-K20 `rlp_list_nth_item`    — per-child length probe

    Calling convention:
      a0 (input)  : branch_rlp ptr
      a1 (input)  : branch_rlp byte length
      a2 (input)  : u64 out ptr (used_count, 0..16)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : not a 17-item list (or RLP parse failure)
        2 : mid-list nth_item failure -/
def mptBranchUsedCountFunction : String :=
  "mpt_branch_used_count:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # branch ptr\n" ++
  "  mv s1, a1                   # branch len\n" ++
  "  mv s2, a2                   # used_count out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # Verify 17-item list.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, mbuc_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lmbuc_not_branch\n" ++
  "  la t0, mbuc_count; ld t1, 0(t0)\n" ++
  "  li t2, 17\n" ++
  "  bne t1, t2, .Lmbuc_not_branch\n" ++
  "  li s3, 0                    # i = 0\n" ++
  "  li s4, 0                    # used = 0\n" ++
  ".Lmbuc_loop:\n" ++
  "  li t0, 16\n" ++
  "  beq s3, t0, .Lmbuc_done\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  mv a2, s3\n" ++
  "  la a3, mbuc_off; la a4, mbuc_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmbuc_nth_fail\n" ++
  "  la t0, mbuc_len; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lmbuc_step\n" ++
  "  addi s4, s4, 1\n" ++
  ".Lmbuc_step:\n" ++
  "  addi s3, s3, 1\n" ++
  "  j .Lmbuc_loop\n" ++
  ".Lmbuc_done:\n" ++
  "  sd s4, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmbuc_ret\n" ++
  ".Lmbuc_not_branch:\n" ++
  "  li a0, 1\n" ++
  "  j .Lmbuc_ret\n" ++
  ".Lmbuc_nth_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lmbuc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"
def mptBranchFirstUsedIndexFunction : String :=
  "mpt_branch_first_used_index:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # branch ptr\n" ++
  "  mv s1, a1                   # branch len\n" ++
  "  mv s2, a2                   # used_count out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # Verify 17-item list.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, mbuc_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lmbuc_not_branch\n" ++
  "  la t0, mbuc_count; ld t1, 0(t0)\n" ++
  "  li t2, 17\n" ++
  "  bne t1, t2, .Lmbuc_not_branch\n" ++
  "  li s3, 0                    # i = 0\n" ++
  "  li s4, 0                    # used = 0\n" ++
  ".Lmbuc_loop:\n" ++
  "  li t0, 16\n" ++
  "  beq s3, t0, .Lmbuc_done\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  mv a2, s3\n" ++
  "  la a3, mbuc_off; la a4, mbuc_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmbuc_nth_fail\n" ++
  "  la t0, mbuc_len; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lmbuc_step\n" ++
  "  addi s4, s4, 1\n" ++
  ".Lmbuc_step:\n" ++
  "  addi s3, s3, 1\n" ++
  "  j .Lmbuc_loop\n" ++
  ".Lmbuc_done:\n" ++
  "  sd s4, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmbuc_ret\n" ++
  ".Lmbuc_not_branch:\n" ++
  "  li a0, 1\n" ++
  "  j .Lmbuc_ret\n" ++
  ".Lmbuc_nth_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lmbuc_ret:\n" ++
  "  mv s2, a2                   # first_index out\n" ++
  "  li t0, 16\n" ++
  "  sd t0, 0(s2)                # default = 16 (none)\n" ++
  "  # Verify 17-item list.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, mbfui_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lmbfui_not_branch\n" ++
  "  la t0, mbfui_count; ld t1, 0(t0)\n" ++
  "  li t2, 17\n" ++
  "  bne t1, t2, .Lmbfui_not_branch\n" ++
  "  li s3, 0                    # i = 0\n" ++
  ".Lmbfui_loop:\n" ++
  "  li t0, 16\n" ++
  "  beq s3, t0, .Lmbfui_done\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  mv a2, s3\n" ++
  "  la a3, mbfui_off; la a4, mbfui_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmbfui_nth_fail\n" ++
  "  la t0, mbfui_len; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lmbfui_step\n" ++
  "  # Found first non-empty child.\n" ++
  "  sd s3, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmbfui_ret\n" ++
  ".Lmbfui_step:\n" ++
  "  addi s3, s3, 1\n" ++
  "  j .Lmbfui_loop\n" ++
  ".Lmbfui_done:\n" ++
  "  # No non-empty children; output stays at sentinel 16.\n" ++
  "  li a0, 0\n" ++
  "  j .Lmbfui_ret\n" ++
  ".Lmbfui_not_branch:\n" ++
  "  li a0, 1\n" ++
  "  j .Lmbfui_ret\n" ++
  ".Lmbfui_nth_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lmbfui_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_mpt_branch_used_count`: probe BuildUnit. Reads
    (branch_len, branch_bytes), writes (status, used_count) to
    OUTPUT (16 bytes). -/
def ziskMptBranchUsedCountPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # branch length\n" ++
  "  addi a0, a3, 16             # branch ptr\n" ++
  "  li a2, 0xa0010008           # used_count out\n" ++
  "  jal ra, mpt_branch_used_count\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmbuc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  mptBranchUsedCountFunction ++ "\n" ++
  ".Lmbuc_pdone:"

def ziskMptBranchUsedCountDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mbuc_count:\n" ++
  "  .zero 8\n" ++
  "mbuc_off:\n" ++
  "  .zero 8\n" ++
  "mbuc_len:\n" ++
  "  .zero 8"

def ziskMptBranchUsedCountProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptBranchUsedCountPrologue
  dataAsm     := ziskMptBranchUsedCountDataSection
}

/-- `zisk_mpt_branch_first_used_index`: probe BuildUnit. Reads
    (branch_len, branch_bytes), writes (status, first_index) to
    OUTPUT (16 bytes). -/
def ziskMptBranchFirstUsedIndexPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # branch length\n" ++
  "  addi a0, a3, 16             # branch ptr\n" ++
  "  li a2, 0xa0010008           # first_index out\n" ++
  "  jal ra, mpt_branch_first_used_index\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmbfui_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  mptBranchFirstUsedIndexFunction ++ "\n" ++
  ".Lmbfui_pdone:"

def ziskMptBranchFirstUsedIndexDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mbfui_count:\n" ++
  "  .zero 8\n" ++
  "mbfui_off:\n" ++
  "  .zero 8\n" ++
  "mbfui_len:\n" ++
  "  .zero 8"

def ziskMptBranchFirstUsedIndexProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptBranchFirstUsedIndexPrologue
  dataAsm     := ziskMptBranchFirstUsedIndexDataSection
}





/-- `zisk_rlp_list_nth_item`: probe BuildUnit. Reads
    (list_len, N, list_bytes) from host input, writes
    (status, offset, length) to OUTPUT.
    Input layout:
      bytes  0.. 8 : list_len (u64)
      bytes  8..16 : N (u64)
      bytes 16..   : RLP list bytes
    Output layout:
      bytes  0.. 8 : status (0 hit / 1 miss)
      bytes  8..16 : content offset (u64)
      bytes 16..24 : content length (u64) -/
def ziskRlpListNthItemPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # list_len\n" ++
  "  ld a2, 16(a5)               # N\n" ++
  "  addi a0, a5, 24             # list ptr\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  sd zero, 0(a3); sd zero, 0(a4)\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lrln_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  ".Lrln_pdone:"

def ziskRlpListNthItemDataSection : String :=
  ".section .data\n" ++
  "rln_scratch:\n" ++
  "  .zero 8"

def ziskRlpListNthItemProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRlpListNthItemPrologue
  dataAsm     := ziskRlpListNthItemDataSection
}



/-! ## hp_encode_nibbles -- PR-K32 inverse of hp_decode_nibbles

    Encode a nibble array + leaf/extension flag into the HP
    byte string format used as the first item of MPT leaf and
    extension nodes. Inverse of PR-K23 `hp_decode_nibbles`.

    HP encoding rules:
      flag = (is_leaf ? 2 : 0) + (is_odd_nibble_count ? 1 : 0)
      byte 0 = (flag << 4) | (first_nibble if odd else 0)
      bytes 1.. = remaining nibble pairs (high then low)

    Output length:
      even nibble count: 1 + nibble_count / 2 bytes
      odd  nibble count: 1 + (nibble_count - 1) / 2 bytes
                       = ceil(nibble_count / 2) + (0 or 1)

    Or more uniformly: ceil((nibble_count + 2) / 2) bytes.

    Calling convention:
      a0 (input)  : nibbles ptr (1 byte per nibble, low 4 bits)
      a1 (input)  : nibble count
      a2 (input)  : is_leaf flag (0 = extension, 1 = leaf)
      a3 (input)  : output byte buffer ptr
      ra (input)  : return
      a0 (output) : number of bytes written

    Pure register arithmetic, no scratch, leaf-callable. -/
def hpEncodeNibblesFunction : String :=
  "hp_encode_nibbles:\n" ++
  "  andi t0, a1, 1             # is_odd = nibble_count & 1\n" ++
  "  mv t1, a3                  # cursor\n" ++
  "  slli t2, a2, 1             # is_leaf * 2\n" ++
  "  or t2, t2, t0              # flag = is_leaf*2 + is_odd\n" ++
  "  slli t2, t2, 4             # flag << 4\n" ++
  "  beqz t0, .Lhpe_even\n" ++
  "  # Odd: byte 0 = (flag << 4) | nibbles[0]; consume one nibble.\n" ++
  "  lbu t3, 0(a0)\n" ++
  "  or t2, t2, t3\n" ++
  "  sb t2, 0(t1)\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi a0, a0, 1\n" ++
  "  addi a1, a1, -1\n" ++
  "  j .Lhpe_pair_loop\n" ++
  ".Lhpe_even:\n" ++
  "  sb t2, 0(t1)\n" ++
  "  addi t1, t1, 1\n" ++
  ".Lhpe_pair_loop:\n" ++
  "  beqz a1, .Lhpe_done\n" ++
  "  lbu t3, 0(a0)\n" ++
  "  slli t3, t3, 4\n" ++
  "  lbu t4, 1(a0)\n" ++
  "  or t3, t3, t4\n" ++
  "  sb t3, 0(t1)\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi a0, a0, 2\n" ++
  "  addi a1, a1, -2\n" ++
  "  j .Lhpe_pair_loop\n" ++
  ".Lhpe_done:\n" ++
  "  sub a0, t1, a3\n" ++
  "  ret"

/-- `zisk_hp_encode_nibbles`: probe BuildUnit. Reads
    (nibble_count, is_leaf, nibbles) from host input, writes
    (bytes_written, hp_bytes) to OUTPUT.
    Input layout:
      bytes  0.. 8 : nibble_count (u64)
      bytes  8..16 : is_leaf (u64; 0 or 1)
      bytes 16..   : nibble bytes (each in [0..15]) -/
def ziskHpEncodeNibblesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # nibble_count\n" ++
  "  ld a2, 16(a4)               # is_leaf\n" ++
  "  addi a0, a4, 24             # nibbles ptr\n" ++
  "  li a3, 0xa0010008           # output at OUTPUT + 8\n" ++
  "  jal ra, hp_encode_nibbles\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # bytes_written\n" ++
  "  j .Lhpe_pdone\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  ".Lhpe_pdone:"

def ziskHpEncodeNibblesDataSection : String :=
  ".section .data\n" ++
  "hpe_pad:\n" ++
  "  .zero 8"

def ziskHpEncodeNibblesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHpEncodeNibblesPrologue
  dataAsm     := ziskHpEncodeNibblesDataSection
}


/-! ## single_leaf_trie_root -- PR-K157

    Compute the Merkle-Patricia-Trie root for a trie containing
    *exactly one* (key, value) entry:

      path_nibbles = bytes_to_nibbles(key)
      hp_path      = hp_encode_nibbles(path_nibbles, is_leaf=true)
      leaf_node    = rlp([hp_path, value])
      trie_root    = keccak256(leaf_node)

    Direct counterpart of PR-K33 `state_root_single_account`,
    generalised for arbitrary `(key, value)` pairs.

    Use cases:
      * `transactions_root` for a single-tx block: key = rlp(0),
        value = tx_rlp (typed envelope or legacy RLP).
      * `withdrawals_root` for a single-withdrawal block: key =
        rlp(0), value = withdrawal_rlp.
      * `receipts_root` for a single-receipt block: key = rlp(0),
        value = receipt_rlp.

    For multi-entry tries this helper does not apply -- those
    require branch / extension nodes and the full MPT construction
    machinery (separate PR series).

    Composes:
      - PR-K25 `bytes_to_nibbles`        -- expand key bytes
      - PR-K32 `hp_encode_nibbles`       -- HP-encode the path
      - PR-K128 `rlp_encode_bytes`       -- encode hp_path
                                            and value as RLP strings
      - PR-K129 `rlp_encode_list_prefix` -- outer list prefix
      - `zkvm_keccak256` (HashBridge)    -- root hash

    Calling convention:
      a0 (input)  : key ptr (raw key bytes)
      a1 (input)  : key byte length
      a2 (input)  : value ptr (raw value bytes)
      a3 (input)  : value byte length
      a4 (input)  : 32-byte output root ptr
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def singleLeafTrieRootFunction : String :=
  "single_leaf_trie_root:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # key ptr\n" ++
  "  mv s1, a1                   # key len\n" ++
  "  mv s2, a2                   # value ptr\n" ++
  "  mv s3, a3                   # value len\n" ++
  "  mv s4, a4                   # output root ptr\n" ++
  "  # ---- Step 1: expand key bytes to nibbles ----\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, sltr_nibbles\n" ++
  "  jal ra, bytes_to_nibbles\n" ++
  "  # a0 = 2 * key_len nibbles emitted -- store for HP step\n" ++
  "  la t0, sltr_nibble_count; sd a0, 0(t0)\n" ++
  "  # ---- Step 2: HP-encode the nibbles (leaf=true) ----\n" ++
  "  la a0, sltr_nibbles\n" ++
  "  la t0, sltr_nibble_count; ld a1, 0(t0)\n" ++
  "  li a2, 1                                    # is_leaf = 1\n" ++
  "  la a3, sltr_hp_buf\n" ++
  "  jal ra, hp_encode_nibbles\n" ++
  "  la t0, sltr_hp_len; sd a0, 0(t0)\n" ++
  "  # ---- Step 3: RLP-encode hp_path into the payload buffer ----\n" ++
  "  la a0, sltr_hp_buf\n" ++
  "  la t0, sltr_hp_len; ld a1, 0(t0)\n" ++
  "  la a2, sltr_payload_buf\n" ++
  "  la a3, sltr_field_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, sltr_field_len; ld t1, 0(t0)         # hp_rlp_len\n" ++
  "  la t0, sltr_cursor; sd t1, 0(t0)            # cursor = hp_rlp_len\n" ++
  "  # ---- Step 4: RLP-encode value at payload[cursor..] ----\n" ++
  "  la t0, sltr_cursor; ld t1, 0(t0)\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  la a2, sltr_payload_buf; add a2, a2, t1\n" ++
  "  la a3, sltr_field_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, sltr_field_len; ld t1, 0(t0)         # value_rlp_len\n" ++
  "  la t0, sltr_cursor; ld t2, 0(t0)\n" ++
  "  add t2, t2, t1                              # total inner payload len\n" ++
  "  la t0, sltr_total_payload; sd t2, 0(t0)\n" ++
  "  # ---- Step 5: write outer list prefix at node_buf[0..] ----\n" ++
  "  mv a0, t2\n" ++
  "  la a1, sltr_node_buf\n" ++
  "  la a2, sltr_field_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  la t0, sltr_field_len; ld t1, 0(t0)         # outer_prefix_len\n" ++
  "  la t0, sltr_total_payload; ld t2, 0(t0)\n" ++
  "  # ---- Step 6: copy payload after prefix in node_buf ----\n" ++
  "  la t3, sltr_node_buf; add t3, t3, t1        # dst\n" ++
  "  la t4, sltr_payload_buf                     # src\n" ++
  "  mv t5, t2                                   # remaining\n" ++
  ".Lsltr_cp:\n" ++
  "  beqz t5, .Lsltr_cp_done\n" ++
  "  lbu t6, 0(t4)\n" ++
  "  sb t6, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t5, t5, -1\n" ++
  "  j .Lsltr_cp\n" ++
  ".Lsltr_cp_done:\n" ++
  "  add t1, t1, t2                              # full leaf-node RLP length\n" ++
  "  # ---- Step 7: keccak256(node_buf, full_len) → root ----\n" ++
  "  la a0, sltr_node_buf\n" ++
  "  mv a1, t1\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_single_leaf_trie_root`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : key_len
      bytes  8..16 : value_len
      bytes 16..16+key_len: key
      bytes 16+key_len..   : value (8-byte aligned padding)
    Output layout (256 B):
      bytes  0..32 : 32-byte trie root -/
def ziskSingleLeafTrieRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # key_len\n" ++
  "  ld a3, 16(a5)               # value_len\n" ++
  "  addi a0, a5, 24             # key ptr\n" ++
  "  # value ptr = key_ptr + key_len (rounded up to 8B alignment? No, raw).\n" ++
  "  add a2, a0, a1\n" ++
  "  li a4, 0xa0010000           # output root ptr (32 B)\n" ++
  "  jal ra, single_leaf_trie_root\n" ++
  "  j .Lsltr_pdone\n" ++
  bytesToNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  singleLeafTrieRootFunction ++ "\n" ++
  ".Lsltr_pdone:"

def ziskSingleLeafTrieRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "sltr_field_len:\n" ++
  "  .zero 8\n" ++
  "sltr_nibble_count:\n" ++
  "  .zero 8\n" ++
  "sltr_hp_len:\n" ++
  "  .zero 8\n" ++
  "sltr_cursor:\n" ++
  "  .zero 8\n" ++
  "sltr_total_payload:\n" ++
  "  .zero 8\n" ++
  "sltr_nibbles:\n" ++
  "  .zero 2048\n" ++
  "sltr_hp_buf:\n" ++
  "  .zero 1024\n" ++
  "sltr_payload_buf:\n" ++
  "  .zero 16384\n" ++
  "sltr_node_buf:\n" ++
  "  .zero 16384"

def ziskSingleLeafTrieRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSingleLeafTrieRootPrologue
  dataAsm     := ziskSingleLeafTrieRootDataSection
}

/-! ## mpt_leaf_node_encode -- PR-K162

    Encode an MPT *leaf node* into RLP, without hashing. This is
    exactly the step before the final keccak in PR-K157
    `single_leaf_trie_root`:

      hp_path     = hp_encode_nibbles(
                      bytes_to_nibbles(path), is_leaf=true)
      leaf_node   = rlp([hp_path, value])
      -- (K157 would now keccak256 this; K162 stops here.)

    Use cases:
      * Multi-leaf MPT construction where a leaf becomes a *child*
        of a branch / extension node. The parent slot encoding
        embeds either the leaf's hash (`keccak256(leaf_node)`)
        if `len(leaf_node) >= 32`, or the leaf's RLP bytes
        verbatim if shorter. K162 produces the bytes that the
        parent-encoder slots in either form.
      * Diagnostics: callers that want to inspect a leaf's wire
        bytes (e.g., for debugging trie shapes) get them without
        the keccak detour.

    Composes:
      - PR-K25 `bytes_to_nibbles`        -- expand path bytes
      - PR-K32 `hp_encode_nibbles`       -- HP-encode (leaf=true)
      - PR-K128 `rlp_encode_bytes`       -- encode hp_path / value
      - PR-K129 `rlp_encode_list_prefix` -- outer list prefix

    Calling convention:
      a0 (input)  : path ptr (raw key bytes)
      a1 (input)  : path byte length
      a2 (input)  : value ptr
      a3 (input)  : value byte length
      a4 (input)  : output buffer ptr
                    (caller supplies enough space)
      a5 (input)  : u64 out length ptr (total bytes written)
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def mptLeafNodeEncodeFunction : String :=
  "mpt_leaf_node_encode:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # path ptr\n" ++
  "  mv s1, a1                   # path len\n" ++
  "  mv s2, a2                   # value ptr\n" ++
  "  mv s3, a3                   # value len\n" ++
  "  mv s4, a4                   # output ptr\n" ++
  "  mv s5, a5                   # out_length ptr\n" ++
  "  # ---- Step 1: expand path bytes to nibbles ----\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, mlne_nibbles\n" ++
  "  jal ra, bytes_to_nibbles\n" ++
  "  la t0, mlne_nibble_count; sd a0, 0(t0)\n" ++
  "  # ---- Step 2: HP-encode (leaf=true) ----\n" ++
  "  la a0, mlne_nibbles\n" ++
  "  la t0, mlne_nibble_count; ld a1, 0(t0)\n" ++
  "  li a2, 1\n" ++
  "  la a3, mlne_hp_buf\n" ++
  "  jal ra, hp_encode_nibbles\n" ++
  "  la t0, mlne_hp_len; sd a0, 0(t0)\n" ++
  "  # ---- Step 3: RLP-encode hp_path into payload_buf ----\n" ++
  "  la a0, mlne_hp_buf\n" ++
  "  la t0, mlne_hp_len; ld a1, 0(t0)\n" ++
  "  la a2, mlne_payload_buf\n" ++
  "  la a3, mlne_field_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, mlne_field_len; ld t1, 0(t0)\n" ++
  "  la t0, mlne_cursor; sd t1, 0(t0)\n" ++
  "  # ---- Step 4: RLP-encode value at payload[cursor..] ----\n" ++
  "  la t0, mlne_cursor; ld t1, 0(t0)\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  la a2, mlne_payload_buf; add a2, a2, t1\n" ++
  "  la a3, mlne_field_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, mlne_field_len; ld t1, 0(t0)\n" ++
  "  la t0, mlne_cursor; ld t2, 0(t0)\n" ++
  "  add t2, t2, t1\n" ++
  "  la t0, mlne_total_payload; sd t2, 0(t0)\n" ++
  "  # ---- Step 5: write outer list prefix to output[0..] ----\n" ++
  "  mv a0, t2\n" ++
  "  mv a1, s4\n" ++
  "  la a2, mlne_field_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  la t0, mlne_field_len; ld t1, 0(t0)\n" ++
  "  la t0, mlne_total_payload; ld t2, 0(t0)\n" ++
  "  # ---- Step 6: copy payload after prefix in output ----\n" ++
  "  add t3, s4, t1\n" ++
  "  la t4, mlne_payload_buf\n" ++
  "  mv t5, t2\n" ++
  ".Lmlne_cp:\n" ++
  "  beqz t5, .Lmlne_cp_done\n" ++
  "  lbu t6, 0(t4)\n" ++
  "  sb t6, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t5, t5, -1\n" ++
  "  j .Lmlne_cp\n" ++
  ".Lmlne_cp_done:\n" ++
  "  add t1, t1, t2\n" ++
  "  sd t1, 0(s5)\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_mpt_leaf_node_encode`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : path_len
      bytes  8..16 : value_len
      bytes 16..16+path_len: path
      bytes (16+path_len)..: value
    Output layout (256 B):
      bytes  0.. 8 : status
      bytes  8..16 : leaf-node RLP length
      bytes 16..   : leaf-node RLP bytes (truncated to fit ziskemu cap) -/
def ziskMptLeafNodeEncodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # path_len\n" ++
  "  ld a3, 16(a6)               # value_len\n" ++
  "  addi a0, a6, 24             # path ptr\n" ++
  "  add a2, a0, a1              # value ptr\n" ++
  "  li a4, 0xa0010010           # output buffer ptr\n" ++
  "  li a5, 0xa0010008           # out_length ptr\n" ++
  "  jal ra, mpt_leaf_node_encode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmlne_pdone\n" ++
  bytesToNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptLeafNodeEncodeFunction ++ "\n" ++
  ".Lmlne_pdone:"

def ziskMptLeafNodeEncodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mlne_field_len:\n" ++
  "  .zero 8\n" ++
  "mlne_nibble_count:\n" ++
  "  .zero 8\n" ++
  "mlne_hp_len:\n" ++
  "  .zero 8\n" ++
  "mlne_cursor:\n" ++
  "  .zero 8\n" ++
  "mlne_total_payload:\n" ++
  "  .zero 8\n" ++
  "mlne_nibbles:\n" ++
  "  .zero 2048\n" ++
  "mlne_hp_buf:\n" ++
  "  .zero 1024\n" ++
  "mlne_payload_buf:\n" ++
  "  .zero 16384"

def ziskMptLeafNodeEncodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptLeafNodeEncodePrologue
  dataAsm     := ziskMptLeafNodeEncodeDataSection
}

/-! ## mpt_node_slot_encode -- PR-K163

    Given a child MPT node's RLP, produce the bytes that go
    *verbatim* into a parent node's child-slot when assembling
    the parent's outer RLP list.

      if len(node_rlp) < 32:
        slot_bytes = node_rlp                  -- inline embed
      else:
        slot_bytes = 0xa0 || keccak256(node_rlp)  -- 32-byte
                                                -- string item

    This is the parent-side complement of PR-K112
    `mpt_encode_internal_node`. K112 returns the *raw reference*
    (either RLP bytes verbatim or just the 32-byte hash); K163
    wraps the hashed case with the 0xa0 RLP string-prefix so the
    output is ready to splice into the parent's RLP payload.

    Building block for `mpt_branch_node_encode` (future) and
    `mpt_extension_node_encode` (future).

    Composes:
      - `zkvm_keccak256` (HashBridge) when node_rlp_len >= 32

    Calling convention:
      a0 (input)  : node_rlp ptr
      a1 (input)  : node_rlp byte length
      a2 (input)  : output bytes ptr
                    (caller supplies max(node_rlp_len, 33) bytes)
      a3 (input)  : u64 out length ptr
                    (33 when hashed, node_rlp_len when inline)
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def mptNodeSlotEncodeFunction : String :=
  "mpt_node_slot_encode:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a2                   # output ptr\n" ++
  "  mv s1, a3                   # out_length ptr\n" ++
  "  li t0, 32\n" ++
  "  bltu a1, t0, .Lmnse_inline\n" ++
  "  # Hash path: out[0] = 0xa0; keccak256(node_rlp) -> out[1..33].\n" ++
  "  li t1, 0xa0\n" ++
  "  sb t1, 0(s0)\n" ++
  "  mv s2, a0                   # node_rlp ptr stashed\n" ++
  "  # zkvm_keccak256(node_rlp, len, out + 1).\n" ++
  "  addi a2, s0, 1\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li t0, 33\n" ++
  "  sd t0, 0(s1)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmnse_ret\n" ++
  ".Lmnse_inline:\n" ++
  "  # Inline path: copy node_rlp bytes to out.\n" ++
  "  mv t0, a0                   # src cursor\n" ++
  "  mv t1, s0                   # dst cursor\n" ++
  "  mv t2, a1                   # remaining\n" ++
  ".Lmnse_cp:\n" ++
  "  beqz t2, .Lmnse_cp_done\n" ++
  "  lbu t3, 0(t0)\n" ++
  "  sb  t3, 0(t1)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Lmnse_cp\n" ++
  ".Lmnse_cp_done:\n" ++
  "  sd a1, 0(s1)\n" ++
  "  li a0, 0\n" ++
  ".Lmnse_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_mpt_node_slot_encode`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : node_rlp_len
      bytes  8..   : node_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : out_length
      bytes 16..   : slot_bytes (up to 33 bytes for hash; up to
                      ziskemu cap minus 16 for inline) -/
def ziskMptNodeSlotEncodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # node_rlp_len\n" ++
  "  addi a0, a4, 16             # node_rlp ptr\n" ++
  "  li a2, 0xa0010010           # output slot ptr\n" ++
  "  li a3, 0xa0010008           # out_length ptr\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmnse_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  ".Lmnse_pdone:"

def ziskMptNodeSlotEncodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskMptNodeSlotEncodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptNodeSlotEncodePrologue
  dataAsm     := ziskMptNodeSlotEncodeDataSection
}

/-! ## mpt_extension_node_encode -- PR-K164

    Encode an MPT *extension* node as RLP:

      ext_node = rlp([hp_encode_nibbles(shared_path, is_leaf=false),
                      child_ref_bytes])

    Where `child_ref_bytes` is the parent-slot encoding of the
    child node produced by PR-K163 `mpt_node_slot_encode` (either
    the child's inline RLP or `0xa0 || keccak256(child_rlp)`).

    Used during multi-leaf MPT root computation: when two
    sub-tries share a path prefix, the parent above the divergence
    is an extension whose path encodes the shared nibbles and
    whose single child is the sub-trie at the divergence point.

    Composes:
      - PR-K32  `hp_encode_nibbles` with is_leaf=false
      - PR-K128 `rlp_encode_bytes`  for hp_path
      - PR-K129 `rlp_encode_list_prefix` for outer list

    Calling convention:
      a0 (input)  : path_nibbles ptr (one byte per nibble,
                    low 4 bits)
      a1 (input)  : nibble count
      a2 (input)  : child_ref_bytes ptr (output of K163 -- already
                    a valid RLP item, embedded verbatim)
      a3 (input)  : child_ref byte length
      a4 (input)  : output buffer ptr
      a5 (input)  : u64 out length ptr (total bytes written)
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def mptExtensionNodeEncodeFunction : String :=
  "mpt_extension_node_encode:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # path_nibbles ptr\n" ++
  "  mv s1, a1                   # nibble count\n" ++
  "  mv s2, a2                   # child_ref ptr\n" ++
  "  mv s3, a3                   # child_ref len\n" ++
  "  mv s4, a4                   # output ptr\n" ++
  "  mv s5, a5                   # out_length ptr\n" ++
  "  # ---- Step 1: HP-encode nibbles (is_leaf=0) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0\n" ++
  "  la a3, mxne_hp_buf\n" ++
  "  jal ra, hp_encode_nibbles\n" ++
  "  la t0, mxne_hp_len; sd a0, 0(t0)\n" ++
  "  # ---- Step 2: RLP-encode hp_path into payload[0..] ----\n" ++
  "  la a0, mxne_hp_buf\n" ++
  "  la t0, mxne_hp_len; ld a1, 0(t0)\n" ++
  "  la a2, mxne_payload_buf\n" ++
  "  la a3, mxne_field_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, mxne_field_len; ld t1, 0(t0)         # hp_rlp_len\n" ++
  "  la t0, mxne_cursor; sd t1, 0(t0)\n" ++
  "  # ---- Step 3: copy child_ref verbatim into payload[cursor..] ----\n" ++
  "  la t0, mxne_cursor; ld t1, 0(t0)\n" ++
  "  la t2, mxne_payload_buf; add t2, t2, t1     # dst\n" ++
  "  mv t3, s2                                    # src\n" ++
  "  mv t4, s3                                    # remaining\n" ++
  ".Lmxne_cref_cp:\n" ++
  "  beqz t4, .Lmxne_cref_done\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb t5, 0(t2)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lmxne_cref_cp\n" ++
  ".Lmxne_cref_done:\n" ++
  "  la t0, mxne_cursor; ld t1, 0(t0)\n" ++
  "  add t2, t1, s3                                # total payload len\n" ++
  "  la t0, mxne_total_payload; sd t2, 0(t0)\n" ++
  "  # ---- Step 4: outer list prefix to output[0..] ----\n" ++
  "  mv a0, t2; mv a1, s4\n" ++
  "  la a2, mxne_field_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  la t0, mxne_field_len; ld t1, 0(t0)          # outer_prefix_len\n" ++
  "  la t0, mxne_total_payload; ld t2, 0(t0)\n" ++
  "  # ---- Step 5: copy payload after prefix ----\n" ++
  "  add t3, s4, t1                                # dst\n" ++
  "  la t4, mxne_payload_buf                       # src\n" ++
  "  mv t5, t2                                     # remaining\n" ++
  ".Lmxne_body_cp:\n" ++
  "  beqz t5, .Lmxne_body_done\n" ++
  "  lbu t6, 0(t4)\n" ++
  "  sb t6, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t5, t5, -1\n" ++
  "  j .Lmxne_body_cp\n" ++
  ".Lmxne_body_done:\n" ++
  "  add t1, t1, t2                                # total written = prefix + payload\n" ++
  "  sd t1, 0(s5)\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_mpt_extension_node_encode`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : nibble_count
      bytes  8..16 : child_ref_len
      bytes 16..16+nibble_count: path_nibbles (1 byte per nibble)
      bytes (16+nibble_count)..: child_ref bytes
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : ext-node RLP length
      bytes 16..   : ext-node RLP bytes (truncated to ziskemu cap) -/
def ziskMptExtensionNodeEncodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # nibble_count\n" ++
  "  ld a3, 16(a6)               # child_ref_len\n" ++
  "  addi a0, a6, 24             # path_nibbles ptr\n" ++
  "  add a2, a0, a1              # child_ref ptr\n" ++
  "  li a4, 0xa0010010           # output buffer ptr\n" ++
  "  li a5, 0xa0010008           # out_length ptr\n" ++
  "  jal ra, mpt_extension_node_encode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmxne_pdone\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptExtensionNodeEncodeFunction ++ "\n" ++
  ".Lmxne_pdone:"

def ziskMptExtensionNodeEncodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mxne_field_len:\n" ++
  "  .zero 8\n" ++
  "mxne_hp_len:\n" ++
  "  .zero 8\n" ++
  "mxne_cursor:\n" ++
  "  .zero 8\n" ++
  "mxne_total_payload:\n" ++
  "  .zero 8\n" ++
  "mxne_hp_buf:\n" ++
  "  .zero 1024\n" ++
  "mxne_payload_buf:\n" ++
  "  .zero 16384"

def ziskMptExtensionNodeEncodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptExtensionNodeEncodePrologue
  dataAsm     := ziskMptExtensionNodeEncodeDataSection
}

/-! ## mpt_branch_node_encode -- PR-K165

    Encode an MPT *branch* node as RLP, given a pre-concatenated
    17-slot payload:

      branch_node = rlp([slot_0, slot_1, ..., slot_15, value])

    Each of the 17 slots is one RLP item, already encoded by the
    caller in one of three forms:
      * empty: `0x80`              (1 byte)
      * inline child: `child_rlp`  (variable; len < 32)
      * hashed child: `0xa0 || keccak256(child_rlp)` (33 bytes)
      * value slot: `0x80` if no value lives at this prefix, else
        the RLP-encoded value bytes.

    The caller arranges all 17 slot encodings in order and passes
    the concatenated payload; this helper just emits the outer
    list prefix for that payload length, then copies the payload.
    Use PR-K163 `mpt_node_slot_encode` to produce each child
    slot's bytes.

    Composes:
      - PR-K129 `rlp_encode_list_prefix` for the outer prefix

    Calling convention:
      a0 (input)  : slot_payload ptr (pre-concatenated 17-slot
                    bytes; caller's responsibility to put the
                    slots in nibble order and end with the value
                    slot)
      a1 (input)  : slot_payload byte length
      a2 (input)  : output buffer ptr
                    (caller supplies >= 9 + a1 bytes)
      a3 (input)  : u64 out length ptr (total bytes written:
                    prefix_len + payload_len)
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def mptBranchNodeEncodeFunction : String :=
  "mpt_branch_node_encode:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # slot_payload ptr\n" ++
  "  mv s1, a1                   # slot_payload len\n" ++
  "  mv s2, a2                   # output ptr\n" ++
  "  mv s3, a3                   # out_length ptr\n" ++
  "  # ---- Write outer list prefix at output[0..] ----\n" ++
  "  mv a0, s1; mv a1, s2\n" ++
  "  la a2, mbne_field_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  la t0, mbne_field_len; ld t1, 0(t0)         # prefix_len\n" ++
  "  # ---- Copy payload after prefix ----\n" ++
  "  add t2, s2, t1                                # dst = output + prefix_len\n" ++
  "  mv t3, s0                                     # src\n" ++
  "  mv t4, s1                                     # remaining\n" ++
  ".Lmbne_cp:\n" ++
  "  beqz t4, .Lmbne_cp_done\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb t5, 0(t2)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lmbne_cp\n" ++
  ".Lmbne_cp_done:\n" ++
  "  add t1, t1, s1                                # total written\n" ++
  "  sd t1, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_mpt_branch_node_encode`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : slot_payload_len
      bytes  8..   : slot_payload (pre-concatenated 17-slot bytes)
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : branch-node RLP length
      bytes 16..   : branch-node RLP bytes (truncated to ziskemu
                     cap if oversized) -/
def ziskMptBranchNodeEncodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # slot_payload_len\n" ++
  "  addi a0, a4, 16             # slot_payload ptr\n" ++
  "  li a2, 0xa0010010           # output buffer ptr\n" ++
  "  li a3, 0xa0010008           # out_length ptr\n" ++
  "  jal ra, mpt_branch_node_encode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmbne_pdone\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptBranchNodeEncodeFunction ++ "\n" ++
  ".Lmbne_pdone:"

def ziskMptBranchNodeEncodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mbne_field_len:\n" ++
  "  .zero 8"

def ziskMptBranchNodeEncodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptBranchNodeEncodePrologue
  dataAsm     := ziskMptBranchNodeEncodeDataSection
}

/-! ## nibbles_common_prefix_len -- PR-K166

    Walk two nibble arrays (one byte per nibble, low 4 bits) from
    the start and return the length of their shared prefix. Stops
    at the first differing nibble or at the end of the shorter
    array, whichever comes first.

    Direct building block for multi-leaf MPT root computation:
    given two leaf paths in nibble form, the depth at which they
    diverge tells the constructor whether to emit an extension
    node (for the shared prefix) followed by a branch (at the
    divergence point), or just a branch directly (if cpl == 0).

    Example: for sequential indices 0 and 1 in an indexed trie,
    `rlp(0) = 0x80` and `rlp(1) = 0x01` expand to nibbles
    `[0x8, 0x0]` and `[0x0, 0x1]`; their common prefix is empty
    (cpl == 0), so the root is a branch.

    Pure register arithmetic, leaf-callable, no scratch.

    Calling convention:
      a0 (input)  : nibbles_a ptr (1 byte per nibble)
      a1 (input)  : nibbles_a count
      a2 (input)  : nibbles_b ptr
      a3 (input)  : nibbles_b count
      a4 (input)  : u64 out ptr (common prefix length, in nibbles)
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def nibblesCommonPrefixLenFunction : String :=
  "nibbles_common_prefix_len:\n" ++
  "  # min(a_count, b_count)\n" ++
  "  bltu a1, a3, .Lncpl_min_ok\n" ++
  "  mv a1, a3\n" ++
  ".Lncpl_min_ok:\n" ++
  "  li t0, 0                   # cpl accumulator\n" ++
  "  mv t1, a0                  # a cursor\n" ++
  "  mv t2, a2                  # b cursor\n" ++
  ".Lncpl_loop:\n" ++
  "  bge t0, a1, .Lncpl_done\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  bne t3, t4, .Lncpl_done\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lncpl_loop\n" ++
  ".Lncpl_done:\n" ++
  "  sd t0, 0(a4)\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_nibbles_common_prefix_len`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : a_count
      bytes  8..16 : b_count
      bytes 16..16+a_count: nibbles_a
      bytes (16+a_count)..: nibbles_b
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : common prefix length -/
def ziskNibblesCommonPrefixLenPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # a_count\n" ++
  "  ld a3, 16(a5)               # b_count\n" ++
  "  addi a0, a5, 24             # nibbles_a ptr\n" ++
  "  add a2, a0, a1              # nibbles_b ptr\n" ++
  "  li a4, 0xa0010008           # cpl out\n" ++
  "  jal ra, nibbles_common_prefix_len\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lncpl_pdone\n" ++
  nibblesCommonPrefixLenFunction ++ "\n" ++
  ".Lncpl_pdone:"

def ziskNibblesCommonPrefixLenDataSection : String :=
  ".section .data\n" ++
  "ncpl_pad:\n" ++
  "  .zero 8"

def ziskNibblesCommonPrefixLenProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskNibblesCommonPrefixLenPrologue
  dataAsm     := ziskNibblesCommonPrefixLenDataSection
}

/-! ## mpt_branch_payload_two_slots -- PR-K167

    Produce the 17-slot payload bytes for an MPT branch node
    with exactly two active slots and the remaining 15 slots
    (plus the value slot at index 16) filled with empty
    encodings (`0x80`).

    Direct building block for **two-leaf MPT root computation**:
    after PR-K166 has determined the divergence nibble and
    PR-K162/K163 have produced each leaf's parent-slot bytes,
    this helper builds the branch payload that PR-K165 then
    wraps into the final branch-node RLP.

    Empty slots use the RLP empty-string marker `0x80` (1 byte
    each). The value slot is always empty for indexed-trie use
    cases (transactions / receipts / withdrawals); callers that
    need a value at the branch's exact prefix pass that slot
    explicitly as one of the two active slots (idx = 16).

    Output length: `16 + len_a + len_b` bytes (15 empty children
    slots + 1 empty value slot at 0x80 each + the two active
    slots' bytes).

    Composes: nothing (pure byte copying / 0x80 fill).

    Calling convention:
      a0 (input)  : idx_a (u64; 0..16)
      a1 (input)  : bytes_a ptr (slot a's parent-slot encoding)
      a2 (input)  : len_a
      a3 (input)  : idx_b (u64; 0..16; must differ from idx_a)
      a4 (input)  : bytes_b ptr
      a5 (input)  : len_b
      a6 (input)  : output buffer ptr
                    (caller supplies >= 16 + len_a + len_b bytes)
      a7 (input)  : u64 out length ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : idx_a >= 17 or idx_b >= 17 or idx_a == idx_b -/
def mptBranchPayloadTwoSlotsFunction : String :=
  "mpt_branch_payload_two_slots:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # idx_a\n" ++
  "  mv s1, a1                   # bytes_a ptr\n" ++
  "  mv s2, a2                   # len_a\n" ++
  "  mv s3, a3                   # idx_b\n" ++
  "  mv s4, a4                   # bytes_b ptr\n" ++
  "  mv s5, a5                   # len_b\n" ++
  "  # ---- Validate ----\n" ++
  "  li t0, 17\n" ++
  "  bgeu s0, t0, .Lmbpts_fail\n" ++
  "  bgeu s3, t0, .Lmbpts_fail\n" ++
  "  beq  s0, s3, .Lmbpts_fail\n" ++
  "  # ---- Walk slot indices 0..16, emitting bytes ----\n" ++
  "  mv t1, a6                   # output cursor\n" ++
  "  li t2, 0                    # i\n" ++
  ".Lmbpts_loop:\n" ++
  "  li t0, 17\n" ++
  "  bge t2, t0, .Lmbpts_done\n" ++
  "  beq t2, s0, .Lmbpts_emit_a\n" ++
  "  beq t2, s3, .Lmbpts_emit_b\n" ++
  "  # Empty slot: write 0x80.\n" ++
  "  li t3, 0x80\n" ++
  "  sb t3, 0(t1)\n" ++
  "  addi t1, t1, 1\n" ++
  "  j .Lmbpts_next\n" ++
  ".Lmbpts_emit_a:\n" ++
  "  # Copy len_a bytes from bytes_a to output.\n" ++
  "  mv t3, s1\n" ++
  "  mv t4, s2\n" ++
  ".Lmbpts_cp_a:\n" ++
  "  beqz t4, .Lmbpts_next\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb t5, 0(t1)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lmbpts_cp_a\n" ++
  ".Lmbpts_emit_b:\n" ++
  "  mv t3, s4\n" ++
  "  mv t4, s5\n" ++
  ".Lmbpts_cp_b:\n" ++
  "  beqz t4, .Lmbpts_next\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb t5, 0(t1)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lmbpts_cp_b\n" ++
  ".Lmbpts_next:\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lmbpts_loop\n" ++
  ".Lmbpts_done:\n" ++
  "  # out_length = cursor - output_start.\n" ++
  "  sub t1, t1, a6\n" ++
  "  sd t1, 0(a7)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmbpts_ret\n" ++
  ".Lmbpts_fail:\n" ++
  "  sd zero, 0(a7)\n" ++
  "  li a0, 1\n" ++
  ".Lmbpts_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_mpt_branch_payload_two_slots`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : idx_a
      bytes  8..16 : len_a
      bytes 16..24 : idx_b
      bytes 24..32 : len_b
      bytes 32..32+len_a: bytes_a
      bytes (32+len_a)..: bytes_b
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : out_length
      bytes 16..   : 17-slot payload bytes (truncated to ziskemu cap) -/
def ziskMptBranchPayloadTwoSlotsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a0, 8(t0)                # idx_a\n" ++
  "  ld a2, 16(t0)               # len_a\n" ++
  "  ld a3, 24(t0)               # idx_b\n" ++
  "  ld a5, 32(t0)               # len_b\n" ++
  "  addi a1, t0, 40             # bytes_a ptr\n" ++
  "  add  a4, a1, a2             # bytes_b ptr\n" ++
  "  li a6, 0xa0010010           # output ptr\n" ++
  "  li a7, 0xa0010008           # out_length ptr\n" ++
  "  jal ra, mpt_branch_payload_two_slots\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lmbpts_pdone\n" ++
  mptBranchPayloadTwoSlotsFunction ++ "\n" ++
  ".Lmbpts_pdone:"

def ziskMptBranchPayloadTwoSlotsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mbpts_pad:\n" ++
  "  .zero 8"

def ziskMptBranchPayloadTwoSlotsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptBranchPayloadTwoSlotsPrologue
  dataAsm     := ziskMptBranchPayloadTwoSlotsDataSection
}


end EvmAsm.Codegen
