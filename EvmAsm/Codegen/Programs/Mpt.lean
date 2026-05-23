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

end EvmAsm.Codegen
