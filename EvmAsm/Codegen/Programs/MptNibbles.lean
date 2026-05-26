/-
  EvmAsm.Codegen.Programs.MptNibbles

  Nibble ↔ compact-encoding helpers carved out of
  `EvmAsm.Codegen.Programs.MptInternal` per the file-size hard
  cap. Hosts:

    K109  mpt_nibbles_to_compact
    K110  mpt_compact_to_nibbles

  Self-contained byte-level helpers — no external Function
  dependencies beyond `Rv64.Program` and `Codegen.Layout`.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

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


end EvmAsm.Codegen
