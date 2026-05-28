/-
  EvmAsm.Codegen.Programs.Storage

  M22 persistent-storage handlers (SLOAD/SSTORE) plus the carried-over
  M17 no-op TLOAD/TSTORE entries. Lifted out of `Programs/Evm.lean`
  per the file-size guard at the bottom of
  `EvmAsm/Codegen/Programs.lean`: the M22 inline-asm scan loops grew
  the storage section past the per-file cap, so the cluster moves
  into its own submodule following the same pattern as
  `Programs/Noop.lean` (M18).

  Exports one builder:
  - `storageHandlers` — SLOAD (0x54), SSTORE (0x55), TLOAD (0x5c),
    TSTORE (0x5d).

  SLOAD / SSTORE are wired against the pre-loaded slot table (see
  `EvmAsm/Codegen/Dispatch.lean` for the prologue plumbing and
  `scripts/pack-bytecode.py --storage` for the input format).
  TLOAD / TSTORE remain M17-style stack no-ops; a later PR adds a
  per-tx-scoped transient table.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- M17 / M22 storage opcodes (SLOAD/SSTORE/TLOAD/TSTORE).

    **M22 update**: SLOAD (0x54) and SSTORE (0x55) graduate from M17
    no-ops to real persistent storage via the pre-loaded slot table
    extension to the `ziskemu -i` input format. The dispatcher
    prologue copies the input's slot segment into a writable
    `.data` region (`evm_slot_table`, 16 KiB = 256 slots × 64 bytes)
    and records the count at `env.slotTableCountOff = 448`.
    SLOAD / SSTORE inline-asm bodies scan the table linearly.

    TLOAD (0x5c) and TSTORE (0x5d) **remain M17 no-ops** — transient
    storage is per-tx scoped and orthogonal; a later PR adds a
    second table for it.

    ### EVM stack contracts

    - **SLOAD**: pops key (at `[x12..x12+31]`), pushes value to the
      same slot. Net stack delta = 0.
    - **SSTORE**: pops key (at `[x12..x12+31]`) then value (at
      `[x12+32..x12+63]`). Net stack delta = +64 (= -2 words).

    ### Inline-asm conventions

    Both bodies use GNU AS **numeric local labels** (`1:`, `1b`,
    `1f`, …) which are unique-per-use across the emitted file, so
    the same numeric labels appear in both SLOAD and SSTORE
    subroutines without colliding. Scratch registers x14–x17 are
    caller-saved in our dispatcher convention and freely
    overwritten by each handler invocation.

    ### Known limitations

    - **Capacity cap**: 256 slots. Programs that touch more keys
      will overflow the `.data` block. Future PR can grow the
      table or swap in a hash-table backend.
    - **Linear scan**: O(slot_count) per access. Fine for tests
      (<10 slots typical); will be a bottleneck for proving real
      blocks. Hash upgrade ships without ABI / env changes. -/
def storageHandlers : List OpcodeHandlerSpec :=
  [ -- M22 real SLOAD. Scan `evm_slot_table` for a key matching the
    -- stack top; on match, overwrite the stack top with the slot's
    -- value (32 bytes); on no match, write 32 zero bytes (the
    -- default Ethereum SLOAD result for an unset slot).
    { label   := "h_SLOAD"
    , opcodes := [0x54]
    , preBody :=
        "  ld x15, 448(x20)\n" ++         -- x15 = slot_count
        "  la x14, evm_slot_table\n" ++   -- x14 = base
        "  beqz x15, 2f\n" ++             -- empty table → zero result
        "1:\n" ++                         -- scan loop
        "  ld x16, 0(x14)\n" ++           -- compare 32-byte key vs [x12..x12+31]
        "  ld x17, 0(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 8(x14)\n" ++
        "  ld x17, 8(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 16(x14)\n" ++
        "  ld x17, 16(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 24(x14)\n" ++
        "  ld x17, 24(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 32(x14)\n" ++          -- match: copy value into stack top
        "  sd x16, 0(x12)\n" ++
        "  ld x16, 40(x14)\n" ++
        "  sd x16, 8(x12)\n" ++
        "  ld x16, 48(x14)\n" ++
        "  sd x16, 16(x12)\n" ++
        "  ld x16, 56(x14)\n" ++
        "  sd x16, 24(x12)\n" ++
        "  j 4f\n" ++
        "3:\n" ++                         -- no match for this entry — advance
        "  addi x14, x14, 64\n" ++
        "  addi x15, x15, -1\n" ++
        "  bnez x15, 1b\n" ++
        "2:\n" ++                         -- no match anywhere — write zeros
        "  sd x0, 0(x12)\n" ++
        "  sd x0, 8(x12)\n" ++
        "  sd x0, 16(x12)\n" ++
        "  sd x0, 24(x12)\n" ++
        "4:"
    , body    := []
    , tail    := .advanceAndRet 1 }
  , -- M22 real SSTORE. Scan `evm_slot_table` for a key matching the
    -- stack top; on match, overwrite that slot's value with
    -- [x12+32..x12+63]; on no match, append a new (key, value) at
    -- table[slot_count] and increment env.slotTableCountOff. The
    -- net -2 stack pop happens via `ADDI x12, x12, 64` in `body`.
    { label   := "h_SSTORE"
    , opcodes := [0x55]
    , preBody :=
        "  ld x15, 448(x20)\n" ++         -- x15 = slot_count
        "  la x14, evm_slot_table\n" ++   -- x14 = base
        "  beqz x15, 2f\n" ++             -- empty table → append
        "1:\n" ++                         -- scan loop
        "  ld x16, 0(x14)\n" ++
        "  ld x17, 0(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 8(x14)\n" ++
        "  ld x17, 8(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 16(x14)\n" ++
        "  ld x17, 16(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 24(x14)\n" ++
        "  ld x17, 24(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 32(x12)\n" ++          -- match: overwrite value
        "  sd x16, 32(x14)\n" ++
        "  ld x16, 40(x12)\n" ++
        "  sd x16, 40(x14)\n" ++
        "  ld x16, 48(x12)\n" ++
        "  sd x16, 48(x14)\n" ++
        "  ld x16, 56(x12)\n" ++
        "  sd x16, 56(x14)\n" ++
        "  j 4f\n" ++
        "3:\n" ++                         -- no match for this entry — advance
        "  addi x14, x14, 64\n" ++
        "  addi x15, x15, -1\n" ++
        "  bnez x15, 1b\n" ++
        "2:\n" ++                         -- append (key, value) at end
        "  ld x15, 448(x20)\n" ++         -- reload count
        "  slli x16, x15, 6\n" ++         -- offset = count * 64
        "  la x14, evm_slot_table\n" ++
        "  add x14, x14, x16\n" ++        -- x14 = &table[count]
        "  ld x16, 0(x12)\n" ++           -- write key
        "  sd x16, 0(x14)\n" ++
        "  ld x16, 8(x12)\n" ++
        "  sd x16, 8(x14)\n" ++
        "  ld x16, 16(x12)\n" ++
        "  sd x16, 16(x14)\n" ++
        "  ld x16, 24(x12)\n" ++
        "  sd x16, 24(x14)\n" ++
        "  ld x16, 32(x12)\n" ++          -- write value
        "  sd x16, 32(x14)\n" ++
        "  ld x16, 40(x12)\n" ++
        "  sd x16, 40(x14)\n" ++
        "  ld x16, 48(x12)\n" ++
        "  sd x16, 48(x14)\n" ++
        "  ld x16, 56(x12)\n" ++
        "  sd x16, 56(x14)\n" ++
        "  addi x15, x15, 1\n" ++         -- count += 1
        "  sd x15, 448(x20)\n" ++
        "4:"
    , body    := ADDI .x12 .x12 (BitVec.ofNat 12 64)
    , tail    := .advanceAndRet 1 }
  , -- TLOAD (M17 no-op, deferred — transient storage uses a separate
    -- per-tx-scoped table; future PR).
    { label := "h_TLOAD", opcodes := [0x5c]
    , body := SD .x12 .x0 0 ;;
              SD .x12 .x0 8 ;;
              SD .x12 .x0 16 ;;
              SD .x12 .x0 24
    , tail := .advanceAndRet 1 }
  , -- TSTORE (M17 no-op, deferred).
    { label := "h_TSTORE", opcodes := [0x5d]
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 64)
    , tail := .advanceAndRet 1 } ]

end EvmAsm.Codegen
