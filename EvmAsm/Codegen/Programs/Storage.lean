/-
  EvmAsm.Codegen.Programs.Storage

  M24 Option A storage handlers (SLOAD, SSTORE, TLOAD, TSTORE).
  Supersedes M22's `(slotKey, value)` 64-byte-entry slot-table
  approach with the Option A spec from issue #7130: a 128-byte
  per-entry append-only log keyed by `(addrHash, slotKey)` with
  separate `original` and `current` value cells.

  Two logs live in `STATE_TRACKER_AREA`:
    0xa0630000  persistent storage log (SLOAD / SSTORE)
    0xa0830000  transient  storage log (TLOAD / TSTORE)

  Each entry is 128 bytes, 8-byte aligned:
    +0..32   addrHash   (M24: always 0 — single-contract; multi-contract is M25)
    +32..64  slotKey    (EVM-stack byte order: 4 LE u64 limbs, low first)
    +64..96  original   (slot's pre-tx value; 0 for cold non-preloaded)
    +96..128 current    (most recent committed value during this tx)

  Log lengths live in env:
    env+448  persistentLogLengthOff  (live counter; SSTORE increments)
    env+456  persistentLogCheckpointOff  (set at prologue end; restored on REVERT)
    env+464  transientLogLengthOff  (live counter; TSTORE increments; reset on REVERT)

  ## Semantics

  **SLOAD (0x54)** — scan persistent log from end (last-write-
  wins); copy matching `current` to the stack-top slot; default
  zero on miss. Net stack delta = 0.

  **SSTORE (0x55)** — scan from end; append a new entry preserving
  the prior `original` on match (or 0 on miss). **Always appends**
  (never mutates existing entries) — this is what makes REVERT a
  single log-length truncation instead of a journal replay.
  Net stack delta = +64 (pops key + value).

  **TLOAD (0x5c)** — same shape as SLOAD against the transient log.

  **TSTORE (0x5d)** — append-only (no scan; transient storage has
  no gas refund logic, so we never need to read the prior
  `original`). Net stack delta = +64.

  ## Inline asm conventions

  Numeric local labels (`1:`, `1b`, `1f`, …) — unique-per-use,
  reusable across handlers without collision. Scratch registers
  x14–x19 are caller-saved per the dispatcher convention.

  ## Known limitations (documented in CODEGEN.md M24)

  - Single-contract only (`addrHash = 0`); multi-contract is M25.
  - Cold SLOAD misses consult the runtime storage witness when present;
    otherwise they keep the deterministic zero fallback used by synthetic tests.
  - 4 MiB per log = ~32K entries each — well past any test workload.
  - Inline asm, not verified bodies. Verified-loop bodies follow later.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64


/-- Copy the 32-byte EVM stack slot key into natural big-endian order for
    trie lookup helpers. Stack bytes are little-endian u256 limbs;
    `slot_at_index` expects a 32-byte big-endian key. -/
private def sloadWitnessSlotCopy : String :=
  String.intercalate "" <|
    (List.range 32).map fun i =>
      s!"  lbu t2, {31 - i}(x12)\n  sb t2, {i}(t1)\n"

/-- Copy the current contract ADDRESS env word into natural 20-byte address
    order for account trie lookup. The env word uses the same stack-byte
    representation as ADDRESS would push. -/
private def sloadWitnessAddressCopy : String :=
  String.intercalate "" <|
    (List.range 20).map fun i =>
      s!"  lbu t2, {19 - i}(x20)\n  sb t2, {i}(t1)\n"

/-- Copy the helper's natural big-endian u256 result back into the
    dispatcher's stack-word byte order. -/
private def sloadWitnessValueCopy : String :=
  String.intercalate "" <|
    (List.range 32).map fun i =>
      s!"  lbu t1, {31 - i}(t0)\n  sb t1, {i}(x12)\n"

/-- Cold-miss fallback for SLOAD. If the runtime account/storage witness
    trailer is absent, keep the old deterministic zero behavior. If present,
    query `sload_at_header_state_root` and copy its 32-byte output into the
    stack slot. Nonzero structural status leaves the helper's pre-zeroed output
    as zero; block-level witness validation reports malformed witnesses. -/
private def sloadWitnessMissPreBody : String :=
  ".Lsload_witness_miss:\n" ++
  "  ld t0, 584(x20)\n" ++          -- parent header length; zero means no witness context
  "  beqz t0, .Lsload_zero\n" ++
  "  la t1, sload_slot_scratch\n" ++
  sloadWitnessSlotCopy ++
  "  la t1, sload_address_scratch\n" ++
  sloadWitnessAddressCopy ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  sd x13, 16(sp)\n" ++
  "  ld a0, 576(x20)\n" ++         -- header ptr
  "  ld a1, 584(x20)\n" ++         -- header len
  "  la a2, sload_address_scratch\n" ++
  "  la a3, sload_slot_scratch\n" ++
  "  ld a4, 592(x20)\n" ++         -- witness.state ptr
  "  ld a5, 600(x20)\n" ++         -- witness.state len
  "  ld a6, 624(x20)\n" ++         -- witness.storage ptr
  "  ld a7, 632(x20)\n" ++         -- witness.storage len
  "  jal ra, sload_at_header_state_root\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  ld x13, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  la t0, sload_u256\n" ++
  sloadWitnessValueCopy ++
  "  j .Lsload_done\n" ++
  ".Lsload_zero:\n" ++
  "  sd x0, 0(x12)\n" ++
  "  sd x0, 8(x12)\n" ++
  "  sd x0, 16(x12)\n" ++
  "  sd x0, 24(x12)\n" ++
  ".Lsload_done:"

private def sloadWitnessTail : HandlerTail :=
  .custom "  addi x10, x10, 1\n  j .dispatch_loop"

/-- M24 Option A storage handlers. -/
def storageHandlers : List OpcodeHandlerSpec :=
  [ -- M24 real SLOAD. Scan persistent log from end (last-write-
    -- wins); copy matching current to stack top; default 0 on miss.
    { label   := "h_SLOAD"
    , opcodes := [0x54]
    , preBody :=
        "  ld x15, 448(x20)\n" ++         -- x15 = persistent log_length
        "  beqz x15, .Lsload_witness_miss\n" ++
        "  li x14, 0xa0630000\n" ++       -- x14 = log base
        "  slli x16, x15, 7\n" ++         -- x16 = log_length * 128
        "  add x14, x14, x16\n" ++        -- x14 = past last entry
        ".Lsload_scan_loop:\n" ++
        "  addi x14, x14, -128\n" ++      -- x14 = &entry[i]
        -- Compare slotKey [x14+32..x14+64] vs stack key [x12+0..x12+32]
        "  ld x16, 32(x14)\n" ++
        "  ld x17, 0(x12)\n" ++
        "  bne x16, x17, .Lsload_scan_step\n" ++
        "  ld x16, 40(x14)\n" ++
        "  ld x17, 8(x12)\n" ++
        "  bne x16, x17, .Lsload_scan_step\n" ++
        "  ld x16, 48(x14)\n" ++
        "  ld x17, 16(x12)\n" ++
        "  bne x16, x17, .Lsload_scan_step\n" ++
        "  ld x16, 56(x14)\n" ++
        "  ld x17, 24(x12)\n" ++
        "  bne x16, x17, .Lsload_scan_step\n" ++
        -- Match: copy current [x14+96..x14+128] → [x12..x12+32]
        "  ld x16, 96(x14)\n" ++
        "  sd x16, 0(x12)\n" ++
        "  ld x16, 104(x14)\n" ++
        "  sd x16, 8(x12)\n" ++
        "  ld x16, 112(x14)\n" ++
        "  sd x16, 16(x12)\n" ++
        "  ld x16, 120(x14)\n" ++
        "  sd x16, 24(x12)\n" ++
        "  j .Lsload_done\n" ++
        ".Lsload_scan_step:\n" ++
        "  addi x15, x15, -1\n" ++
        "  bnez x15, .Lsload_scan_loop\n" ++
        sloadWitnessMissPreBody
    , body    := []
    , tail    := sloadWitnessTail }
  , -- M24 real SSTORE. Scan persistent log from end; if found, save
    -- &found.original for the append step. Then ALWAYS append a new
    -- 128-byte entry at log[log_length] with (addrHash=0,
    -- slotKey=stack[0..32], original=found_or_zero,
    -- current=stack[32..64]). Increment log_length. Body's
    -- `ADDI x12, x12, 64` does the net -2 stack pop.
    --
    -- Append-only is load-bearing: REVERT rolls back via log-length
    -- truncation, which requires existing entries to be immutable.
    { label   := "h_SSTORE"
    , opcodes := [0x55]
    , preBody :=
        "  li x18, 0\n" ++                -- x18 = "found.original ptr" (0 = not found)
        "  ld x15, 448(x20)\n" ++         -- x15 = log_length
        "  beqz x15, 2f\n" ++             -- empty log → skip scan, append with original=0
        "  li x14, 0xa0630000\n" ++       -- x14 = log base
        "  slli x16, x15, 7\n" ++
        "  add x14, x14, x16\n" ++        -- x14 = past last entry
        "1:\n" ++                         -- scan loop iter
        "  addi x14, x14, -128\n" ++
        "  ld x16, 32(x14)\n" ++
        "  ld x17, 0(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 40(x14)\n" ++
        "  ld x17, 8(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 48(x14)\n" ++
        "  ld x17, 16(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 56(x14)\n" ++
        "  ld x17, 24(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        -- Match: x18 = &found.original (= x14 + 64), break to append
        "  addi x18, x14, 64\n" ++
        "  j 2f\n" ++
        "3:\n" ++                         -- no match this entry — advance
        "  addi x15, x15, -1\n" ++
        "  bnez x15, 1b\n" ++
        "2:\n" ++                         -- append step
        "  ld x15, 448(x20)\n" ++         -- reload current log_length
        "  li x14, 0xa0630000\n" ++
        "  slli x16, x15, 7\n" ++
        "  add x14, x14, x16\n" ++        -- x14 = &log[log_length] (append target)
        -- addrHash = 0 (32 bytes)
        "  sd x0, 0(x14)\n" ++
        "  sd x0, 8(x14)\n" ++
        "  sd x0, 16(x14)\n" ++
        "  sd x0, 24(x14)\n" ++
        -- slotKey from stack [x12+0..x12+32] → [x14+32..x14+64]
        "  ld x16, 0(x12)\n" ++
        "  sd x16, 32(x14)\n" ++
        "  ld x16, 8(x12)\n" ++
        "  sd x16, 40(x14)\n" ++
        "  ld x16, 16(x12)\n" ++
        "  sd x16, 48(x14)\n" ++
        "  ld x16, 24(x12)\n" ++
        "  sd x16, 56(x14)\n" ++
        -- original: copy from x18 if found; else write zeros
        "  beqz x18, 6f\n" ++
        "  ld x16, 0(x18)\n" ++
        "  sd x16, 64(x14)\n" ++
        "  ld x16, 8(x18)\n" ++
        "  sd x16, 72(x14)\n" ++
        "  ld x16, 16(x18)\n" ++
        "  sd x16, 80(x14)\n" ++
        "  ld x16, 24(x18)\n" ++
        "  sd x16, 88(x14)\n" ++
        "  j 7f\n" ++
        "6:\n" ++
        "  sd x0, 64(x14)\n" ++
        "  sd x0, 72(x14)\n" ++
        "  sd x0, 80(x14)\n" ++
        "  sd x0, 88(x14)\n" ++
        "7:\n" ++
        -- current from stack [x12+32..x12+64] → [x14+96..x14+128]
        "  ld x16, 32(x12)\n" ++
        "  sd x16, 96(x14)\n" ++
        "  ld x16, 40(x12)\n" ++
        "  sd x16, 104(x14)\n" ++
        "  ld x16, 48(x12)\n" ++
        "  sd x16, 112(x14)\n" ++
        "  ld x16, 56(x12)\n" ++
        "  sd x16, 120(x14)\n" ++
        -- increment log_length
        "  addi x15, x15, 1\n" ++
        "  sd x15, 448(x20)"
    , body    := ADDI .x12 .x12 (BitVec.ofNat 12 64)
    , tail    := .advanceAndRet 1 }
  , -- M24 real TLOAD. Scan transient log from end; copy matching
    -- current to stack top; default 0 on miss. Same shape as SLOAD
    -- but base 0xa0830000 and length env+464.
    { label   := "h_TLOAD"
    , opcodes := [0x5c]
    , preBody :=
        "  ld x15, 464(x20)\n" ++         -- x15 = transient log_length
        "  beqz x15, 4f\n" ++
        "  li x14, 0xa0830000\n" ++       -- x14 = transient log base
        "  slli x16, x15, 7\n" ++
        "  add x14, x14, x16\n" ++
        "1:\n" ++
        "  addi x14, x14, -128\n" ++
        "  ld x16, 32(x14)\n" ++
        "  ld x17, 0(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 40(x14)\n" ++
        "  ld x17, 8(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 48(x14)\n" ++
        "  ld x17, 16(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 56(x14)\n" ++
        "  ld x17, 24(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 96(x14)\n" ++
        "  sd x16, 0(x12)\n" ++
        "  ld x16, 104(x14)\n" ++
        "  sd x16, 8(x12)\n" ++
        "  ld x16, 112(x14)\n" ++
        "  sd x16, 16(x12)\n" ++
        "  ld x16, 120(x14)\n" ++
        "  sd x16, 24(x12)\n" ++
        "  j 5f\n" ++
        "3:\n" ++
        "  addi x15, x15, -1\n" ++
        "  bnez x15, 1b\n" ++
        "4:\n" ++
        "  sd x0, 0(x12)\n" ++
        "  sd x0, 8(x12)\n" ++
        "  sd x0, 16(x12)\n" ++
        "  sd x0, 24(x12)\n" ++
        "5:"
    , body    := []
    , tail    := .advanceAndRet 1 }
  , -- M24 real TSTORE. Append-only (no scan). Transient storage has
    -- no gas refund logic, so we never need to track / preserve
    -- `original` — every TSTORE just appends a fresh entry. Subsequent
    -- TLOADs scan from end and find the most-recent (correct) value.
    { label   := "h_TSTORE"
    , opcodes := [0x5d]
    , preBody :=
        "  ld x15, 464(x20)\n" ++         -- x15 = transient log_length
        "  li x14, 0xa0830000\n" ++
        "  slli x16, x15, 7\n" ++
        "  add x14, x14, x16\n" ++        -- x14 = append target
        -- addrHash = 0
        "  sd x0, 0(x14)\n" ++
        "  sd x0, 8(x14)\n" ++
        "  sd x0, 16(x14)\n" ++
        "  sd x0, 24(x14)\n" ++
        -- slotKey from stack
        "  ld x16, 0(x12)\n" ++
        "  sd x16, 32(x14)\n" ++
        "  ld x16, 8(x12)\n" ++
        "  sd x16, 40(x14)\n" ++
        "  ld x16, 16(x12)\n" ++
        "  sd x16, 48(x14)\n" ++
        "  ld x16, 24(x12)\n" ++
        "  sd x16, 56(x14)\n" ++
        -- original = 0 (unused for transient)
        "  sd x0, 64(x14)\n" ++
        "  sd x0, 72(x14)\n" ++
        "  sd x0, 80(x14)\n" ++
        "  sd x0, 88(x14)\n" ++
        -- current from stack [x12+32..x12+64]
        "  ld x16, 32(x12)\n" ++
        "  sd x16, 96(x14)\n" ++
        "  ld x16, 40(x12)\n" ++
        "  sd x16, 104(x14)\n" ++
        "  ld x16, 48(x12)\n" ++
        "  sd x16, 112(x14)\n" ++
        "  ld x16, 56(x12)\n" ++
        "  sd x16, 120(x14)\n" ++
        -- increment transient log_length
        "  addi x15, x15, 1\n" ++
        "  sd x15, 464(x20)"
    , body    := ADDI .x12 .x12 (BitVec.ofNat 12 64)
    , tail    := .advanceAndRet 1 } ]

end EvmAsm.Codegen
