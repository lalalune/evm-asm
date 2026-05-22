/-
  EvmAsm.Codegen.Programs

  Registry of programs the codegen tool knows how to emit, each as a
  `BuildUnit` (verified body + optional wrapping).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Evm64.Add.Program
import EvmAsm.Evm64.AddMod.Program
import EvmAsm.Evm64.And.Program
import EvmAsm.Evm64.Byte.Program
import EvmAsm.Evm64.DivMod.Callable
import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Evm64.Dup.Program
import EvmAsm.Evm64.Eq.Program
-- EXP wrapper is parametric over caller-saved registers (x6, x16)
-- that mul_callable clobbers; deferred until upstream lands a
-- fully callee-saved variant. import re-added when wiring lands.
-- import EvmAsm.Evm64.Exp.Program
import EvmAsm.Evm64.Gt.Program
import EvmAsm.Evm64.IsZero.Program
import EvmAsm.Evm64.Lt.Program
import EvmAsm.Evm64.MLoad.Program
import EvmAsm.Evm64.MStore.Program
import EvmAsm.Evm64.MStore8.Program
-- import EvmAsm.Evm64.Multiply.Callable -- only needed by EXP (deferred)
import EvmAsm.Evm64.Multiply.Program
import EvmAsm.Evm64.Not.Program
import EvmAsm.Evm64.Or.Program
import EvmAsm.Evm64.Pop.Program
import EvmAsm.Evm64.Push.Program
import EvmAsm.Evm64.SDiv.Program
import EvmAsm.Evm64.SMod.Program
import EvmAsm.Evm64.Sgt.Program
import EvmAsm.Evm64.Shift.Program
import EvmAsm.Evm64.SignExtend.Program
import EvmAsm.Evm64.Slt.Program
import EvmAsm.Evm64.Sub.Program
import EvmAsm.Evm64.Swap.Program
import EvmAsm.Evm64.Xor.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Dispatch
import EvmAsm.Stateless.Entry
import EvmAsm.Stateless.SSZ.HashTreeRoot.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## ZisK host-IO memory map

Both constants are mirrored from
`zisk/ziskos/entrypoint/src/ziskos_definitions.rs`. ZisK uses
memory-mapped I/O (not ECALL syscalls) for guest-↔-host data.

Empirical input layout (determined by `input_echo` + `ziskemu -i`):

```
INPUT_ADDR + 0..8   = 8 bytes of ziskemu-side metadata (currently zero)
INPUT_ADDR + 8..16  = LE u64 length of the first record
                      (matches the first 8 bytes of the `-i` file)
INPUT_ADDR + 16..   = first record's data, packed verbatim from the
                      `-i` file after the length prefix
```

Matches the SDK's `INPUT_INITIAL_OFFSET = 8` in
`ziskos/entrypoint/src/lib.rs`: the SDK skips those 8 bytes before
reading the first length-prefixed record.
-/

/-- ZisK private-input region. Bytes loaded from `ziskemu -i <file>`
    surface here at runtime. `MAX_INPUT = 0x2000` (8 KiB). -/
def INPUT_ADDR : Word := 0x40000000

/-- Byte offset within the `INPUT_ADDR` region where the first
    length-prefixed record's data starts: skip 8 bytes of ziskemu
    metadata + 8 bytes of u64 length prefix. -/
def INPUT_DATA_OFFSET : Nat := 16

/-- ZisK public-output region. Plain stores here at `OUTPUT_ADDR + 4·k`
    surface in `ziskemu`'s `-o <file>` and `-c` console log.
    `MAX_OUTPUT = 0x1_0000` (64 KiB) per the ABI but ziskemu's default
    `-o` dumps the first 256 bytes (64 × u32 slots). -/
def OUTPUT_ADDR : Word := 0xa0010000

/-! ## smoke — M0 toolchain validation -/

/-- M0 smoke target. Loads two immediates, adds them, falls through to the
    halt stub appended by `emitBuildUnit`. Expected post-state: `x12 = 100`.
    No memory setup or I/O needed; the post-state isn't observable from
    `ziskemu` until M2 wires `write_output`. -/
def smoke : Program :=
  LI .x10 (42 : Word) ;;
  LI .x11 (58 : Word) ;;
  ADD .x12 .x10 .x11

def smokeUnit : BuildUnit := { body := smoke }

/-! ## input_echo — M4 probe for ziskemu's `-i <file>` layout

    Copies 32 bytes from `INPUT_ADDR + 0..32` to `OUTPUT_ADDR + 0..32`.
    Used by `scripts/codegen-input-echo-probe.sh` to determine
    empirically where bytes from a `ziskemu -i <file>` invocation land:
    starting at `INPUT_ADDR + 0` (raw blob) or `INPUT_ADDR + 8` (after
    `INPUT_INITIAL_OFFSET`), and whether ziskemu prepends/skips a
    length prefix. -/
def input_echo : Program :=
  LI .x5 INPUT_ADDR ;;
  LI .x6 OUTPUT_ADDR ;;
  LD .x7 .x5 0  ;; SD .x6 .x7 0  ;;
  LD .x7 .x5 8  ;; SD .x6 .x7 8  ;;
  LD .x7 .x5 16 ;; SD .x6 .x7 16 ;;
  LD .x7 .x5 24 ;; SD .x6 .x7 24

def inputEchoUnit : BuildUnit := { body := input_echo }

/-! ## evm_add — M2 first verified-body end-to-end -/

/-- Operand A as four little-endian 64-bit limbs (low limb first).
    Chosen so the test exercises the limb-0→limb-1 carry: A = 2^64 - 1. -/
def evmAddOperandA : List UInt64 := [0xFFFFFFFFFFFFFFFF, 0, 0, 0]

/-- Operand B as four little-endian 64-bit limbs (low limb first).
    B = 1. -/
def evmAddOperandB : List UInt64 := [0x1, 0, 0, 0]

/-- Expected 256-bit sum, also four LE 64-bit limbs.
    A + B = 2^64, which means limb 0 = 0 and limb 1 = 1, others 0. -/
def evmAddExpectedSum : List UInt64 := [0x0, 0x1, 0, 0]

/-- evm_add expects `x12` to point at 64 bytes of memory: the 32-byte
    operand A at offset 0..32 and operand B at offset 32..64. After it
    runs, `x12` has been advanced by 32 and points at the 32-byte sum
    that overwrote operand B's slot.

    `la x12, operands` is a GNU-as pseudo that expands to
    `auipc x12, %hi(operands)` + `addi x12, x12, %lo(operands)` —
    PC-relative, resolved by the linker after the `.data` section's
    address is known. We keep it as raw asm text because `la` isn't in
    our `Instr` enum. -/
def evmAddPrologue : String :=
  "  la x12, operands"

/-- Copy the 32-byte sum from `mem[x12 .. x12+32]` into ZisK's public
    output region (`OUTPUT_ADDR .. OUTPUT_ADDR+32`). Plain 64-bit
    stores; no syscall (ZisK output is memory-mapped, not ecall-based).

    Lives in the verified Program world: every instruction is in
    `Instr`, so it benefits from `emitInstr` totality and the round-trip
    tests. -/
def evmAddEpilogue : Program :=
  LI .x5 OUTPUT_ADDR ;;
  LD .x6 .x12 0  ;; SD .x5 .x6 0  ;;
  LD .x6 .x12 8  ;; SD .x5 .x6 8  ;;
  LD .x6 .x12 16 ;; SD .x5 .x6 16 ;;
  LD .x6 .x12 24 ;; SD .x5 .x6 24

/-- `.data` section seeded with A and B back-to-back, eight LE doublewords. -/
def evmAddDataSection : String :=
  emitDataLabel ".data" "operands" (evmAddOperandA ++ evmAddOperandB)

def evmAddUnit : BuildUnit := {
  body        := EvmAsm.Evm64.evm_add ++ evmAddEpilogue
  prologueAsm := evmAddPrologue
  dataAsm     := evmAddDataSection
}

/-! ## evm_add_from_input — M4 prover-supplied operands -/

/-- Copy 64 bytes (8 little-endian dwords) from `mem[src]` to `mem[dst]`.
    Caller sets `dst` and `src`; `scratch` is clobbered. Lives in the
    verified `Program` world. -/
def copy64 (dst src scratch : Reg) : Program :=
  LD scratch src 0  ;; SD dst scratch 0  ;;
  LD scratch src 8  ;; SD dst scratch 8  ;;
  LD scratch src 16 ;; SD dst scratch 16 ;;
  LD scratch src 24 ;; SD dst scratch 24 ;;
  LD scratch src 32 ;; SD dst scratch 32 ;;
  LD scratch src 40 ;; SD dst scratch 40 ;;
  LD scratch src 48 ;; SD dst scratch 48 ;;
  LD scratch src 56 ;; SD dst scratch 56

/-- Same wrapping as `evmAddUnit`, but instead of seeding the two
    operands as `.data`, copy them in at runtime from the
    ziskemu-loaded input region (`INPUT_ADDR + INPUT_DATA_OFFSET`).

    Prologue (raw text, since `la` is a pseudo): `la x12, operands_ram`.
    Body: load `INPUT_ADDR + 16` into x5, copy 64 bytes to RAM
    pointed at by x12, run `evm_add`, then `evmAddEpilogue` writes
    the 32-byte sum to `OUTPUT_ADDR`.

    The 64-byte scratch region is a `.data` section reserved as eight
    zero doublewords; ziskemu's loader places `.data` in RAM at
    `0xa0000000` (per `-Tdata=0xa0000000` in `Driver.lean`), so the
    region is writable. -/
def evm_add_from_input : Program :=
  LI .x5 (INPUT_ADDR + (BitVec.ofNat 64 INPUT_DATA_OFFSET)) ;;
  copy64 .x12 .x5 .x6 ++
  EvmAsm.Evm64.evm_add ++
  evmAddEpilogue

def evmAddFromInputPrologue : String :=
  "  la x12, operands_ram"

/-- 64 bytes of writable scratch RAM, label `operands_ram`,
    pre-initialized to zero. The runtime copy from INPUT overwrites it. -/
def evmAddFromInputDataSection : String :=
  emitDataLabel ".data" "operands_ram" (List.replicate 8 (0 : UInt64))

def evmAddFromInputUnit : BuildUnit := {
  body        := evm_add_from_input
  prologueAsm := evmAddFromInputPrologue
  dataAsm     := evmAddFromInputDataSection
}

/-! ## tiny_interp — M5a unrolled tiny EVM interpreter

    Two hand-picked EVM bytecodes laid out as `.data` bytes, executed
    by *chaining* verified opcode `Program`s with explicit `x10`
    advances between handlers. No runtime fetch/decode/dispatch loop
    (deferred to M5b). The point is to validate that verified opcode
    Programs compose under `++` while honoring the `x10` code-pointer
    convention that `evm_push` reads its immediates from.

    Stack layout: 256 bytes of writable scratch ending at label
    `evm_stack_top`. The EVM stack grows downward; the prologue
    initializes `x12 = evm_stack_top` and each `evm_push` decrements
    `x12` by 32 to allocate a new slot. Worst-case depth across both
    test programs is 2 slots = 64 bytes, so 256 leaves comfortable
    headroom. -/

/-- Dispatcher glue between unrolled opcode `Program`s: advance the
    EVM code pointer (`x10`) by the byte width of the opcode just
    executed (`1 + n` for `PUSHn`, `1` for `ADD`/`STOP`).

    In the M5b full dispatch loop this advance is computed inside the
    decoder; M5a inlines it directly so chained verified Programs read
    their PUSH immediates from the right byte. Stays in the verified
    `Program` world. -/
def advancePc (off : Nat) : Program :=
  ADDI .x10 .x10 (BitVec.ofNat 12 off)

/-- Prologue shared by all tiny-interp units. `la x10, evm_code`
    points the EVM code pointer at the start of the bytecode; `la
    x12, evm_stack_top` initializes the EVM stack pointer at the
    high-address end of a 256-byte writable scratch region. -/
def tinyInterpPrologue : String :=
  "  la x10, evm_code\n" ++
  "  la x12, evm_stack_top"

/-- `.data` section: a label `evm_code` holding the bytecode bytes,
    followed by 256 bytes of writable scratch ending at label
    `evm_stack_top`. `bytecodeBytes` is a comma-separated `.byte`
    directive payload (e.g. `"0x60, 0xff, 0x60, 0x01, 0x01, 0x00"`).

    Written as raw asm text rather than `emitDataLabel` because the
    layout is hybrid (`.byte` payload for the bytecode, `.zero` for
    the stack scratch) — `emitDataLabel` only takes `UInt64` dwords. -/
def tinyInterpDataSection (bytecodeBytes : String) : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "evm_code:\n" ++
  s!"  .byte {bytecodeBytes}\n" ++
  ".balign 32\n" ++
  "evm_stack_low:\n" ++
  "  .zero 256\n" ++
  "evm_stack_top:"

/-- M5a test case 1: `PUSH1 0xFF; PUSH1 0x01; ADD; STOP`. Expected
    256-bit sum = `0x100`, which as four LE u64 limbs is
    `[0x100, 0, 0, 0]` — first 8 bytes `00 01 00 00 00 00 00 00`.

    The chain is `Program ++ Program ++ ...`; each `advancePc`
    between opcode handlers is the only dispatcher glue. STOP needs
    no body — falling through to the halt stub appended by
    `emitBuildUnit` is equivalent. -/
def tinyInterpAdd : Program :=
  EvmAsm.Evm64.evm_push 1 ++ advancePc 2 ++
  EvmAsm.Evm64.evm_push 1 ++ advancePc 2 ++
  EvmAsm.Evm64.evm_add  ++ advancePc 1

/-- Bytecode for `tinyInterpAdd`: `60 ff 60 01 01 00`. -/
def tinyInterpAddBytecode : String :=
  "0x60, 0xff, 0x60, 0x01, 0x01, 0x00"

def tinyInterpAddUnit : BuildUnit := {
  body        := tinyInterpAdd ++ evmAddEpilogue
  prologueAsm := tinyInterpPrologue
  dataAsm     := tinyInterpDataSection tinyInterpAddBytecode
}

/-- M5a test case 2: `PUSH1 0x10; PUSH1 0x20; ADD; PUSH1 0x30; ADD;
    STOP`. Expected sum = `0x60`, LE limbs `[0x60, 0, 0, 0]` — first
    8 bytes `60 00 00 00 00 00 00 00`. Exercises chained ADDs and a
    stack-pointer history that walks back up after each ADD. -/
def tinyInterpAdd2 : Program :=
  EvmAsm.Evm64.evm_push 1 ++ advancePc 2 ++
  EvmAsm.Evm64.evm_push 1 ++ advancePc 2 ++
  EvmAsm.Evm64.evm_add  ++ advancePc 1 ++
  EvmAsm.Evm64.evm_push 1 ++ advancePc 2 ++
  EvmAsm.Evm64.evm_add  ++ advancePc 1

/-- Bytecode for `tinyInterpAdd2`: `60 10 60 20 01 60 30 01 00`. -/
def tinyInterpAdd2Bytecode : String :=
  "0x60, 0x10, 0x60, 0x20, 0x01, 0x60, 0x30, 0x01, 0x00"

def tinyInterpAdd2Unit : BuildUnit := {
  body        := tinyInterpAdd2 ++ evmAddEpilogue
  prologueAsm := tinyInterpPrologue
  dataAsm     := tinyInterpDataSection tinyInterpAdd2Bytecode
}

/-! ## divK NOP-splice helpers (used by both M2 standalone DIV/MOD
    wrappers and the M8 dispatcher handlers, so hoisted above the
    M5b registry section that references them) -/

/-- `EvmAsm.Evm64.evm_div` with the NOP "exit PC" at internal index 267
    replaced by a forward `JAL .x0 +304` that skips the 75-instruction
    inline `divK_div128_v4` subroutine and lands at the instruction
    immediately following the body. In the M2 standalone wrapper that
    landing site is the start of `evmAddEpilogue`; in the M8
    dispatcher wrapper (M5b registry) it is the `mv x10, x9` of the
    handler's `x10RestoreAdvance1` tail. -/
def evmDivPatched : Program :=
  (EvmAsm.Evm64.evm_div : List Instr).take 267 ++
  [Instr.JAL .x0 (304 : BitVec 21)] ++
  (EvmAsm.Evm64.evm_div : List Instr).drop 268

/-- `EvmAsm.Evm64.evm_mod` with the same NOP-splice as `evmDivPatched`.
    Same +304 byte offset because the MOD body has the identical
    343-instruction layout (267 main + NOP + 75 subroutine). -/
def evmModPatched : Program :=
  (EvmAsm.Evm64.evm_mod : List Instr).take 267 ++
  [Instr.JAL .x0 (304 : BitVec 21)] ++
  (EvmAsm.Evm64.evm_mod : List Instr).drop 268

/-- `EvmAsm.Evm64.evm_sdiv` with the leading `ADDI .x18 .x1 0`
    save_ra_block removed (413 instructions instead of 414). The
    M9 trampoline handler sets `x18 = &h_SDIV_done` in `preBody`;
    the body's existing `JALR x0, x18, 0` then jumps to our
    restore stub instead of clobbering `x18` with `x1`.

    The first instruction of `evm_sdiv_wrapper` is
    `evm_sdiv_save_ra_block .x18` = `ADDI .x18 .x1 0`
    (`EvmAsm/Evm64/SDiv/Program.lean:180`). Splicing it off lets
    our trampoline target stick. -/
def evmSdivPatched : Program :=
  (EvmAsm.Evm64.evm_sdiv : List Instr).drop 1

/-- `EvmAsm.Evm64.evm_smod` with the same leading-save_ra splice
    as `evmSdivPatched`. SMOD's wrapper is structurally identical
    to SDIV's at the entry/exit boundary (only the conditional-
    negate path differs). -/
def evmSmodPatched : Program :=
  (EvmAsm.Evm64.evm_smod : List Instr).drop 1

/-! ## tiny_interp_dispatch — M5b runtime fetch/decode/dispatch loop

    Same EVM bytecodes as M5a, but routed through an actual RISC-V
    dispatch loop. The dispatcher scaffolding (loop body, 256-entry
    jump table, `h_invalid` fallback, `.exit_label`) now lives in
    `EvmAsm.Codegen.Dispatch`; this section declares only the opcode
    handler registry.

    **Adding a new opcode = adding one `OpcodeHandlerSpec` entry below.**

    Calling convention (informal):
      x10  EVM code pointer  (preserved across handler calls; each
                              handler with `tail := .advanceAndRet n`
                              advances `x10` by `n` before returning)
      x12  EVM stack pointer (handlers update freely; persistent
                              across the loop)
      x1   return address    (clobbered by `jalr ra, ...`; each
                              `advanceAndRet` handler ends in `ret`)
      x5, x6, x7   scratch   (clobbered by both the dispatcher's
                              fetch/lookup *and* the verified handler
                              bodies; the dispatcher reloads from x10
                              and the table base on every iteration,
                              so no preservation needed)

    Coverage (M6b): 81 opcodes wired —
      - **PUSH0..PUSH32** (33) via `pushHandlers`
      - **DUP1..DUP16** (16) via `dupHandlers`
      - **SWAP1..SWAP16** (16) via `swapHandlers`
      - **16 fixed-shape singletons** via `singletonHandlers`:
        SUB, MUL, SIGNEXTEND, AND, OR, XOR, NOT, LT, GT, SLT, SGT,
        EQ, ISZERO, BYTE, SHR, POP — each a parameter-free verified
        `Program` with the standard `<body>` + `addi x10, x10, 1` +
        `ret` ABI.
      - **STOP** via `stopHandler` (jumps to `.exit_label` instead
        of returning to the dispatcher).

    All other opcode bytes fall to `h_invalid` (emitted automatically
    by `emitDispatcherEpilogue`), which takes the same exit path as
    STOP. -/

/-- PUSH0..PUSH32. Opcode byte = `0x5f + n`; the handler advances
    `x10` by `1 + n` (one opcode byte + `n` immediate bytes). -/
def pushHandlers : List OpcodeHandlerSpec :=
  (List.range 33).map (fun n =>
    { label   := s!"h_PUSH{n}"
      opcodes := [0x5f + n]
      body    := EvmAsm.Evm64.evm_push n
      tail    := .advanceAndRet (1 + n) })

/-- DUP1..DUP16. Opcode byte = `0x7f + n` (so DUP1 = `0x80`);
    width 1. `evm_dup n` duplicates the n-th stack item (1-indexed
    from top) onto the top. -/
def dupHandlers : List OpcodeHandlerSpec :=
  (List.range 16).map (fun i =>
    let n := i + 1
    { label   := s!"h_DUP{n}"
      opcodes := [0x7f + n]
      body    := EvmAsm.Evm64.evm_dup n
      tail    := .advanceAndRet 1 })

/-- SWAP1..SWAP16. Opcode byte = `0x8f + n` (so SWAP1 = `0x90`);
    width 1. `evm_swap n` swaps the top with the (n+1)-th stack
    item. -/
def swapHandlers : List OpcodeHandlerSpec :=
  (List.range 16).map (fun i =>
    let n := i + 1
    { label   := s!"h_SWAP{n}"
      opcodes := [0x8f + n]
      body    := EvmAsm.Evm64.evm_swap n
      tail    := .advanceAndRet 1 })

/-- Tail used by handlers whose verified body clobbers `x10` (the
    EVM code pointer in our dispatcher convention). Restores `x10`
    from `x9` (saved via `preBody`), then advances by 1 and returns. -/
private def x10RestoreAdvance1 : HandlerTail :=
  .custom "  mv x10, x9\n  addi x10, x10, 1\n  ret"

/-- Fixed-shape singleton opcodes: parameter-free verified `Program`s
    that fit the standard `<body>` + `addi x10, x10, 1` + `ret` ABI.

    Four bodies (`evm_mul`, `evm_signextend`, `evm_byte`, `evm_shr`)
    use `x10` as an internal scratch / accumulator register, which
    clobbers our dispatcher's preserved EVM code pointer. They carry
    `preBody := "  mv x9, x10"` to stash x10 in x9 (a register no
    verified opcode body touches) and use `x10RestoreAdvance1` as
    the tail to restore before advancing. -/
def singletonHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_ADD"        , opcodes := [0x01], body := EvmAsm.Evm64.evm_add       , tail := .advanceAndRet 1 }
  , { label := "h_MUL"        , opcodes := [0x02], preBody := "  mv x9, x10", body := EvmAsm.Evm64.evm_mul       , tail := x10RestoreAdvance1 }
  , { label := "h_SUB"        , opcodes := [0x03], body := EvmAsm.Evm64.evm_sub       , tail := .advanceAndRet 1 }
  , { label := "h_SIGNEXTEND" , opcodes := [0x0b], preBody := "  mv x9, x10", body := EvmAsm.Evm64.evm_signextend, tail := x10RestoreAdvance1 }
  , { label := "h_LT"         , opcodes := [0x10], body := EvmAsm.Evm64.evm_lt        , tail := .advanceAndRet 1 }
  , { label := "h_GT"         , opcodes := [0x11], body := EvmAsm.Evm64.evm_gt        , tail := .advanceAndRet 1 }
  , { label := "h_SLT"        , opcodes := [0x12], body := EvmAsm.Evm64.evm_slt       , tail := .advanceAndRet 1 }
  , { label := "h_SGT"        , opcodes := [0x13], body := EvmAsm.Evm64.evm_sgt       , tail := .advanceAndRet 1 }
  , { label := "h_EQ"         , opcodes := [0x14], body := EvmAsm.Evm64.evm_eq        , tail := .advanceAndRet 1 }
  , { label := "h_ISZERO"     , opcodes := [0x15], body := EvmAsm.Evm64.evm_iszero    , tail := .advanceAndRet 1 }
  , { label := "h_AND"        , opcodes := [0x16], body := EvmAsm.Evm64.evm_and       , tail := .advanceAndRet 1 }
  , { label := "h_OR"         , opcodes := [0x17], body := EvmAsm.Evm64.evm_or        , tail := .advanceAndRet 1 }
  , { label := "h_XOR"        , opcodes := [0x18], body := EvmAsm.Evm64.evm_xor       , tail := .advanceAndRet 1 }
  , { label := "h_NOT"        , opcodes := [0x19], body := EvmAsm.Evm64.evm_not       , tail := .advanceAndRet 1 }
  , { label := "h_BYTE"       , opcodes := [0x1a], preBody := "  mv x9, x10", body := EvmAsm.Evm64.evm_byte      , tail := x10RestoreAdvance1 }
  , { label := "h_SHR"        , opcodes := [0x1c], preBody := "  mv x9, x10", body := EvmAsm.Evm64.evm_shr       , tail := x10RestoreAdvance1 }
  , { label := "h_POP"        , opcodes := [0x50], body := EvmAsm.Evm64.evm_pop       , tail := .advanceAndRet 1 } ]

/-- M7 memory opcodes. Register-parameterized; the dispatcher
    prologue sets up `x13 = &evm_memory` (see
    `EvmAsm/Codegen/Dispatch.lean`). The scratch registers `x14..x18`
    are caller-saved across the `jalr` from the dispatcher loop;
    nothing else in the registry preserves them.

    Stack-pointer bookkeeping is internal to the verified bodies:
    `evm_mload` is net stack-neutral, while `evm_mstore` and
    `evm_mstore8` each end with `ADDI .x12 .x12 64` so the wrapper
    uses the standard `.advanceAndRet 1` tail. None of the memory
    opcodes touch `x10`, so no `preBody` is needed. -/
def memoryHandlers : List OpcodeHandlerSpec :=
  [ -- MLOAD: pop offset, push value. memBase=x13;
    -- scratch: offReg=x15, byteReg=x16, accReg=x17, addrReg=x18.
    { label   := "h_MLOAD"
      opcodes := [0x51]
      body    := EvmAsm.Evm64.evm_mload .x15 .x16 .x17 .x18 .x13
      tail    := .advanceAndRet 1 }
  , -- MSTORE: pop offset + value, write 32 bytes BE to memory.
    -- valReg=x14 (scratch; placeholder per evm_mstore docstring).
    { label   := "h_MSTORE"
      opcodes := [0x52]
      body    := EvmAsm.Evm64.evm_mstore .x15 .x14 .x16 .x17 .x18 .x13
      tail    := .advanceAndRet 1 }
  , -- MSTORE8: pop offset + value, write 1 byte to memory.
    { label   := "h_MSTORE8"
      opcodes := [0x53]
      body    := EvmAsm.Evm64.evm_mstore8 .x15 .x14 .x18 .x13
      tail    := .advanceAndRet 1 } ]

/-- M8 unsigned division opcodes. Both `evm_div` and `evm_mod` carry
    a 75-instruction `divK_div128_v4` subroutine appended after a
    NOP "exit PC" at body index 267; the `evmDivPatched` /
    `evmModPatched` helpers (above) replace that NOP with `JAL .x0
    (304 : BitVec 21)` so the main path skips the inline subroutine
    and lands at the handler's wrapper tail.

    Both bodies clobber `x10` heavily (Knuth-D quotient accumulator,
    69 references) AND `x9` heavily (loop counter `j`, 94 refs).
    So we can't reuse the standard `x9`-as-save pattern from M6b —
    DIV/MOD save `x10` to **`x14`** instead, with a custom tail that
    restores from `x14`. `x14` is unused by `evm_div` / `evm_mod` (and
    their internal subroutine `divK_div128_v4`), and it's outside the
    dispatcher's preserved set, so clobbering it post-handler is fine.

    Stack-scratch: `evm_div` writes to negative `x12` offsets down to
    `-152` bytes (per `divK_*` scratch layout). The dispatcher's
    256-byte `evm_stack_low` block leaves 192 bytes below `x12`
    after two PUSH ops — comfortably > 152.

    **SDIV / SMOD are deferred to M8.5 / M9.** Their verified bodies
    end with a "saved-ra-ret" pattern (`JALR x0, x18, 0`) that
    bypasses the dispatcher's standard wrapper tail; integrating them
    needs a trampoline-style wrapper (set `x18` to a per-handler
    "restore" stub before the body runs, splice off the body's
    initial save_ra_block). Tracked as the next codegen PR. -/
private def divModTail : HandlerTail :=
  .custom "  mv x10, x14\n  addi x10, x10, 1\n  ret"

def divModHandlers : List OpcodeHandlerSpec :=
  [ { label   := "h_DIV"
      opcodes := [0x04]
      preBody := "  mv x14, x10"
      body    := evmDivPatched
      tail    := divModTail }
  , { label   := "h_MOD"
      opcodes := [0x06]
      preBody := "  mv x14, x10"
      body    := evmModPatched
      tail    := divModTail } ]

/-- Tail for SDIV/SMOD: restore `x10` from `x14`, advance the EVM
    code pointer by 1, then jump directly to `.dispatch_loop`
    rather than `ret`-ing. The standard `ret` (= `jalr x0, x1, 0`)
    won't work for these handlers because the wrapper's inner
    `JAL .x1` into `evm_div_callable_v4` / `evm_mod_callable_v4`
    clobbers `x1` mid-body — `x1` no longer holds the dispatcher's
    continuation by the time control reaches this tail. -/
private def signedDivModTail : HandlerTail :=
  .custom "  mv x10, x14\n  addi x10, x10, 1\n  j .dispatch_loop"

/-- M9 signed division handlers: SDIV (0x05) and SMOD (0x07).

    Different wrapping than M8's DIV/MOD because `evm_sdiv` /
    `evm_smod` end with a "saved-ra-ret" pattern (`JALR x0, x18, 0`
    after the wrapper copies `x1` into `x18` at entry) — this
    bypasses the dispatcher's standard `.advanceAndRet` / `divModTail`
    tail entirely.

    **Trampoline pattern:**
    1. `preBody` saves `x10` to `x14` (same register convention as
       M8 DIV/MOD; `x14` is untouched by both the SDIV/SMOD
       wrappers and the inner `evm_div_callable_v4` /
       `evm_mod_callable_v4`) AND loads `x18` with the address of the
       per-handler `postBodyLabel` stub via `la x18, h_<NAME>_done`.
    2. The verified body is `evmSdivPatched` / `evmSmodPatched`,
       which is the verified `evm_sdiv` / `evm_smod` with the
       leading `ADDI .x18 .x1 0` save_ra_block dropped. Without
       the splice, that instruction would overwrite the `x18` we
       just set up in `preBody`.
    3. When the body's `JALR x0, x18, 0` fires (mid-body, at the
       wrapper's `evm_sdiv_saved_ra_ret_block`), control jumps to
       our `postBodyLabel` stub (one of `h_SDIV_done` /
       `h_SMOD_done`).
    4. `signedDivModTail` restores `x10` from `x14`, advances the
       EVM PC, then `j .dispatch_loop` — bypassing the standard
       `ret` because the inner `JAL` into the divider clobbered
       `x1` (so `ret` would jump to garbage).

    Both canonical signed wrappers now route through the v4 callable
    divider/modulo bodies; the trampoline shape is unchanged by that
    migration because the saved-ra return convention is the same. -/
def signedDivModHandlers : List OpcodeHandlerSpec :=
  [ { label         := "h_SDIV"
      opcodes       := [0x05]
      preBody       := "  mv x14, x10\n  la x18, h_SDIV_done"
      body          := evmSdivPatched
      postBodyLabel := some "h_SDIV_done"
      tail          := signedDivModTail }
  , { label         := "h_SMOD"
      opcodes       := [0x07]
      preBody       := "  mv x14, x10\n  la x18, h_SMOD_done"
      body          := evmSmodPatched
      postBodyLabel := some "h_SMOD_done"
      tail          := signedDivModTail } ]

/-! ## M10 self-calling opcode — ADDMOD (0x08)

    `evm_addmod` is parametric over a JAL byte offset that targets
    a callable variant of another handler (`evm_mod_callable_v4`).
    The natural composition is `<wrapper>(<offset>) ++ <callable>`
    — the callable is inlined in the same handler subroutine; the
    offset is chosen so the wrapper's JAL lands on the callable's
    first instruction.

    Unlike SDIV/SMOD's M9 trampoline, ADDMOD doesn't have a
    saved-ra-ret pattern. It DOES clobber `x1` (via the inner
    `JAL .x1` into the callable), so the wrapper tail must use
    `j .dispatch_loop` instead of `ret` — reusing M9's
    `signedDivModTail` helper. It also clobbers `x10` via the
    inline mod callable, so `preBody` saves `x10` to `x14`.

    EXP (0x0a) was planned for this milestone but is deferred. The
    `evm_exp_msb_saved_bit_two_mul_fixed` wrapper uses `x6` and
    `x16` as per-limb counter / limb pointer, but those are LP64
    caller-saved registers — `mul_callable` clobbers `x6` 39 times
    per call. The "fix" only addresses `x19` (cursor) clobber, not
    `x6`/`x16`. A complete fix requires a `_fixed_fixed` variant
    using callee-saved registers (e.g. `x20`/`x21`) for the
    per-limb counter and limb pointer; until that lands upstream,
    EXP can't run through the dispatcher. -/

/-- ADDMOD handler body. **Skips `evm_addmod_epilogue` deliberately**:
    the verified `evm_addmod` composes prologue + phase1_carry +
    phase2_reduce + epilogue, but the epilogue does `ADDI x12, x12, 32`
    on TOP of the `ADDI x12, x12, 32` already done by
    `divK_mod_epilogue` inside `evm_mod_callable_v4`. Including both
    over-advances `x12` by 32, leaving the result outside the EVM
    stack. (The verified `evm_addmod` is a slice 3a skeleton; slice
    3c hasn't been implemented.)

    Composition:
      - prologue (`evm_add`): 30 instr (120 B), pops 2 / pushes 1, x12 += 32
      - phase1_carry: 1 instr (4 B), `ADDI x7, x5, 0`
      - phase2_reduce 8: 1 instr (4 B), `JAL .x1 +8` → mod_callable_v4
      - skip-JAL: 1 instr (4 B), `JAL .x0 +1372` → past callable to tail
      - `evm_mod_callable_v4`: 343 instr (1372 B), advances x12 by 32

    Net x12 advance: 32 (prologue) + 32 (callable) = 64 B (= 3 pops -
    1 push). ✓

    modOff for phase2_reduce: JAL at byte 124, callable at byte 132,
    offset = 8 bytes. Skip-JAL at byte 128, target = byte 128 + 1376
    = 1504 (end of body, just past the callable), offset = 1376 bytes
    (= 4 bytes for the skip-JAL itself + 1372 bytes for the callable). -/
def evmAddmodComposed : Program :=
  EvmAsm.Evm64.evm_addmod_prologue ;;
  EvmAsm.Evm64.evm_addmod_phase1_carry ;;
  EvmAsm.Evm64.evm_addmod_phase2_reduce 8 ;;
  single (Instr.JAL .x0 (1376 : BitVec 21)) ;;
  EvmAsm.Evm64.evm_mod_callable_v4

/-- M10 self-calling handlers. Currently just ADDMOD; EXP is
    deferred (see the milestone-header comment). Reuses
    `signedDivModTail` because the wrapper's inner `JAL .x1` into
    the inline callable clobbers `x1`, so the standard `ret` (=
    `jalr x0, x1, 0`) would jump to garbage. -/
def selfCallingHandlers : List OpcodeHandlerSpec :=
  [ { label         := "h_ADDMOD"
      opcodes       := [0x08]
      preBody       := "  mv x14, x10"
      body          := evmAddmodComposed
      tail          := signedDivModTail } ]

/-- STOP: transitions out of the dispatcher loop instead of returning
    to it. The body is empty; the dispatcher's `jalr` lands on
    `h_STOP:` which jumps to `.exit_label`. -/
def stopHandler : OpcodeHandlerSpec :=
  { label   := "h_STOP"
    opcodes := [0x00]
    body    := []
    tail    := .custom "  j .exit_label" }

/-- M5b dispatch registry. Order doesn't affect correctness — the
    256-entry jump table is built by `jumpTargetLabel`, which scans
    the list for a spec whose `opcodes` contains the byte. -/
def tinyInterpRegistry : List OpcodeHandlerSpec :=
  pushHandlers ++ dupHandlers ++ swapHandlers ++ singletonHandlers ++
  memoryHandlers ++ divModHandlers ++ signedDivModHandlers ++
  selfCallingHandlers ++ [stopHandler]

def tinyInterpDispatchAddUnit : BuildUnit :=
  buildDispatchUnit tinyInterpRegistry evmAddEpilogue tinyInterpAddBytecode

def tinyInterpDispatchAdd2Unit : BuildUnit :=
  buildDispatchUnit tinyInterpRegistry evmAddEpilogue tinyInterpAdd2Bytecode

/-! ## runtime_dispatcher — M8.5 runtime-bytecode dispatcher

    Same `tinyInterpRegistry` and `evmAddEpilogue` as the
    `tiny_interp_dispatch_*` units, but the dispatcher prologue
    reads `x10` from `INPUT_ADDR + INPUT_DATA_OFFSET = 0x40000010`
    instead of an in-`.data` label. One ELF runs any bytecode; the
    bash test harness packs each per-case bytecode into a
    ziskemu `-i <file>` payload and reuses the same dispatcher
    ELF for every case.

    See `EvmAsm/Codegen/Dispatch.lean` for `buildRuntimeDispatchUnit`
    and the runtime prologue/data-section helpers. -/
def runtimeDispatcherUnit : BuildUnit :=
  buildRuntimeDispatchUnit tinyInterpRegistry evmAddEpilogue

/-! ## evm_div — M2 first DIV end-to-end through ziskemu

    NOTE: `evm_div` is not yet proven correct in Lean — the spec
    composition (Phase 2a, see bead `evm-asm-9iqmw`) is still in
    flight. The scripts under `scripts/codegen-evm_div*` provide
    empirical confirmation by running the codegen output on ziskemu.

    `evm_div` shares ADD's `x12`-points-at-operands convention: before,
    `x12 = sp` with dividend `a` at `sp+0..32` and divisor `b` at
    `sp+32..64`; after, the quotient lives at `sp+32..64` and `x12 = sp+32`.
    So `evmAddEpilogue` (which copies `[x12, x12+32)` to `OUTPUT_ADDR`)
    works unchanged for DIV.

    Unlike ADD, `evm_div` also uses scratch at "negative" offsets from
    `x12` — the body encodes them as the unsigned bit pattern of
    12-bit signed negatives (`3936..4088 ≡ -160..-8`). The `.data`
    layout therefore places a 256-byte zero-filled `div_scratch:` block
    *before* the `operands:` label so that `x12 - 160..-8` lands in
    writable RAM.

    `evm_div`'s body lays out main code, then a NOP "exit PC" at index
    267, then the 75-instruction `divK_div128_v4` subroutine. When the
    main path completes (via `divK_div_epilogue`'s JAL +24 to the NOP)
    it falls through into the subroutine instead of halting — and the
    codegen's halt stub, appended after the body, is unreachable. We
    splice the body to replace that NOP with `JAL .x0 +304`, which
    skips over the 75 subroutine instructions (75·4 + 4 = 304 bytes)
    and lands at the start of `evmAddEpilogue`. The in-loop callers of
    the subroutine still use the original `jal x2, +560` offsets, which
    remain correct because we only replaced the NOP, not the
    subroutine's position relative to its callers. -/

/-- Dividend as four LE limbs. 2^64, exercises the phase-B n=2 cascade
    plus the normalize/loop path (not an early-exit). -/
def evmDivDividend : List UInt64 := [0, 1, 0, 0]

/-- Divisor as four LE limbs. 2. -/
def evmDivDivisor : List UInt64 := [2, 0, 0, 0]

/-- Expected quotient = 2^64 / 2 = 2^63, LE limbs. The actual on-disk
    expected hex is asserted by `scripts/codegen-evm_div-check.sh`; this
    constant is documentation. -/
def evmDivExpectedQuotient : List UInt64 := [0x8000000000000000, 0, 0, 0]

/-- Same `la x12, operands` as ADD — points the EVM stack pointer at
    the dividend, with the divisor packed directly after it. -/
def evmDivPrologue : String :=
  "  la x12, operands"

/-- `.data` section: 256 bytes of zero-filled scratch labeled
    `div_scratch:` *first*, then `operands:` with dividend ++ divisor
    (eight LE dwords). The scratch comes first so that `x12 - 160..-8`
    (the DIV body's scratch range, encoded as unsigned 12-bit offsets
    `3936..4088`) falls inside writable RAM.

    Written as raw asm rather than `emitDataLabel` because the layout
    mixes `.zero` and `.dword`. -/
def evmDivDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands:\n" ++
  String.intercalate "\n"
    ((evmDivDividend ++ evmDivDivisor).map emitDword)

def evmDivUnit : BuildUnit := {
  body        := evmDivPatched ++ evmAddEpilogue
  prologueAsm := evmDivPrologue
  dataAsm     := evmDivDataSection
}

/-! ## evm_div_from_input — M4 prover-supplied DIV operands

    Same wrapping as `evmDivUnit`, but operands arrive at runtime from
    the ziskemu `-i` input region instead of being baked into `.data`.
    Lets one ELF cover many test vectors. Layout is identical to
    `evm_add_from_input` plus the 256 B `div_scratch:` block in front
    of `operands_ram:`. -/

def evm_div_from_input : Program :=
  LI .x5 (INPUT_ADDR + (BitVec.ofNat 64 INPUT_DATA_OFFSET)) ;;
  copy64 .x12 .x5 .x6 ++
  evmDivPatched ++
  evmAddEpilogue

def evmDivFromInputPrologue : String :=
  "  la x12, operands_ram"

/-- `.data` section: 256 B of writable `div_scratch:` *before*
    `operands_ram:` (64 B reserved zero, overwritten at runtime). -/
def evmDivFromInputDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands_ram:\n" ++
  "  .zero 64"

def evmDivFromInputUnit : BuildUnit := {
  body        := evm_div_from_input
  prologueAsm := evmDivFromInputPrologue
  dataAsm     := evmDivFromInputDataSection
}

/-! ## evm_mod — M2 first MOD end-to-end through ziskemu

    Same calling convention and scratch layout as `evm_div`. `evm_mod`
    differs only in the epilogue: `divK_mod_epilogue` copies `u[0..3]`
    (the de-normalized remainder) to `sp+32..64` instead of `q[0..3]`.
    The body structure (NOP "exit PC" at index 267 followed by the
    75-instruction `divK_div128_v4` subroutine) is identical, so the
    same NOP-splice fix applies. Like `evm_div`, `evm_mod` is not yet
    proven correct in Lean — the scripts under `scripts/codegen-evm_mod*`
    provide empirical confirmation by running on ziskemu. -/

/-- Dividend as four LE limbs. 2^64, exercises the phase-B n=1 cascade
    on the divisor (b=3, limb 0 only) plus the loop body. -/
def evmModDividend : List UInt64 := [0, 1, 0, 0]

/-- Divisor as four LE limbs. 3. -/
def evmModDivisor : List UInt64 := [3, 0, 0, 0]

/-- Expected remainder = 2^64 mod 3 = 1 (since 2^64 = 3·6148914691236517205 + 1). -/
def evmModExpectedRemainder : List UInt64 := [1, 0, 0, 0]

def evmModPrologue : String :=
  "  la x12, operands"

def evmModDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands:\n" ++
  String.intercalate "\n"
    ((evmModDividend ++ evmModDivisor).map emitDword)

def evmModUnit : BuildUnit := {
  body        := evmModPatched ++ evmAddEpilogue
  prologueAsm := evmModPrologue
  dataAsm     := evmModDataSection
}

/-! ## evm_mod_from_input — M4 prover-supplied MOD operands

    Same wrapping as `evmModUnit`, but operands arrive at runtime from
    the ziskemu `-i` input region (mirrors `evm_div_from_input`). -/

def evm_mod_from_input : Program :=
  LI .x5 (INPUT_ADDR + (BitVec.ofNat 64 INPUT_DATA_OFFSET)) ;;
  copy64 .x12 .x5 .x6 ++
  evmModPatched ++
  evmAddEpilogue

def evmModFromInputPrologue : String :=
  "  la x12, operands_ram"

def evmModFromInputDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands_ram:\n" ++
  "  .zero 64"

def evmModFromInputUnit : BuildUnit := {
  body        := evm_mod_from_input
  prologueAsm := evmModFromInputPrologue
  dataAsm     := evmModFromInputDataSection
}

/-! ## evm_sdiv_v4 — signed DIV end-to-end through ziskemu

    `evm_sdiv_v4` uses the SDIV sign-handling wrapper and the corrected v4
    unsigned callable divider. Unlike standalone DIV/MOD, the wrapper returns
    via the caller return address saved in `x18`, so codegen seeds `x1` with a
    raw-asm label immediately after the verified body. -/

def evmSdivV4Dividend : List UInt64 := [0xffffffffffffff9c, 0xffffffffffffffff,
  0xffffffffffffffff, 0xffffffffffffffff]

def evmSdivV4Divisor : List UInt64 := [7, 0, 0, 0]

def evmSdivV4ExpectedQuotient : List UInt64 := [0xfffffffffffffff2,
  0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff]

def evmSdivV4Prologue : String :=
  "  la x1, after_sdiv\n" ++
  "  la x12, operands"

def evmSdivV4Epilogue : String :=
  "after_sdiv:\n" ++ emitProgram evmAddEpilogue

def evmSdivV4DataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands:\n" ++
  String.intercalate "\n"
    ((evmSdivV4Dividend ++ evmSdivV4Divisor).map emitDword)

def evmSdivV4Unit : BuildUnit := {
  body        := EvmAsm.Evm64.evm_sdiv_v4
  prologueAsm := evmSdivV4Prologue
  epilogueAsm := evmSdivV4Epilogue
  dataAsm     := evmSdivV4DataSection
}

/-! ## evm_sdiv_v4_from_input — prover-supplied signed DIV operands -/

def evm_sdiv_v4_from_input : Program :=
  LI .x5 (INPUT_ADDR + (BitVec.ofNat 64 INPUT_DATA_OFFSET)) ;;
  copy64 .x12 .x5 .x6 ++
  EvmAsm.Evm64.evm_sdiv_v4

def evmSdivV4FromInputPrologue : String :=
  "  la x1, after_sdiv\n" ++
  "  la x12, operands_ram"

def evmSdivV4FromInputDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands_ram:\n" ++
  "  .zero 64"

def evmSdivV4FromInputUnit : BuildUnit := {
  body        := evm_sdiv_v4_from_input
  prologueAsm := evmSdivV4FromInputPrologue
  epilogueAsm := evmSdivV4Epilogue
  dataAsm     := evmSdivV4FromInputDataSection
}

/-! ## evm_smod_v4 — signed MOD end-to-end through ziskemu -/

def evmSmodV4Dividend : List UInt64 := [0xffffffffffffff9c, 0xffffffffffffffff,
  0xffffffffffffffff, 0xffffffffffffffff]

def evmSmodV4Divisor : List UInt64 := [7, 0, 0, 0]

def evmSmodV4ExpectedRemainder : List UInt64 := [0xfffffffffffffffd,
  0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff]

def evmSmodV4Prologue : String :=
  "  la x1, after_smod\n" ++
  "  la x12, operands"

def evmSmodV4Epilogue : String :=
  "after_smod:\n" ++ emitProgram evmAddEpilogue

def evmSmodV4DataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands:\n" ++
  String.intercalate "\n"
    ((evmSmodV4Dividend ++ evmSmodV4Divisor).map emitDword)

def evmSmodV4Unit : BuildUnit := {
  body        := EvmAsm.Evm64.evm_smod
  prologueAsm := evmSmodV4Prologue
  epilogueAsm := evmSmodV4Epilogue
  dataAsm     := evmSmodV4DataSection
}

def evmSmodUnit : BuildUnit := evmSmodV4Unit

/-! ## evm_smod_v4_from_input — prover-supplied signed MOD operands -/

def evm_smod_v4_from_input : Program :=
  LI .x5 (INPUT_ADDR + (BitVec.ofNat 64 INPUT_DATA_OFFSET)) ;;
  copy64 .x12 .x5 .x6 ++
  EvmAsm.Evm64.evm_smod

def evm_smod_from_input : Program := evm_smod_v4_from_input

def evmSmodV4FromInputPrologue : String :=
  "  la x1, after_smod\n" ++
  "  la x12, operands_ram"

def evmSmodV4FromInputDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands_ram:\n" ++
  "  .zero 64"

def evmSmodV4FromInputUnit : BuildUnit := {
  body        := evm_smod_v4_from_input
  prologueAsm := evmSmodV4FromInputPrologue
  epilogueAsm := evmSmodV4Epilogue
  dataAsm     := evmSmodV4FromInputDataSection
}

def evmSmodFromInputUnit : BuildUnit := {
  body        := evm_smod_from_input
  prologueAsm := evmSmodV4FromInputPrologue
  epilogueAsm := evmSmodV4Epilogue
  dataAsm     := evmSmodV4FromInputDataSection
}

/-! ## stateless_guest — PR2 SSZ-output stub

    See the definition of `statelessGuestUnit` below
    (after `zkvmKeccak256Function`, which the epilogue inlines). -/

/-! ## zisk_keccak_probe — PR-K1 ziskemu Keccak-f[1600] intrinsic probe

    Emits a raw-asm probe that triggers ziskemu's built-in
    Keccak-f[1600] accelerator (`_opcode_keccak` in
    `~/.zisk/zisk/emulator-asm/src/emu.c:507`). The accelerator is
    invoked by writing the state pointer into a non-standard CSR at
    address 0x800 -- which is the syscall ID the Zisk compiler
    expects, per `ziskos/entrypoint/src/syscalls/keccakf.rs` (uses
    `csrs 0x800, <reg>` via the `ziskos_syscall!` macro).

    GNU-as `csrs csr, rs1` expands to `csrrs x0, csr, rs1`. The
    32-bit encoding for `csrs 0x800, a0`:

      csr(0x800)    rs1(x10=01010)  f3(010)  rd(x0)    op(0x73)
      [31..20]      [19..15]        [14..12] [11..7]   [6..0]
      = 0x80052073

    We emit this as a raw `.4byte` directive rather than the
    `csrs` mnemonic so the existing
    `riscv64-unknown-elf-as -march=rv64imac` toolchain string
    works without enabling the `Zicsr` extension. The 32-bit value
    is what `as -march=rv64imac_zicsr` produces for the same
    mnemonic; pinning it here is the whole point of PR-K1.

    Probe sequence:
      la a0, zisk_keccak_state    # state pointer
      .4byte 0x80052073           # csrs 0x800, a0 -> _opcode_keccak
      <copy 200 bytes to OUTPUT_ADDR>
      <halt>

    Verified Program body is a single NOP -- everything observable
    happens in raw asm, so the verified semantics carry no claim
    about the probe yet. PR-K2 wires this through verified Instrs
    once the CSR instruction is added to `Rv64.Instr`. -/

/-- Asm prologue: probe the keccak intrinsic and stream the
    post-permutation 200-byte state to ziskemu's public-output
    region. Hard-codes `OUTPUT_ADDR = 0xa0010000` (mirrors the
    constant above). -/
def ziskKeccakProbePrologue : String :=
  "  la a0, zisk_keccak_state\n" ++
  "  .4byte 0x80052073           # csrs 0x800, a0\n" ++
  "  li t0, 0xa0010000\n" ++
  "  li t1, 25\n" ++
  ".Lzkp_copy_loop:\n" ++
  "  ld t2, 0(a0)\n" ++
  "  sd t2, 0(t0)\n" ++
  "  addi a0, a0, 8\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, .Lzkp_copy_loop"

/-- `.data` section: 200 zero bytes labeled `zisk_keccak_state`.
    Lands in ziskemu RAM (0xa0000000..0xc0000000) via the standard
    `-Tdata=0xa0000000` link flag from `Codegen/Driver.lean`. -/
def ziskKeccakProbeDataSection : String :=
  ".section .data\n" ++
  "zisk_keccak_state:\n" ++
  "  .zero 200"

def ziskKeccakProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskKeccakProbePrologue
  dataAsm     := ziskKeccakProbeDataSection
}

/-! ## zisk_keccak256_empty — PR-K2 keccak256 sponge over empty input

    First wrapper around PR-K1's intrinsic: the keccak256 sponge
    construction applied to a zero-byte message. Concretely:

      1. Zero the 200-byte state buffer.
      2. Pad: set byte 0 = 0x01, byte 135 = 0x80
         (Ethereum Keccak padding; rate = 1088 bits = 136 bytes).
      3. Trigger `_opcode_keccak` (csrs 0x800, a0).
      4. Copy the first 32 bytes of state to OUTPUT_ADDR -- those
         are the 256-bit hash digest.

    Expected output (32 bytes):
      c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

    Matches the canonical keccak256("") hash and the value produced
    by `eth_utils.keccak(b"")` / `Cryptodome.Hash.keccak.new(...).digest()`.
    This is the simplest possible exercise of the full sponge wrapper:
    no input blocks to absorb, just the final padded block. Future
    PRs extend this to one-block ("abc") and multi-block inputs. -/

/-- Asm prologue: zero state, apply Ethereum Keccak padding for the
    empty-message case, call the keccak-f intrinsic, copy the 32-byte
    digest to OUTPUT_ADDR. -/
def ziskKeccak256EmptyPrologue : String :=
  "  la s0, k256e_state\n" ++
  "  # zero state (25 × u64)\n" ++
  "  mv t3, s0\n" ++
  "  li t4, 25\n" ++
  ".Lk256e_zero:\n" ++
  "  sd zero, 0(t3)\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lk256e_zero\n" ++
  "  # apply Ethereum Keccak padding to empty message\n" ++
  "  li t0, 0x01\n" ++
  "  sb t0, 0(s0)              # state[0] = 0x01\n" ++
  "  li t0, 0x80\n" ++
  "  sb t0, 135(s0)            # state[135] = 0x80\n" ++
  "  # call keccak-f via PR-K1 intrinsic (csrs 0x800, a0)\n" ++
  "  mv a0, s0\n" ++
  "  .4byte 0x80052073\n" ++
  "  # copy first 32 bytes of state to OUTPUT_ADDR\n" ++
  "  li t0, 0xa0010000         # OUTPUT_ADDR\n" ++
  "  ld t1, 0(s0);  sd t1, 0(t0)\n" ++
  "  ld t1, 8(s0);  sd t1, 8(t0)\n" ++
  "  ld t1, 16(s0); sd t1, 16(t0)\n" ++
  "  ld t1, 24(s0); sd t1, 24(t0)"

def ziskKeccak256EmptyDataSection : String :=
  ".section .data\n" ++
  "k256e_state:\n" ++
  "  .zero 200"

def ziskKeccak256EmptyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskKeccak256EmptyPrologue
  dataAsm     := ziskKeccak256EmptyDataSection
}

/-! ## zisk_keccak256_abc — PR-K2a single-block input

    Same sponge skeleton as PR-K2 but with the 3-byte input "abc"
    (RFC test vector) XORed into state positions 0..3 before the
    padding bytes (`0x01` at byte 3, `0x80` at byte 135). Single
    absorb block, single keccak-f call, then squeeze.

    Expected:
      keccak256(b"abc") =
        4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45

    Demonstrates the single-block absorb path (input ≤ rate). The
    multi-block path lands in a follow-up. -/
def ziskKeccak256AbcPrologue : String :=
  "  la s0, k256a_state\n" ++
  "  # zero state\n" ++
  "  mv t3, s0\n" ++
  "  li t4, 25\n" ++
  ".Lk256a_zero:\n" ++
  "  sd zero, 0(t3)\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lk256a_zero\n" ++
  "  # input \"abc\" at state[0..3]\n" ++
  "  li t0, 0x61; sb t0, 0(s0)\n" ++
  "  li t0, 0x62; sb t0, 1(s0)\n" ++
  "  li t0, 0x63; sb t0, 2(s0)\n" ++
  "  # Ethereum Keccak padding (length 3 < rate 136)\n" ++
  "  li t0, 0x01; sb t0, 3(s0)\n" ++
  "  li t0, 0x80; sb t0, 135(s0)\n" ++
  "  # call keccak-f\n" ++
  "  mv a0, s0\n" ++
  "  .4byte 0x80052073\n" ++
  "  # squeeze 32 bytes to OUTPUT_ADDR\n" ++
  "  li t0, 0xa0010000\n" ++
  "  ld t1, 0(s0);  sd t1, 0(t0)\n" ++
  "  ld t1, 8(s0);  sd t1, 8(t0)\n" ++
  "  ld t1, 16(s0); sd t1, 16(t0)\n" ++
  "  ld t1, 24(s0); sd t1, 24(t0)"

def ziskKeccak256AbcDataSection : String :=
  ".section .data\n" ++
  "k256a_state:\n" ++
  "  .zero 200"

def ziskKeccak256AbcProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskKeccak256AbcPrologue
  dataAsm     := ziskKeccak256AbcDataSection
}

/-! ## zisk_sha256_probe_le — PR-K15 SHA-256 intrinsic probe (LE-u32 layout)

    Earlier PR-S1 v1 (`task #17`) tried the SHA-256 intrinsic at
    CSR `0x805` with the 0.15.0-documented BE-per-u64 packing
    (state[0] = (h0 BE-u32 << 32) | h1 BE-u32, stored LE as a
    single u64). Output didn't match `sha256(b"")`.

    Hypothesis: the installed ziskemu (0.18.0) uses a different
    state packing -- specifically LE-u32 within u64 (state bytes
    are u32 BE in spec, stored as LE u32s -- so the 64-bit memory
    layout is `LE(h0) || LE(h1)` = bytes `67 e6 09 6a 85 ae 67 bb`
    for the first u64). As a u64 value this is
    `0xbb67ae856a09e667`.

    Probe re-runs the empty-message compression with this
    alternative layout. If it matches `sha256(b"")`, the 0.18.0
    intrinsic layout is pinned; if not, document further.

    Expected on success (SHA-256("") in LE-u32 packed memory):
      67 e6 09 6a 85 ae 67 bb 72 f3 6e 3c 3a f5 4f a5
      7f 52 0e 51 8c 68 05 9b ab d9 83 1f 19 cd e0 5b
    Then post-compression state should be SHA-256("")'s words
    packed the same way:
      sha256(empty) = e3 b0 c4 42 98 fc 1c 14 9a fb f4 c8 99 6f
                      b9 24 27 ae 41 e4 64 9b 93 4c a4 95 99 1b
                      78 52 b8 55
    As LE-u32 within u64 (per-byte memory order):
      42 c4 b0 e3 14 1c fc 98 c8 f4 fb 9a 24 b9 6f 99
      e4 41 ae 27 4c 93 9b 64 1b 99 95 a4 55 b8 52 78
-/
def ziskSha256ProbeLePrologue : String :=
  "  la a0, sha256_le_params\n" ++
  "  .4byte 0x80552073           # csrs 0x805, a0\n" ++
  "  # copy 32-byte post-compression state to OUTPUT_ADDR\n" ++
  "  la t0, sha256_le_state\n" ++
  "  li t1, 0xa0010000\n" ++
  "  ld t2, 0(t0);  sd t2, 0(t1)\n" ++
  "  ld t2, 8(t0);  sd t2, 8(t1)\n" ++
  "  ld t2, 16(t0); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t0); sd t2, 24(t1)"

def ziskSha256ProbeLeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_le_state:\n" ++
  "  # state[0..4] = LE-u32-pack (each u32 stored LE in memory)\n" ++
  "  .quad 0xbb67ae856a09e667    # LE(h0) || LE(h1)\n" ++
  "  .quad 0xa54ff53a3c6ef372    # LE(h2) || LE(h3)\n" ++
  "  .quad 0x9b05688c510e527f    # LE(h4) || LE(h5)\n" ++
  "  .quad 0x5be0cd191f83d9ab    # LE(h6) || LE(h7)\n" ++
  ".balign 8\n" ++
  "sha256_le_input:\n" ++
  "  # input[0] = LE-u32-pack of message u32[0..2]\n" ++
  "  # padded empty: u32[0] = 0x80 (LE bytes [80 00 00 00]) || u32[1] = 0\n" ++
  "  .quad 0x80\n" ++
  "  .quad 0\n" ++
  "  .quad 0\n" ++
  "  .quad 0\n" ++
  "  .quad 0\n" ++
  "  .quad 0\n" ++
  "  .quad 0\n" ++
  "  .quad 0                     # u32[15] = length BE bits = 0\n" ++
  ".balign 8\n" ++
  "sha256_le_params:\n" ++
  "  .quad sha256_le_state\n" ++
  "  .quad sha256_le_input"

def ziskSha256ProbeLeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSha256ProbeLePrologue
  dataAsm     := ziskSha256ProbeLeDataSection
}

/-! ## zkvm_sha256 — PR-S2 Merkle-Damgård wrapper

    Parameterised SHA-256 callable matching the zkvm-standards C
    signature:

        zkvm_status zkvm_sha256(const uint8_t* data, size_t len,
                                zkvm_sha256_hash* output);

    Sister to PR-K3's `zkvm_keccak256`. Composes the LE-u32
    intrinsic pinned in PR-S1 (#5286) with the FIPS 180-4
    Merkle-Damgård wrapper:

      1. Initialise state to the SHA-256 IV (LE-u32 packing).
      2. For each full 64-byte input block: copy into the
         intrinsic's `sha256_input` buffer, `csrs 0x805, a0` to
         compress.
      3. Final block: copy <64 remainder bytes, append 0x80,
         append 8-byte big-endian bit-length at offset 56..64.
         If remainder >= 56, use two blocks (current + a fresh
         length-only block).
      4. Squeeze: byte-swap each u32 of the LE-packed state to
         produce canonical SHA-256 wire bytes
         (`e3b0c442 98fc1c14 ...` byte order). The byte-swap uses
         the `xori 3` index trick (within each 4-byte group,
         byte j maps to byte (3 ^ j)).

    Calling convention (RV64 ABI, mirrors `zkvm_keccak256`):
      a0 = data ptr; a1 = len; a2 = output ptr;
      ra = return; returns a0 = ZKVM_EOK = 0. -/

def zkvmSha256Function : String :=
  "zkvm_sha256:\n" ++
  "  # save callee-saved regs (s0..s5)\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd s0, 0(sp)\n" ++
  "  sd s1, 8(sp)\n" ++
  "  sd s2, 16(sp)\n" ++
  "  sd s3, 24(sp)\n" ++
  "  sd s4, 32(sp)\n" ++
  "  sd s5, 40(sp)\n" ++
  "  # s0 = state ptr; s1 = data ptr; s2 = remaining len;\n" ++
  "  # s3 = output ptr (= caller's a2); s4 = bit-length;\n" ++
  "  # s5 = sha256_input buffer base.\n" ++
  "  la s0, sha256_w_state\n" ++
  "  mv s1, a0\n" ++
  "  mv s2, a1\n" ++
  "  mv s3, a2\n" ++
  "  slli s4, a1, 3\n" ++
  "  la s5, sha256_w_input\n" ++
  "  # initialise state from IV (LE-u32 packed, 4 × u64)\n" ++
  "  la t0, sha256_w_iv\n" ++
  "  ld t1, 0(t0);  sd t1, 0(s0)\n" ++
  "  ld t1, 8(t0);  sd t1, 8(s0)\n" ++
  "  ld t1, 16(t0); sd t1, 16(s0)\n" ++
  "  ld t1, 24(t0); sd t1, 24(s0)\n" ++
  "  # absorb full 64-byte blocks\n" ++
  ".Lzkv_sha_loop:\n" ++
  "  li t0, 64\n" ++
  "  blt s2, t0, .Lzkv_sha_final\n" ++
  "  ld t0, 0(s1);  sd t0, 0(s5)\n" ++
  "  ld t0, 8(s1);  sd t0, 8(s5)\n" ++
  "  ld t0, 16(s1); sd t0, 16(s5)\n" ++
  "  ld t0, 24(s1); sd t0, 24(s5)\n" ++
  "  ld t0, 32(s1); sd t0, 32(s5)\n" ++
  "  ld t0, 40(s1); sd t0, 40(s5)\n" ++
  "  ld t0, 48(s1); sd t0, 48(s5)\n" ++
  "  ld t0, 56(s1); sd t0, 56(s5)\n" ++
  "  la a0, sha256_w_params\n" ++
  "  .4byte 0x80552073           # csrs 0x805, a0\n" ++
  "  addi s1, s1, 64\n" ++
  "  addi s2, s2, -64\n" ++
  "  j .Lzkv_sha_loop\n" ++
  ".Lzkv_sha_final:\n" ++
  "  # zero the input buffer\n" ++
  "  sd zero, 0(s5);  sd zero, 8(s5);  sd zero, 16(s5); sd zero, 24(s5)\n" ++
  "  sd zero, 32(s5); sd zero, 40(s5); sd zero, 48(s5); sd zero, 56(s5)\n" ++
  "  # byte-copy remaining s2 bytes from s1 to s5\n" ++
  "  mv t0, s5\n" ++
  "  mv t1, s1\n" ++
  "  mv t2, s2\n" ++
  ".Lzkv_sha_bcopy:\n" ++
  "  beqz t2, .Lzkv_sha_pad\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  sb  t3, 0(t0)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Lzkv_sha_bcopy\n" ++
  ".Lzkv_sha_pad:\n" ++
  "  # write 0x80 at offset s2 in input buffer\n" ++
  "  add t0, s5, s2\n" ++
  "  li  t1, 0x80\n" ++
  "  sb  t1, 0(t0)\n" ++
  "  # if remainder < 56: single final block; else two-block path\n" ++
  "  li  t0, 56\n" ++
  "  blt s2, t0, .Lzkv_sha_writelen\n" ++
  "  # two-block: compress this block (data + 0x80, no length yet)\n" ++
  "  la  a0, sha256_w_params\n" ++
  "  .4byte 0x80552073\n" ++
  "  # zero input buffer for the second (length-only) block\n" ++
  "  sd zero, 0(s5);  sd zero, 8(s5);  sd zero, 16(s5); sd zero, 24(s5)\n" ++
  "  sd zero, 32(s5); sd zero, 40(s5); sd zero, 48(s5); sd zero, 56(s5)\n" ++
  ".Lzkv_sha_writelen:\n" ++
  "  # 8-byte BE bit-length at offset 56..64 of input buffer\n" ++
  "  addi t0, s5, 56\n" ++
  "  srli t1, s4, 56; sb t1, 0(t0)\n" ++
  "  srli t1, s4, 48; sb t1, 1(t0)\n" ++
  "  srli t1, s4, 40; sb t1, 2(t0)\n" ++
  "  srli t1, s4, 32; sb t1, 3(t0)\n" ++
  "  srli t1, s4, 24; sb t1, 4(t0)\n" ++
  "  srli t1, s4, 16; sb t1, 5(t0)\n" ++
  "  srli t1, s4,  8; sb t1, 6(t0)\n" ++
  "  sb   s4, 7(t0)\n" ++
  "  # compress final block\n" ++
  "  la  a0, sha256_w_params\n" ++
  "  .4byte 0x80552073\n" ++
  "  # squeeze: byte-swap each u32 of state into output\n" ++
  "  # output[i] = state[i ^ 3]   (reverses bytes within each 4-byte group)\n" ++
  "  li  t0, 0\n" ++
  ".Lzkv_sha_squeeze:\n" ++
  "  li  t1, 32\n" ++
  "  beq t0, t1, .Lzkv_sha_return\n" ++
  "  xori t2, t0, 3\n" ++
  "  add t3, s0, t2\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  add t5, s3, t0\n" ++
  "  sb  t4, 0(t5)\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lzkv_sha_squeeze\n" ++
  ".Lzkv_sha_return:\n" ++
  "  li  a0, 0\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp); ld s3, 24(sp); ld s4, 32(sp); ld s5, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskZkvmSha256Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  # call 1: sha256(empty)\n" ++
  "  la a0, zsha_empty\n" ++
  "  li a1, 0\n" ++
  "  li a2, 0xa0010000\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  # call 2: sha256(\"abc\")\n" ++
  "  la a0, zsha_abc\n" ++
  "  li a1, 3\n" ++
  "  li a2, 0xa0010020\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  # call 3: sha256(0xaa × 200)\n" ++
  "  la a0, zsha_aa\n" ++
  "  li a1, 200\n" ++
  "  li a2, 0xa0010040\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  j .Lzkv_sha_done\n" ++
  zkvmSha256Function ++ "\n" ++
  ".Lzkv_sha_done:"

def ziskZkvmSha256DataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667    # LE(h0) || LE(h1)\n" ++
  "  .quad 0xa54ff53a3c6ef372    # LE(h2) || LE(h3)\n" ++
  "  .quad 0x9b05688c510e527f    # LE(h4) || LE(h5)\n" ++
  "  .quad 0x5be0cd191f83d9ab    # LE(h6) || LE(h7)\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n" ++
  "zsha_empty:\n" ++
  "  .byte 0\n" ++
  "zsha_abc:\n" ++
  "  .ascii \"abc\"\n" ++
  "zsha_aa:\n" ++
  "  .fill 200, 1, 0xaa"

def ziskZkvmSha256ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskZkvmSha256Prologue
  dataAsm     := ziskZkvmSha256DataSection
}

/-! ## zisk_sha256_from_input — PR-S3 host-supplied input

    Mirror of PR-K4 `zisk_keccak256_from_input` for SHA-256:
    hash whatever's at `INPUT_ADDR + 16` (length given at
    `INPUT_ADDR + 8` per ziskemu's input-region layout) and
    write the 32-byte digest to `OUTPUT_ADDR + 0..32`.

    Uses PR-S2's `zkvm_sha256` (the Merkle-Damgård wrapper)
    inlined per-BuildUnit. Test exercises arbitrary input
    lengths via the Python harness (`--shape header` for an
    RLP-encoded amsterdam Header ~658 bytes, `--shape long`
    for 1024 bytes of 0x55). -/
def ziskSha256FromInputPrologue : String :=
  "  # set up stack\n" ++
  "  li sp, 0xa0050000\n" ++
  "  # read length and data ptr from ziskemu input region\n" ++
  "  li a3, 0x40000000           # INPUT_ADDR\n" ++
  "  ld a1, 8(a3)                # a1 = length (u64 LE at INPUT_ADDR + 8)\n" ++
  "  addi a0, a3, 16             # a0 = data ptr (INPUT_ADDR + 16)\n" ++
  "  li a2, 0xa0010000           # a2 = OUTPUT_ADDR\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  j .Lzks_done\n" ++
  zkvmSha256Function ++ "\n" ++
  ".Lzks_done:"

def ziskSha256FromInputDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input"

def ziskSha256FromInputProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSha256FromInputPrologue
  dataAsm     := ziskSha256FromInputDataSection
}

/-! ## zisk_zkvm_keccak256 — PR-K3 parameterised wrapper

    Refactors the three hardcoded sponge probes (PR-K2 empty,
    PR-K2a "abc", PR-K2b multi-block) into a single jal-callable
    function matching the zkvm-standards C signature:

        zkvm_status zkvm_keccak256(const uint8_t* data, size_t len,
                                   zkvm_keccak256_hash* output);

    Calling convention (RV64 ABI):
      a0 = data ptr
      a1 = len
      a2 = output ptr (32 bytes will be written)
      ra = return address
      returns: a0 = 0 on success (ZKVM_EOK = 0)

    Internally clobbers t0..t6, a0..a2. Saves s0/s1/s2/s4 on the
    stack and restores them before returning. Caller is
    responsible for sp pointing at usable RAM.

    The build unit's test driver initialises sp, then makes three
    calls (empty / "abc" / 200×0xaa) writing the three 32-byte
    digests to OUTPUT[0..96]. After the third call, jumps past
    the function definition and falls through to halt.

    Expected OUTPUT[0..96]:
      0..32  : keccak256(b"")               = c5d2460186f7233c...
      32..64 : keccak256(b"abc")            = 4e03657aea45a94f...
      64..96 : keccak256(b"\xaa" * 200)     = ebad1a3694934 0cb... -/

/-- The parameterised `zkvm_keccak256` function definition (raw
    asm). Lives in the prologue after the test driver, guarded by
    a forward jump so it isn't executed on _start fall-through. -/
def zkvmKeccak256Function : String :=
  "zkvm_keccak256:\n" ++
  "  # save s0/s1/s2/s4 (callee-saved per RV64 ABI)\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd s0, 0(sp)\n" ++
  "  sd s1, 8(sp)\n" ++
  "  sd s2, 16(sp)\n" ++
  "  sd s4, 24(sp)\n" ++
  "  # stash args (a0/a1/a2 get clobbered during the absorb loop)\n" ++
  "  mv s4, a0                # data ptr\n" ++
  "  mv s1, a1                # remaining length\n" ++
  "  mv s2, a2                # output ptr\n" ++
  "  la s0, zk3_state\n" ++
  "  # zero state (25 × u64)\n" ++
  "  mv t3, s0\n" ++
  "  li t4, 25\n" ++
  ".Lzk3_zero:\n" ++
  "  sd zero, 0(t3)\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lzk3_zero\n" ++
  "  # absorb full blocks (rate = 136 bytes)\n" ++
  ".Lzk3_full:\n" ++
  "  li t4, 136\n" ++
  "  blt s1, t4, .Lzk3_final\n" ++
  "  mv t3, s0\n" ++
  "  mv t5, s4\n" ++
  "  li t6, 17\n" ++
  ".Lzk3_xor:\n" ++
  "  ld t0, 0(t5)\n" ++
  "  ld t1, 0(t3)\n" ++
  "  xor t1, t1, t0\n" ++
  "  sd t1, 0(t3)\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t5, t5, 8\n" ++
  "  addi t6, t6, -1\n" ++
  "  bnez t6, .Lzk3_xor\n" ++
  "  mv a0, s0\n" ++
  "  .4byte 0x80052073\n" ++
  "  addi s4, s4, 136\n" ++
  "  addi s1, s1, -136\n" ++
  "  j .Lzk3_full\n" ++
  ".Lzk3_final:\n" ++
  "  mv t3, s0\n" ++
  "  mv t5, s4\n" ++
  "  beqz s1, .Lzk3_pad\n" ++
  ".Lzk3_bxor:\n" ++
  "  lbu t0, 0(t5)\n" ++
  "  lbu t1, 0(t3)\n" ++
  "  xor t0, t0, t1\n" ++
  "  sb t0, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi s1, s1, -1\n" ++
  "  bnez s1, .Lzk3_bxor\n" ++
  ".Lzk3_pad:\n" ++
  "  lbu t0, 0(t3)\n" ++
  "  xori t0, t0, 0x01\n" ++
  "  sb t0, 0(t3)\n" ++
  "  addi t3, s0, 135\n" ++
  "  lbu t0, 0(t3)\n" ++
  "  xori t0, t0, 0x80\n" ++
  "  sb t0, 0(t3)\n" ++
  "  mv a0, s0\n" ++
  "  .4byte 0x80052073\n" ++
  "  # squeeze 32 bytes to s2 (= output ptr)\n" ++
  "  ld t0, 0(s0);  sd t0, 0(s2)\n" ++
  "  ld t0, 8(s0);  sd t0, 8(s2)\n" ++
  "  ld t0, 16(s0); sd t0, 16(s2)\n" ++
  "  ld t0, 24(s0); sd t0, 24(s2)\n" ++
  "  # return ZKVM_EOK\n" ++
  "  li a0, 0\n" ++
  "  ld s0, 0(sp)\n" ++
  "  ld s1, 8(sp)\n" ++
  "  ld s2, 16(sp)\n" ++
  "  ld s4, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- Test driver: initialises sp, calls `zkvm_keccak256` three times
    with the empty / abc / 200×0xaa inputs, then jumps over the
    function definition so we fall through to halt. -/
def ziskZkvmKeccak256Prologue : String :=
  "  # set up a usable stack pointer in RAM\n" ++
  "  li sp, 0xa0050000\n" ++
  "  # call 1: keccak256(empty)\n" ++
  "  la a0, zk3_empty_marker\n" ++
  "  li a1, 0\n" ++
  "  li a2, 0xa0010000\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # call 2: keccak256(\"abc\")\n" ++
  "  la a0, zk3_abc_input\n" ++
  "  li a1, 3\n" ++
  "  li a2, 0xa0010020\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # call 3: keccak256(0xaa × 200)\n" ++
  "  la a0, zk3_aa_input\n" ++
  "  li a1, 200\n" ++
  "  li a2, 0xa0010040\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # skip over the function definition, fall through to halt\n" ++
  "  j .Lzk3_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  ".Lzk3_done:"

def ziskZkvmKeccak256DataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "zk3_empty_marker:\n" ++
  "  .byte 0\n" ++
  "zk3_abc_input:\n" ++
  "  .ascii \"abc\"\n" ++
  "zk3_aa_input:\n" ++
  "  .fill 200, 1, 0xaa"

def ziskZkvmKeccak256ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskZkvmKeccak256Prologue
  dataAsm     := ziskZkvmKeccak256DataSection
}

/-! ## zisk_keccak256_from_input — PR-K4 host-supplied input

    First real-shape consumer of the parameterised
    `zkvm_keccak256` from PR-K3: hash an arbitrary byte buffer
    that the host streamed in via `ziskemu -i <file>`. ziskemu
    places file bytes 0..8 (the u64 LE length prefix) at
    `INPUT_ADDR + 8..16` and file bytes 8.. (the data) at
    `INPUT_ADDR + 16..`. The probe reads the length, points at
    the data, calls `zkvm_keccak256`, writes the 32-byte digest
    at OUTPUT_ADDR.

    Designed to test header-shaped inputs (typical Ethereum
    header RLP is ~530-540 bytes), but accepts any byte stream.
    The Python harness (`scripts/keccak256-gen-input.py`)
    SSZ/RLP-encodes a real Header dataclass and emits the
    ziskemu-formatted input file. The test script runs ziskemu,
    diffs the OUTPUT digest against the Python-computed
    reference hash. -/
def ziskKeccak256FromInputPrologue : String :=
  "  # set up stack\n" ++
  "  li sp, 0xa0050000\n" ++
  "  # read length and data ptr from ziskemu input region\n" ++
  "  li a3, 0x40000000           # INPUT_ADDR\n" ++
  "  ld a1, 8(a3)                # a1 = length (u64 LE at INPUT_ADDR + 8)\n" ++
  "  addi a0, a3, 16             # a0 = data ptr (INPUT_ADDR + 16)\n" ++
  "  li a2, 0xa0010000           # a2 = OUTPUT_ADDR\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  j .Lzk4_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  ".Lzk4_done:"

/-- `.data` for the from-input probe: 200-byte state buffer used
    by `zkvm_keccak256`. Input data lives in the
    `INPUT_ADDR` region (host-supplied via `ziskemu -i`), not in
    `.data`. -/
def ziskKeccak256FromInputDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskKeccak256FromInputProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskKeccak256FromInputPrologue
  dataAsm     := ziskKeccak256FromInputDataSection
}

/-! ## headers_keccak_chain -- PR-K15 walk an SSZ list section,
    keccak each element, return the last digest + count.

    Walks the SSZ inner-offset table to derive per-element
    bounds (same parsing shape as the SSZ list-merkleize work),
    then calls `zkvm_keccak256(el_i_start, el_i_len, out_ptr)`
    for each element. The output buffer is overwritten on every
    iteration; after the loop, it holds the LAST element's
    digest. Returns the element count `N` in `a0`.

    Calling convention:
      a0 (input)  : SSZ list section ptr (read-only)
      a1 (input)  : section_len (0 ⇒ empty list)
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) : N (element count)
      32 bytes at *a2 : keccak256(element[N-1]) if N > 0, else 0.

    No per-element scratch; works for any N. -/
def headersKeccakChainFunction : String :=
  "headers_keccak_chain:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                  # s0 = section ptr\n" ++
  "  mv s1, a1                  # s1 = section_len\n" ++
  "  mv s2, a2                  # s2 = output ptr\n" ++
  "  beqz s1, .Lhkc_n0          # empty section ⇒ N = 0\n" ++
  "  lwu t0, 0(s0)              # offset_0 = 4 * N\n" ++
  "  srli s3, t0, 2             # s3 = N\n" ++
  "  li s4, 0                   # s4 = i\n" ++
  ".Lhkc_loop:\n" ++
  "  beq s4, s3, .Lhkc_done\n" ++
  "  slli t0, s4, 2             # 4*i\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  add a0, s0, t2             # el_i_start\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lhkc_use_end\n" ++
  "  slli t3, t3, 2             # 4*(i+1)\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # el_i_end\n" ++
  "  j .Lhkc_have_end\n" ++
  ".Lhkc_use_end:\n" ++
  "  add t4, s0, s1             # el_i_end = section_end\n" ++
  ".Lhkc_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  mv a2, s2                  # output (overwritten each iter)\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lhkc_loop\n" ++
  ".Lhkc_n0:\n" ++
  "  sd zero,  0(s2)\n" ++
  "  sd zero,  8(s2)\n" ++
  "  sd zero, 16(s2)\n" ++
  "  sd zero, 24(s2)\n" ++
  "  li s3, 0                   # N = 0\n" ++
  ".Lhkc_done:\n" ++
  "  mv a0, s3                  # return N\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_headers_keccak_chain`: probe BuildUnit that reads an
    SSZ list section from host input and writes the count + last
    digest to OUTPUT.
    Input layout:
      bytes  0.. 8 : section_len (u64)
      bytes  8..   : SSZ list section bytes
    Output layout:
      bytes  0.. 8 : N (u64 LE)
      bytes  8..40 : keccak256(element[N-1]) or 0 if N=0 -/
def ziskHeadersKeccakChainPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # section_len\n" ++
  "  addi a0, a3, 16             # section ptr\n" ++
  "  li a2, 0xa0010008           # last_hash output (OUTPUT + 8)\n" ++
  "  jal ra, headers_keccak_chain\n" ++
  "  li t0, 0xa0010000           # write N at OUTPUT + 0\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhkc_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersKeccakChainFunction ++ "\n" ++
  ".Lhkc_pdone:"

def ziskHeadersKeccakChainDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskHeadersKeccakChainProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeadersKeccakChainPrologue
  dataAsm     := ziskHeadersKeccakChainDataSection
}

/-! ## headers_keccak_array -- PR-K16 walk SSZ list section,
    keccak each element, store every digest in caller table.

    Sibling of `headers_keccak_chain` (PR-K15): same SSZ-list
    parsing loop, but each iteration writes the digest to
    `table[i]` instead of overwriting the same slot. Returns the
    element count `N`.

    Calling convention:
      a0 (input)  : section ptr (read-only)
      a1 (input)  : section_len (0 = empty list)
      a2 (input)  : table base ptr (must hold N*32 bytes)
      ra (input)  : return
      a0 (output) : N (element count)
      32 bytes at *(table + 32*i) = keccak256(element[i])
        for each i in 0..N. -/
def headersKeccakArrayFunction : String :=
  "headers_keccak_array:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                  # s0 = section ptr\n" ++
  "  mv s1, a1                  # s1 = section_len\n" ++
  "  mv s2, a2                  # s2 = table base\n" ++
  "  beqz s1, .Lhka_n0\n" ++
  "  lwu t0, 0(s0)\n" ++
  "  srli s3, t0, 2             # s3 = N\n" ++
  "  li s4, 0                   # s4 = i\n" ++
  ".Lhka_loop:\n" ++
  "  beq s4, s3, .Lhka_done\n" ++
  "  slli t0, s4, 2             # 4*i\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  add a0, s0, t2             # el_i_start\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lhka_use_end\n" ++
  "  slli t3, t3, 2             # 4*(i+1)\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # el_i_end\n" ++
  "  j .Lhka_have_end\n" ++
  ".Lhka_use_end:\n" ++
  "  add t4, s0, s1             # el_i_end = section_end\n" ++
  ".Lhka_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  slli t0, s4, 5             # 32*i\n" ++
  "  add a2, s2, t0             # a2 = &table[i]\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lhka_loop\n" ++
  ".Lhka_n0:\n" ++
  "  li s3, 0\n" ++
  ".Lhka_done:\n" ++
  "  mv a0, s3                  # return N\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_headers_keccak_array`: probe BuildUnit that reads an
    SSZ list section from host input and writes (count, table)
    to OUTPUT, capped at N ≤ 7 to fit ziskemu's 256-byte output
    channel.
    Input layout:
      bytes  0.. 8 : section_len (u64)
      bytes  8..   : SSZ list section bytes
    Output layout:
      bytes  0.. 8     : N (u64 LE)
      bytes  8..8+32*N : N digests of 32 bytes each -/
def ziskHeadersKeccakArrayPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # section_len\n" ++
  "  addi a0, a3, 16             # section ptr\n" ++
  "  li a2, 0xa0010008           # table at OUTPUT + 8\n" ++
  "  jal ra, headers_keccak_array\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # write N at OUTPUT + 0\n" ++
  "  j .Lhka_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersKeccakArrayFunction ++ "\n" ++
  ".Lhka_pdone:"

def ziskHeadersKeccakArrayDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskHeadersKeccakArrayProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeadersKeccakArrayPrologue
  dataAsm     := ziskHeadersKeccakArrayDataSection
}

/-! ## headers_parent_hash -- PR-K17 RLP-walk to extract the
    first 32-byte field of an RLP-encoded Ethereum header
    (`parent_hash`).

    Skips the outer list prefix (0xc0..0xc0+55 short form, 0xf8
    1-byte-length, or 0xf9 2-byte-length forms), expects a
    0xa0 Bytes32 string prefix, then copies the 32 raw bytes
    to the caller's output.

    Calling convention:
      a0 (input)  : RLP-encoded header ptr (read-only)
      a1 (input)  : header byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 on success; 32 bytes at *a2 = parent_hash
        1 on RLP parse failure

    Pure register arithmetic; no scratch memory, no callee-saved
    registers used. Leaf-callable. -/
def headersParentHashFunction : String :=
  "headers_parent_hash:\n" ++
  "  # a0 = header ptr, a1 = header_len, a2 = out ptr\n" ++
  "  lbu t0, 0(a0)                # first byte\n" ++
  "  li t1, 0xc0\n" ++
  "  bltu t0, t1, .Lhph_fail      # not an RLP list (< 0xc0)\n" ++
  "  li t1, 0xf8\n" ++
  "  bltu t0, t1, .Lhph_short     # 0xc0..0xf7 → short list, 1-byte prefix\n" ++
  "  # long list: t0 in [0xf8..0xff].\n" ++
  "  # length_of_length = t0 - 0xf7. Outer prefix = 1 + length_of_length bytes.\n" ++
  "  li t1, 0xf7\n" ++
  "  sub t2, t0, t1               # length_of_length\n" ++
  "  li t3, 2                     # cap: support 0xf8 (LoL=1), 0xf9 (LoL=2)\n" ++
  "  bltu t3, t2, .Lhph_fail      # LoL > 2 → unsupported\n" ++
  "  addi t2, t2, 1               # prefix bytes = LoL + 1\n" ++
  "  add a0, a0, t2               # skip prefix\n" ++
  "  sub a1, a1, t2\n" ++
  "  j .Lhph_after_prefix\n" ++
  ".Lhph_short:\n" ++
  "  addi a0, a0, 1               # skip 1-byte prefix\n" ++
  "  addi a1, a1, -1\n" ++
  ".Lhph_after_prefix:\n" ++
  "  # Expect 0xa0 Bytes32 prefix.\n" ++
  "  li t0, 33\n" ++
  "  bltu a1, t0, .Lhph_fail      # not enough bytes for 0xa0 + 32\n" ++
  "  lbu t1, 0(a0)\n" ++
  "  li t2, 0xa0\n" ++
  "  bne t1, t2, .Lhph_fail       # not a Bytes32 string\n" ++
  "  # Copy 32 bytes from a0+1 to a2.\n" ++
  "  ld t0,  1(a0); sd t0,  0(a2)\n" ++
  "  ld t0,  9(a0); sd t0,  8(a2)\n" ++
  "  ld t0, 17(a0); sd t0, 16(a2)\n" ++
  "  ld t0, 25(a0); sd t0, 24(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lhph_fail:\n" ++
  "  li a0, 1\n" ++
  "  ret"

/-- `zisk_headers_parent_hash`: probe BuildUnit that reads an
    RLP-encoded header from host input and writes
    `(status, parent_hash)` to OUTPUT.
    Input layout:
      bytes  0.. 8 : header_len (u64)
      bytes  8..   : RLP-encoded header bytes
    Output layout:
      bytes  0.. 8 : status (u64 LE; 0 = ok, 1 = parse fail)
      bytes  8..40 : parent_hash (32 bytes; meaningful only on
                     status=0; on failure, contains zeros) -/
def ziskHeadersParentHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  li a2, 0xa0010008           # parent_hash output (OUTPUT + 8)\n" ++
  "  # Pre-zero output[8..40] so a parse failure surfaces as zeros.\n" ++
  "  sd zero,  0(a2); sd zero,  8(a2); sd zero, 16(a2); sd zero, 24(a2)\n" ++
  "  jal ra, headers_parent_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # write status at OUTPUT + 0\n" ++
  "  j .Lhph_pdone\n" ++
  headersParentHashFunction ++ "\n" ++
  ".Lhph_pdone:"

def ziskHeadersParentHashDataSection : String :=
  ".section .data\n" ++
  "hph_scratch:\n" ++
  "  .zero 8"

def ziskHeadersParentHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeadersParentHashPrologue
  dataAsm     := ziskHeadersParentHashDataSection
}

/-! ## headers_validate_chain -- PR-K18 parent_hash chain check

    Composes PR-K16 `headers_keccak_array` (build per-header
    digest table) with PR-K17 `headers_parent_hash` (RLP-extract
    each header's first 32-byte field) to verify the
    `validate_headers` invariant:

        header[i].parent_hash == keccak256(header[i-1])
            for every i in 1..N

    matches the Python check in
    `execution-specs/.../stateless.py::validate_headers`.

    Calling convention:
      a0 (input)  : SSZ list section ptr (witness.headers)
      a1 (input)  : section_len (0 = empty list)
      a2 (input)  : 8-byte output ptr (receives N as u64 LE)
      ra (input)  : return
      a0 (output) : 0 on success (chain valid) or N ≤ 1
                    1 on mismatch / RLP-decode failure

    Walks the list using the same SSZ inner-offset table as
    PR-K15/K16. Caps at N ≤ 256 (matches `MAX_WITNESS_HEADERS`).

    Uses two `.data` scratch buffers:
      vh_keccak_table          : 256 × 32 = 8 KB
      vh_extracted_parent_hash : 32 B
-/
def headersValidateChainFunction : String :=
  "headers_validate_chain:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                  # s0 = section ptr\n" ++
  "  mv s1, a1                  # s1 = section_len\n" ++
  "  mv s2, a2                  # s2 = N out ptr\n" ++
  "  # Step 1: keccak each header into vh_keccak_table.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, vh_keccak_table\n" ++
  "  jal ra, headers_keccak_array\n" ++
  "  mv s3, a0                  # s3 = N\n" ++
  "  sd s3, 0(s2)               # *N_out = N\n" ++
  "  # If N ≤ 1, no chain links to check → ok.\n" ++
  "  li t0, 2\n" ++
  "  bltu s3, t0, .Lvh_ok\n" ++
  "  # Loop i = 1..N.\n" ++
  "  li s4, 1\n" ++
  ".Lvh_loop:\n" ++
  "  beq s4, s3, .Lvh_ok\n" ++
  "  # Find element i bounds from inner-offset table.\n" ++
  "  slli t0, s4, 2             # 4*i\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  add a0, s0, t2             # el_i_start\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lvh_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4\n" ++
  "  j .Lvh_have_end\n" ++
  ".Lvh_use_end:\n" ++
  "  add t4, s0, s1\n" ++
  ".Lvh_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  la a2, vh_extracted_parent_hash\n" ++
  "  jal ra, headers_parent_hash\n" ++
  "  bnez a0, .Lvh_fail         # RLP parse failed\n" ++
  "  # Compare extracted parent_hash against vh_keccak_table[i-1].\n" ++
  "  la t0, vh_keccak_table\n" ++
  "  addi t1, s4, -1\n" ++
  "  slli t1, t1, 5             # (i-1) * 32\n" ++
  "  add t0, t0, t1             # &table[i-1]\n" ++
  "  la t1, vh_extracted_parent_hash\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lvh_fail\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lvh_fail\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lvh_fail\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lvh_fail\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lvh_loop\n" ++
  ".Lvh_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Lvh_ret\n" ++
  ".Lvh_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lvh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_headers_validate_chain`: probe BuildUnit that reads an
    SSZ list of RLP-encoded headers from host input and writes
    (status, N) to OUTPUT.
    Input layout:
      bytes  0.. 8 : section_len (u64)
      bytes  8..   : SSZ list section bytes
    Output layout:
      bytes  0.. 8 : status (u64 LE; 0 ok / 1 mismatch)
      bytes  8..16 : N (u64 LE; element count) -/
def ziskHeadersValidateChainPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # section_len\n" ++
  "  addi a0, a3, 16             # section ptr\n" ++
  "  li a2, 0xa0010008           # N out ptr (OUTPUT + 8)\n" ++
  "  jal ra, headers_validate_chain\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Lvh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersKeccakArrayFunction ++ "\n" ++
  headersParentHashFunction ++ "\n" ++
  headersValidateChainFunction ++ "\n" ++
  ".Lvh_pdone:"

def ziskHeadersValidateChainDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "vh_keccak_table:\n" ++
  "  .zero 8192                 # 256 × 32-byte digests\n" ++
  ".balign 32\n" ++
  "vh_extracted_parent_hash:\n" ++
  "  .zero 32"

def ziskHeadersValidateChainProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeadersValidateChainPrologue
  dataAsm     := ziskHeadersValidateChainDataSection
}

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

/-- `zisk_rlp_list_count_items`: probe BuildUnit. Reads
    (list_len, list_bytes) from host input, writes
    (status, count) to OUTPUT. -/
def ziskRlpListCountItemsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # list_len\n" ++
  "  addi a0, a3, 16             # list ptr\n" ++
  "  li a2, 0xa0010008           # count out at OUTPUT + 8\n" ++
  "  sd zero, 0(a2)\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lrlc_pdone\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  ".Lrlc_pdone:"

def ziskRlpListCountItemsDataSection : String :=
  ".section .data\n" ++
  "rlc_pad:\n" ++
  "  .zero 8"

def ziskRlpListCountItemsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRlpListCountItemsPrologue
  dataAsm     := ziskRlpListCountItemsDataSection
}

/-! ## access_list_count -- PR-K48 EIP-2930+ access-list cardinality

    Walk an RLP-encoded EIP-2930+ access_list and return
    `(num_addresses, num_storage_keys)`. These are the two
    inputs to the EIP-2930+ intrinsic-gas formula:

      gas_access_list = 2400 × num_addresses + 1900 × num_storage_keys

    Access-list shape:

      access_list = [
        [address (20 B), [slot1 (32 B), slot2 (32 B), ...]],
        ...
      ]

    Both `access_list` and each per-address `[slots...]` sub-list
    are RLP lists. This helper composes:

      1. PR-K47 `rlp_list_count_items` on the outer access_list to
         get N = num_addresses (and validate the outer shape).
      2. PR-K20 `rlp_list_nth_item` to extract each entry's bounds.
      3. PR-K20 `rlp_list_nth_item` on each entry to get field 1
         (the slots sub-list).
      4. PR-K47 `rlp_list_count_items` on the slots sub-list to add
         to num_storage_keys.

    Empty access_list (`0xc0`) → (0, 0).

    Calling convention:
      a0 (input)  : access_list bytes ptr (whole encoded item incl.
                    outer RLP list prefix)
      a1 (input)  : access_list byte length
      a2 (input)  : u64 out ptr for num_addresses
      a3 (input)  : u64 out ptr for num_storage_keys
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail.

    Uses three 8-byte `.data` scratch slots
    (`alc_scratch`, `alc_entry_offset`, `alc_entry_length`,
    `alc_keys_offset`, `alc_keys_length`). -/
def accessListCountFunction : String :=
  "access_list_count:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # outer list ptr\n" ++
  "  mv s1, a1                   # outer list len\n" ++
  "  mv s2, a2                   # num_addresses out\n" ++
  "  mv s3, a3                   # num_storage_keys out\n" ++
  "  sd zero, 0(s2); sd zero, 0(s3)\n" ++
  "  # Step 1: outer count → s4 = N.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, alc_scratch\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lalc_fail\n" ++
  "  la t0, alc_scratch; ld s4, 0(t0)\n" ++
  "  beqz s4, .Lalc_done\n" ++
  "  # Step 2: iterate entries 0..N-1.\n" ++
  "  li s5, 0                    # entry index\n" ++
  ".Lalc_loop:\n" ++
  "  beq s5, s4, .Lalc_done\n" ++
  "  # Fetch entry s5 bounds in the outer list.\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s5\n" ++
  "  la a3, alc_entry_offset\n" ++
  "  la a4, alc_entry_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lalc_fail\n" ++
  "  # entry_ptr = outer_ptr + entry_offset.\n" ++
  "  la t0, alc_entry_offset; ld t1, 0(t0)\n" ++
  "  la t0, alc_entry_length; ld t2, 0(t0)\n" ++
  "  add a0, s0, t1              # entry_ptr\n" ++
  "  mv a1, t2                   # entry_len\n" ++
  "  # Fetch entry field 1 (the slots sub-list) bounds.\n" ++
  "  li a2, 1\n" ++
  "  la a3, alc_keys_offset\n" ++
  "  la a4, alc_keys_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lalc_fail\n" ++
  "  # keys_ptr = outer_ptr + entry_offset + keys_offset.\n" ++
  "  la t0, alc_entry_offset; ld t1, 0(t0)\n" ++
  "  la t0, alc_keys_offset; ld t3, 0(t0)\n" ++
  "  add t1, t1, t3\n" ++
  "  add a0, s0, t1              # keys_ptr\n" ++
  "  la t0, alc_keys_length; ld a1, 0(t0)\n" ++
  "  la a2, alc_scratch\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lalc_fail\n" ++
  "  la t0, alc_scratch; ld t1, 0(t0)\n" ++
  "  ld t2, 0(s3)\n" ++
  "  add t2, t2, t1\n" ++
  "  sd t2, 0(s3)\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lalc_loop\n" ++
  ".Lalc_done:\n" ++
  "  sd s4, 0(s2)                # num_addresses = N\n" ++
  "  li a0, 0\n" ++
  "  j .Lalc_ret\n" ++
  ".Lalc_fail:\n" ++
  "  sd zero, 0(s2); sd zero, 0(s3)\n" ++
  "  li a0, 1\n" ++
  ".Lalc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_access_list_count`: probe BuildUnit. Reads (list_len,
    list_bytes) from host input, writes (status, num_addresses,
    num_storage_keys) to OUTPUT. -/
def ziskAccessListCountPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # list_len\n" ++
  "  addi a0, a4, 16             # list ptr\n" ++
  "  li a2, 0xa0010008           # num_addresses out\n" ++
  "  li a3, 0xa0010010           # num_storage_keys out\n" ++
  "  sd zero, 0(a2); sd zero, 0(a3)\n" ++
  "  jal ra, access_list_count\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lalc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  accessListCountFunction ++ "\n" ++
  ".Lalc_pdone:"

def ziskAccessListCountDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "alc_scratch:\n" ++
  "  .zero 8\n" ++
  "alc_entry_offset:\n" ++
  "  .zero 8\n" ++
  "alc_entry_length:\n" ++
  "  .zero 8\n" ++
  "alc_keys_offset:\n" ++
  "  .zero 8\n" ++
  "alc_keys_length:\n" ++
  "  .zero 8"

def ziskAccessListCountProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccessListCountPrologue
  dataAsm     := ziskAccessListCountDataSection
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

/-! ## account_decode -- PR-K27 RLP splitter for Account records

    Decode an RLP-encoded Ethereum Account (the value bytes
    that `mpt_lookup_by_key` returns for state-trie addresses)
    into four caller-supplied output slots.

    Calling convention:
      a0 (input)  : account RLP bytes ptr
      a1 (input)  : account RLP byte length
      a2 (input)  : u64 nonce out ptr (8 bytes; written LE u64)
      a3 (input)  : u256 balance out ptr (32 bytes; written BE,
                    left-zero-padded for values < 32 bytes)
      a4 (input)  : storage_root out ptr (32 bytes)
      a5 (input)  : code_hash out ptr (32 bytes)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail

    Composes PR-K20 `rlp_list_nth_item` four times. Field types
    enforced:
      * nonce / balance : variable-length BE big-int (length
                          in [0, 8] for nonce, [0, 32] for balance)
      * storage_root / code_hash : exactly 32 bytes each. -/
def accountDecodeFunction : String :=
  "account_decode:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                  # account ptr\n" ++
  "  mv s1, a1                  # account_len\n" ++
  "  mv s2, a2                  # nonce out\n" ++
  "  mv s3, a3                  # balance out\n" ++
  "  mv s4, a4                  # storage_root out\n" ++
  "  mv s5, a5                  # code_hash out\n" ++
  "  # Field 0: nonce (u64 BE → LE store)\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  li a2, 0\n" ++
  "  la a3, ad_offset\n" ++
  "  la a4, ad_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lad_fail\n" ++
  "  la t0, ad_length; ld t1, 0(t0)\n" ++
  "  li t2, 8\n" ++
  "  bgtu t1, t2, .Lad_fail      # nonce > 8 bytes\n" ++
  "  la t0, ad_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  li t2, 0                   # accumulator\n" ++
  ".Lad_nonce_loop:\n" ++
  "  beqz t1, .Lad_nonce_done\n" ++
  "  slli t2, t2, 8\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  or t2, t2, t4\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lad_nonce_loop\n" ++
  ".Lad_nonce_done:\n" ++
  "  sd t2, 0(s2)               # nonce_out (LE u64)\n" ++
  "  # Field 1: balance (u256 BE → BE 32-byte buffer)\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  li a2, 1\n" ++
  "  la a3, ad_offset\n" ++
  "  la a4, ad_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lad_fail\n" ++
  "  la t0, ad_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bgtu t1, t2, .Lad_fail      # balance > 32 bytes\n" ++
  "  # Zero balance_out\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  # Right-align: write to s3 + (32 - length)\n" ++
  "  sub t2, t2, t1             # 32 - length\n" ++
  "  add t4, s3, t2             # dst\n" ++
  "  la t0, ad_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  ".Lad_bal_loop:\n" ++
  "  beqz t1, .Lad_bal_done\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb  t5, 0(t4)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lad_bal_loop\n" ++
  ".Lad_bal_done:\n" ++
  "  # Field 2: storage_root (must be exactly 32 bytes)\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  li a2, 2\n" ++
  "  la a3, ad_offset\n" ++
  "  la a4, ad_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lad_fail\n" ++
  "  la t0, ad_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lad_fail\n" ++
  "  la t0, ad_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  ld t4,  0(t3); sd t4,  0(s4)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s4)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s4)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s4)\n" ++
  "  # Field 3: code_hash (must be exactly 32 bytes)\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  li a2, 3\n" ++
  "  la a3, ad_offset\n" ++
  "  la a4, ad_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lad_fail\n" ++
  "  la t0, ad_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lad_fail\n" ++
  "  la t0, ad_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  ld t4,  0(t3); sd t4,  0(s5)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s5)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s5)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s5)\n" ++
  "  li a0, 0\n" ++
  "  j .Lad_ret\n" ++
  ".Lad_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lad_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_account_decode`: probe BuildUnit. Reads
    (account_len, account_bytes) from host input, writes
    (status, nonce, balance, storage_root, code_hash) to OUTPUT.
    Input layout:
      bytes  0.. 8 : account_len (u64)
      bytes  8..   : account RLP bytes
    Output layout:
      bytes   0.. 8 : status (u64)
      bytes   8..16 : nonce (u64 LE)
      bytes  16..48 : balance (u256 BE)
      bytes  48..80 : storage_root
      bytes  80..112: code_hash -/
def ziskAccountDecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # account_len\n" ++
  "  addi a0, a6, 16             # account ptr\n" ++
  "  li a2, 0xa0010008\n" ++
  "  li a3, 0xa0010010\n" ++
  "  li a4, 0xa0010030\n" ++
  "  li a5, 0xa0010050\n" ++
  "  # Pre-zero all outputs so a parse failure surfaces as zeros.\n" ++
  "  sd zero, 0(a2)\n" ++
  "  sd zero,  0(a3); sd zero,  8(a3); sd zero, 16(a3); sd zero, 24(a3)\n" ++
  "  sd zero,  0(a4); sd zero,  8(a4); sd zero, 16(a4); sd zero, 24(a4)\n" ++
  "  sd zero,  0(a5); sd zero,  8(a5); sd zero, 16(a5); sd zero, 24(a5)\n" ++
  "  jal ra, account_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lad_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountDecodeFunction ++ "\n" ++
  ".Lad_pdone:"

def ziskAccountDecodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ad_offset:\n" ++
  "  .zero 8\n" ++
  "ad_length:\n" ++
  "  .zero 8"

def ziskAccountDecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountDecodePrologue
  dataAsm     := ziskAccountDecodeDataSection
}

/-! ## account_at_address -- PR-K28 compose lookup + decode

    Take a raw Ethereum address, walk the state trie, decode
    the resulting Account RLP into its four fields. The
    cleanest top-of-K-stack abstraction: caller sees only
    `(address, state_root, witness) → fields`.

    Output struct layout (104 bytes at caller-supplied ptr):
      offset  0..  8 : nonce (u64 LE)
      offset  8.. 40 : balance (u256 BE, left-zero-padded)
      offset 40.. 72 : storage_root (32 B)
      offset 72..104 : code_hash (32 B)

    Calling convention:
      a0 (input)  : address bytes ptr
      a1 (input)  : address byte length (typically 20)
      a2 (input)  : state_root ptr (32 bytes)
      a3 (input)  : witness section ptr
      a4 (input)  : witness section_len
      a5 (input)  : output struct ptr (104 bytes)
      ra (input)  : return

      a0 (output) :
        0 = found and decoded
        1 = not found in trie     (output zeroed)
        2 = mpt_walk parse error  (output zeroed)
        3 = account_decode failure (output zeroed)

    Internal:
      Step 1: mpt_lookup_by_key(addr, ..., aa_value_scratch).
      Step 2: account_decode(scratch_val, scratch_len, ...).
    Reuses the K-stack primitive scratches. -/
def accountAtAddressFunction : String :=
  "account_at_address:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a5                   # output struct ptr\n" ++
  "  # Step 1: mpt_lookup_by_key.\n" ++
  "  la a5, aa_value_scratch\n" ++
  "  la a6, aa_value_len\n" ++
  "  jal ra, mpt_lookup_by_key\n" ++
  "  mv s1, a0                   # save lookup status\n" ++
  "  beqz a0, .Laa_lookup_ok\n" ++
  "  # Not found / parse error: zero the output struct.\n" ++
  "  sd zero,  0(s0); sd zero,  8(s0); sd zero, 16(s0); sd zero, 24(s0)\n" ++
  "  sd zero, 32(s0); sd zero, 40(s0); sd zero, 48(s0); sd zero, 56(s0)\n" ++
  "  sd zero, 64(s0); sd zero, 72(s0); sd zero, 80(s0); sd zero, 88(s0)\n" ++
  "  sd zero, 96(s0)\n" ++
  "  mv a0, s1\n" ++
  "  j .Laa_ret\n" ++
  ".Laa_lookup_ok:\n" ++
  "  la a0, aa_value_scratch\n" ++
  "  la t0, aa_value_len; ld a1, 0(t0)\n" ++
  "  mv a2, s0                   # nonce at struct + 0\n" ++
  "  addi a3, s0, 8              # balance at struct + 8\n" ++
  "  addi a4, s0, 40             # storage_root at struct + 40\n" ++
  "  addi a5, s0, 72             # code_hash at struct + 72\n" ++
  "  jal ra, account_decode\n" ++
  "  beqz a0, .Laa_done\n" ++
  "  # account_decode failed: zero struct, return 3.\n" ++
  "  sd zero,  0(s0); sd zero,  8(s0); sd zero, 16(s0); sd zero, 24(s0)\n" ++
  "  sd zero, 32(s0); sd zero, 40(s0); sd zero, 48(s0); sd zero, 56(s0)\n" ++
  "  sd zero, 64(s0); sd zero, 72(s0); sd zero, 80(s0); sd zero, 88(s0)\n" ++
  "  sd zero, 96(s0)\n" ++
  "  li a0, 3\n" ++
  "  j .Laa_ret\n" ++
  ".Laa_done:\n" ++
  "  li a0, 0\n" ++
  ".Laa_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_account_at_address`: probe BuildUnit. Reads
    (witness_len, addr_len, state_root, addr, witness) from
    host input. Writes (status, nonce, balance, storage_root,
    code_hash) to OUTPUT.
    Output layout:
      bytes   0.. 8 : status
      bytes   8..16 : nonce
      bytes  16..48 : balance
      bytes  48..80 : storage_root
      bytes  80..112: code_hash -/
def ziskAccountAtAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld t6, 8(a7)                # witness_len\n" ++
  "  ld t5, 16(a7)               # addr_len\n" ++
  "  addi a2, a7, 24             # state_root ptr\n" ++
  "  addi a0, a7, 56             # address ptr\n" ++
  "  mv a1, t5                   # addr_len\n" ++
  "  add a3, a0, t5              # witness ptr = address + addr_len\n" ++
  "  mv a4, t6                   # witness_len\n" ++
  "  li a5, 0xa0010008           # output struct at OUTPUT + 8\n" ++
  "  # Pre-zero 104 bytes of output struct so a failure surfaces as zeros.\n" ++
  "  sd zero, 0(a5); sd zero, 8(a5); sd zero, 16(a5); sd zero, 24(a5)\n" ++
  "  sd zero, 32(a5); sd zero, 40(a5); sd zero, 48(a5); sd zero, 56(a5)\n" ++
  "  sd zero, 64(a5); sd zero, 72(a5); sd zero, 80(a5); sd zero, 88(a5)\n" ++
  "  sd zero, 96(a5)\n" ++
  "  jal ra, account_at_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Laa_pdone\n" ++
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
  ".Laa_pdone:"

def ziskAccountAtAddressDataSection : String :=
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
  "  .zero 256"

def ziskAccountAtAddressProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountAtAddressPrologue
  dataAsm     := ziskAccountAtAddressDataSection
}

/-! ## slot_at_index -- PR-K29 storage trie lookup

    Storage-trie counterpart to `account_at_address`. Takes a
    32-byte slot index (big-endian u256) and walks the
    per-account storage trie, decoding the looked-up value as
    a u256.

    Per `execution-specs/.../trie.py::encode_node`, the value
    stored in the storage trie is `rlp.encode(slot_value:U256)`
    -- one RLP layer on top of the canonical leading-zero-
    stripped big-int. `mpt_walk` strips the leaf's outer item-1
    string prefix (one layer), so the value bytes we receive
    are exactly `rlp.encode(slot_value)`. We then apply one
    more layer of RLP decoding to recover the u256.

    Encoding cheat-sheet for slot values:
      slot_value = 0          → 0x80         (RLP empty)
      slot_value = 1          → 0x01         (single byte)
      slot_value = 0x7f       → 0x7f
      slot_value = 0x80       → 0x81 0x80    (1-byte string)
      slot_value = 0x0100     → 0x82 0x01 0x00 (2-byte string)
      slot_value = 2^256 - 1  → 0xa0 + 32 × 0xff

    Calling convention:
      a0 (input)  : slot_idx bytes ptr (32-byte big-endian u256)
      a1 (input)  : slot_idx byte length (typically 32)
      a2 (input)  : storage_root ptr (32 bytes)
      a3 (input)  : witness section ptr
      a4 (input)  : witness section_len
      a5 (input)  : output u256 BE ptr (32 bytes)
      ra (input)  : return

      a0 (output) :
        0 found and decoded
        1 not found (output zeroed)
        2 mpt_walk parse error (output zeroed)
        3 RLP-u256 decode failure (output zeroed)

    Internal: `mpt_lookup_by_key(slot_idx, ..., si_value_scratch)`
    then `slot_decode_u256` over the looked-up bytes. -/
def slotDecodeU256Function : String :=
  "slot_decode_u256:\n" ++
  "  # a0 = val_bytes ptr, a1 = val_len, a2 = 32-byte BE out ptr.\n" ++
  "  # Returns 0 (ok) / 1 (fail). Output is zeroed on every path.\n" ++
  "  sd zero,  0(a2); sd zero,  8(a2); sd zero, 16(a2); sd zero, 24(a2)\n" ++
  "  beqz a1, .Lsdu_fail        # empty input: malformed encoded value\n" ++
  "  lbu t0, 0(a0)\n" ++
  "  li t1, 0x80\n" ++
  "  bltu t0, t1, .Lsdu_single  # b0 < 0x80: single byte\n" ++
  "  beq t0, t1, .Lsdu_zero     # b0 == 0x80: empty string ⇒ 0\n" ++
  "  li t1, 0xa1\n" ++
  "  bgeu t0, t1, .Lsdu_fail    # b0 ≥ 0xa1: too long for a u256\n" ++
  "  # Short string of n bytes (1 ≤ n ≤ 32).\n" ++
  "  li t1, 0x80\n" ++
  "  sub t2, t0, t1             # n\n" ++
  "  addi t3, a1, -1\n" ++
  "  bltu t3, t2, .Lsdu_fail    # not enough bytes for declared length\n" ++
  "  li t4, 32\n" ++
  "  sub t4, t4, t2             # 32 - n\n" ++
  "  add t5, a2, t4             # dst (right-aligned)\n" ++
  "  addi t6, a0, 1             # src\n" ++
  "  mv t3, t2                  # remaining\n" ++
  ".Lsdu_copy:\n" ++
  "  beqz t3, .Lsdu_ok\n" ++
  "  lbu t1, 0(t6)\n" ++
  "  sb  t1, 0(t5)\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t6, t6, 1\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lsdu_copy\n" ++
  ".Lsdu_single:\n" ++
  "  sb t0, 31(a2)              # write u256 = b0 at byte 31 (BE LSB)\n" ++
  ".Lsdu_zero:\n" ++
  ".Lsdu_ok:\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lsdu_fail:\n" ++
  "  li a0, 1\n" ++
  "  ret"

def slotAtIndexFunction : String :=
  "slot_at_index:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a5                  # u256 out ptr\n" ++
  "  la a5, si_value_scratch\n" ++
  "  la a6, si_value_len\n" ++
  "  jal ra, mpt_lookup_by_key\n" ++
  "  mv s1, a0\n" ++
  "  beqz a0, .Lsi_decode\n" ++
  "  sd zero,  0(s0); sd zero,  8(s0); sd zero, 16(s0); sd zero, 24(s0)\n" ++
  "  mv a0, s1\n" ++
  "  j .Lsi_ret\n" ++
  ".Lsi_decode:\n" ++
  "  la a0, si_value_scratch\n" ++
  "  la t0, si_value_len; ld a1, 0(t0)\n" ++
  "  mv a2, s0\n" ++
  "  jal ra, slot_decode_u256\n" ++
  "  beqz a0, .Lsi_done\n" ++
  "  sd zero,  0(s0); sd zero,  8(s0); sd zero, 16(s0); sd zero, 24(s0)\n" ++
  "  li a0, 3\n" ++
  "  j .Lsi_ret\n" ++
  ".Lsi_done:\n" ++
  "  li a0, 0\n" ++
  ".Lsi_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_slot_at_index`: probe BuildUnit. Reads
    (witness_len, slot_len, storage_root, slot_idx, witness)
    from host input. Writes (status, u256) to OUTPUT. -/
def ziskSlotAtIndexPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld t6, 8(a7)                # witness_len\n" ++
  "  ld t5, 16(a7)               # slot_len\n" ++
  "  addi a2, a7, 24             # storage_root ptr\n" ++
  "  addi a0, a7, 56             # slot_idx ptr\n" ++
  "  mv a1, t5                   # slot_len\n" ++
  "  add a3, a0, t5              # witness ptr = slot_idx + slot_len\n" ++
  "  mv a4, t6                   # witness_len\n" ++
  "  li a5, 0xa0010008           # u256 out at OUTPUT + 8\n" ++
  "  sd zero, 0(a5); sd zero, 8(a5); sd zero, 16(a5); sd zero, 24(a5)\n" ++
  "  jal ra, slot_at_index\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsi_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  slotDecodeU256Function ++ "\n" ++
  slotAtIndexFunction ++ "\n" ++
  ".Lsi_pdone:"

def ziskSlotAtIndexDataSection : String :=
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
  "si_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "si_value_scratch:\n" ++
  "  .zero 256"

def ziskSlotAtIndexProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSlotAtIndexPrologue
  dataAsm     := ziskSlotAtIndexDataSection
}

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

/-- `zisk_rlp_encode_uint_be`: probe BuildUnit. Reads
    (src_len, src_bytes) from host input, writes
    (bytes_written, encoded_bytes) to OUTPUT. -/
def ziskRlpEncodeUintBePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # src_len\n" ++
  "  addi a0, a3, 16             # src ptr\n" ++
  "  li a2, 0xa0010008           # output at OUTPUT + 8\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # bytes_written at OUTPUT + 0\n" ++
  "  j .Lreu_pdone\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  ".Lreu_pdone:"

def ziskRlpEncodeUintBeDataSection : String :=
  ".section .data\n" ++
  "reu_pad:\n" ++
  "  .zero 8"

def ziskRlpEncodeUintBeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRlpEncodeUintBePrologue
  dataAsm     := ziskRlpEncodeUintBeDataSection
}

/-! ## account_encode -- PR-K31 mutating side of account_decode

    Encode (nonce, balance, storage_root, code_hash) into the
    canonical 4-field RLP list bytes used as the value of a
    state-trie leaf node. The inverse of PR-K27 account_decode.

    Composition:
      payload = rlp_encode_uint_be(nonce_be, 8) +
                rlp_encode_uint_be(balance_be, 32) +
                0xa0 + storage_root +
                0xa0 + code_hash
      out = 0xf8 + len(payload) + payload

    The 0xf8 prefix is correct because the payload is always
    > 55 bytes (storage_root + code_hash already total 66 bytes,
    plus at least 2 bytes for nonce/balance encodings).

    Calling convention:
      a0 (input)  : nonce 8-byte BE ptr
      a1 (input)  : balance 32-byte BE ptr
      a2 (input)  : storage_root ptr (32 bytes)
      a3 (input)  : code_hash ptr (32 bytes)
      a4 (input)  : output buffer ptr (≥ 128 bytes)
      a5 (input)  : u64 out ptr (bytes_written)
      ra (input)  : return
      a0 (output) : 0 (always success; cap fixed by caller)

    Scratch: ae_scratch (64 bytes) for staging nonce_rlp +
    balance_rlp before they're copied to the output buffer. -/
def accountEncodeFunction : String :=
  "account_encode:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # nonce_be ptr\n" ++
  "  mv s1, a1                   # balance_be ptr\n" ++
  "  mv s2, a2                   # storage_root ptr\n" ++
  "  mv s3, a3                   # code_hash ptr\n" ++
  "  mv s4, a4                   # output buf\n" ++
  "  mv s5, a5                   # bytes_written out\n" ++
  "  # Step 1: rlp_encode_uint_be(nonce_be, 8) → ae_scratch.\n" ++
  "  mv a0, s0\n" ++
  "  li a1, 8\n" ++
  "  la a2, ae_scratch\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  la t0, ae_nonce_len; sd a0, 0(t0)\n" ++
  "  # Step 2: rlp_encode_uint_be(balance_be, 32) → ae_scratch + nonce_len.\n" ++
  "  la t0, ae_nonce_len; ld t1, 0(t0)\n" ++
  "  la t2, ae_scratch\n" ++
  "  add a2, t2, t1\n" ++
  "  mv a0, s1\n" ++
  "  li a1, 32\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  la t0, ae_balance_len; sd a0, 0(t0)\n" ++
  "  # Step 3: payload_len = nonce_len + balance_len + 33 + 33.\n" ++
  "  la t0, ae_nonce_len; ld t1, 0(t0)\n" ++
  "  la t0, ae_balance_len; ld t2, 0(t0)\n" ++
  "  add t3, t1, t2\n" ++
  "  addi t3, t3, 66            # + 33 + 33 (storage_root + code_hash)\n" ++
  "  # Step 4: write outer prefix 0xf8 + payload_len.\n" ++
  "  mv t4, s4                  # cursor\n" ++
  "  li t5, 0xf8\n" ++
  "  sb t5, 0(t4)\n" ++
  "  sb t3, 1(t4)\n" ++
  "  addi t4, t4, 2\n" ++
  "  # Step 5: copy nonce_rlp (t1 bytes) from ae_scratch to t4.\n" ++
  "  la t5, ae_scratch\n" ++
  "  mv t6, t1                  # remaining\n" ++
  ".Lae_copy_nonce:\n" ++
  "  beqz t6, .Lae_copy_balance_init\n" ++
  "  lbu t1, 0(t5)\n" ++
  "  sb  t1, 0(t4)\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t6, t6, -1\n" ++
  "  j .Lae_copy_nonce\n" ++
  ".Lae_copy_balance_init:\n" ++
  "  # Step 6: copy balance_rlp from ae_scratch + nonce_len. t5 is already there.\n" ++
  "  la t0, ae_balance_len; ld t6, 0(t0)\n" ++
  ".Lae_copy_balance:\n" ++
  "  beqz t6, .Lae_copy_storage_root\n" ++
  "  lbu t1, 0(t5)\n" ++
  "  sb  t1, 0(t4)\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t6, t6, -1\n" ++
  "  j .Lae_copy_balance\n" ++
  ".Lae_copy_storage_root:\n" ++
  "  # Step 7: write 0xa0 + storage_root (32 bytes).\n" ++
  "  li t5, 0xa0\n" ++
  "  sb t5, 0(t4)\n" ++
  "  addi t4, t4, 1\n" ++
  "  ld t5,  0(s2); sd t5,  0(t4)\n" ++
  "  ld t5,  8(s2); sd t5,  8(t4)\n" ++
  "  ld t5, 16(s2); sd t5, 16(t4)\n" ++
  "  ld t5, 24(s2); sd t5, 24(t4)\n" ++
  "  addi t4, t4, 32\n" ++
  "  # Step 8: write 0xa0 + code_hash.\n" ++
  "  li t5, 0xa0\n" ++
  "  sb t5, 0(t4)\n" ++
  "  addi t4, t4, 1\n" ++
  "  ld t5,  0(s3); sd t5,  0(t4)\n" ++
  "  ld t5,  8(s3); sd t5,  8(t4)\n" ++
  "  ld t5, 16(s3); sd t5, 16(t4)\n" ++
  "  ld t5, 24(s3); sd t5, 24(t4)\n" ++
  "  addi t4, t4, 32\n" ++
  "  # bytes_written = (t4 - s4)\n" ++
  "  sub t4, t4, s4\n" ++
  "  sd t4, 0(s5)\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_account_encode`: probe BuildUnit. Reads
    (nonce_be8, balance_be32, storage_root, code_hash) from
    host input (104 bytes total). Writes (bytes_written, RLP)
    to OUTPUT.
    Input layout:
      bytes  0.. 8 : nonce (8-byte BE)
      bytes  8..40 : balance (32-byte BE)
      bytes 40..72 : storage_root (32 B)
      bytes 72..104: code_hash (32 B) -/
def ziskAccountEncodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  addi a0, a6, 8              # nonce_be\n" ++
  "  addi a1, a6, 16             # balance_be\n" ++
  "  addi a2, a6, 48             # storage_root\n" ++
  "  addi a3, a6, 80             # code_hash\n" ++
  "  li a4, 0xa0010008           # output RLP at OUTPUT + 8\n" ++
  "  li a5, 0xa0010000           # bytes_written at OUTPUT + 0\n" ++
  "  jal ra, account_encode\n" ++
  "  j .Lae_pdone\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  accountEncodeFunction ++ "\n" ++
  ".Lae_pdone:"

def ziskAccountEncodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ae_nonce_len:\n" ++
  "  .zero 8\n" ++
  "ae_balance_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "ae_scratch:\n" ++
  "  .zero 64"

def ziskAccountEncodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountEncodePrologue
  dataAsm     := ziskAccountEncodeDataSection
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

/-! ## state_root_single_account -- PR-K33 end-to-end recompute

    Compute the state-trie root for a trie containing exactly
    one account. Composes every mutating primitive shipped so
    far:

      keccak(address)                       (PR-K3)
      bytes_to_nibbles → 64-nibble path     (PR-K25)
      hp_encode_nibbles(path, leaf=true)    (PR-K32)
      account_encode(nonce, balance,
                     storage_root,
                     code_hash)             (PR-K31)
      leaf_rlp = rlp([hp_bytes, account_rlp_bytes])
      state_root = keccak(leaf_rlp)

    This is the smallest useful "compute state_root from
    fields" operation. Future PRs scale to multi-account tries
    by composing branch / extension node builders on top.

    Calling convention:
      a0 (input)  : address bytes ptr
      a1 (input)  : address byte length (typically 20)
      a2 (input)  : nonce 8-byte BE ptr
      a3 (input)  : balance 32-byte BE ptr
      a4 (input)  : storage_root ptr (32 bytes)
      a5 (input)  : code_hash ptr (32 bytes)
      a6 (input)  : state_root output ptr (32 bytes)
      ra (input)  : return
      a0 (output) : 0 success

    Reuses K-stack primitive functions. New scratches:
      srsa_keccak_buf  (32 B)
      srsa_nibble_buf  (64 B)
      srsa_hp_buf      (33 B)  -- 64-nibble path HP-encodes to 33 bytes
      srsa_acc_buf     (128 B) -- account RLP, typically 70..104 B
      srsa_acc_len     (8 B)
      srsa_leaf_buf    (256 B) -- leaf RLP -/
def stateRootSingleAccountFunction : String :=
  "state_root_single_account:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a2                   # nonce_be ptr\n" ++
  "  mv s1, a3                   # balance_be ptr\n" ++
  "  mv s2, a4                   # storage_root ptr\n" ++
  "  mv s3, a5                   # code_hash ptr\n" ++
  "  mv s4, a6                   # state_root output ptr\n" ++
  "  # Step 1: keccak(address) → srsa_keccak_buf.\n" ++
  "  la a2, srsa_keccak_buf\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # Step 2: bytes_to_nibbles → srsa_nibble_buf (64 nibbles).\n" ++
  "  la a0, srsa_keccak_buf\n" ++
  "  li a1, 32\n" ++
  "  la a2, srsa_nibble_buf\n" ++
  "  jal ra, bytes_to_nibbles\n" ++
  "  # Step 3: hp_encode → srsa_hp_buf (33 bytes for 64-nibble leaf).\n" ++
  "  la a0, srsa_nibble_buf\n" ++
  "  li a1, 64\n" ++
  "  li a2, 1\n" ++
  "  la a3, srsa_hp_buf\n" ++
  "  jal ra, hp_encode_nibbles\n" ++
  "  # Step 4: account_encode → srsa_acc_buf.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s2\n" ++
  "  mv a3, s3\n" ++
  "  la a4, srsa_acc_buf\n" ++
  "  la a5, srsa_acc_len\n" ++
  "  jal ra, account_encode\n" ++
  "  # Step 5: build leaf RLP at srsa_leaf_buf.\n" ++
  "  la t0, srsa_acc_len; ld t1, 0(t0)\n" ++
  "  # payload_len = 34 (hp) + (1 or 2) prefix + acc_len\n" ++
  "  # For acc_len ≥ 56: acc prefix = 2 bytes (0xb8 + len). 0xa1 + 33 hp = 34. Total 34 + 2 + acc_len.\n" ++
  "  li t2, 56\n" ++
  "  bltu t1, t2, .Lsrsa_acc_short\n" ++
  "  addi t2, t1, 36              # payload = 34 + 2 + acc_len\n" ++
  "  j .Lsrsa_have_payload\n" ++
  ".Lsrsa_acc_short:\n" ++
  "  addi t2, t1, 35              # payload = 34 + 1 + acc_len\n" ++
  ".Lsrsa_have_payload:\n" ++
  "  # Write outer prefix: 0xf8 + payload_len.\n" ++
  "  la t3, srsa_leaf_buf\n" ++
  "  li t4, 0xf8\n" ++
  "  sb t4, 0(t3)\n" ++
  "  sb t2, 1(t3)\n" ++
  "  addi t3, t3, 2\n" ++
  "  # Write 0xa1 + 33 hp bytes.\n" ++
  "  li t4, 0xa1\n" ++
  "  sb t4, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  "  la t5, srsa_hp_buf\n" ++
  "  li t6, 33\n" ++
  ".Lsrsa_copy_hp:\n" ++
  "  beqz t6, .Lsrsa_hp_done\n" ++
  "  lbu t4, 0(t5)\n" ++
  "  sb  t4, 0(t3)\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t6, t6, -1\n" ++
  "  j .Lsrsa_copy_hp\n" ++
  ".Lsrsa_hp_done:\n" ++
  "  # Write account_rlp prefix.\n" ++
  "  li t4, 56\n" ++
  "  bltu t1, t4, .Lsrsa_acc_short_pfx\n" ++
  "  li t4, 0xb8\n" ++
  "  sb t4, 0(t3)\n" ++
  "  sb t1, 1(t3)\n" ++
  "  addi t3, t3, 2\n" ++
  "  j .Lsrsa_acc_copy\n" ++
  ".Lsrsa_acc_short_pfx:\n" ++
  "  li t4, 0x80\n" ++
  "  add t4, t4, t1\n" ++
  "  sb t4, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  ".Lsrsa_acc_copy:\n" ++
  "  la t5, srsa_acc_buf\n" ++
  "  mv t6, t1\n" ++
  ".Lsrsa_copy_acc:\n" ++
  "  beqz t6, .Lsrsa_acc_done\n" ++
  "  lbu t4, 0(t5)\n" ++
  "  sb  t4, 0(t3)\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t6, t6, -1\n" ++
  "  j .Lsrsa_copy_acc\n" ++
  ".Lsrsa_acc_done:\n" ++
  "  # leaf_len = t3 - srsa_leaf_buf; keccak the leaf into s4.\n" ++
  "  la t5, srsa_leaf_buf\n" ++
  "  sub a1, t3, t5\n" ++
  "  mv a0, t5\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_state_root_single_account`: probe BuildUnit. Reads
    (addr_len, address, nonce_be, balance_be, storage_root,
     code_hash) from host input, writes the 32-byte state_root
    to OUTPUT. -/
def ziskStateRootSingleAccountPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld t6, 8(a7)                # addr_len\n" ++
  "  addi a0, a7, 16             # addr ptr\n" ++
  "  mv a1, t6\n" ++
  "  add a2, a0, t6              # nonce_be at addr + addr_len\n" ++
  "  addi a3, a2, 8              # balance_be at +8\n" ++
  "  addi a4, a3, 32             # storage_root at +32\n" ++
  "  addi a5, a4, 32             # code_hash at +32\n" ++
  "  li a6, 0xa0010000           # state_root out at OUTPUT + 0\n" ++
  "  jal ra, state_root_single_account\n" ++
  "  j .Lsrsa_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  accountEncodeFunction ++ "\n" ++
  stateRootSingleAccountFunction ++ "\n" ++
  ".Lsrsa_pdone:"

def ziskStateRootSingleAccountDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "srsa_keccak_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "srsa_nibble_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "srsa_hp_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "srsa_acc_buf:\n" ++
  "  .zero 128\n" ++
  ".balign 8\n" ++
  "srsa_acc_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "ae_nonce_len:\n" ++
  "  .zero 8\n" ++
  "ae_balance_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "ae_scratch:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "srsa_leaf_buf:\n" ++
  "  .zero 256"

def ziskStateRootSingleAccountProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskStateRootSingleAccountPrologue
  dataAsm     := ziskStateRootSingleAccountDataSection
}

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

/-! ## header_minimal_decode -- PR-K38

    Decode the 4 STF-essential fields of an RLP-encoded
    Ethereum block header into a flat 96-byte output struct:

       0..32   parent_hash    (RLP field 0)
      32..64   state_root     (RLP field 3)
      64..72   number (u64)   (RLP field 8)
      72..80   timestamp(u64) (RLP field 11; rejected if > 8 B)

    Header RLP field count varies by fork (15..22 fields).
    This decoder reads only the first 12 fields' indices, so
    it works on any post-Berlin header.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 96-byte output struct ptr
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail (not an RLP list,
                    parent_hash or state_root not 32 bytes,
                    or timestamp > 8 bytes BE).

    Composes PR-K20 `rlp_list_nth_item` + PR-K34
    `rlp_field_to_u64`. The hash fields are copied via 4 ×
    8-byte `ld`/`sd` (each 32-byte hash). -/
def headerMinimalDecodeFunction : String :=
  "header_minimal_decode:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_len\n" ++
  "  mv s2, a2                  # struct out\n" ++
  "  # Field 0: parent_hash (32 bytes)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0\n" ++
  "  la a3, hmd_offset; la a4, hmd_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhmd_fail\n" ++
  "  la t0, hmd_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhmd_fail\n" ++
  "  la t0, hmd_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  # Field 3: state_root (32 bytes at struct + 32)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  la a3, hmd_offset; la a4, hmd_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhmd_fail\n" ++
  "  la t0, hmd_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhmd_fail\n" ++
  "  la t0, hmd_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  addi t4, s2, 32\n" ++
  "  ld t5,  0(t3); sd t5,  0(t4)\n" ++
  "  ld t5,  8(t3); sd t5,  8(t4)\n" ++
  "  ld t5, 16(t3); sd t5, 16(t4)\n" ++
  "  ld t5, 24(t3); sd t5, 24(t4)\n" ++
  "  # Field 8: number (u64 at struct + 64)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 8\n" ++
  "  addi a3, s2, 64\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lhmd_fail\n" ++
  "  # Field 11: timestamp (u64 at struct + 72)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 11\n" ++
  "  addi a3, s2, 72\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lhmd_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lhmd_ret\n" ++
  ".Lhmd_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lhmd_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_minimal_decode`: probe BuildUnit. Reads
    (header_len, header_bytes) from host input, writes
    (status, 96-byte struct) to OUTPUT. -/
def ziskHeaderMinimalDecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 96 bytes.\n" ++
  "  mv t0, a2; li t1, 12\n" ++
  ".Lhmd_zinit:\n" ++
  "  beqz t1, .Lhmd_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lhmd_zinit\n" ++
  ".Lhmd_zdone:\n" ++
  "  jal ra, header_minimal_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhmd_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerMinimalDecodeFunction ++ "\n" ++
  ".Lhmd_pdone:"

def ziskHeaderMinimalDecodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "hmd_offset:\n" ++
  "  .zero 8\n" ++
  "hmd_length:\n" ++
  "  .zero 8"

def ziskHeaderMinimalDecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderMinimalDecodePrologue
  dataAsm     := ziskHeaderMinimalDecodeDataSection
}

/-! ## header_extended_decode -- PR-K39

    Extends PR-K38 `header_minimal_decode` with three more
    STF-essential fields:

       0..32   parent_hash    (field 0)
      32..64   state_root     (field 3)
      64..72   number         (field 8, u64)
      72..80   timestamp      (field 11, u64)
      80..88   gas_limit      (field 9, u64)
      88..96   gas_used       (field 10, u64)
      96..128  base_fee_per_gas (field 15, u256 BE)

    The base_fee_per_gas field exists from EIP-1559 (London)
    onward. Headers older than London don't have it; this
    function rejects (status=1) if field 15 doesn't exist.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header byte length
      a2 (input)  : 128-byte output struct ptr
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail. -/
def headerExtendedDecodeFunction : String :=
  "header_extended_decode:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_len\n" ++
  "  mv s2, a2                  # struct out\n" ++
  "  # Field 0: parent_hash\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0\n" ++
  "  la a3, hmd_offset; la a4, hmd_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhed_fail\n" ++
  "  la t0, hmd_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhed_fail\n" ++
  "  la t0, hmd_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  # Field 3: state_root\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  la a3, hmd_offset; la a4, hmd_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhed_fail\n" ++
  "  la t0, hmd_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhed_fail\n" ++
  "  la t0, hmd_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  addi t4, s2, 32\n" ++
  "  ld t5,  0(t3); sd t5,  0(t4)\n" ++
  "  ld t5,  8(t3); sd t5,  8(t4)\n" ++
  "  ld t5, 16(t3); sd t5, 16(t4)\n" ++
  "  ld t5, 24(t3); sd t5, 24(t4)\n" ++
  "  # Field 8: number\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 8\n" ++
  "  addi a3, s2, 64\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lhed_fail\n" ++
  "  # Field 11: timestamp\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 11\n" ++
  "  addi a3, s2, 72\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lhed_fail\n" ++
  "  # Field 9: gas_limit\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 9\n" ++
  "  addi a3, s2, 80\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lhed_fail\n" ++
  "  # Field 10: gas_used\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 10\n" ++
  "  addi a3, s2, 88\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lhed_fail\n" ++
  "  # Field 15: base_fee_per_gas (u256)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 15\n" ++
  "  addi a3, s2, 96\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lhed_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lhed_ret\n" ++
  ".Lhed_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lhed_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_extended_decode`: probe BuildUnit. -/
def ziskHeaderExtendedDecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 128 bytes.\n" ++
  "  mv t0, a2; li t1, 16\n" ++
  ".Lhed_zinit:\n" ++
  "  beqz t1, .Lhed_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lhed_zinit\n" ++
  ".Lhed_zdone:\n" ++
  "  jal ra, header_extended_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhed_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  headerExtendedDecodeFunction ++ "\n" ++
  ".Lhed_pdone:"

def ziskHeaderExtendedDecodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "hmd_offset:\n" ++
  "  .zero 8\n" ++
  "hmd_length:\n" ++
  "  .zero 8"

def ziskHeaderExtendedDecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtendedDecodePrologue
  dataAsm     := ziskHeaderExtendedDecodeDataSection
}

/-! ## coinbase_extract_from_header -- PR-K55 beneficiary getter

    Extract the 20-byte beneficiary (coinbase) address — field 2
    of an RLP-encoded block header. Direct input to
    `process_transaction`'s priority-fee credit:

      coinbase.balance += effective_priority_fee × gas_used

    The header decoders PR-K38 / PR-K39 read parent_hash,
    state_root, gas_limit, gas_used, etc., but skip the
    beneficiary since it isn't part of the STF skeleton's
    minimal/extended struct. This helper is the dedicated getter
    for callers that only need the coinbase.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 20-byte output ptr (caller-supplied)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail (not a list or field
                    2 not 20 bytes). On failure, output is zeroed.

    Composes PR-K20 `rlp_list_nth_item`. Uses two 8-byte `.data`
    scratch slots (`ceh_offset`, `ceh_length`). -/
def coinbaseExtractFromHeaderFunction : String :=
  "coinbase_extract_from_header:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_len\n" ++
  "  mv s2, a2                  # output 20B ptr\n" ++
  "  # Get field 2 (coinbase) bounds.\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  la a3, ceh_offset; la a4, ceh_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lceh_fail\n" ++
  "  la t0, ceh_length; ld t1, 0(t0)\n" ++
  "  li t2, 20\n" ++
  "  bne t1, t2, .Lceh_fail\n" ++
  "  la t0, ceh_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  # Copy 20 bytes: 8 + 8 + 4 = 20.\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  lwu t4, 16(t3); sw t4, 16(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lceh_ret\n" ++
  ".Lceh_fail:\n" ++
  "  sd zero,  0(s2); sd zero, 8(s2); sw zero, 16(s2)\n" ++
  "  li a0, 1\n" ++
  ".Lceh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_coinbase_extract_from_header`: probe BuildUnit. Reads
    (header_len, header_bytes) from host input, writes
    (status, 20B address + 4B pad) to OUTPUT (32 bytes total). -/
def ziskCoinbaseExtractFromHeaderPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  li a2, 0xa0010008           # 20B output at OUTPUT + 8\n" ++
  "  # Pre-zero the 20B output + 4B trailing pad.\n" ++
  "  mv t0, a2\n" ++
  "  sd zero, 0(t0); sd zero, 8(t0); sw zero, 16(t0)\n" ++
  "  jal ra, coinbase_extract_from_header\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lceh_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  coinbaseExtractFromHeaderFunction ++ "\n" ++
  ".Lceh_pdone:"

def ziskCoinbaseExtractFromHeaderDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ceh_offset:\n" ++
  "  .zero 8\n" ++
  "ceh_length:\n" ++
  "  .zero 8"

def ziskCoinbaseExtractFromHeaderProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCoinbaseExtractFromHeaderPrologue
  dataAsm     := ziskCoinbaseExtractFromHeaderDataSection
}

/-! ## header_extract_blob_gas_pair -- PR-K90 Cancun blob fields

    Extract the EIP-4844 blob-gas fields from an Amsterdam header:

      blob_gas_used    (header field 17, u64) — total blob gas
        consumed by all transactions in this block (= sum of
        `len(tx.blob_versioned_hashes) × GAS_PER_BLOB` over type-3
        txs). Cross-checks against PR-K89.

      excess_blob_gas  (header field 18, u64) — running total used
        for the blob-fee adjustment formula.

    Cancun-era (and later) headers always have both. Pre-Cancun
    headers don't, and the extractor reports a parse failure.

    Direct inputs to:
      * the apply_body invariant
        `header.blob_gas_used == sum(tx.blob_gas_used)`
      * the next-block `excess_blob_gas` recurrence used in
        `calculate_excess_blob_gas`.

    Output layout (16 bytes):
       0..  8  blob_gas_used    (u64 LE)
       8.. 16  excess_blob_gas  (u64 LE)

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 16-byte output ptr (caller-supplied)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : header parse failed / field 17 missing / not u64
        2 : field 18 missing / not u64

    Composes PR-K20 `rlp_list_nth_item` via PR-K53
    `rlp_field_to_u64`. Uses two 8-byte `.data` scratch slots
    (`rfu_offset`, `rfu_length`) shared with other K-helpers. -/
def headerExtractBlobGasPairFunction : String :=
  "header_extract_blob_gas_pair:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_len\n" ++
  "  mv s2, a2                  # output 16B ptr\n" ++
  "  # Field 17: blob_gas_used → out[0..8]\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 17\n" ++
  "  mv a3, s2\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  beqz a0, .Lhebgp_f18\n" ++
  "  sd zero, 0(s2); sd zero, 8(s2)\n" ++
  "  li a0, 1\n" ++
  "  j .Lhebgp_ret\n" ++
  ".Lhebgp_f18:\n" ++
  "  # Field 18: excess_blob_gas → out[8..16]\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 18\n" ++
  "  addi a3, s2, 8\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  beqz a0, .Lhebgp_ok\n" ++
  "  sd zero, 0(s2); sd zero, 8(s2)\n" ++
  "  li a0, 2\n" ++
  "  j .Lhebgp_ret\n" ++
  ".Lhebgp_ok:\n" ++
  "  li a0, 0\n" ++
  ".Lhebgp_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_extract_blob_gas_pair`: probe BuildUnit. Reads
    (header_len, header_bytes), writes (status, blob_gas_used,
    excess_blob_gas) to OUTPUT (24 bytes total). -/
def ziskHeaderExtractBlobGasPairPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  li a2, 0xa0010008           # 16B output at OUTPUT + 8\n" ++
  "  sd zero, 0(a2); sd zero, 8(a2)\n" ++
  "  jal ra, header_extract_blob_gas_pair\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lhebgp_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractBlobGasPairFunction ++ "\n" ++
  ".Lhebgp_pdone:"

def ziskHeaderExtractBlobGasPairDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractBlobGasPairProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractBlobGasPairPrologue
  dataAsm     := ziskHeaderExtractBlobGasPairDataSection
}

/-! ## validate_header_basic -- PR-K43 per-header semantic checks

    Three u64 invariants from `validate_header` (Python:
    `forks/amsterdam/fork.py`):

      1. gas_used <= gas_limit
      2. number == parent.number + 1
      3. timestamp > parent.timestamp

    Both inputs are 128-byte extended-header structs as produced
    by PR-K39 `header_extended_decode`. Only the u64 fields at
    offsets 64 (number), 72 (timestamp), 80 (gas_limit), 88
    (gas_used) are read; the hash fields (parent_hash,
    state_root) and base_fee_per_gas are ignored here -- those
    are checked elsewhere (PR-K18 `validate_chain` for the hash
    chain, future PR for the EIP-1559 base-fee formula).

    Calling convention:
      a0 (input)  : header_ptr (128-byte struct, this header)
      a1 (input)  : parent_ptr (128-byte struct, parent header)
      ra (input)  : return
      a0 (output) : 0 ok
                    1 gas_used > gas_limit
                    2 number != parent.number + 1
                    3 timestamp <= parent.timestamp

    Pure register arithmetic, no scratch memory, leaf-callable. -/
def validateHeaderBasicFunction : String :=
  "validate_header_basic:\n" ++
  "  ld t0, 88(a0)              # this.gas_used\n" ++
  "  ld t1, 80(a0)              # this.gas_limit\n" ++
  "  bgtu t0, t1, .Lvhb_fail_gas\n" ++
  "  ld t0, 64(a0)              # this.number\n" ++
  "  ld t1, 64(a1)              # parent.number\n" ++
  "  addi t1, t1, 1\n" ++
  "  bne t0, t1, .Lvhb_fail_number\n" ++
  "  ld t0, 72(a0)              # this.timestamp\n" ++
  "  ld t1, 72(a1)              # parent.timestamp\n" ++
  "  bgeu t1, t0, .Lvhb_fail_timestamp  # parent_ts >= this_ts → fail\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lvhb_fail_gas:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Lvhb_fail_number:\n" ++
  "  li a0, 2\n" ++
  "  ret\n" ++
  ".Lvhb_fail_timestamp:\n" ++
  "  li a0, 3\n" ++
  "  ret"

/-- `zisk_validate_header_basic`: probe BuildUnit. Reads two
    128-byte extended-header structs from host input (after an
    8-byte tag) and writes the 8-byte status to OUTPUT. -/
def ziskValidateHeaderBasicPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  # Input layout: [pad u64][header 128B][parent 128B]\n" ++
  "  addi a0, a3, 8              # header_ptr\n" ++
  "  addi a1, a3, 136            # parent_ptr (8 + 128)\n" ++
  "  jal ra, validate_header_basic\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lvhb_pdone\n" ++
  validateHeaderBasicFunction ++ "\n" ++
  ".Lvhb_pdone:"

def ziskValidateHeaderBasicDataSection : String :=
  ".section .data\n" ++
  "vhb_pad:\n" ++
  "  .zero 8"

def ziskValidateHeaderBasicProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateHeaderBasicPrologue
  dataAsm     := ziskValidateHeaderBasicDataSection
}

/-! ## check_gas_limit -- PR-K72 gas-limit continuity check

    Verify the per-header gas-limit elasticity rules per
    Ethereum's `check_gas_limit`:

      max_adjustment_delta = parent_gas_limit // 1024
      |gas_limit - parent_gas_limit| < max_adjustment_delta
      gas_limit >= GAS_LIMIT_MINIMUM (5000)

    Used by `validate_header` to ensure consecutive blocks
    smoothly adjust their gas-limit ceiling. Adoption is
    EIP-1985 + EIP-1559 elasticity.

    Pure u64 arithmetic (shift, sub, compare). No scratch
    memory, leaf-callable.

    Calling convention:
      a0 (input)  : new.gas_limit    (u64)
      a1 (input)  : parent.gas_limit (u64)
      ra (input)  : return
      a0 (output) :
        0  : all checks pass
        1  : new.gas_limit < GAS_LIMIT_MINIMUM (5000)
        2  : |new - parent| >= parent / 1024 (jumped too far) -/
def checkGasLimitFunction : String :=
  "check_gas_limit:\n" ++
  "  li t0, 5000                 # GAS_LIMIT_MINIMUM\n" ++
  "  bltu a0, t0, .Lcgl_fail_min\n" ++
  "  # max_adjustment_delta = parent_gas_limit >> 10  (== /1024)\n" ++
  "  srli t1, a1, 10\n" ++
  "  # abs_diff = |new - parent|\n" ++
  "  bgtu a0, a1, .Lcgl_pos\n" ++
  "  sub t2, a1, a0\n" ++
  "  j .Lcgl_check\n" ++
  ".Lcgl_pos:\n" ++
  "  sub t2, a0, a1\n" ++
  ".Lcgl_check:\n" ++
  "  bgeu t2, t1, .Lcgl_fail_jump\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lcgl_fail_min:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Lcgl_fail_jump:\n" ++
  "  li a0, 2\n" ++
  "  ret"

/-- `zisk_check_gas_limit`: probe BuildUnit. Reads (new_limit,
    parent_limit) as 2 u64s from host input, writes 8-byte
    status to OUTPUT. -/
def ziskCheckGasLimitPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a0,  8(t0)               # new.gas_limit\n" ++
  "  ld a1, 16(t0)               # parent.gas_limit\n" ++
  "  jal ra, check_gas_limit\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lcgl_pdone\n" ++
  checkGasLimitFunction ++ "\n" ++
  ".Lcgl_pdone:"

def ziskCheckGasLimitDataSection : String :=
  ".section .data\n" ++
  "cgl_pad:\n" ++
  "  .zero 8"

def ziskCheckGasLimitProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCheckGasLimitPrologue
  dataAsm     := ziskCheckGasLimitDataSection
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

/-! ## calc_excess_blob_gas -- PR-K63 EIP-4844 excess blob gas formula

    Compute the next header's `excess_blob_gas` field from the
    parent header. Python (`forks/cancun/fork.py::
    calculate_excess_blob_gas`):

      def calculate_excess_blob_gas(parent_header):
          excess_blob_gas = (
              parent_header.excess_blob_gas
              + parent_header.blob_gas_used
          )
          if excess_blob_gas < TARGET_BLOB_GAS_PER_BLOCK:
              return 0
          return excess_blob_gas - TARGET_BLOB_GAS_PER_BLOCK

    Equivalent to: `max(0, parent.excess_blob_gas +
    parent.blob_gas_used - target)`.

    Used by `validate_header` to check that
    `header.excess_blob_gas == calc_excess_blob_gas(parent,
    target)`.

    The `target` is parameterized — Cancun uses 3 blobs × 131072
    bytes = 393216; Prague/Amsterdam may use a higher target via
    EIP-7691 (e.g. 6 blobs × 131072 = 786432). The function takes
    `target` as an explicit u64 input so it works across forks.

    ## Precondition

    `parent_excess + parent_blob_used` must not overflow u64. In
    practice both terms are small (each < 2^30 on mainnet), so
    overflow doesn't occur. The function does NOT check.

    Calling convention:
      a0 (input)  : parent.excess_blob_gas (u64)
      a1 (input)  : parent.blob_gas_used (u64)
      a2 (input)  : target_blob_gas_per_block (u64)
      ra (input)  : return
      a0 (output) : excess_blob_gas for this header (u64).

    Pure register arithmetic, no scratch memory, leaf-callable. -/
def calcExcessBlobGasFunction : String :=
  "calc_excess_blob_gas:\n" ++
  "  add t0, a0, a1              # parent_excess + parent_used\n" ++
  "  bgeu t0, a2, .Lcebg_pos     # >= target → return diff\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lcebg_pos:\n" ++
  "  sub a0, t0, a2\n" ++
  "  ret"

/-- `zisk_calc_excess_blob_gas`: probe BuildUnit. Reads
    (parent_excess, parent_used, target) from host input, writes
    the u64 result to OUTPUT. -/
def ziskCalcExcessBlobGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a0, 8(a3)                # parent_excess_blob_gas\n" ++
  "  ld a1, 16(a3)               # parent_blob_gas_used\n" ++
  "  ld a2, 24(a3)               # target_blob_gas_per_block\n" ++
  "  jal ra, calc_excess_blob_gas\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcebg_pdone\n" ++
  calcExcessBlobGasFunction ++ "\n" ++
  ".Lcebg_pdone:"

def ziskCalcExcessBlobGasDataSection : String :=
  ".section .data\n" ++
  "cebg_pad:\n" ++
  "  .zero 8"

def ziskCalcExcessBlobGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCalcExcessBlobGasPrologue
  dataAsm     := ziskCalcExcessBlobGasDataSection
}

/-! ## header_validate_post_merge -- PR-K67

    Verify the three post-merge header invariants:

      1. header.ommers_hash == EMPTY_OMMERS_HASH
         (= keccak256(rlp([])) = 0x1dcc4de8...49347)
      2. header.difficulty == 0   (canonical RLP: empty-string,
                                   content_length == 0)
      3. header.nonce == 0x0000000000000000   (8 zero bytes)

    Mirrors the Python `validate_header` checks added at the
    Merge fork:

      assert header.ommers_hash == EMPTY_OMMERS_HASH
      assert header.difficulty == 0
      assert header.nonce == b"\\x00" * 8

    Composes PR-K20 `rlp_list_nth_item` for field extraction.
    Each check has a distinct return code so callers can pinpoint
    which invariant failed.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      ra (input)  : return
      a0 (output) :
        0  : all three invariants hold
        1  : ommers_hash mismatch
        2  : difficulty != 0
        3  : nonce not 8 zero bytes
        4  : RLP parse failure (e.g. not a list, field missing)

    Uses 40 bytes of `.data` scratch (`hvpm_off`, `hvpm_len`
    + 32-byte `empty_ommers_hash` constant). -/
def headerValidatePostMergeFunction : String :=
  "header_validate_post_merge:\n" ++
  "  addi sp, sp, -24\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0                   # header ptr\n" ++
  "  mv s1, a1                   # header_len\n" ++
  "  # Check 1: field 1 (ommers_hash) == EMPTY_OMMERS_HASH.\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  la a3, hvpm_off; la a4, hvpm_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhvpm_fail_parse\n" ++
  "  la t0, hvpm_len; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhvpm_fail_oh\n" ++
  "  la t0, hvpm_off; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  la t4, empty_ommers_hash\n" ++
  "  ld t5,  0(t3); ld t6,  0(t4); bne t5, t6, .Lhvpm_fail_oh\n" ++
  "  ld t5,  8(t3); ld t6,  8(t4); bne t5, t6, .Lhvpm_fail_oh\n" ++
  "  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Lhvpm_fail_oh\n" ++
  "  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Lhvpm_fail_oh\n" ++
  "  # Check 2: field 7 (difficulty) is canonical-zero (len 0).\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 7\n" ++
  "  la a3, hvpm_off; la a4, hvpm_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhvpm_fail_parse\n" ++
  "  la t0, hvpm_len; ld t1, 0(t0)\n" ++
  "  bnez t1, .Lhvpm_fail_diff\n" ++
  "  # Check 3: field 14 (nonce) is 8 zero bytes.\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 14\n" ++
  "  la a3, hvpm_off; la a4, hvpm_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhvpm_fail_parse\n" ++
  "  la t0, hvpm_len; ld t1, 0(t0)\n" ++
  "  li t2, 8\n" ++
  "  bne t1, t2, .Lhvpm_fail_nonce\n" ++
  "  la t0, hvpm_off; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  ld t5, 0(t3)\n" ++
  "  bnez t5, .Lhvpm_fail_nonce\n" ++
  "  li a0, 0\n" ++
  "  j .Lhvpm_ret\n" ++
  ".Lhvpm_fail_oh:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhvpm_ret\n" ++
  ".Lhvpm_fail_diff:\n" ++
  "  li a0, 2\n" ++
  "  j .Lhvpm_ret\n" ++
  ".Lhvpm_fail_nonce:\n" ++
  "  li a0, 3\n" ++
  "  j .Lhvpm_ret\n" ++
  ".Lhvpm_fail_parse:\n" ++
  "  li a0, 4\n" ++
  ".Lhvpm_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 24\n" ++
  "  ret"

/-- `zisk_header_validate_post_merge`: probe BuildUnit. Reads
    (header_len, header_bytes) from host input, writes 8-byte
    status to OUTPUT. -/
def ziskHeaderValidatePostMergePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  jal ra, header_validate_post_merge\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhvpm_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerValidatePostMergeFunction ++ "\n" ++
  ".Lhvpm_pdone:"

def ziskHeaderValidatePostMergeDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "empty_ommers_hash:\n" ++
  "  .byte 0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a\n" ++
  "  .byte 0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a\n" ++
  "  .byte 0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13\n" ++
  "  .byte 0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47\n" ++
  ".balign 8\n" ++
  "hvpm_off:\n" ++
  "  .zero 8\n" ++
  "hvpm_len:\n" ++
  "  .zero 8"

def ziskHeaderValidatePostMergeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderValidatePostMergePrologue
  dataAsm     := ziskHeaderValidatePostMergeDataSection
}


/-! ## header_validate_extra_data_length -- PR-K68

    Verify the Ethereum spec constraint that `header.extra_data`
    is at most 32 bytes (Yellow Paper §4.4.4).

    Mirrors the Python check in `validate_header`:

      assert len(header.extra_data) <= 32

    Composes PR-K20 `rlp_list_nth_item` to extract field 12
    (extra_data) and a single u64 compare.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      ra (input)  : return
      a0 (output) :
        0  : extra_data length ≤ 32 bytes
        1  : extra_data length > 32 bytes (reject)
        2  : RLP parse failure (e.g. not a list, field missing)

    Uses two 8-byte `.data` scratch slots (`hved_off`,
    `hved_len`). -/
def headerValidateExtraDataLengthFunction : String :=
  "header_validate_extra_data_length:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra,  0(sp)\n" ++
  "  li a2, 12\n" ++
  "  la a3, hved_off\n" ++
  "  la a4, hved_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhved_parse_fail\n" ++
  "  la t0, hved_len; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bgtu t1, t2, .Lhved_too_long\n" ++
  "  li a0, 0\n" ++
  "  j .Lhved_ret\n" ++
  ".Lhved_too_long:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhved_ret\n" ++
  ".Lhved_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhved_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_header_validate_extra_data_length`: probe BuildUnit.
    Reads (header_len, header_bytes), writes 8-byte status. -/
def ziskHeaderValidateExtraDataLengthPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  jal ra, header_validate_extra_data_length\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhved_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerValidateExtraDataLengthFunction ++ "\n" ++
  ".Lhved_pdone:"

def ziskHeaderValidateExtraDataLengthDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "hved_off:\n" ++
  "  .zero 8\n" ++
  "hved_len:\n" ++
  "  .zero 8"

def ziskHeaderValidateExtraDataLengthProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderValidateExtraDataLengthPrologue
  dataAsm     := ziskHeaderValidateExtraDataLengthDataSection
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

/-! ## account_charge_gas_pre_exec -- PR-K81

    Apply the pre-EVM sender-account mutation per Python's
    `process_transaction`:

      sender.balance -= effective_gas_price * gas_limit
      sender.nonce   += 1

    Mirrors the upfront max-gas-fee withdrawal in Python:

      sender_account.balance -= effective_gas_price * tx.gas
      sender_account.nonce   += 1

    Note: tx.value is NOT deducted here — it's transferred
    internally by the EVM via CALL/CREATE semantics. This helper
    only handles the gas-fee deduction + nonce bump.

    Post-execution, the caller refunds unused gas via:

      sender.balance += remaining_gas * effective_gas_price

    Composes:
      - PR-K54 `u256_mul_u64_be` — compute gas_fee
      - PR-K52 `u256_sub_be`     — deduct from balance

    The caller passes the current nonce via an in-out `nonce_ptr`
    (u64); this helper reads it, then writes back `nonce + 1`.
    The balance is modified in place.

    Calling convention:
      a0 (input)  : balance ptr (32 B u256 BE; modified in place)
      a1 (input)  : effective_gas_price ptr (32 B u256 BE)
      a2 (input)  : gas_limit (u64)
      a3 (input)  : nonce ptr (u64; in-out; receives nonce+1)
      ra (input)  : return
      a0 (output) :
        0  : success — balance reduced, nonce incremented
        1  : gas_fee computation overflowed u256
        2  : balance < gas_fee (caller should have already
             rejected via PR-K79 `validate_transaction_balance`,
             but the underflow is reported as a safety net)

    Uses 32 bytes of `.data` scratch (`acpg_gas_fee`) plus the
    40-byte `u256m_acc` scratch from PR-K54. -/
def accountChargeGasPreExecFunction : String :=
  "account_charge_gas_pre_exec:\n" ++
  "  addi sp, sp, -24\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0                   # balance ptr\n" ++
  "  mv s1, a3                   # nonce ptr (in-out)\n" ++
  "  # gas_fee = effective_gas_price × gas_limit\n" ++
  "  mv a0, a1\n" ++
  "  mv a1, a2\n" ++
  "  la a2, acpg_gas_fee\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lacpg_fail_mul\n" ++
  "  # balance -= gas_fee\n" ++
  "  mv a0, s0\n" ++
  "  la a1, acpg_gas_fee\n" ++
  "  mv a2, s0\n" ++
  "  jal ra, u256_sub_be\n" ++
  "  bnez a0, .Lacpg_fail_sub\n" ++
  "  # *nonce_ptr += 1\n" ++
  "  ld t0, 0(s1)\n" ++
  "  addi t0, t0, 1\n" ++
  "  sd t0, 0(s1)\n" ++
  "  li a0, 0\n" ++
  "  j .Lacpg_ret\n" ++
  ".Lacpg_fail_mul:\n" ++
  "  li a0, 1\n" ++
  "  j .Lacpg_ret\n" ++
  ".Lacpg_fail_sub:\n" ++
  "  li a0, 2\n" ++
  ".Lacpg_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 24\n" ++
  "  ret"

/-- `zisk_account_charge_gas_pre_exec`: probe BuildUnit. Reads
    (32B balance, 32B egp, 8B gas_limit LE, 8B nonce LE) from
    host input; copies them into OUTPUT-resident buffers; calls
    the helper; writes (status, new_balance, new_nonce) to
    OUTPUT (8 + 32 + 8 = 48 bytes). -/
def ziskAccountChargeGasPreExecPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  # Copy balance to OUTPUT + 8 (in-place mutation target)\n" ++
  "  li a0, 0xa0010008\n" ++
  "  addi t1, a4, 8\n" ++
  "  ld t2,  0(t1); sd t2,  0(a0)\n" ++
  "  ld t2,  8(t1); sd t2,  8(a0)\n" ++
  "  ld t2, 16(t1); sd t2, 16(a0)\n" ++
  "  ld t2, 24(t1); sd t2, 24(a0)\n" ++
  "  # egp ptr → input region\n" ++
  "  addi a1, a4, 40             # egp ptr at file offset 32\n" ++
  "  ld a2, 72(a4)               # gas_limit\n" ++
  "  # Copy nonce to OUTPUT + 40 (8 B in-out scratch)\n" ++
  "  li a3, 0xa0010028\n" ++
  "  ld t2, 80(a4)\n" ++
  "  sd t2, 0(a3)\n" ++
  "  jal ra, account_charge_gas_pre_exec\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lacpg_pdone\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  accountChargeGasPreExecFunction ++ "\n" ++
  ".Lacpg_pdone:"

def ziskAccountChargeGasPreExecDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40\n" ++
  ".balign 32\n" ++
  "acpg_gas_fee:\n" ++
  "  .zero 32"

def ziskAccountChargeGasPreExecProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountChargeGasPreExecPrologue
  dataAsm     := ziskAccountChargeGasPreExecDataSection
}

/-! ## account_refund_gas_post_exec -- PR-K82

    Apply the post-EVM gas accounting mutations per Python's
    `process_transaction`:

      gas_refund    = remaining_gas * effective_gas_price
      sender.balance   += gas_refund
      priority_credit  = gas_used * priority_fee_per_gas
      coinbase.balance += priority_credit

    Where `priority_fee_per_gas = effective_gas_price - base_fee_per_gas`
    (the pre-computed result from PR-K62
    `priority_fee_per_gas_eip1559`).

    Sister to PR-K81 `account_charge_gas_pre_exec`. Together they
    bracket `execute_message`:

      pre:  K81 → sender.balance -= max_gas_fee; sender.nonce++
      ...   EVM run
      post: K82 → sender.balance += gas_refund;
                 coinbase.balance += priority_credit

    Composes:
      - PR-K54 `u256_mul_u64_be` × 2 (sender_refund + coinbase_credit)
      - PR-K51 `u256_add_be` × 2

    Calling convention:
      a0 (input)  : sender.balance ptr (32 B u256 BE; mod in place)
      a1 (input)  : coinbase.balance ptr (32 B u256 BE; mod in place)
      a2 (input)  : effective_gas_price ptr (32 B u256 BE)
      a3 (input)  : priority_fee_per_gas ptr (32 B u256 BE)
      a4 (input)  : gas_used (u64)
      a5 (input)  : remaining_gas (u64)
      ra (input)  : return
      a0 (output) :
        0  : success — both balances updated
        1  : mul overflow on refund or credit
        2  : add overflow on either balance

    Uses 64 bytes of `.data` scratch (`arg_sender_refund` +
    `arg_coinbase_credit`) plus the 40-byte `u256m_acc`. -/
def accountRefundGasPostExecFunction : String :=
  "account_refund_gas_post_exec:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # sender ptr\n" ++
  "  mv s1, a1                   # coinbase ptr\n" ++
  "  mv s2, a3                   # priority_fee ptr (saved for step 2)\n" ++
  "  mv s3, a4                   # gas_used (saved for step 2)\n" ++
  "  mv s4, a2                   # egp ptr (also saved; step 1 uses)\n" ++
  "  # Step 1: sender_refund = remaining_gas × egp\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, a5\n" ++
  "  la a2, arg_sender_refund\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Largpe_fail_mul\n" ++
  "  # Step 2: coinbase_credit = gas_used × priority_fee\n" ++
  "  mv a0, s2\n" ++
  "  mv a1, s3\n" ++
  "  la a2, arg_coinbase_credit\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Largpe_fail_mul\n" ++
  "  # Step 3: sender.balance += sender_refund\n" ++
  "  mv a0, s0\n" ++
  "  la a1, arg_sender_refund\n" ++
  "  mv a2, s0\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Largpe_fail_add\n" ++
  "  # Step 4: coinbase.balance += coinbase_credit\n" ++
  "  mv a0, s1\n" ++
  "  la a1, arg_coinbase_credit\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Largpe_fail_add\n" ++
  "  li a0, 0\n" ++
  "  j .Largpe_ret\n" ++
  ".Largpe_fail_mul:\n" ++
  "  li a0, 1\n" ++
  "  j .Largpe_ret\n" ++
  ".Largpe_fail_add:\n" ++
  "  li a0, 2\n" ++
  ".Largpe_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_account_refund_gas_post_exec`: probe BuildUnit. Reads
    (32B sender_bal, 32B coinbase_bal, 32B egp, 32B priority_fee,
    8B gas_used, 8B remaining_gas) from host input. Copies the
    two balances to OUTPUT-resident scratch buffers, calls the
    helper, then writes (status, new_sender, new_coinbase) to
    OUTPUT. Total OUTPUT bytes: 8 + 32 + 32 = 72. -/
def ziskAccountRefundGasPostExecPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  # Copy sender balance to OUTPUT + 8\n" ++
  "  li a0, 0xa0010008\n" ++
  "  addi t1, a6, 8\n" ++
  "  ld t2,  0(t1); sd t2,  0(a0)\n" ++
  "  ld t2,  8(t1); sd t2,  8(a0)\n" ++
  "  ld t2, 16(t1); sd t2, 16(a0)\n" ++
  "  ld t2, 24(t1); sd t2, 24(a0)\n" ++
  "  # Copy coinbase balance to OUTPUT + 40\n" ++
  "  li a1, 0xa0010028\n" ++
  "  addi t1, a6, 40\n" ++
  "  ld t2,  0(t1); sd t2,  0(a1)\n" ++
  "  ld t2,  8(t1); sd t2,  8(a1)\n" ++
  "  ld t2, 16(t1); sd t2, 16(a1)\n" ++
  "  ld t2, 24(t1); sd t2, 24(a1)\n" ++
  "  addi a2, a6, 72             # egp ptr\n" ++
  "  addi a3, a6, 104            # priority_fee ptr\n" ++
  "  ld a4, 136(a6)              # gas_used\n" ++
  "  ld a5, 144(a6)              # remaining_gas\n" ++
  "  jal ra, account_refund_gas_post_exec\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Largpe_pdone\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  accountRefundGasPostExecFunction ++ "\n" ++
  ".Largpe_pdone:"

def ziskAccountRefundGasPostExecDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40\n" ++
  ".balign 32\n" ++
  "arg_sender_refund:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "arg_coinbase_credit:\n" ++
  "  .zero 32"

def ziskAccountRefundGasPostExecProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountRefundGasPostExecPrologue
  dataAsm     := ziskAccountRefundGasPostExecDataSection
}

/-! ## eip1559_calc_base_fee_per_gas -- PR-K73

    Full EIP-1559 base-fee formula. Mirrors Python's
    `calculate_base_fee_per_gas`:

      parent_gas_target = parent.gas_limit // 2

      if parent.gas_used == parent_gas_target:
          expected = parent.base_fee_per_gas
      elif parent.gas_used > parent_gas_target:
          gas_used_delta = parent.gas_used - parent_gas_target
          parent_fee_gas_delta = parent.base_fee_per_gas * gas_used_delta
          target_fee_gas_delta = parent_fee_gas_delta // parent_gas_target
          base_fee_delta = max(target_fee_gas_delta // 8, 1)
          expected = parent.base_fee_per_gas + base_fee_delta
      else:
          gas_used_delta = parent_gas_target - parent.gas_used
          parent_fee_gas_delta = parent.base_fee_per_gas * gas_used_delta
          target_fee_gas_delta = parent_fee_gas_delta // parent_gas_target
          base_fee_delta = target_fee_gas_delta // 8
          expected = parent.base_fee_per_gas - base_fee_delta

    Where `ELASTICITY_MULTIPLIER = 2` and
    `BASE_FEE_MAX_CHANGE_DENOMINATOR = 8`.

    First end-to-end EIP-1559 helper composed on the u256 toolkit:
    - PR-K54 `u256_mul_u64_be` — parent.base_fee × gas_used_delta
    - PR-K61 `u256_div_u64_be` — divide by parent_gas_target, then by 8
    - PR-K58 `u256_is_zero`    — max(_, 1) on the above path
    - PR-K56 `u256_from_u64_be` — materialize the literal 1
    - PR-K51 `u256_add_be`     — final add (above path)
    - PR-K52 `u256_sub_be`     — final sub (below path)

    ## Preconditions

    - `parent.gas_limit >= 2` (so `parent_gas_target >= 1`; we
      divide by it). Mainnet has GAS_LIMIT_MINIMUM = 5000, so
      this always holds for valid chains.
    - `parent.base_fee_per_gas <= 2^56` (PR-K61 div precondition).
      All mainnet base fees fit easily.

    Calling convention:
      a0 (input)  : parent.gas_limit       (u64)
      a1 (input)  : parent.gas_used        (u64)
      a2 (input)  : parent.base_fee_per_gas ptr (u256 BE, 32 B)
      a3 (input)  : output ptr (u256 BE, 32 B; receives expected
                    base_fee_per_gas)
      ra (input)  : return
      a0 (output) : 0 on success, 1 on overflow at any step. -/
def eip1559CalcBaseFeePerGasFunction : String :=
  "eip1559_calc_base_fee_per_gas:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a2                    # base_fee ptr\n" ++
  "  mv s1, a3                    # out ptr\n" ++
  "  srli s2, a0, 1               # parent_gas_target = parent.gas_limit / 2\n" ++
  "  beq a1, s2, .Lebf_eq         # gas_used == target → expected = base_fee\n" ++
  "  li s4, 0                     # path flag: 0 = below, 1 = above\n" ++
  "  bgtu a1, s2, .Lebf_set_above\n" ++
  "  sub s3, s2, a1               # below: delta = target - gas_used\n" ++
  "  j .Lebf_compute\n" ++
  ".Lebf_set_above:\n" ++
  "  li s4, 1\n" ++
  "  sub s3, a1, s2               # above: delta = gas_used - target\n" ++
  ".Lebf_compute:\n" ++
  "  # parent_fee_gas_delta = parent.base_fee × gas_used_delta\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s3\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lebf_fail\n" ++
  "  # target_fee_gas_delta = parent_fee_gas_delta / parent_gas_target\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_div_u64_be\n" ++
  "  # base_fee_delta = target_fee_gas_delta / 8\n" ++
  "  mv a0, s1\n" ++
  "  li a1, 8\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_div_u64_be\n" ++
  "  # If above path: max(delta, 1).\n" ++
  "  beqz s4, .Lebf_apply\n" ++
  "  mv a0, s1\n" ++
  "  jal ra, u256_is_zero\n" ++
  "  beqz a0, .Lebf_apply\n" ++
  "  li a0, 1\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, u256_from_u64_be\n" ++
  ".Lebf_apply:\n" ++
  "  beqz s4, .Lebf_sub_path\n" ++
  "  # above: out = base_fee + delta\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Lebf_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lebf_ret\n" ++
  ".Lebf_sub_path:\n" ++
  "  # below: out = base_fee - delta\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_sub_be\n" ++
  "  bnez a0, .Lebf_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lebf_ret\n" ++
  ".Lebf_eq:\n" ++
  "  # Copy base_fee to out (32 B chunk copy).\n" ++
  "  ld t0,  0(s0); sd t0,  0(s1)\n" ++
  "  ld t0,  8(s0); sd t0,  8(s1)\n" ++
  "  ld t0, 16(s0); sd t0, 16(s1)\n" ++
  "  ld t0, 24(s0); sd t0, 24(s1)\n" ++
  "  li a0, 0\n" ++
  "  j .Lebf_ret\n" ++
  ".Lebf_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lebf_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_eip1559_calc_base_fee_per_gas`: probe BuildUnit. Reads
    (parent_gas_limit u64, parent_gas_used u64, parent_base_fee
    u256 BE) from host input, writes (status, expected_base_fee
    BE) to OUTPUT (40 bytes total). -/
def ziskEip1559CalcBaseFeePerGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a0,  8(a4)               # parent.gas_limit\n" ++
  "  ld a1, 16(a4)               # parent.gas_used\n" ++
  "  addi a2, a4, 24             # parent.base_fee ptr\n" ++
  "  li a3, 0xa0010008           # out ptr\n" ++
  "  mv t0, a3; li t1, 4\n" ++
  ".Lebf_zout:\n" ++
  "  beqz t1, .Lebf_zout_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lebf_zout\n" ++
  ".Lebf_zout_done:\n" ++
  "  jal ra, eip1559_calc_base_fee_per_gas\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lebf_pdone\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256DivU64BeFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  eip1559CalcBaseFeePerGasFunction ++ "\n" ++
  ".Lebf_pdone:"

def ziskEip1559CalcBaseFeePerGasDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40"

def ziskEip1559CalcBaseFeePerGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskEip1559CalcBaseFeePerGasPrologue
  dataAsm     := ziskEip1559CalcBaseFeePerGasDataSection
}

/-! ## header_validate_base_fee -- PR-K74

    Verify a header's `base_fee_per_gas` matches the value
    computed from the parent header by EIP-1559's
    `calculate_base_fee_per_gas`:

      expected = eip1559_calc_base_fee_per_gas(
                   parent.gas_limit,
                   parent.gas_used,
                   parent.base_fee_per_gas)
      assert header.base_fee_per_gas == expected

    This is the per-block invariant added by EIP-1559 §4.4.4
    (Python: `validate_header`).

    Composes PR-K73 `eip1559_calc_base_fee_per_gas` +
    PR-K53 `u256_eq`. The 32-byte computed expected base fee
    lands in `.data` scratch, then is compared bytewise against
    the header's claimed value.

    Calling convention:
      a0 (input)  : header.base_fee_per_gas ptr (u256 BE, 32 B)
      a1 (input)  : parent.gas_limit (u64)
      a2 (input)  : parent.gas_used (u64)
      a3 (input)  : parent.base_fee_per_gas ptr (u256 BE, 32 B)
      ra (input)  : return
      a0 (output) :
        0  : header.base_fee_per_gas == expected
        1  : mismatch (reject)
        2  : compute step (K73) overflow / precondition failure

    Uses 32 bytes of `.data` scratch (`hvbf_expected`). -/
def headerValidateBaseFeeFunction : String :=
  "header_validate_base_fee:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  mv s0, a0                   # save header.base_fee ptr\n" ++
  "  # expected = eip1559_calc_base_fee_per_gas(...)  → hvbf_expected\n" ++
  "  mv a0, a1                   # parent.gas_limit\n" ++
  "  mv a1, a2                   # parent.gas_used\n" ++
  "  mv a2, a3                   # parent.base_fee\n" ++
  "  la a3, hvbf_expected\n" ++
  "  jal ra, eip1559_calc_base_fee_per_gas\n" ++
  "  bnez a0, .Lhvbf_fail_compute\n" ++
  "  # Compare header.base_fee vs expected.\n" ++
  "  mv a0, s0\n" ++
  "  la a1, hvbf_expected\n" ++
  "  jal ra, u256_eq             # a0 = 1 if equal, 0 if not\n" ++
  "  beqz a0, .Lhvbf_fail_mismatch\n" ++
  "  li a0, 0\n" ++
  "  j .Lhvbf_ret\n" ++
  ".Lhvbf_fail_mismatch:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhvbf_ret\n" ++
  ".Lhvbf_fail_compute:\n" ++
  "  li a0, 2\n" ++
  ".Lhvbf_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_header_validate_base_fee`: probe BuildUnit. Reads
    (header_bf u256 BE, parent_gas_limit u64, parent_gas_used u64,
    parent_bf u256 BE) from host input, writes 8-byte status. -/
def ziskHeaderValidateBaseFeePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  addi a0, a4, 8              # header_bf ptr\n" ++
  "  ld a1, 40(a4)               # parent.gas_limit\n" ++
  "  ld a2, 48(a4)               # parent.gas_used\n" ++
  "  addi a3, a4, 56             # parent_bf ptr\n" ++
  "  jal ra, header_validate_base_fee\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lhvbf_pdone\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256DivU64BeFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  u256EqFunction ++ "\n" ++
  eip1559CalcBaseFeePerGasFunction ++ "\n" ++
  headerValidateBaseFeeFunction ++ "\n" ++
  ".Lhvbf_pdone:"

def ziskHeaderValidateBaseFeeDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "hvbf_expected:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40"

def ziskHeaderValidateBaseFeeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderValidateBaseFeePrologue
  dataAsm     := ziskHeaderValidateBaseFeeDataSection
}

/-! ## validate_header_full -- PR-K75 complete per-header validation

    Run all five per-header validation checks in sequence, returning
    a single status code that distinguishes which step failed:

      1. PR-K67 `header_validate_post_merge`        — ommers/difficulty/nonce
      2. PR-K68 `header_validate_extra_data_length` — extra_data ≤ 32 bytes
      3. PR-K43 `validate_header_basic`             — gas_used ≤ gas_limit + number/timestamp
      4. PR-K72 `check_gas_limit`                   — elasticity
      5. PR-K74 `header_validate_base_fee`          — EIP-1559 invariant

    Chain-level checks (parent_hash continuity, validate_chain
    PR-K18) are NOT included here — they iterate across multiple
    headers and live at the SSZ-list walk level.

    Status encoding:

      0                : all five checks pass
      100..104         : step 1 failed with K67's sub-status 0..4
      201..202         : step 2 failed with K68's sub-status 1..2
      301..303         : step 3 failed with K43's sub-status 1..3
      401..402         : step 4 failed with K72's sub-status 1..2
      501..502         : step 5 failed with K74's sub-status 1..2

    Distinct decades let callers `floor(status/100)` to identify
    the failing step.

    Calling convention:
      a0 (input)  : this header's RLP ptr
      a1 (input)  : this header's RLP byte length
      a2 (input)  : this header's PR-K39 extended-decode struct
                    (128 B, with gas_limit @ 80, gas_used @ 88,
                    base_fee_per_gas @ 96..128)
      a3 (input)  : parent header's PR-K39 extended-decode struct
                    (same layout)
      ra (input)  : return
      a0 (output) : composite status (see encoding above).

    Composes 5 validators + their transitive deps (rlp_list_nth_item,
    eip1559_calc_base_fee_per_gas plus the u256 toolkit). The probe
    inlines every function it transitively calls. -/
def validateHeaderFullFunction : String :=
  "validate_header_full:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # this_rlp ptr\n" ++
  "  mv s1, a1                   # this_rlp_len\n" ++
  "  mv s2, a2                   # this_struct (128 B)\n" ++
  "  mv s3, a3                   # parent_struct (128 B)\n" ++
  "  # Step 1: post_merge check\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  jal ra, header_validate_post_merge\n" ++
  "  beqz a0, .Lvhf_s2\n" ++
  "  li t0, 100\n" ++
  "  add a0, a0, t0\n" ++
  "  j .Lvhf_ret\n" ++
  ".Lvhf_s2:\n" ++
  "  # Step 2: extra_data length check\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  jal ra, header_validate_extra_data_length\n" ++
  "  beqz a0, .Lvhf_s3\n" ++
  "  li t0, 200\n" ++
  "  add a0, a0, t0\n" ++
  "  j .Lvhf_ret\n" ++
  ".Lvhf_s3:\n" ++
  "  # Step 3: gas_used/number/timestamp\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  jal ra, validate_header_basic\n" ++
  "  beqz a0, .Lvhf_s4\n" ++
  "  li t0, 300\n" ++
  "  add a0, a0, t0\n" ++
  "  j .Lvhf_ret\n" ++
  ".Lvhf_s4:\n" ++
  "  # Step 4: check_gas_limit(this.gas_limit, parent.gas_limit)\n" ++
  "  ld a0, 80(s2)\n" ++
  "  ld a1, 80(s3)\n" ++
  "  jal ra, check_gas_limit\n" ++
  "  beqz a0, .Lvhf_s5\n" ++
  "  li t0, 400\n" ++
  "  add a0, a0, t0\n" ++
  "  j .Lvhf_ret\n" ++
  ".Lvhf_s5:\n" ++
  "  # Step 5: base_fee continuity\n" ++
  "  addi a0, s2, 96\n" ++
  "  ld a1, 80(s3)\n" ++
  "  ld a2, 88(s3)\n" ++
  "  addi a3, s3, 96\n" ++
  "  jal ra, header_validate_base_fee\n" ++
  "  beqz a0, .Lvhf_ret\n" ++
  "  li t0, 500\n" ++
  "  add a0, a0, t0\n" ++
  ".Lvhf_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_validate_header_full`: probe BuildUnit. Reads (this_rlp_len,
    this_rlp_bytes [up to 1024 B], this_struct 128 B, parent_struct
    128 B) from host input, writes 8-byte composite status to OUTPUT. -/
def ziskValidateHeaderFullPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # this_rlp_len\n" ++
  "  addi a0, a4, 16             # this_rlp ptr\n" ++
  "  addi a2, a4, 16             # placeholder; reset after rlp\n" ++
  "  # this_struct offset = 16 + rlp_len_aligned\n" ++
  "  # parent_struct offset = this_struct + 128\n" ++
  "  # We require the caller to lay them out at fixed positions:\n" ++
  "  # bytes 8..16  : rlp_len\n" ++
  "  # bytes 16..16+1024 : this_rlp (padded to 1024)\n" ++
  "  # bytes 1040..1168  : this_struct (128 B)\n" ++
  "  # bytes 1168..1296  : parent_struct (128 B)\n" ++
  "  li a2, 0x40000410           # this_struct  (= INPUT_ADDR + 1040)\n" ++
  "  li a3, 0x40000490           # parent_struct (= INPUT_ADDR + 1168)\n" ++
  "  jal ra, validate_header_full\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lvhf_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256DivU64BeFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  u256EqFunction ++ "\n" ++
  validateHeaderBasicFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  headerValidatePostMergeFunction ++ "\n" ++
  headerValidateExtraDataLengthFunction ++ "\n" ++
  eip1559CalcBaseFeePerGasFunction ++ "\n" ++
  headerValidateBaseFeeFunction ++ "\n" ++
  validateHeaderFullFunction ++ "\n" ++
  ".Lvhf_pdone:"

def ziskValidateHeaderFullDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "empty_ommers_hash:\n" ++
  "  .byte 0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a\n" ++
  "  .byte 0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a\n" ++
  "  .byte 0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13\n" ++
  "  .byte 0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47\n" ++
  ".balign 32\n" ++
  "hvbf_expected:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40\n" ++
  ".balign 8\n" ++
  "hvpm_off:\n" ++
  "  .zero 8\n" ++
  "hvpm_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "hved_off:\n" ++
  "  .zero 8\n" ++
  "hved_len:\n" ++
  "  .zero 8"

def ziskValidateHeaderFullProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateHeaderFullPrologue
  dataAsm     := ziskValidateHeaderFullDataSection
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

/-! ## withdrawal_decode -- PR-K49 4-field withdrawal RLP decoder

    Decode a post-Shanghai Withdrawal record into a flat struct.
    Each withdrawal is an RLP list with 4 fields (Python:
    `ethereum.forks.shanghai.fork_types.Withdrawal`):

      rlp([index, validator_index, address, amount])

    `apply_body` iterates `block.withdrawals`, decodes each one
    via this helper, and applies the credit to the recipient's
    balance (amount is in Gwei).

    Output struct (48 bytes; 8-byte aligned for sd):

       0..  8  index           (u64 LE)
       8.. 16  validator_index (u64 LE)
      16.. 36  address         (20 B)
      36.. 40  zero pad
      40.. 48  amount          (u64 LE; in Gwei)

    Calling convention:
      a0 (input)  : withdrawal_rlp ptr
      a1 (input)  : withdrawal_rlp byte length
      a2 (input)  : 48-byte output struct ptr
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail (not a 4-item list,
                    field too long, or address not 20 bytes). -/
def withdrawalDecodeFunction : String :=
  "withdrawal_decode:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # wd_rlp ptr\n" ++
  "  mv s1, a1                  # wd_rlp_len\n" ++
  "  mv s2, a2                  # struct out\n" ++
  "  # Field 0: index (u64 at offset 0)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0; mv a3, s2\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lwd_fail\n" ++
  "  # Field 1: validator_index (u64 at offset 8)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  addi a3, s2, 8\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lwd_fail\n" ++
  "  # Field 2: address (20 bytes at offset 16)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  la a3, wd_offset; la a4, wd_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lwd_fail\n" ++
  "  la t0, wd_length; ld t1, 0(t0)\n" ++
  "  li t2, 20\n" ++
  "  bne t1, t2, .Lwd_fail\n" ++
  "  la t0, wd_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  addi t4, s2, 16\n" ++
  "  ld t5,  0(t3); sd t5,  0(t4)\n" ++
  "  ld t5,  8(t3); sd t5,  8(t4)\n" ++
  "  lwu t5, 16(t3); sw t5, 16(t4)\n" ++
  "  # Pad bytes 20..24 of address slot (struct 36..40) are zero (from caller zeroing).\n" ++
  "  # Field 3: amount (u64 at offset 40)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  addi a3, s2, 40\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lwd_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lwd_ret\n" ++
  ".Lwd_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lwd_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_withdrawal_decode`: probe BuildUnit. Reads (wd_len,
    wd_bytes) from host input, writes (status, 48-byte struct)
    to OUTPUT. -/
def ziskWithdrawalDecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # wd_len\n" ++
  "  addi a0, a3, 16             # wd ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 48 bytes (6 dwords).\n" ++
  "  mv t0, a2\n" ++
  "  li t1, 6\n" ++
  ".Lwd_zinit:\n" ++
  "  beqz t1, .Lwd_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lwd_zinit\n" ++
  ".Lwd_zdone:\n" ++
  "  jal ra, withdrawal_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lwd_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  withdrawalDecodeFunction ++ "\n" ++
  ".Lwd_pdone:"

def ziskWithdrawalDecodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wd_offset:\n" ++
  "  .zero 8\n" ++
  "wd_length:\n" ++
  "  .zero 8"

def ziskWithdrawalDecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWithdrawalDecodePrologue
  dataAsm     := ziskWithdrawalDecodeDataSection
}

/-! ## block_body_decode -- PR-K83

    Decode a post-Shanghai block body RLP into three sub-list
    (offset, length) pairs. The body is `rlp([transactions,
    ommers, withdrawals])`:

      Field 0: transactions   (list of typed tx envelopes)
      Field 1: ommers         (empty list post-merge: 0xc0)
      Field 2: withdrawals    (Shanghai+: list of [index, vi,
                              address, amount])

    Output struct layout (48 bytes):

         0..  8  transactions_offset (u64; within body_rlp)
         8.. 16  transactions_length (u64; full encoded sub-list)
        16.. 24  ommers_offset       (u64)
        24.. 32  ommers_length       (u64)
        32.. 40  withdrawals_offset  (u64)
        40.. 48  withdrawals_length  (u64)

    Composes PR-K20 `rlp_list_nth_item` three times. The
    (offset, length) of each sub-list is the FULL encoded item
    (including its own RLP list prefix), per K20's list-item
    contract — so callers can recurse into each with another
    `rlp_list_nth_item` call.

    For pre-Shanghai bodies (only 2 fields), this helper fails
    on the third call. Such bodies aren't relevant for the
    amsterdam stateless guest.

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : 48-byte output struct ptr
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail (not a 3-item list).

    Pure composition of PR-K20. No new `.data` scratch beyond
    what K20 needs (none). -/
def blockBodyDecodeFunction : String :=
  "block_body_decode:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # body_rlp ptr\n" ++
  "  mv s1, a1                   # body_len\n" ++
  "  mv s2, a2                   # output struct ptr\n" ++
  "  # Field 0: transactions\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0\n" ++
  "  mv a3, s2\n" ++
  "  addi a4, s2, 8\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbd_fail\n" ++
  "  # Field 1: ommers\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  addi a3, s2, 16\n" ++
  "  addi a4, s2, 24\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbd_fail\n" ++
  "  # Field 2: withdrawals\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  addi a3, s2, 32\n" ++
  "  addi a4, s2, 40\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbd_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lbbd_ret\n" ++
  ".Lbbd_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbbd_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_body_decode`: probe BuildUnit. Reads (body_len,
    body_bytes) from host input, writes (status, 48-byte struct)
    to OUTPUT (56 bytes total). -/
def ziskBlockBodyDecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # body_len\n" ++
  "  addi a0, a3, 16             # body ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  mv t0, a2; li t1, 6\n" ++
  ".Lbbd_zinit:\n" ++
  "  beqz t1, .Lbbd_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lbbd_zinit\n" ++
  ".Lbbd_zdone:\n" ++
  "  jal ra, block_body_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbbd_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  ".Lbbd_pdone:"

def ziskBlockBodyDecodeDataSection : String :=
  ".section .data\n" ++
  "bbd_pad:\n" ++
  "  .zero 8"

def ziskBlockBodyDecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockBodyDecodePrologue
  dataAsm     := ziskBlockBodyDecodeDataSection
}

/-! ## block_validate_ommers_empty -- PR-K84

    Verify the post-merge invariant that a block body's ommers
    field is the empty RLP list (`0xc0`). The Merge fork removed
    uncle blocks; every post-merge block must have an empty
    ommers list, matching `EMPTY_OMMERS_HASH` in the header.

    Composes PR-K83 `block_body_decode` + a single-byte check
    on the ommers sub-list.

    An empty RLP list is encoded as the single byte `0xc0`. So
    the check is:
      - ommers_length == 1
      - body_rlp[ommers_offset] == 0xc0

    Calling convention:
      a0 (input)  : block_body_rlp ptr
      a1 (input)  : block_body_rlp byte length
      ra (input)  : return
      a0 (output) :
        0 : ommers is empty (post-merge ok)
        1 : ommers is non-empty (reject — pre-merge or invalid)
        2 : RLP parse failure

    Uses 48 bytes of `.data` scratch (`bvoe_struct`). -/
def blockValidateOmmersEmptyFunction : String :=
  "block_validate_ommers_empty:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  mv s0, a0                   # body_rlp ptr\n" ++
  "  la a2, bvoe_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbvoe_parse_fail\n" ++
  "  la t0, bvoe_struct\n" ++
  "  ld t1, 24(t0)               # ommers_length\n" ++
  "  li t2, 1\n" ++
  "  bne t1, t2, .Lbvoe_not_empty\n" ++
  "  ld t3, 16(t0)               # ommers_offset\n" ++
  "  add t3, s0, t3\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  li t5, 0xc0\n" ++
  "  bne t4, t5, .Lbvoe_not_empty\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvoe_ret\n" ++
  ".Lbvoe_not_empty:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbvoe_ret\n" ++
  ".Lbvoe_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbvoe_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_block_validate_ommers_empty`: probe BuildUnit. Reads
    (body_len, body_bytes) from host input, writes 8-byte status
    to OUTPUT. -/
def ziskBlockValidateOmmersEmptyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # body_len\n" ++
  "  addi a0, a3, 16             # body ptr\n" ++
  "  jal ra, block_validate_ommers_empty\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbvoe_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockValidateOmmersEmptyFunction ++ "\n" ++
  ".Lbvoe_pdone:"

def ziskBlockValidateOmmersEmptyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bvoe_struct:\n" ++
  "  .zero 48"

def ziskBlockValidateOmmersEmptyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateOmmersEmptyPrologue
  dataAsm     := ziskBlockValidateOmmersEmptyDataSection
}

/-! ## process_withdrawal -- PR-K77

    Apply a Shanghai+ Withdrawal credit to a recipient's account
    balance. Per Python's `process_withdrawal`:

      account.balance += withdrawal.amount * 10^9

    The withdrawal amount is denominated in Gwei; the balance is
    in wei. We convert by multiplying by `GWEI_TO_WEI = 10^9`.

    Composes:
      - PR-K56 `u256_from_u64_be` — zero-extend amount to u256
      - PR-K54 `u256_mul_u64_be`  — × 10^9 to convert Gwei → wei
      - PR-K51 `u256_add_be`      — fold credit into balance

    The mul step can't realistically overflow u256: amount ≤ 2^41
    Gwei (full validator balance ~32 ETH ≈ 2^35 Gwei; ≤ 2^41
    even for stake-pool aggregates), so amount × 10^9 < 2^71 ≪
    2^256. The add can't realistically overflow either since
    mainnet total wei < 2^87. Both are checked as safety nets.

    Calling convention:
      a0 (input)  : withdrawal struct ptr (48 B; from PR-K49
                    `withdrawal_decode`, with amount at offset 40)
      a1 (input)  : account.balance ptr (32 B u256 BE; modified
                    in place)
      ra (input)  : return
      a0 (output) : 0 success / 1 overflow on mul or add.

    Uses 32 bytes of `.data` scratch (`pw_amount_wei`) plus the
    40-byte `u256m_acc` scratch from PR-K54. -/
def processWithdrawalFunction : String :=
  "process_withdrawal:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0                   # withdrawal struct ptr\n" ++
  "  mv s1, a1                   # balance ptr\n" ++
  "  # Step 1: zero-extend amount (Gwei) to u256.\n" ++
  "  ld t0, 40(s0)               # amount (u64)\n" ++
  "  mv a0, t0\n" ++
  "  la a1, pw_amount_wei\n" ++
  "  jal ra, u256_from_u64_be\n" ++
  "  # Step 2: amount_wei = amount × 10^9 (in place).\n" ++
  "  la a0, pw_amount_wei\n" ++
  "  li a1, 1000000000\n" ++
  "  la a2, pw_amount_wei\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lpw_fail\n" ++
  "  # Step 3: balance += amount_wei.\n" ++
  "  mv a0, s1\n" ++
  "  la a1, pw_amount_wei\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Lpw_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lpw_ret\n" ++
  ".Lpw_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lpw_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_process_withdrawal`: probe BuildUnit. Reads (48 B
    withdrawal struct, 32 B initial balance) from host input;
    copies initial balance to OUTPUT + 8, calls
    process_withdrawal on it, then writes status to OUTPUT. -/
def ziskProcessWithdrawalPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a2, 0x40000000\n" ++
  "  addi a0, a2, 8              # withdrawal struct ptr\n" ++
  "  li a1, 0xa0010008           # balance buffer at OUTPUT + 8\n" ++
  "  # Copy initial balance (input offset 48..80) to OUTPUT + 8.\n" ++
  "  addi t0, a2, 56             # initial balance ptr\n" ++
  "  ld t1,  0(t0); sd t1,  0(a1)\n" ++
  "  ld t1,  8(t0); sd t1,  8(a1)\n" ++
  "  ld t1, 16(t0); sd t1, 16(a1)\n" ++
  "  ld t1, 24(t0); sd t1, 24(a1)\n" ++
  "  jal ra, process_withdrawal\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lpw_pdone\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  processWithdrawalFunction ++ "\n" ++
  ".Lpw_pdone:"

def ziskProcessWithdrawalDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40\n" ++
  ".balign 32\n" ++
  "pw_amount_wei:\n" ++
  "  .zero 32"

def ziskProcessWithdrawalProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskProcessWithdrawalPrologue
  dataAsm     := ziskProcessWithdrawalDataSection
}

/-! ## process_withdrawals_block -- PR-K78

    Iterate over a block's RLP-encoded withdrawals list and apply
    each Gwei→wei credit to a parallel pre-fetched balance array.
    Mirrors the inner loop of Python's `apply_body`:

      for wd in block.withdrawals:
          process_withdrawal(state, wd)

    Caller responsibilities:
      1. Pre-fetch the current balance of each withdrawal recipient
         from the state trie (via PR-K28 `account_at_address` etc.)
         into a parallel `balances[N]` array (each 32 B u256 BE).
      2. After this helper returns, write each updated `balances[i]`
         back to state (via the still-pending MPT mutation path).

    The parallel-array indirection lets this PR ship without
    requiring the MPT mutation infrastructure that
    `compute_state_root_and_trie_changes` will add.

    Composes:
      - PR-K47 `rlp_list_count_items` — outer cardinality
      - PR-K20 `rlp_list_nth_item`    — per-entry bounds
      - PR-K49 `withdrawal_decode`    — extract amount
      - PR-K77 `process_withdrawal`   — credit `balances[i]`

    Calling convention:
      a0 (input)  : withdrawals_rlp ptr
      a1 (input)  : withdrawals_rlp byte length
      a2 (input)  : balances array ptr (N × 32 B; in-place updated)
      ra (input)  : return
      a0 (output) :
        0  : success (every entry credited)
        1  : RLP parse failure at outer count or entry walk
        2  : `withdrawal_decode` failed on an entry
        3  : `process_withdrawal` overflow on credit step

    Uses 64 bytes of `.data` scratch (`pwb_count`,
    `pwb_entry_offset`, `pwb_entry_length`, `pwb_struct[48]`)
    plus `pw_amount_wei` and `u256m_acc` carried in from K77. -/
def processWithdrawalsBlockFunction : String :=
  "process_withdrawals_block:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # rlp_ptr\n" ++
  "  mv s1, a1                   # rlp_len\n" ++
  "  mv s2, a2                   # balances ptr\n" ++
  "  # Step 1: count outer entries\n" ++
  "  la a2, pwb_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lpwb_fail_parse\n" ++
  "  la t0, pwb_count; ld s3, 0(t0)\n" ++
  "  li s5, 0                    # current entry index i\n" ++
  ".Lpwb_loop:\n" ++
  "  beq s5, s3, .Lpwb_done\n" ++
  "  # Get entry i bounds\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s5\n" ++
  "  la a3, pwb_entry_offset\n" ++
  "  la a4, pwb_entry_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lpwb_fail_parse\n" ++
  "  # Decode entry into pwb_struct (48 B)\n" ++
  "  la t0, pwb_entry_offset; ld t1, 0(t0)\n" ++
  "  la t0, pwb_entry_length; ld t2, 0(t0)\n" ++
  "  add a0, s0, t1\n" ++
  "  mv a1, t2\n" ++
  "  la a2, pwb_struct\n" ++
  "  jal ra, withdrawal_decode\n" ++
  "  bnez a0, .Lpwb_fail_decode\n" ++
  "  # process_withdrawal(struct, &balances[i])\n" ++
  "  la a0, pwb_struct\n" ++
  "  # balances[i] = s2 + i * 32\n" ++
  "  slli s4, s5, 5\n" ++
  "  add a1, s2, s4\n" ++
  "  jal ra, process_withdrawal\n" ++
  "  bnez a0, .Lpwb_fail_credit\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lpwb_loop\n" ++
  ".Lpwb_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lpwb_ret\n" ++
  ".Lpwb_fail_parse:\n" ++
  "  li a0, 1\n" ++
  "  j .Lpwb_ret\n" ++
  ".Lpwb_fail_decode:\n" ++
  "  li a0, 2\n" ++
  "  j .Lpwb_ret\n" ++
  ".Lpwb_fail_credit:\n" ++
  "  li a0, 3\n" ++
  ".Lpwb_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_process_withdrawals_block`: probe BuildUnit. Reads
    (wd_count u64, balances initial N × 32 B, rlp_len u64,
    rlp_bytes) from host input. Writes (status, balances after
    credits) to OUTPUT. -/
def ziskProcessWithdrawalsBlockPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld t1, 8(a4)                # wd_count (N)\n" ++
  "  # Copy initial balances (input offset 16..16+N*32) to OUTPUT + 8.\n" ++
  "  addi t2, a4, 16             # source ptr\n" ++
  "  li t3, 0xa0010008           # dst ptr\n" ++
  "  slli t4, t1, 5              # N × 32 bytes\n" ++
  "  add t5, t3, t4              # dst end\n" ++
  ".Lpwb_copy:\n" ++
  "  beq t3, t5, .Lpwb_copy_done\n" ++
  "  ld t6, 0(t2)\n" ++
  "  sd t6, 0(t3)\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, 8\n" ++
  "  j .Lpwb_copy\n" ++
  ".Lpwb_copy_done:\n" ++
  "  # Now read rlp_len and rlp ptr.\n" ++
  "  add t0, a4, t4              # 0x40000000 + 16 + N*32\n" ++
  "  ld a1, 16(t0)               # rlp_len at offset 16+N*32\n" ++
  "  addi a0, t0, 24             # rlp ptr after the length\n" ++
  "  li a2, 0xa0010008           # balances array\n" ++
  "  jal ra, process_withdrawals_block\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lpwb_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  withdrawalDecodeFunction ++ "\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  processWithdrawalFunction ++ "\n" ++
  processWithdrawalsBlockFunction ++ "\n" ++
  ".Lpwb_pdone:"

def ziskProcessWithdrawalsBlockDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wd_offset:\n" ++
  "  .zero 8\n" ++
  "wd_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40\n" ++
  ".balign 32\n" ++
  "pw_amount_wei:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "pwb_count:\n" ++
  "  .zero 8\n" ++
  "pwb_entry_offset:\n" ++
  "  .zero 8\n" ++
  "pwb_entry_length:\n" ++
  "  .zero 8\n" ++
  "pwb_struct:\n" ++
  "  .zero 48"

def ziskProcessWithdrawalsBlockProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskProcessWithdrawalsBlockPrologue
  dataAsm     := ziskProcessWithdrawalsBlockDataSection
}

/-! ## withdrawals_sum_amounts -- PR-K65 block withdrawal-credit total

    Walk an RLP-encoded list of Shanghai+ Withdrawal records
    (one Withdrawal = `rlp([index, validator_index, address,
    amount])`) and return the total of all `amount` fields
    (in Gwei) as a `u64`.

    Used by `apply_body` to compute the block's total
    withdrawal credit before applying it to recipient
    balances — useful as a sanity check against the
    `withdrawals_root` MPT computation and for tracking
    coinbase credits per block.

    First multi-helper composition on the K-stack:
    - PR-K47 `rlp_list_count_items` — outer cardinality
    - PR-K20 `rlp_list_nth_item` — per-entry bounds
    - PR-K49 `withdrawal_decode` — extract `amount` (u64 at
      struct offset 40)

    Each entry's `amount` is added to a u64 accumulator with
    overflow detection (unsigned-wrap check: if `sum < prev`,
    we overflowed). On overflow the function returns status=2
    so the caller can react (in practice withdrawals per block
    are capped at 16 with amounts ≤ ~2^41 Gwei, so overflow
    can't occur on valid chains, but the check makes garbage
    input safe).

    Calling convention:
      a0 (input)  : withdrawals_rlp ptr
      a1 (input)  : withdrawals_rlp byte length
      a2 (input)  : u64 out ptr (sum of all amounts in Gwei)
      ra (input)  : return
      a0 (output) :
        0  : success
        1  : parse fail (output zeroed)
        2  : sum overflowed u64 (output zeroed)

    Uses 64 bytes of `.data` scratch
    (`wsa_count`, `wsa_entry_offset`, `wsa_entry_length`,
    `wsa_struct[48]`). -/
def withdrawalsSumAmountsFunction : String :=
  "withdrawals_sum_amounts:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # rlp_ptr\n" ++
  "  mv s1, a1                   # rlp_len\n" ++
  "  mv s2, a2                   # out_ptr\n" ++
  "  # Step 1: count = rlp_list_count_items(...)\n" ++
  "  la a2, wsa_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lwsa_fail\n" ++
  "  la t0, wsa_count; ld s3, 0(t0)\n" ++
  "  li s4, 0                    # acc (u64)\n" ++
  "  li s5, 0                    # i\n" ++
  ".Lwsa_loop:\n" ++
  "  beq s5, s3, .Lwsa_done\n" ++
  "  # Step 2: get entry i bounds.\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s5\n" ++
  "  la a3, wsa_entry_offset\n" ++
  "  la a4, wsa_entry_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lwsa_fail\n" ++
  "  # Step 3: decode entry into wsa_struct.\n" ++
  "  la t0, wsa_entry_offset; ld t1, 0(t0)\n" ++
  "  la t0, wsa_entry_length; ld t2, 0(t0)\n" ++
  "  add a0, s0, t1\n" ++
  "  mv a1, t2\n" ++
  "  la a2, wsa_struct\n" ++
  "  jal ra, withdrawal_decode\n" ++
  "  bnez a0, .Lwsa_fail\n" ++
  "  # Step 4: accumulate amount (at struct offset 40) with overflow.\n" ++
  "  la t0, wsa_struct; ld t1, 40(t0)\n" ++
  "  add t2, s4, t1\n" ++
  "  bltu t2, s4, .Lwsa_overflow\n" ++
  "  mv s4, t2\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lwsa_loop\n" ++
  ".Lwsa_done:\n" ++
  "  sd s4, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lwsa_ret\n" ++
  ".Lwsa_overflow:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 2\n" ++
  "  j .Lwsa_ret\n" ++
  ".Lwsa_fail:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 1\n" ++
  ".Lwsa_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_withdrawals_sum_amounts`: probe BuildUnit. Reads
    (rlp_len, rlp_bytes) from host input, writes (status, sum)
    to OUTPUT (16 bytes total). -/
def ziskWithdrawalsSumAmountsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # rlp_len\n" ++
  "  addi a0, a3, 16             # rlp ptr\n" ++
  "  li a2, 0xa0010008           # out ptr\n" ++
  "  sd zero, 0(a2)\n" ++
  "  jal ra, withdrawals_sum_amounts\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwsa_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  withdrawalDecodeFunction ++ "\n" ++
  withdrawalsSumAmountsFunction ++ "\n" ++
  ".Lwsa_pdone:"

def ziskWithdrawalsSumAmountsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wd_offset:\n" ++
  "  .zero 8\n" ++
  "wd_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wsa_count:\n" ++
  "  .zero 8\n" ++
  "wsa_entry_offset:\n" ++
  "  .zero 8\n" ++
  "wsa_entry_length:\n" ++
  "  .zero 8\n" ++
  "wsa_struct:\n" ++
  "  .zero 48"

def ziskWithdrawalsSumAmountsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWithdrawalsSumAmountsPrologue
  dataAsm     := ziskWithdrawalsSumAmountsDataSection
}

/-! ## block_withdrawals_total -- PR-K85

    Extract the withdrawals sub-list from a block body RLP and
    return the total of all withdrawal `amount` fields (in Gwei)
    as a u64.

    Composes:
      - PR-K83 `block_body_decode` — split body → 3 (off, len) pairs
      - PR-K65 `withdrawals_sum_amounts` — sum amount across the
        decoded withdrawals sub-list

    Useful for cross-checking block-level invariants (e.g., the
    `withdrawals_root` MPT computation) and for receipt analysis.

    Status encoding lets callers floor(status / 100) to identify
    the failing step:

      0          : success — total written to *out
      1          : block_body_decode failed (not a 3-item list)
      101..102   : withdrawals_sum_amounts failed
                   (101 = parse error, 102 = u64 overflow)

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : u64 out ptr (total Gwei across all
                    withdrawals)
      ra (input)  : return
      a0 (output) : composite status code.

    Uses 48 bytes of `.data` scratch (`bwt_struct`) — separate
    from K83's probe-only struct so the two compose cleanly. -/
def blockWithdrawalsTotalFunction : String :=
  "block_withdrawals_total:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # body_rlp ptr\n" ++
  "  mv s1, a1                   # body_len\n" ++
  "  mv s2, a2                   # out ptr\n" ++
  "  # Step 1: block_body_decode\n" ++
  "  la a2, bwt_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbwt_body_fail\n" ++
  "  # Step 2: withdrawals_sum_amounts on withdrawals sub-list.\n" ++
  "  la t0, bwt_struct\n" ++
  "  ld t1, 32(t0)               # withdrawals_offset\n" ++
  "  ld t2, 40(t0)               # withdrawals_length\n" ++
  "  add a0, s0, t1\n" ++
  "  mv a1, t2\n" ++
  "  mv a2, s2\n" ++
  "  jal ra, withdrawals_sum_amounts\n" ++
  "  beqz a0, .Lbwt_ret\n" ++
  "  li t3, 100\n" ++
  "  add a0, a0, t3              # 1 → 101, 2 → 102\n" ++
  "  j .Lbwt_ret\n" ++
  ".Lbwt_body_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbwt_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_withdrawals_total`: probe BuildUnit. Reads
    (body_len, body_bytes) from host input, writes (status,
    total_gwei u64) to OUTPUT (16 bytes total). -/
def ziskBlockWithdrawalsTotalPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # body_len\n" ++
  "  addi a0, a3, 16             # body ptr\n" ++
  "  li a2, 0xa0010008           # out ptr\n" ++
  "  sd zero, 0(a2)\n" ++
  "  jal ra, block_withdrawals_total\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbwt_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  withdrawalDecodeFunction ++ "\n" ++
  withdrawalsSumAmountsFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockWithdrawalsTotalFunction ++ "\n" ++
  ".Lbwt_pdone:"

def ziskBlockWithdrawalsTotalDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wd_offset:\n" ++
  "  .zero 8\n" ++
  "wd_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wsa_count:\n" ++
  "  .zero 8\n" ++
  "wsa_entry_offset:\n" ++
  "  .zero 8\n" ++
  "wsa_entry_length:\n" ++
  "  .zero 8\n" ++
  "wsa_struct:\n" ++
  "  .zero 48\n" ++
  ".balign 8\n" ++
  "bwt_struct:\n" ++
  "  .zero 48"

def ziskBlockWithdrawalsTotalProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockWithdrawalsTotalPrologue
  dataAsm     := ziskBlockWithdrawalsTotalDataSection
}

/-! ## block_summary -- PR-K86

    One-pass block body audit. Decode the body, then extract:

      tx_count                u64   — count of transactions
      withdrawal_total_gwei   u64   — sum of withdrawal amounts
      ommers_empty            u64   — 1 if ommers is empty, else 0

    Useful for receipt / consensus-layer cross-checks and as a
    convenient single-call entry point for callers that need
    multiple block-level summaries.

    Composes:
      - PR-K83 `block_body_decode`      — split body
      - PR-K47 `rlp_list_count_items`   — count txs
      - PR-K65 `withdrawals_sum_amounts` — sum withdrawal amounts
      - Inline check                    — ommers length == 1, byte == 0xc0

    Output struct (24 bytes):
      0..  8  tx_count
      8.. 16  withdrawal_total_gwei
     16.. 24  ommers_empty (0 or 1)

    Status encoding:
      0          : success
      1          : block_body_decode failed
      101..102   : rlp_list_count_items on txs failed (1=parse fail)
                   — only code 101 is observed in practice
      201..202   : withdrawals_sum_amounts failed (1=parse / 2=overflow)

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : 24-byte output struct ptr
      ra (input)  : return
      a0 (output) : composite status code.

    Uses 48 bytes of `.data` scratch (`bsum_struct`). -/
def blockSummaryFunction : String :=
  "block_summary:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # body_rlp ptr\n" ++
  "  mv s1, a1                   # body_len\n" ++
  "  mv s2, a2                   # output struct ptr\n" ++
  "  # Step 1: block_body_decode → bsum_struct.\n" ++
  "  la a2, bsum_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbsum_body_fail\n" ++
  "  # Step 2: tx_count = rlp_list_count_items(txs sub-list).\n" ++
  "  la t0, bsum_struct\n" ++
  "  ld t1, 0(t0)                # txs_offset\n" ++
  "  ld t2, 8(t0)                # txs_length\n" ++
  "  add a0, s0, t1\n" ++
  "  mv a1, t2\n" ++
  "  addi a2, s2, 0              # out[0..8] = tx_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  beqz a0, .Lbsum_s3\n" ++
  "  li t3, 100\n" ++
  "  add a0, a0, t3              # 1 → 101\n" ++
  "  j .Lbsum_ret\n" ++
  ".Lbsum_s3:\n" ++
  "  # Step 3: withdrawals_sum_amounts → out[8..16].\n" ++
  "  la t0, bsum_struct\n" ++
  "  ld t1, 32(t0)               # withdrawals_offset\n" ++
  "  ld t2, 40(t0)               # withdrawals_length\n" ++
  "  add a0, s0, t1\n" ++
  "  mv a1, t2\n" ++
  "  addi a2, s2, 8              # out[8..16] = total\n" ++
  "  jal ra, withdrawals_sum_amounts\n" ++
  "  beqz a0, .Lbsum_s4\n" ++
  "  li t3, 200\n" ++
  "  add a0, a0, t3              # 1 → 201, 2 → 202\n" ++
  "  j .Lbsum_ret\n" ++
  ".Lbsum_s4:\n" ++
  "  # Step 4: ommers_empty check → out[16..24] (0 or 1).\n" ++
  "  la t0, bsum_struct\n" ++
  "  ld t1, 24(t0)               # ommers_length\n" ++
  "  li t2, 1\n" ++
  "  bne t1, t2, .Lbsum_ommers_not_empty\n" ++
  "  ld t3, 16(t0)               # ommers_offset\n" ++
  "  add t3, s0, t3\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  li t5, 0xc0\n" ++
  "  bne t4, t5, .Lbsum_ommers_not_empty\n" ++
  "  li t6, 1\n" ++
  "  sd t6, 16(s2)\n" ++
  "  j .Lbsum_ok\n" ++
  ".Lbsum_ommers_not_empty:\n" ++
  "  sd zero, 16(s2)\n" ++
  ".Lbsum_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Lbsum_ret\n" ++
  ".Lbsum_body_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbsum_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_summary`: probe BuildUnit. Reads (body_len,
    body_bytes), writes (status, tx_count, wd_total, ommers_empty)
    to OUTPUT (32 bytes total). -/
def ziskBlockSummaryPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # body_len\n" ++
  "  addi a0, a3, 16             # body ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  sd zero,  0(a2)\n" ++
  "  sd zero,  8(a2)\n" ++
  "  sd zero, 16(a2)\n" ++
  "  jal ra, block_summary\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbsum_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  withdrawalDecodeFunction ++ "\n" ++
  withdrawalsSumAmountsFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockSummaryFunction ++ "\n" ++
  ".Lbsum_pdone:"

def ziskBlockSummaryDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wd_offset:\n" ++
  "  .zero 8\n" ++
  "wd_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wsa_count:\n" ++
  "  .zero 8\n" ++
  "wsa_entry_offset:\n" ++
  "  .zero 8\n" ++
  "wsa_entry_length:\n" ++
  "  .zero 8\n" ++
  "wsa_struct:\n" ++
  "  .zero 48\n" ++
  ".balign 8\n" ++
  "bsum_struct:\n" ++
  "  .zero 48"

def ziskBlockSummaryProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockSummaryPrologue
  dataAsm     := ziskBlockSummaryDataSection
}

/-! ## block_body_blob_gas_total -- PR-K89

    Sum blob_gas_used over all EIP-4844 (type 3) txs in a block body:

      block.blob_gas_used = sum(
        len(tx.blob_versioned_hashes) × GAS_PER_BLOB
        for tx in block.transactions
        if tx.type == 3
      )

    Useful for the consensus rule
    `header.blob_gas_used == this sum` (post-Cancun).

    Composes:
      - PR-K83 `block_body_decode`            — split body
      - PR-K47 `rlp_list_count_items`         — number of txs
      - PR-K20 `rlp_list_nth_item`            — i-th tx bytes
      - PR-K40 `tx_type_dispatch`             — typed-tx detector
      - PR-K88 `tx_eip4844_compute_blob_gas`  — per-tx blob gas

    Iteration policy: skip every non-type-3 tx without examining
    its body. Pre-Cancun blocks (no type-3 txs) return 0 cleanly.

    Status encoding (callers can floor(status/100) to identify
    the failing step):

      0          : success
      1          : block_body_decode failed
      101        : rlp_list_count_items failed
      201        : rlp_list_nth_item failed
      301        : tx_type_dispatch failed
      401..402   : tx_eip4844_compute_blob_gas failed
                   (1=K45 decode fail, 2=K64 sum fail)

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : gas_per_blob (u64; 131072 on mainnet Cancun)
      a3 (input)  : u64 out ptr (receives total blob_gas_used)
      ra (input)  : return
      a0 (output) : composite status code

    Uses 48 bytes `.data` scratch (`bbbgt_struct`) plus the small
    scratch buffers inherited from K88 / K83. -/
def blockBodyBlobGasTotalFunction : String :=
  "block_body_blob_gas_total:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                   # body_rlp ptr\n" ++
  "  mv s3, a2                   # gas_per_blob\n" ++
  "  mv s4, a3                   # out ptr\n" ++
  "  li s5, 0                    # total = 0\n" ++
  "  # Step 1: block_body_decode → bbbgt_struct\n" ++
  "  la a2, bbbgt_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbbbgt_body_fail\n" ++
  "  # Load txs sub-list bounds.\n" ++
  "  la t0, bbbgt_struct\n" ++
  "  ld t1, 0(t0)                # txs_offset\n" ++
  "  ld s2, 8(t0)                # s2 = txs_length\n" ++
  "  add s1, s0, t1              # s1 = absolute txs ptr\n" ++
  "  # Step 2: tx_count = rlp_list_count_items(txs)\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  la a2, bbbgt_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  beqz a0, .Lbbbgt_loop_init\n" ++
  "  li a0, 101\n" ++
  "  j .Lbbbgt_ret\n" ++
  ".Lbbbgt_loop_init:\n" ++
  "  la t0, bbbgt_count\n" ++
  "  ld s7, 0(t0)                # s7 = tx_count\n" ++
  "  li s6, 0                    # s6 = i\n" ++
  ".Lbbbgt_loop:\n" ++
  "  beq s6, s7, .Lbbbgt_done\n" ++
  "  # rlp_list_nth_item(s1, s2, s6, &item_off, &item_len)\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s6\n" ++
  "  la a3, bbbgt_item_off\n" ++
  "  la a4, bbbgt_item_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  beqz a0, .Lbbbgt_after_nth\n" ++
  "  li a0, 201\n" ++
  "  j .Lbbbgt_ret\n" ++
  ".Lbbbgt_after_nth:\n" ++
  "  la t0, bbbgt_item_off\n" ++
  "  ld t1, 0(t0)                # item_off\n" ++
  "  la t0, bbbgt_item_len\n" ++
  "  ld t2, 0(t0)                # item_len\n" ++
  "  add t3, s1, t1              # tx_ptr = txs + item_off\n" ++
  "  # tx_type_dispatch(tx_ptr, item_len, &type, &inner_off)\n" ++
  "  mv a0, t3\n" ++
  "  mv a1, t2\n" ++
  "  la a2, bbbgt_type\n" ++
  "  la a3, bbbgt_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  beqz a0, .Lbbbgt_after_dispatch\n" ++
  "  li a0, 301\n" ++
  "  j .Lbbbgt_ret\n" ++
  ".Lbbbgt_after_dispatch:\n" ++
  "  la t0, bbbgt_type\n" ++
  "  ld t1, 0(t0)                # type\n" ++
  "  li t4, 3\n" ++
  "  bne t1, t4, .Lbbbgt_step\n" ++
  "  # type 3: compute blob_gas\n" ++
  "  la t0, bbbgt_item_off\n" ++
  "  ld t1, 0(t0)                # item_off\n" ++
  "  la t0, bbbgt_item_len\n" ++
  "  ld t2, 0(t0)                # item_len\n" ++
  "  la t0, bbbgt_inner_off\n" ++
  "  ld t5, 0(t0)                # inner_off\n" ++
  "  add t3, s1, t1\n" ++
  "  add a0, t3, t5              # inner_ptr = tx_ptr + inner_off\n" ++
  "  sub a1, t2, t5              # inner_len = item_len - inner_off\n" ++
  "  mv a2, s3                   # gas_per_blob\n" ++
  "  la a3, bbbgt_blob_gas\n" ++
  "  jal ra, tx_eip4844_compute_blob_gas\n" ++
  "  beqz a0, .Lbbbgt_after_blob\n" ++
  "  li t0, 400\n" ++
  "  add a0, a0, t0              # 1 → 401, 2 → 402\n" ++
  "  j .Lbbbgt_ret\n" ++
  ".Lbbbgt_after_blob:\n" ++
  "  la t0, bbbgt_blob_gas\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s5, s5, t1              # total += blob_gas\n" ++
  ".Lbbbgt_step:\n" ++
  "  addi s6, s6, 1\n" ++
  "  j .Lbbbgt_loop\n" ++
  ".Lbbbgt_done:\n" ++
  "  sd s5, 0(s4)                # *out = total\n" ++
  "  li a0, 0\n" ++
  "  j .Lbbbgt_ret\n" ++
  ".Lbbbgt_body_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbbbgt_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_block_body_blob_gas_total`: probe BuildUnit. Reads
    (body_len, gas_per_blob, body_bytes) from host input,
    writes (status, total_blob_gas) to OUTPUT (16 bytes). -/
def ziskBlockBodyBlobGasTotalPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # body_len\n" ++
  "  ld a2, 16(a4)               # gas_per_blob\n" ++
  "  addi a0, a4, 24             # body ptr\n" ++
  "  li a3, 0xa0010008           # out u64 ptr\n" ++
  "  sd zero, 0(a3)\n" ++
  "  jal ra, block_body_blob_gas_total\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbbbgt_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  blobGasUsedFromVersionedHashesFunction ++ "\n" ++
  txEip4844ComputeBlobGasFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockBodyBlobGasTotalFunction ++ "\n" ++
  ".Lbbbgt_pdone:"

def ziskBlockBodyBlobGasTotalDataSection : String :=
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
  "bbbgt_struct:\n" ++
  "  .zero 48\n" ++
  ".balign 8\n" ++
  "bbbgt_count:\n" ++
  "  .zero 8\n" ++
  "bbbgt_item_off:\n" ++
  "  .zero 8\n" ++
  "bbbgt_item_len:\n" ++
  "  .zero 8\n" ++
  "bbbgt_type:\n" ++
  "  .zero 8\n" ++
  "bbbgt_inner_off:\n" ++
  "  .zero 8\n" ++
  "bbbgt_blob_gas:\n" ++
  "  .zero 8"

def ziskBlockBodyBlobGasTotalProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockBodyBlobGasTotalPrologue
  dataAsm     := ziskBlockBodyBlobGasTotalDataSection
}

/-! ## block_validate_blob_gas_consistency -- PR-K91

    Cancun-era consensus rule: the value of `header.blob_gas_used`
    must equal the sum of per-tx blob gas across the block's body.

      header.blob_gas_used == sum(
        len(tx.blob_versioned_hashes) × GAS_PER_BLOB
        for tx in block.transactions
        if tx.type == 3
      )

    Composes:
      - PR-K53 `rlp_field_to_u64`        — extract header field 17
      - PR-K89 `block_body_blob_gas_total` — sum over body

    The Python reference (`forks/amsterdam/fork.py`) enforces this
    inside `apply_body`. This helper packages the check into a
    single ECALL-shaped routine so callers don't need to thread
    intermediate values through registers.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : body_rlp ptr
      a3 (input)  : body_rlp byte length
      a4 (input)  : gas_per_blob (u64; 131072 on mainnet Cancun)
      ra (input)  : return
      a0 (output) : composite status code

    Status decade encoding (floor(status/100) identifies the
    failing step):

      0          : success — header.blob_gas_used == body total
      1          : header parse / field 17 missing / not u64
      2          : mismatch (header.blob_gas_used ≠ body total)
      101        : body decode failed
      201        : body rlp_list_count_items failed
      301        : body rlp_list_nth_item failed
      401        : body tx_type_dispatch failed
      501..502   : body tx_eip4844_compute_blob_gas forwarded
                   (501 = K45 decode, 502 = K64 sum)

    Uses 32 bytes of `.data` scratch (`bvbgc_header_bgu` +
    `bvbgc_body_total`) plus the scratch buffers inherited from
    PR-K89 / K88 / K83. -/
def blockValidateBlobGasConsistencyFunction : String :=
  "block_validate_blob_gas_consistency:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a2                   # body_rlp ptr\n" ++
  "  mv s1, a3                   # body_len\n" ++
  "  mv s2, a4                   # gas_per_blob\n" ++
  "  # Step 1: extract header.blob_gas_used (field 17, u64).\n" ++
  "  # a0,a1 still hold (header_ptr, header_len).\n" ++
  "  li a2, 17\n" ++
  "  la a3, bvbgc_header_bgu\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  beqz a0, .Lbvbgc_step2\n" ++
  "  li a0, 1\n" ++
  "  j .Lbvbgc_ret\n" ++
  ".Lbvbgc_step2:\n" ++
  "  # Step 2: body total via K89.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s2                   # gas_per_blob\n" ++
  "  la a3, bvbgc_body_total\n" ++
  "  jal ra, block_body_blob_gas_total\n" ++
  "  beqz a0, .Lbvbgc_compare\n" ++
  "  # K89 returns: 1=body decode, 101=count, 201=nth, 301=dispatch,\n" ++
  "  # 401..402=K88 forwarded. Re-map onto our 101+ decade space.\n" ++
  "  li t0, 100\n" ++
  "  add a0, a0, t0              # 1→101, 101→201, 201→301, 301→401,\n" ++
  "                              # 401→501, 402→502\n" ++
  "  j .Lbvbgc_ret\n" ++
  ".Lbvbgc_compare:\n" ++
  "  la t0, bvbgc_header_bgu\n" ++
  "  ld t1, 0(t0)\n" ++
  "  la t0, bvbgc_body_total\n" ++
  "  ld t2, 0(t0)\n" ++
  "  beq t1, t2, .Lbvbgc_ok\n" ++
  "  li a0, 2\n" ++
  "  j .Lbvbgc_ret\n" ++
  ".Lbvbgc_ok:\n" ++
  "  li a0, 0\n" ++
  ".Lbvbgc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_validate_blob_gas_consistency`: probe BuildUnit.
    Input layout (LE u64s + variable bytes):
      bytes  0.. 8 : header_len
      bytes  8..16 : body_len
      bytes 16..24 : gas_per_blob
      bytes 24..   : header_rlp ‖ body_rlp (concatenated, no padding
                     between)
    OUTPUT layout (8 bytes):
      bytes  0.. 8 : status code -/
def ziskBlockValidateBlobGasConsistencyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # header_len\n" ++
  "  ld a3, 16(a5)               # body_len\n" ++
  "  ld a4, 24(a5)               # gas_per_blob\n" ++
  "  addi a0, a5, 32             # header_ptr\n" ++
  "  add a2, a0, a1              # body_ptr = header_ptr + header_len\n" ++
  "  jal ra, block_validate_blob_gas_consistency\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbvbgc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  blobGasUsedFromVersionedHashesFunction ++ "\n" ++
  txEip4844ComputeBlobGasFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockBodyBlobGasTotalFunction ++ "\n" ++
  blockValidateBlobGasConsistencyFunction ++ "\n" ++
  ".Lbvbgc_pdone:"

def ziskBlockValidateBlobGasConsistencyDataSection : String :=
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
  "bbbgt_struct:\n" ++
  "  .zero 48\n" ++
  ".balign 8\n" ++
  "bbbgt_count:\n" ++
  "  .zero 8\n" ++
  "bbbgt_item_off:\n" ++
  "  .zero 8\n" ++
  "bbbgt_item_len:\n" ++
  "  .zero 8\n" ++
  "bbbgt_type:\n" ++
  "  .zero 8\n" ++
  "bbbgt_inner_off:\n" ++
  "  .zero 8\n" ++
  "bbbgt_blob_gas:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bvbgc_header_bgu:\n" ++
  "  .zero 8\n" ++
  "bvbgc_body_total:\n" ++
  "  .zero 8"

def ziskBlockValidateBlobGasConsistencyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateBlobGasConsistencyPrologue
  dataAsm     := ziskBlockValidateBlobGasConsistencyDataSection
}



/-! ## zisk_ssz_pair_hash — PR-S4 SSZ merkleization primitive

    First consumer of the SSZ `hash_tree_root` shim:
    `sha256_pair(L, R) = sha256(L ‖ R)`.

    The shim lives at `Stateless/SSZ/HashTreeRoot/Program.lean`
    (`sszPairHashCallAsm`); this BuildUnit is the executable that
    exercises it end-to-end on ziskemu. The driver reads two
    32-byte values from the host-supplied input region (laid out
    contiguously at INPUT_ADDR + 16..80 so they're already in
    L ‖ R order), passes the buffer base in `a0` and the OUTPUT
    pointer in `a2`, and lets the shim hand off to the PR-S2
    `zkvm_sha256` wrapper.

    ### Fixture (32-byte SSZ "zero leaf" pair)

      L = 0x00..00 (32 bytes)
      R = 0x00..00 (32 bytes)

    Expected (this is `Z_1` in the SSZ zero-hashes sequence):

      sha256(0x00 * 64) =
        f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b

    The test script feeds those 64 zero bytes via `ziskemu -i` and
    diffs the 32-byte digest at OUTPUT_ADDR against Python's
    `hashlib.sha256(b"\\x00" * 64).digest()`.

    ### Why this isn't redundant with the PR-S2 in-data fixture

    PR-S2 tested `zkvm_sha256` on `.data`-resident constants;
    PR-S3 tested it on host-supplied input. PR-S4 additionally
    pins the `ssz_pair_hash` *symbol* -- the named entry point
    that higher SSZ machinery (PR-S5+ merkleize, mix_in_length)
    will call. Once that symbol exists, the merkleize loop is a
    straightforward "load chunk, call `ssz_pair_hash`, store
    result" iteration; no further sha256 layout decisions.
-/
def ziskSszPairHashPrologue : String :=
  "  # set up stack\n" ++
  "  li sp, 0xa0050000\n" ++
  "  # point at the 64-byte L||R buffer in host input region\n" ++
  "  li a3, 0x40000000           # INPUT_ADDR\n" ++
  "  addi a0, a3, 16             # a0 = L||R ptr (INPUT_ADDR + 16)\n" ++
  "  li a2, 0xa0010000           # a2 = OUTPUT_ADDR\n" ++
  EvmAsm.Stateless.SSZ.HashTreeRoot.sszPairHashCallAsm ++ "\n" ++
  "  j .Lzs4_done\n" ++
  zkvmSha256Function ++ "\n" ++
  ".Lzs4_done:"

/-- `.data` for the SSZ pair-hash probe: same scratch buffers
    used by `zkvm_sha256` (IV, state, input block, params). The
    L‖R bytes come from host input, not from `.data`. -/
def ziskSszPairHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667    # LE(h0) || LE(h1)\n" ++
  "  .quad 0xa54ff53a3c6ef372    # LE(h2) || LE(h3)\n" ++
  "  .quad 0x9b05688c510e527f    # LE(h4) || LE(h5)\n" ++
  "  .quad 0x5be0cd191f83d9ab    # LE(h6) || LE(h7)\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input"

def ziskSszPairHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszPairHashPrologue
  dataAsm     := ziskSszPairHashDataSection
}

/-! ## ssz_zero_hashes — PR-S5 precomputed SSZ Z_0..Z_31 table

    Pre-computed SSZ "zero hashes" sequence:
      Z_0 = 0x00..00 (32 zero bytes)
      Z_i = sha256(Z_{i-1} ‖ Z_{i-1})

    Emitted as a single 1024-byte `.rodata` block. Entry `i` lives
    at `ssz_zero_hashes + i * 32`. Cached at codegen time so the
    PR-S6 merkleize loop can short-circuit all-zero subtrees of
    depth ≤ 31 without re-running SHA-256.

    Values generated once with Python:

        import hashlib
        z = [b"\x00" * 32]
        for _ in range(31):
            z.append(hashlib.sha256(z[-1] + z[-1]).digest())

    `z[1]` matches the PR-S4 fixture (`f5a5fd42..fb4b`), and the
    full table is regression-checked by the
    `zisk_ssz_zero_hashes` probe BuildUnit below: it accepts a
    depth `i` via host input, looks up Z_i, and writes 32 bytes
    to OUTPUT. The check script iterates i = 0..31 and diffs
    each Z_i against Python's recomputation.
-/
def sszZeroHashesDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "ssz_zero_hashes:\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00    # Z_0\n" ++
  "  .byte 0xf5, 0xa5, 0xfd, 0x42, 0xd1, 0x6a, 0x20, 0x30, 0x27, 0x98, 0xef, 0x6e, 0xd3, 0x09, 0x97, 0x9b, 0x43, 0x00, 0x3d, 0x23, 0x20, 0xd9, 0xf0, 0xe8, 0xea, 0x98, 0x31, 0xa9, 0x27, 0x59, 0xfb, 0x4b    # Z_1\n" ++
  "  .byte 0xdb, 0x56, 0x11, 0x4e, 0x00, 0xfd, 0xd4, 0xc1, 0xf8, 0x5c, 0x89, 0x2b, 0xf3, 0x5a, 0xc9, 0xa8, 0x92, 0x89, 0xaa, 0xec, 0xb1, 0xeb, 0xd0, 0xa9, 0x6c, 0xde, 0x60, 0x6a, 0x74, 0x8b, 0x5d, 0x71    # Z_2\n" ++
  "  .byte 0xc7, 0x80, 0x09, 0xfd, 0xf0, 0x7f, 0xc5, 0x6a, 0x11, 0xf1, 0x22, 0x37, 0x06, 0x58, 0xa3, 0x53, 0xaa, 0xa5, 0x42, 0xed, 0x63, 0xe4, 0x4c, 0x4b, 0xc1, 0x5f, 0xf4, 0xcd, 0x10, 0x5a, 0xb3, 0x3c    # Z_3\n" ++
  "  .byte 0x53, 0x6d, 0x98, 0x83, 0x7f, 0x2d, 0xd1, 0x65, 0xa5, 0x5d, 0x5e, 0xea, 0xe9, 0x14, 0x85, 0x95, 0x44, 0x72, 0xd5, 0x6f, 0x24, 0x6d, 0xf2, 0x56, 0xbf, 0x3c, 0xae, 0x19, 0x35, 0x2a, 0x12, 0x3c    # Z_4\n" ++
  "  .byte 0x9e, 0xfd, 0xe0, 0x52, 0xaa, 0x15, 0x42, 0x9f, 0xae, 0x05, 0xba, 0xd4, 0xd0, 0xb1, 0xd7, 0xc6, 0x4d, 0xa6, 0x4d, 0x03, 0xd7, 0xa1, 0x85, 0x4a, 0x58, 0x8c, 0x2c, 0xb8, 0x43, 0x0c, 0x0d, 0x30    # Z_5\n" ++
  "  .byte 0xd8, 0x8d, 0xdf, 0xee, 0xd4, 0x00, 0xa8, 0x75, 0x55, 0x96, 0xb2, 0x19, 0x42, 0xc1, 0x49, 0x7e, 0x11, 0x4c, 0x30, 0x2e, 0x61, 0x18, 0x29, 0x0f, 0x91, 0xe6, 0x77, 0x29, 0x76, 0x04, 0x1f, 0xa1    # Z_6\n" ++
  "  .byte 0x87, 0xeb, 0x0d, 0xdb, 0xa5, 0x7e, 0x35, 0xf6, 0xd2, 0x86, 0x67, 0x38, 0x02, 0xa4, 0xaf, 0x59, 0x75, 0xe2, 0x25, 0x06, 0xc7, 0xcf, 0x4c, 0x64, 0xbb, 0x6b, 0xe5, 0xee, 0x11, 0x52, 0x7f, 0x2c    # Z_7\n" ++
  "  .byte 0x26, 0x84, 0x64, 0x76, 0xfd, 0x5f, 0xc5, 0x4a, 0x5d, 0x43, 0x38, 0x51, 0x67, 0xc9, 0x51, 0x44, 0xf2, 0x64, 0x3f, 0x53, 0x3c, 0xc8, 0x5b, 0xb9, 0xd1, 0x6b, 0x78, 0x2f, 0x8d, 0x7d, 0xb1, 0x93    # Z_8\n" ++
  "  .byte 0x50, 0x6d, 0x86, 0x58, 0x2d, 0x25, 0x24, 0x05, 0xb8, 0x40, 0x01, 0x87, 0x92, 0xca, 0xd2, 0xbf, 0x12, 0x59, 0xf1, 0xef, 0x5a, 0xa5, 0xf8, 0x87, 0xe1, 0x3c, 0xb2, 0xf0, 0x09, 0x4f, 0x51, 0xe1    # Z_9\n" ++
  "  .byte 0xff, 0xff, 0x0a, 0xd7, 0xe6, 0x59, 0x77, 0x2f, 0x95, 0x34, 0xc1, 0x95, 0xc8, 0x15, 0xef, 0xc4, 0x01, 0x4e, 0xf1, 0xe1, 0xda, 0xed, 0x44, 0x04, 0xc0, 0x63, 0x85, 0xd1, 0x11, 0x92, 0xe9, 0x2b    # Z_10\n" ++
  "  .byte 0x6c, 0xf0, 0x41, 0x27, 0xdb, 0x05, 0x44, 0x1c, 0xd8, 0x33, 0x10, 0x7a, 0x52, 0xbe, 0x85, 0x28, 0x68, 0x89, 0x0e, 0x43, 0x17, 0xe6, 0xa0, 0x2a, 0xb4, 0x76, 0x83, 0xaa, 0x75, 0x96, 0x42, 0x20    # Z_11\n" ++
  "  .byte 0xb7, 0xd0, 0x5f, 0x87, 0x5f, 0x14, 0x00, 0x27, 0xef, 0x51, 0x18, 0xa2, 0x24, 0x7b, 0xbb, 0x84, 0xce, 0x8f, 0x2f, 0x0f, 0x11, 0x23, 0x62, 0x30, 0x85, 0xda, 0xf7, 0x96, 0x0c, 0x32, 0x9f, 0x5f    # Z_12\n" ++
  "  .byte 0xdf, 0x6a, 0xf5, 0xf5, 0xbb, 0xdb, 0x6b, 0xe9, 0xef, 0x8a, 0xa6, 0x18, 0xe4, 0xbf, 0x80, 0x73, 0x96, 0x08, 0x67, 0x17, 0x1e, 0x29, 0x67, 0x6f, 0x8b, 0x28, 0x4d, 0xea, 0x6a, 0x08, 0xa8, 0x5e    # Z_13\n" ++
  "  .byte 0xb5, 0x8d, 0x90, 0x0f, 0x5e, 0x18, 0x2e, 0x3c, 0x50, 0xef, 0x74, 0x96, 0x9e, 0xa1, 0x6c, 0x77, 0x26, 0xc5, 0x49, 0x75, 0x7c, 0xc2, 0x35, 0x23, 0xc3, 0x69, 0x58, 0x7d, 0xa7, 0x29, 0x37, 0x84    # Z_14\n" ++
  "  .byte 0xd4, 0x9a, 0x75, 0x02, 0xff, 0xcf, 0xb0, 0x34, 0x0b, 0x1d, 0x78, 0x85, 0x68, 0x85, 0x00, 0xca, 0x30, 0x81, 0x61, 0xa7, 0xf9, 0x6b, 0x62, 0xdf, 0x9d, 0x08, 0x3b, 0x71, 0xfc, 0xc8, 0xf2, 0xbb    # Z_15\n" ++
  "  .byte 0x8f, 0xe6, 0xb1, 0x68, 0x92, 0x56, 0xc0, 0xd3, 0x85, 0xf4, 0x2f, 0x5b, 0xbe, 0x20, 0x27, 0xa2, 0x2c, 0x19, 0x96, 0xe1, 0x10, 0xba, 0x97, 0xc1, 0x71, 0xd3, 0xe5, 0x94, 0x8d, 0xe9, 0x2b, 0xeb    # Z_16\n" ++
  "  .byte 0x8d, 0x0d, 0x63, 0xc3, 0x9e, 0xba, 0xde, 0x85, 0x09, 0xe0, 0xae, 0x3c, 0x9c, 0x38, 0x76, 0xfb, 0x5f, 0xa1, 0x12, 0xbe, 0x18, 0xf9, 0x05, 0xec, 0xac, 0xfe, 0xcb, 0x92, 0x05, 0x76, 0x03, 0xab    # Z_17\n" ++
  "  .byte 0x95, 0xee, 0xc8, 0xb2, 0xe5, 0x41, 0xca, 0xd4, 0xe9, 0x1d, 0xe3, 0x83, 0x85, 0xf2, 0xe0, 0x46, 0x61, 0x9f, 0x54, 0x49, 0x6c, 0x23, 0x82, 0xcb, 0x6c, 0xac, 0xd5, 0xb9, 0x8c, 0x26, 0xf5, 0xa4    # Z_18\n" ++
  "  .byte 0xf8, 0x93, 0xe9, 0x08, 0x91, 0x77, 0x75, 0xb6, 0x2b, 0xff, 0x23, 0x29, 0x4d, 0xbb, 0xe3, 0xa1, 0xcd, 0x8e, 0x6c, 0xc1, 0xc3, 0x5b, 0x48, 0x01, 0x88, 0x7b, 0x64, 0x6a, 0x6f, 0x81, 0xf1, 0x7f    # Z_19\n" ++
  "  .byte 0xcd, 0xdb, 0xa7, 0xb5, 0x92, 0xe3, 0x13, 0x33, 0x93, 0xc1, 0x61, 0x94, 0xfa, 0xc7, 0x43, 0x1a, 0xbf, 0x2f, 0x54, 0x85, 0xed, 0x71, 0x1d, 0xb2, 0x82, 0x18, 0x3c, 0x81, 0x9e, 0x08, 0xeb, 0xaa    # Z_20\n" ++
  "  .byte 0x8a, 0x8d, 0x7f, 0xe3, 0xaf, 0x8c, 0xaa, 0x08, 0x5a, 0x76, 0x39, 0xa8, 0x32, 0x00, 0x14, 0x57, 0xdf, 0xb9, 0x12, 0x8a, 0x80, 0x61, 0x14, 0x2a, 0xd0, 0x33, 0x56, 0x29, 0xff, 0x23, 0xff, 0x9c    # Z_21\n" ++
  "  .byte 0xfe, 0xb3, 0xc3, 0x37, 0xd7, 0xa5, 0x1a, 0x6f, 0xbf, 0x00, 0xb9, 0xe3, 0x4c, 0x52, 0xe1, 0xc9, 0x19, 0x5c, 0x96, 0x9b, 0xd4, 0xe7, 0xa0, 0xbf, 0xd5, 0x1d, 0x5c, 0x5b, 0xed, 0x9c, 0x11, 0x67    # Z_22\n" ++
  "  .byte 0xe7, 0x1f, 0x0a, 0xa8, 0x3c, 0xc3, 0x2e, 0xdf, 0xbe, 0xfa, 0x9f, 0x4d, 0x3e, 0x01, 0x74, 0xca, 0x85, 0x18, 0x2e, 0xec, 0x9f, 0x3a, 0x09, 0xf6, 0xa6, 0xc0, 0xdf, 0x63, 0x77, 0xa5, 0x10, 0xd7    # Z_23\n" ++
  "  .byte 0x31, 0x20, 0x6f, 0xa8, 0x0a, 0x50, 0xbb, 0x6a, 0xbe, 0x29, 0x08, 0x50, 0x58, 0xf1, 0x62, 0x12, 0x21, 0x2a, 0x60, 0xee, 0xc8, 0xf0, 0x49, 0xfe, 0xcb, 0x92, 0xd8, 0xc8, 0xe0, 0xa8, 0x4b, 0xc0    # Z_24\n" ++
  "  .byte 0x21, 0x35, 0x2b, 0xfe, 0xcb, 0xed, 0xdd, 0xe9, 0x93, 0x83, 0x9f, 0x61, 0x4c, 0x3d, 0xac, 0x0a, 0x3e, 0xe3, 0x75, 0x43, 0xf9, 0xb4, 0x12, 0xb1, 0x61, 0x99, 0xdc, 0x15, 0x8e, 0x23, 0xb5, 0x44    # Z_25\n" ++
  "  .byte 0x61, 0x9e, 0x31, 0x27, 0x24, 0xbb, 0x6d, 0x7c, 0x31, 0x53, 0xed, 0x9d, 0xe7, 0x91, 0xd7, 0x64, 0xa3, 0x66, 0xb3, 0x89, 0xaf, 0x13, 0xc5, 0x8b, 0xf8, 0xa8, 0xd9, 0x04, 0x81, 0xa4, 0x67, 0x65    # Z_26\n" ++
  "  .byte 0x7c, 0xdd, 0x29, 0x86, 0x26, 0x82, 0x50, 0x62, 0x8d, 0x0c, 0x10, 0xe3, 0x85, 0xc5, 0x8c, 0x61, 0x91, 0xe6, 0xfb, 0xe0, 0x51, 0x91, 0xbc, 0xc0, 0x4f, 0x13, 0x3f, 0x2c, 0xea, 0x72, 0xc1, 0xc4    # Z_27\n" ++
  "  .byte 0x84, 0x89, 0x30, 0xbd, 0x7b, 0xa8, 0xca, 0xc5, 0x46, 0x61, 0x07, 0x21, 0x13, 0xfb, 0x27, 0x88, 0x69, 0xe0, 0x7b, 0xb8, 0x58, 0x7f, 0x91, 0x39, 0x29, 0x33, 0x37, 0x4d, 0x01, 0x7b, 0xcb, 0xe1    # Z_28\n" ++
  "  .byte 0x88, 0x69, 0xff, 0x2c, 0x22, 0xb2, 0x8c, 0xc1, 0x05, 0x10, 0xd9, 0x85, 0x32, 0x92, 0x80, 0x33, 0x28, 0xbe, 0x4f, 0xb0, 0xe8, 0x04, 0x95, 0xe8, 0xbb, 0x8d, 0x27, 0x1f, 0x5b, 0x88, 0x96, 0x36    # Z_29\n" ++
  "  .byte 0xb5, 0xfe, 0x28, 0xe7, 0x9f, 0x1b, 0x85, 0x0f, 0x86, 0x58, 0x24, 0x6c, 0xe9, 0xb6, 0xa1, 0xe7, 0xb4, 0x9f, 0xc0, 0x6d, 0xb7, 0x14, 0x3e, 0x8f, 0xe0, 0xb4, 0xf2, 0xb0, 0xc5, 0x52, 0x3a, 0x5c    # Z_30\n" ++
  "  .byte 0x98, 0x5e, 0x92, 0x9f, 0x70, 0xaf, 0x28, 0xd0, 0xbd, 0xd1, 0xa9, 0x0a, 0x80, 0x8f, 0x97, 0x7f, 0x59, 0x7c, 0x7c, 0x77, 0x8c, 0x48, 0x9e, 0x98, 0xd3, 0xbd, 0x89, 0x10, 0xd3, 0x1a, 0xc0, 0xf7    # Z_31"

/-- `zisk_ssz_zero_hashes`: probe BuildUnit that reads a u64
    depth index from `INPUT_ADDR + 8` (LE; first 8 bytes of the
    ziskemu input file) and writes the 32 bytes of `Z_i` to
    `OUTPUT_ADDR`. -/
def ziskSszZeroHashesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000           # INPUT_ADDR\n" ++
  "  ld a0, 8(a3)                # a0 = depth index i (u64 LE)\n" ++
  "  slli a0, a0, 5              # a0 = i * 32 (byte offset)\n" ++
  "  la a1, ssz_zero_hashes\n" ++
  "  add a1, a1, a0              # a1 = &Z_i\n" ++
  "  li a2, 0xa0010000           # a2 = OUTPUT_ADDR\n" ++
  "  ld t0, 0(a1);  sd t0, 0(a2)\n" ++
  "  ld t0, 8(a1);  sd t0, 8(a2)\n" ++
  "  ld t0, 16(a1); sd t0, 16(a2)\n" ++
  "  ld t0, 24(a1); sd t0, 24(a2)"

def ziskSszZeroHashesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszZeroHashesPrologue
  dataAsm     := sszZeroHashesDataSection
}

/-! ## ssz_merkleize_pow2 — PR-S6 pair-hash reduction loop

    SSZ pairwise merkleization for a power-of-two chunk count.
    Implements:

        while n > 1:
            for i in 0..n/2:
                chunks[i] = sha256_pair(chunks[2i], chunks[2i+1])
            n = n / 2
        root = chunks[0]

    Reads `n * 32` bytes from the caller's input pointer into
    `ssz_merkleize_scratch` (a 1024-byte working buffer), then
    reduces in place. Final root is copied to the caller's output
    pointer; the scratch buffer's first 32 bytes hold the same
    root after the call (intentional, reusable by chained
    merkleizers).

    Calling convention:
      a0 (input)  : ptr to `n * 32` chunk bytes
      a1 (input)  : n (power of two; 1 ≤ n ≤ 32)
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) : 0 (ZKVM_EOK)

    Clobbers t0..t6, a0..a2. Saves/restores s0..s6 and ra via
    its own 64-byte stack frame. Requires `sp` to point at
    writable RAM. -/
def sszMerkleizePow2Function : String :=
  "ssz_merkleize_pow2:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp)\n" ++
  "  sd s6, 56(sp)\n" ++
  "  # s0 = n (current chunk count); s5 = scratch base; s6 = caller out ptr\n" ++
  "  mv s0, a1\n" ++
  "  mv s6, a2\n" ++
  "  la s5, ssz_merkleize_scratch\n" ++
  "  # copy n*32 input bytes into scratch (in 8-byte units)\n" ++
  "  mv t0, a0\n" ++
  "  mv t1, s5\n" ++
  "  slli t2, s0, 5             # t2 = n * 32 bytes to copy\n" ++
  ".Lmrk_copy:\n" ++
  "  beqz t2, .Lmrk_iter\n" ++
  "  ld t3, 0(t0)\n" ++
  "  sd t3, 0(t1)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t2, t2, -8\n" ++
  "  j .Lmrk_copy\n" ++
  ".Lmrk_iter:\n" ++
  "  # if n == 1: root is at scratch[0..32]\n" ++
  "  li t0, 1\n" ++
  "  beq s0, t0, .Lmrk_done\n" ++
  "  # pair-hash adjacent chunks into the lower half of scratch\n" ++
  "  srli s1, s0, 1             # s1 = n/2 = pair count\n" ++
  "  mv s2, s5                  # s2 = src pair ptr (64-byte step)\n" ++
  "  mv s3, s5                  # s3 = dst slot ptr (32-byte step)\n" ++
  ".Lmrk_pair:\n" ++
  "  beqz s1, .Lmrk_advance\n" ++
  "  mv a0, s2\n" ++
  "  mv a2, s3\n" ++
  "  li a1, 64\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  addi s2, s2, 64\n" ++
  "  addi s3, s3, 32\n" ++
  "  addi s1, s1, -1\n" ++
  "  j .Lmrk_pair\n" ++
  ".Lmrk_advance:\n" ++
  "  srli s0, s0, 1             # n /= 2\n" ++
  "  j .Lmrk_iter\n" ++
  ".Lmrk_done:\n" ++
  "  # copy 32 bytes scratch[0..32] -> caller out ptr (s6)\n" ++
  "  ld t0,  0(s5);  sd t0,  0(s6)\n" ++
  "  ld t0,  8(s5);  sd t0,  8(s6)\n" ++
  "  ld t0, 16(s5);  sd t0, 16(s6)\n" ++
  "  ld t0, 24(s5);  sd t0, 24(s6)\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp)\n" ++
  "  ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_ssz_merkleize_pow2`: probe BuildUnit that reads `n`
    from `INPUT_ADDR + 8` (u64 LE) and `n * 32` chunk bytes
    starting at `INPUT_ADDR + 16`, then calls `ssz_merkleize_pow2`
    and writes the 32-byte root to `OUTPUT_ADDR`.

    Test fixtures (in `scripts/codegen-zisk-ssz-merkleize-pow2-check.sh`):
      * n = 1, single zero chunk           → Z_0
      * n = 2, two zero chunks             → Z_1
      * n = 4, four zero chunks            → Z_2
      * n = 8, eight zero chunks           → Z_3
      * n = 16, sixteen zero chunks        → Z_4
      * n = 32, thirty-two zero chunks     → Z_5

    These align with the PR-S5 `Z_d` table values, so a passing
    probe confirms the merkleize loop walks the tree correctly. -/
def ziskSszMerkleizePow2Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000           # INPUT_ADDR\n" ++
  "  ld a1, 8(a3)                # a1 = n\n" ++
  "  addi a0, a3, 16             # a0 = chunks ptr\n" ++
  "  li a2, 0xa0010000           # a2 = OUTPUT_ADDR\n" ++
  "  jal ra, ssz_merkleize_pow2\n" ++
  "  j .Lzs6_done\n" ++
  zkvmSha256Function ++ "\n" ++
  sszMerkleizePow2Function ++ "\n" ++
  ".Lzs6_done:"

def ziskSszMerkleizePow2DataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_scratch:\n" ++
  "  .zero 1024"

def ziskSszMerkleizePow2ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszMerkleizePow2Prologue
  dataAsm     := ziskSszMerkleizePow2DataSection
}

/-! ## ssz_merkleize — PR-S7 arbitrary-length SSZ merkleization

    Lifts `ssz_merkleize_pow2` (PR-S6) to the general SSZ case
    by zero-padding short inputs out to a power of two, then
    further padding the resulting root up to the SSZ capacity by
    pair-hashing with `Z_d` from the PR-S5 table at each missing
    depth.

    Two phases:
      1. Pad chunks up to `M = next_pow2(n)` with `Z_0`. Reduce
         in place via `ssz_merkleize_pow2`. Result: partial root
         at depth `d_M = log2(M)`.
      2. For `d` from `d_M` to `limit_log2 - 1`:
             partial_root = sha256_pair(partial_root, Z_d)

    Edge case `n = 0`: result is `Z_{limit_log2}` straight from
    the zero-hashes table; phase 1 is skipped.

    Calling convention:
      a0 (input)  : ptr to `n * 32` chunk bytes
      a1 (input)  : n (0 ≤ n ≤ 32)
      a2 (input)  : limit_log2 L (0 ≤ L ≤ 31; capacity = 2^L)
      a3 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) : 0 (ZKVM_EOK)

    Clobbers t0..t6, a0..a3. Saves/restores s0..s6 and ra via
    a 64-byte stack frame. -/
def sszMerkleizeFunction : String :=
  "ssz_merkleize:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp)\n" ++
  "  sd s6, 56(sp)\n" ++
  "  # s5 = chunks_in ptr; s0 = n; s1 = limit_log2 L; s6 = out ptr\n" ++
  "  mv s5, a0\n" ++
  "  mv s0, a1\n" ++
  "  mv s1, a2\n" ++
  "  mv s6, a3\n" ++
  "  # n == 0 → root is Z_L (look up directly)\n" ++
  "  beqz s0, .Lszm_zero_path\n" ++
  "  # phase 1: compute M = next_pow2(n) and depth_M = log2(M)\n" ++
  "  li t0, 1                    # candidate M\n" ++
  "  li s4, 0                    # candidate depth\n" ++
  ".Lszm_pow2_scan:\n" ++
  "  bge t0, s0, .Lszm_have_M\n" ++
  "  slli t0, t0, 1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lszm_pow2_scan\n" ++
  ".Lszm_have_M:\n" ++
  "  mv s3, t0                   # s3 = M; s4 = depth_M = log2(M)\n" ++
  "  # copy n*32 input bytes into ssz_merkleize_padded, zero-pad the rest\n" ++
  "  la t0, ssz_merkleize_padded\n" ++
  "  slli t1, s0, 5              # t1 = n*32 bytes to copy\n" ++
  "  mv t2, s5                   # src\n" ++
  "  mv t3, t0                   # dst\n" ++
  ".Lszm_cp:\n" ++
  "  beqz t1, .Lszm_pad\n" ++
  "  ld t4, 0(t2)\n" ++
  "  sd t4, 0(t3)\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t1, t1, -8\n" ++
  "  j .Lszm_cp\n" ++
  ".Lszm_pad:\n" ++
  "  sub t1, s3, s0              # t1 = M - n (slots to zero)\n" ++
  "  slli t1, t1, 5              # t1 = (M-n)*32 bytes\n" ++
  ".Lszm_zr:\n" ++
  "  beqz t1, .Lszm_call_pow2\n" ++
  "  sd zero, 0(t3)\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t1, t1, -8\n" ++
  "  j .Lszm_zr\n" ++
  ".Lszm_call_pow2:\n" ++
  "  # call ssz_merkleize_pow2(padded, M, ssz_merkleize_partial)\n" ++
  "  la a0, ssz_merkleize_padded\n" ++
  "  mv a1, s3\n" ++
  "  la a2, ssz_merkleize_partial\n" ++
  "  jal ra, ssz_merkleize_pow2\n" ++
  "  # phase 2: mix in Z_d for d in [depth_M, L)\n" ++
  ".Lszm_mix:\n" ++
  "  beq s4, s1, .Lszm_copy_out\n" ++
  "  # ssz_merkleize_partial[0..32]   = current root (input L)\n" ++
  "  # ssz_merkleize_partial[32..64]  = Z_{s4}        (input R)\n" ++
  "  la t0, ssz_zero_hashes\n" ++
  "  slli t1, s4, 5              # offset = s4*32\n" ++
  "  add t0, t0, t1              # &Z_{s4}\n" ++
  "  la t2, ssz_merkleize_partial\n" ++
  "  addi t2, t2, 32             # &partial[32..]\n" ++
  "  ld t3,  0(t0); sd t3,  0(t2)\n" ++
  "  ld t3,  8(t0); sd t3,  8(t2)\n" ++
  "  ld t3, 16(t0); sd t3, 16(t2)\n" ++
  "  ld t3, 24(t0); sd t3, 24(t2)\n" ++
  "  la a0, ssz_merkleize_partial\n" ++
  "  li a1, 64\n" ++
  "  la a2, ssz_merkleize_partial\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lszm_mix\n" ++
  ".Lszm_copy_out:\n" ++
  "  la t0, ssz_merkleize_partial\n" ++
  "  ld t1,  0(t0); sd t1,  0(s6)\n" ++
  "  ld t1,  8(t0); sd t1,  8(s6)\n" ++
  "  ld t1, 16(t0); sd t1, 16(s6)\n" ++
  "  ld t1, 24(t0); sd t1, 24(s6)\n" ++
  "  j .Lszm_ret\n" ++
  ".Lszm_zero_path:\n" ++
  "  # root = Z_L (n == 0 case)\n" ++
  "  la t0, ssz_zero_hashes\n" ++
  "  slli t1, s1, 5\n" ++
  "  add t0, t0, t1\n" ++
  "  ld t1,  0(t0); sd t1,  0(s6)\n" ++
  "  ld t1,  8(t0); sd t1,  8(s6)\n" ++
  "  ld t1, 16(t0); sd t1, 16(s6)\n" ++
  "  ld t1, 24(t0); sd t1, 24(s6)\n" ++
  ".Lszm_ret:\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp)\n" ++
  "  ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_ssz_merkleize`: probe BuildUnit that reads
    `(limit_log2 : u64, n : u64, chunks : n * 32 bytes)` from
    the host input region and writes the SSZ root to OUTPUT.
    Input layout:
      bytes  0.. 8 : ignored ziskemu length prefix
      bytes  8..16 : limit_log2 (u64 LE)
      bytes 16..24 : n (u64 LE)
      bytes 24..   : n * 32 chunk bytes -/
def ziskSszMerkleizePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a2, 8(a3)                # a2 = limit_log2 L\n" ++
  "  ld a1, 16(a3)               # a1 = n\n" ++
  "  addi a0, a3, 24             # a0 = chunks ptr\n" ++
  "  li a3, 0xa0010000           # a3 = OUTPUT_ADDR (now caller out ptr)\n" ++
  "  jal ra, ssz_merkleize\n" ++
  "  j .Lzs7_done\n" ++
  zkvmSha256Function ++ "\n" ++
  sszMerkleizePow2Function ++ "\n" ++
  sszMerkleizeFunction ++ "\n" ++
  ".Lzs7_done:"

def ziskSszMerkleizeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_scratch:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_padded:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_partial:\n" ++
  "  .zero 64\n" ++
  sszZeroHashesDataSection

def ziskSszMerkleizeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszMerkleizePrologue
  dataAsm     := ziskSszMerkleizeDataSection
}

/-! ## ssz_pack_bytes — PR-S8 SSZ byte chunker

    Packs an arbitrary byte string into 32-byte chunks for
    consumption by `ssz_merkleize`. The byte stream is copied
    verbatim; the final chunk is right-zero-padded if the byte
    count is not a multiple of 32. Returns the chunk count.

    Calling convention:
      a0 (input)  : src ptr
      a1 (input)  : byte length L (0 ≤ L ≤ 1024)
      a2 (input)  : dst chunk buffer ptr (32 * ceil(L/32) bytes)
      ra (input)  : return
      a0 (output) : chunk count = ceil(L / 32)
      bytes at *a2: source bytes followed by zero-padding

    Byte-at-a-time copy (slow path, ~L instructions). Acceptable
    for bring-up; a future PR can specialise to 8-byte units
    when alignment is known. -/
def sszPackBytesFunction : String :=
  "ssz_pack_bytes:\n" ++
  "  # a0 = src, a1 = L, a2 = dst.\n" ++
  "  # First copy L bytes from src to dst (byte-wise).\n" ++
  "  mv t0, a0                  # t0 = src cursor\n" ++
  "  mv t1, a2                  # t1 = dst cursor\n" ++
  "  mv t2, a1                  # t2 = remaining bytes\n" ++
  ".Lszpb_copy:\n" ++
  "  beqz t2, .Lszpb_check_pad\n" ++
  "  lbu t3, 0(t0)\n" ++
  "  sb  t3, 0(t1)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Lszpb_copy\n" ++
  ".Lszpb_check_pad:\n" ++
  "  # remainder = L & 31; if zero, skip pad. else pad = 32 - remainder.\n" ++
  "  andi t2, a1, 31\n" ++
  "  beqz t2, .Lszpb_count\n" ++
  "  li t3, 32\n" ++
  "  sub t2, t3, t2             # t2 = pad bytes\n" ++
  ".Lszpb_pad:\n" ++
  "  beqz t2, .Lszpb_count\n" ++
  "  sb zero, 0(t1)\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Lszpb_pad\n" ++
  ".Lszpb_count:\n" ++
  "  # chunks = ceil(L / 32) = (L + 31) >> 5\n" ++
  "  addi t0, a1, 31\n" ++
  "  srli a0, t0, 5\n" ++
  "  ret"

/-- `zisk_ssz_pack_bytes`: probe BuildUnit that reads
    `(L : u64, data : L bytes)` from the host input region,
    calls `ssz_pack_bytes`, and writes the result to OUTPUT in
    the layout `(chunk_count : u64, chunks : chunk_count * 32
    bytes)`. The test script diffs the entire OUTPUT against
    Python's recomputation. Input layout:
      bytes  0.. 8 : L (u64 LE)
      bytes  8..   : L source bytes -/
def ziskSszPackBytesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # a1 = L\n" ++
  "  addi a0, a3, 16             # a0 = src ptr\n" ++
  "  li a2, 0xa0010008           # a2 = dst chunks (OUTPUT + 8)\n" ++
  "  jal ra, ssz_pack_bytes\n" ++
  "  # write chunk count (a0) at OUTPUT + 0\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lzs8_done\n" ++
  sszPackBytesFunction ++ "\n" ++
  ".Lzs8_done:"

def ziskSszPackBytesDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ssz_pack_bytes_scratch:\n" ++
  "  .zero 8"

def ziskSszPackBytesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszPackBytesPrologue
  dataAsm     := ziskSszPackBytesDataSection
}

/-! ## ssz_hash_tree_root_bytes — PR-S9 SSZ hash_tree_root(Bytes)

    Composes PR-S8 `ssz_pack_bytes`, PR-S7 `ssz_merkleize`, and
    PR-S2 `zkvm_sha256` into a single named entry point:

        chunks       = pack(value)
        partial_root = merkleize(chunks, limit_log2_chunks)
        root         = sha256(partial_root || u256_le(len))

    Matches the SSZ spec for variable-length `Bytes` with
    declared capacity `B_max = 32 * 2^limit_log2_chunks` bytes.

    Calling convention:
      a0 (input)  : src bytes ptr
      a1 (input)  : L (0 ≤ L ≤ 1024)
      a2 (input)  : limit_log2_chunks (0 ≤ L_log2 ≤ 31)
      a3 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) : 0 (ZKVM_EOK)

    Uses three scratches in `.data`:
      ssz_hb_chunks  (1024 B) -- packed chunks before merkleize
      ssz_hb_partial (32 B)   -- partial root from merkleize
      ssz_hb_mix     (64 B)   -- (partial || length) buffer
                                 for the final sha256 -/
def sszHashTreeRootBytesFunction : String :=
  "ssz_hash_tree_root_bytes:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  # s0 = src; s1 = L; s2 = limit_log2; s3 = out ptr\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv s3, a3\n" ++
  "  # Step 1: pack(src, L) -> ssz_hb_chunks. Returns chunk count in a0.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, ssz_hb_chunks\n" ++
  "  jal ra, ssz_pack_bytes\n" ++
  "  mv s4, a0                  # s4 = chunks count\n" ++
  "  # Step 2: merkleize(ssz_hb_chunks, s4, s2, ssz_hb_partial)\n" ++
  "  la a0, ssz_hb_chunks\n" ++
  "  mv a1, s4\n" ++
  "  mv a2, s2\n" ++
  "  la a3, ssz_hb_partial\n" ++
  "  jal ra, ssz_merkleize\n" ++
  "  # Step 3: write length chunk (u256 LE of L) at ssz_hb_mix + 32..64\n" ++
  "  # Copy partial root into ssz_hb_mix[0..32]\n" ++
  "  la t0, ssz_hb_partial\n" ++
  "  la t1, ssz_hb_mix\n" ++
  "  ld t2,  0(t0); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t0); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t0); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t0); sd t2, 24(t1)\n" ++
  "  # Length chunk at ssz_hb_mix + 32..64: u64 LE of L, then 24 zero bytes.\n" ++
  "  sd s1, 32(t1)               # low 8 bytes = L (LE)\n" ++
  "  sd zero, 40(t1)\n" ++
  "  sd zero, 48(t1)\n" ++
  "  sd zero, 56(t1)\n" ++
  "  # Step 4: sha256(ssz_hb_mix, 64) -> caller's out ptr (s3)\n" ++
  "  la a0, ssz_hb_mix\n" ++
  "  li a1, 64\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_ssz_hash_tree_root_bytes`: probe BuildUnit that reads
    `(L, limit_log2, data)` from host input, calls the wrapper,
    writes the 32-byte SSZ root to OUTPUT_ADDR.
    Input layout:
      file bytes  0.. 8 : L            (at INPUT_ADDR +  8)
      file bytes  8..16 : limit_log2   (at INPUT_ADDR + 16)
      file bytes 16..   : L source bytes (at INPUT_ADDR + 24) -/
def ziskSszHashTreeRootBytesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # a1 = L\n" ++
  "  ld a2, 16(a4)               # a2 = limit_log2_chunks\n" ++
  "  addi a0, a4, 24             # a0 = src ptr\n" ++
  "  li a3, 0xa0010000           # a3 = OUTPUT_ADDR\n" ++
  "  jal ra, ssz_hash_tree_root_bytes\n" ++
  "  j .Lzs9_done\n" ++
  zkvmSha256Function ++ "\n" ++
  sszPackBytesFunction ++ "\n" ++
  sszMerkleizePow2Function ++ "\n" ++
  sszMerkleizeFunction ++ "\n" ++
  sszHashTreeRootBytesFunction ++ "\n" ++
  ".Lzs9_done:"

def ziskSszHashTreeRootBytesDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_scratch:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_padded:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_partial:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "ssz_hb_chunks:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_hb_partial:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "ssz_hb_mix:\n" ++
  "  .zero 64\n" ++
  sszZeroHashesDataSection

def ziskSszHashTreeRootBytesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszHashTreeRootBytesPrologue
  dataAsm     := ziskSszHashTreeRootBytesDataSection
}

/-! ## ssz_hash_tree_root_list_bytelist — PR-S11

    SSZ hash_tree_root for `List[ByteList[B], M]`.

    Reads the SSZ-encoded list section directly (inner-offset
    table at the start, concatenated element bytes after).
    Iterates over elements, recursively SSZ-hashes each as a
    `ByteList[B]` via `ssz_hash_tree_root_bytes`, merkleizes the
    resulting child roots with capacity `2^count_log2`, then
    mixes in the element count.

    Calling convention:
      a0 (input)  : section ptr (read-only)
      a1 (input)  : section_len (0 = empty list)
      a2 (input)  : per-element byte_limit_log2_chunks
      a3 (input)  : list count_limit_log2 (capacity = 2^a3)
      a4 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) : 0 (ZKVM_EOK)

    PR-S11 caps N (element count) at 32, matching the inner
    merkleize cap. Output is byte-identical to
    `SszList[ByteList[B], M](...).hash_tree_root()` from
    `remerkleable` for any compliant input. -/
def sszHashTreeRootListByteListFunction : String :=
  "ssz_hash_tree_root_list_bytelist:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # s0 = section ptr\n" ++
  "  mv s1, a1                  # s1 = section_len\n" ++
  "  mv s2, a2                  # s2 = byte_log2\n" ++
  "  mv s3, a3                  # s3 = count_log2\n" ++
  "  mv s4, a4                  # s4 = out ptr\n" ++
  "  beqz s1, .Lszls_N0          # empty section ⇒ N = 0\n" ++
  "  lwu t0, 0(s0)              # offset_0 = 4 * N\n" ++
  "  srli s5, t0, 2             # s5 = N (element count)\n" ++
  "  li s6, 0                   # s6 = i (loop counter)\n" ++
  ".Lszls_loop:\n" ++
  "  beq s6, s5, .Lszls_done_loop\n" ++
  "  slli t0, s6, 2             # 4*i\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  add a0, s0, t2             # el_i_start\n" ++
  "  addi t3, s6, 1\n" ++
  "  beq t3, s5, .Lszls_use_end\n" ++
  "  slli t3, t3, 2             # 4*(i+1)\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)              # inner_off_{i+1}\n" ++
  "  add t4, s0, t4             # el_i_end\n" ++
  "  j .Lszls_have_end\n" ++
  ".Lszls_use_end:\n" ++
  "  add t4, s0, s1             # el_i_end = section_end\n" ++
  ".Lszls_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  mv a2, s2                  # byte_log2\n" ++
  "  la a3, ssz_ltb_child_roots\n" ++
  "  slli t0, s6, 5             # 32*i\n" ++
  "  add a3, a3, t0             # &child_roots[i]\n" ++
  "  jal ra, ssz_hash_tree_root_bytes\n" ++
  "  addi s6, s6, 1\n" ++
  "  j .Lszls_loop\n" ++
  ".Lszls_done_loop:\n" ++
  "  la a0, ssz_ltb_child_roots\n" ++
  "  mv a1, s5                  # N\n" ++
  "  mv a2, s3                  # count_log2\n" ++
  "  la a3, ssz_ltb_partial\n" ++
  "  jal ra, ssz_merkleize\n" ++
  "  la t0, ssz_ltb_partial\n" ++
  "  la t1, ssz_ltb_mix\n" ++
  "  ld t2,  0(t0); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t0); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t0); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t0); sd t2, 24(t1)\n" ++
  "  sd s5, 32(t1)              # length = N (u64 LE)\n" ++
  "  sd zero, 40(t1)\n" ++
  "  sd zero, 48(t1)\n" ++
  "  sd zero, 56(t1)\n" ++
  "  la a0, ssz_ltb_mix\n" ++
  "  li a1, 64\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  j .Lszls_ret\n" ++
  ".Lszls_N0:\n" ++
  "  la t0, ssz_zero_hashes\n" ++
  "  slli t1, s3, 5\n" ++
  "  add t0, t0, t1             # &Z_{count_log2}\n" ++
  "  la t1, ssz_ltb_mix\n" ++
  "  ld t2,  0(t0); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t0); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t0); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t0); sd t2, 24(t1)\n" ++
  "  sd zero, 32(t1); sd zero, 40(t1)\n" ++
  "  sd zero, 48(t1); sd zero, 56(t1)\n" ++
  "  la a0, ssz_ltb_mix\n" ++
  "  li a1, 64\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, zkvm_sha256\n" ++
  ".Lszls_ret:\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_ssz_hash_tree_root_list_bytelist`: probe BuildUnit
    that reads the SSZ-encoded list section from host input and
    writes the SSZ root to OUTPUT.
    Input layout:
      bytes  0.. 8 : section_len
      bytes  8..16 : byte_limit_log2
      bytes 16..24 : count_limit_log2
      bytes 24..   : SSZ list section bytes -/
def ziskSszHashTreeRootListByteListPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # section_len\n" ++
  "  ld a2, 16(a5)               # byte_log2\n" ++
  "  ld a3, 24(a5)               # count_log2\n" ++
  "  addi a0, a5, 32             # section ptr\n" ++
  "  li a4, 0xa0010000           # OUTPUT_ADDR\n" ++
  "  jal ra, ssz_hash_tree_root_list_bytelist\n" ++
  "  j .Lzs11_done\n" ++
  zkvmSha256Function ++ "\n" ++
  sszPackBytesFunction ++ "\n" ++
  sszMerkleizePow2Function ++ "\n" ++
  sszMerkleizeFunction ++ "\n" ++
  sszHashTreeRootBytesFunction ++ "\n" ++
  sszHashTreeRootListByteListFunction ++ "\n" ++
  ".Lzs11_done:"

def ziskSszHashTreeRootListByteListDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_scratch:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_padded:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_partial:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "ssz_hb_chunks:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_hb_partial:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "ssz_hb_mix:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "ssz_ltb_child_roots:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_ltb_partial:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "ssz_ltb_mix:\n" ++
  "  .zero 64\n" ++
  sszZeroHashesDataSection

def ziskSszHashTreeRootListByteListProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszHashTreeRootListByteListPrologue
  dataAsm     := ziskSszHashTreeRootListByteListDataSection
}

/-! ## ssz_hash_tree_root_execution_witness — PR-S12

    SSZ Container hash for the amsterdam `ExecutionWitness`.
    Three variable-size fields (state, codes, headers); each
    field is itself a `List[ByteList[B_i], M_i]` and gets
    hashed via `ssz_hash_tree_root_list_bytelist` (PR-S11). The
    three resulting child roots are merkleized with capacity 4
    slots (`limit_log2 = ceil(log2(3)) = 2`) to produce the
    Container root.

    Per the SSZ spec for Containers, NO mix_in_length step
    follows -- only variable-length List/Bytes types mix in
    length.

    Calling convention:
      a0 (input)  : section ptr (SSZ-encoded ExecutionWitness)
      a1 (input)  : section_len
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) : 0 (ZKVM_EOK)

    Per-field caps inherited from PR-S11: each list's N ≤ 32.
    Test fixtures stay well below; production-sized witnesses
    are a follow-up. -/
def sszHashTreeRootExecutionWitnessFunction : String :=
  "ssz_hash_tree_root_execution_witness:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # s0 = section ptr\n" ++
  "  mv s1, a1                   # s1 = section_len\n" ++
  "  mv s2, a2                   # s2 = out ptr\n" ++
  "  lwu s3, 0(s0)               # off_state\n" ++
  "  lwu s4, 4(s0)               # off_codes\n" ++
  "  lwu s5, 8(s0)               # off_headers\n" ++
  "  add s6, s0, s1              # section_end\n" ++
  "  # Field 0: state (List[ByteList[2^20], 2^20]; byte_log2=15, count_log2=20)\n" ++
  "  add a0, s0, s3              # state_start\n" ++
  "  add t0, s0, s4              # state_end\n" ++
  "  sub a1, t0, a0\n" ++
  "  li a2, 15\n" ++
  "  li a3, 20\n" ++
  "  la a4, ssz_ew_field_roots\n" ++
  "  jal ra, ssz_hash_tree_root_list_bytelist\n" ++
  "  # Field 1: codes (List[ByteList[2^24], 2^16]; byte_log2=19, count_log2=16)\n" ++
  "  add a0, s0, s4              # codes_start\n" ++
  "  add t0, s0, s5              # codes_end\n" ++
  "  sub a1, t0, a0\n" ++
  "  li a2, 19\n" ++
  "  li a3, 16\n" ++
  "  la a4, ssz_ew_field_roots\n" ++
  "  addi a4, a4, 32\n" ++
  "  jal ra, ssz_hash_tree_root_list_bytelist\n" ++
  "  # Field 2: headers (List[ByteList[2^10], 2^8]; byte_log2=5, count_log2=8)\n" ++
  "  add a0, s0, s5              # headers_start\n" ++
  "  sub a1, s6, a0\n" ++
  "  li a2, 5\n" ++
  "  li a3, 8\n" ++
  "  la a4, ssz_ew_field_roots\n" ++
  "  addi a4, a4, 64\n" ++
  "  jal ra, ssz_hash_tree_root_list_bytelist\n" ++
  "  # Merkleize 3 field roots, capacity = 4 slots (limit_log2 = 2)\n" ++
  "  la a0, ssz_ew_field_roots\n" ++
  "  li a1, 3\n" ++
  "  li a2, 2\n" ++
  "  mv a3, s2\n" ++
  "  jal ra, ssz_merkleize\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_ssz_hash_tree_root_execution_witness`: probe BuildUnit
    that reads the SSZ-encoded ExecutionWitness section from host
    input and writes the SSZ root to OUTPUT.
    Input layout:
      bytes  0.. 8 : section_len
      bytes  8..   : SSZ ExecutionWitness section bytes -/
def ziskSszHashTreeRootExecutionWitnessPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # section_len\n" ++
  "  addi a0, a3, 16             # section ptr\n" ++
  "  li a2, 0xa0010000           # OUTPUT_ADDR\n" ++
  "  jal ra, ssz_hash_tree_root_execution_witness\n" ++
  "  j .Lzs12_done\n" ++
  zkvmSha256Function ++ "\n" ++
  sszPackBytesFunction ++ "\n" ++
  sszMerkleizePow2Function ++ "\n" ++
  sszMerkleizeFunction ++ "\n" ++
  sszHashTreeRootBytesFunction ++ "\n" ++
  sszHashTreeRootListByteListFunction ++ "\n" ++
  sszHashTreeRootExecutionWitnessFunction ++ "\n" ++
  ".Lzs12_done:"

def ziskSszHashTreeRootExecutionWitnessDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_scratch:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_padded:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_partial:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "ssz_hb_chunks:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_hb_partial:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "ssz_hb_mix:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "ssz_ltb_child_roots:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_ltb_partial:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "ssz_ltb_mix:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "ssz_ew_field_roots:\n" ++
  "  .zero 96\n" ++
  sszZeroHashesDataSection

def ziskSszHashTreeRootExecutionWitnessProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszHashTreeRootExecutionWitnessPrologue
  dataAsm     := ziskSszHashTreeRootExecutionWitnessDataSection
}

/-! ## stateless_guest body — PR-K5 keccak hash field

    Replaces the zero-stub `new_payload_request_root` field in
    `Stateless.Entry.run_stateless_guest`'s SSZ output with the
    keccak256 of the entire SSZ-input byte string the host
    streamed in via `ziskemu -i`. Concretely:

    - Body: the unchanged `Stateless.Entry.run_stateless_guest`
      Program. It writes:
        bytes  0..32 : zero hash (placeholder)
        byte      32 : successful_validation (PR4/PR5 derived)
        bytes 33..41 : chain_id (PR3 from-decode)
        bytes 41..48 : zero gap
        bytes 48..56 : header_count diagnostic (PR6 from-decode)
    - Epilogue (raw asm): set up sp, load (data ptr, len) from
      INPUT_ADDR + (16, 8), set output = OUTPUT_ADDR + 0, and
      `jal ra, zkvm_keccak256`. The function overwrites
      OUTPUT[0..32] with keccak256(input bytes), clobbering the
      zero stub.

    The host-side `compute_new_payload_request_root` per the spec
    is SSZ `hash_tree_root` (SHA-256), not Keccak. PR-K5 stamps a
    *content-dependent* hash there so the test harness has a
    non-trivial value to verify and the keccak bridge is wired
    into the encoder pipeline end-to-end. Once PR-S series lands,
    the SHA-256 hash_tree_root replaces this keccak. -/
def statelessGuestEpilogue : String :=
  "  # PR-S12: overwrite OUTPUT[0..32] with the SSZ\n" ++
  "  # `hash_tree_root` of the entire `witness:\n" ++
  "  # ExecutionWitness` field -- a 3-field Container holding\n" ++
  "  # state / codes / headers lists.\n" ++
  "  # \n" ++
  "  # SSZ algorithm (Container, NO mix_in_length):\n" ++
  "  #   state_root   = hash_tree_root(List[ByteList[2^20], 2^20])\n" ++
  "  #   codes_root   = hash_tree_root(List[ByteList[2^24], 2^16])\n" ++
  "  #   headers_root = hash_tree_root(List[ByteList[2^10], 2^8])\n" ++
  "  #   root         = merkleize([state_root, codes_root,\n" ++
  "  #                             headers_root], log2=2)\n" ++
  "  # \n" ++
  "  # Per-field caps: each list's N ≤ 32 (inherited from\n" ++
  "  # PR-S11's `ssz_hash_tree_root_list_bytelist`). Test\n" ++
  "  # fixtures stay well below.\n" ++
  "  # \n" ++
  "  # Navigation: chase the outer SSZ offset chain to find\n" ++
  "  # the bounds of the `witness` field within the SSZ-encoded\n" ++
  "  # `SszStatelessInput`, then delegate the per-sub-field\n" ++
  "  # walk + recursive hashing to\n" ++
  "  # `ssz_hash_tree_root_execution_witness`.\n" ++
  "  li sp, 0xa0050000\n" ++
  "  li t3, 0x40000000\n" ++
  "  addi t3, t3, 16             # t3 = ssz_start\n" ++
  "  lwu t4, 4(t3)               # outer offset_1 (witness offset)\n" ++
  "  add a0, t3, t4              # a0 = witness_start (section ptr)\n" ++
  "  lwu t5, 16(t3)              # outer offset_3 (witness end)\n" ++
  "  add t5, t3, t5              # witness_end\n" ++
  "  sub a1, t5, a0              # a1 = witness section_len\n" ++
  "  li a2, 0xa0010000           # a2 = OUTPUT_ADDR (hash field)\n" ++
  "  jal ra, ssz_hash_tree_root_execution_witness\n" ++
  "  j .Lsg_done\n" ++
  zkvmSha256Function ++ "\n" ++
  sszPackBytesFunction ++ "\n" ++
  sszMerkleizePow2Function ++ "\n" ++
  sszMerkleizeFunction ++ "\n" ++
  sszHashTreeRootBytesFunction ++ "\n" ++
  sszHashTreeRootListByteListFunction ++ "\n" ++
  sszHashTreeRootExecutionWitnessFunction ++ "\n" ++
  ".Lsg_done:"

def statelessGuestDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_scratch:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_padded:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_partial:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "ssz_hb_chunks:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_hb_partial:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "ssz_hb_mix:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "ssz_ltb_child_roots:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_ltb_partial:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "ssz_ltb_mix:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "ssz_ew_field_roots:\n" ++
  "  .zero 96\n" ++
  sszZeroHashesDataSection

def statelessGuestUnit : BuildUnit := {
  body        := EvmAsm.Stateless.run_stateless_guest
  epilogueAsm := statelessGuestEpilogue
  dataAsm     := statelessGuestDataSection
}

/-! ## registry -/

/-- Look up a program by name. Returns `none` for unknown names so the CLI
    can produce a clean error. -/
def lookupProgram : String → Option BuildUnit
  | "smoke"                     => some smokeUnit
  | "evm_add"                   => some evmAddUnit
  | "evm_div"                   => some evmDivUnit
  | "evm_div_from_input"        => some evmDivFromInputUnit
  | "evm_mod"                   => some evmModUnit
  | "evm_mod_from_input"        => some evmModFromInputUnit
  | "evm_sdiv"                  => some evmSdivV4Unit
  | "evm_sdiv_from_input"       => some evmSdivV4FromInputUnit
  | "evm_sdiv_v4"               => some evmSdivV4Unit
  | "evm_sdiv_v4_from_input"    => some evmSdivV4FromInputUnit
  | "evm_smod"                  => some evmSmodUnit
  | "evm_smod_from_input"       => some evmSmodFromInputUnit
  | "evm_smod_v4"               => some evmSmodV4Unit
  | "evm_smod_v4_from_input"    => some evmSmodV4FromInputUnit
  | "input_echo"                => some inputEchoUnit
  | "evm_add_from_input"        => some evmAddFromInputUnit
  | "tiny_interp_add"           => some tinyInterpAddUnit
  | "tiny_interp_add2"          => some tinyInterpAdd2Unit
  | "tiny_interp_dispatch_add"  => some tinyInterpDispatchAddUnit
  | "tiny_interp_dispatch_add2" => some tinyInterpDispatchAdd2Unit
  | "runtime_dispatcher"        => some runtimeDispatcherUnit
  | "stateless_guest"           => some statelessGuestUnit
  | "zisk_keccak_probe"         => some ziskKeccakProbeUnit
  | "zisk_keccak256_empty"      => some ziskKeccak256EmptyProbeUnit
  | "zisk_keccak256_abc"        => some ziskKeccak256AbcProbeUnit
  | "zisk_zkvm_keccak256"       => some ziskZkvmKeccak256ProbeUnit
  | "zisk_sha256_probe_le"      => some ziskSha256ProbeLeUnit
  | "zisk_zkvm_sha256"          => some ziskZkvmSha256ProbeUnit
  | "zisk_keccak256_from_input" => some ziskKeccak256FromInputProbeUnit
  | "zisk_headers_keccak_chain" => some ziskHeadersKeccakChainProbeUnit
  | "zisk_headers_keccak_array" => some ziskHeadersKeccakArrayProbeUnit
  | "zisk_headers_parent_hash"  => some ziskHeadersParentHashProbeUnit
  | "zisk_headers_validate_chain" => some ziskHeadersValidateChainProbeUnit
  | "zisk_witness_lookup_by_hash" => some ziskWitnessLookupByHashProbeUnit
  | "zisk_rlp_list_nth_item"    => some ziskRlpListNthItemProbeUnit
  | "zisk_rlp_list_count_items" => some ziskRlpListCountItemsProbeUnit
  | "zisk_access_list_count"    => some ziskAccessListCountProbeUnit
  | "zisk_blob_gas_used_from_versioned_hashes" => some ziskBlobGasUsedFromVersionedHashesProbeUnit
  | "zisk_mpt_node_kind"        => some ziskMptNodeKindProbeUnit
  | "zisk_mpt_branch_child"     => some ziskMptBranchChildProbeUnit
  | "zisk_hp_decode_nibbles"    => some ziskHpDecodeNibblesProbeUnit
  | "zisk_mpt_walk"             => some ziskMptWalkProbeUnit
  | "zisk_bytes_to_nibbles"     => some ziskBytesToNibblesProbeUnit
  | "zisk_mpt_lookup_by_key"    => some ziskMptLookupByKeyProbeUnit
  | "zisk_account_decode"       => some ziskAccountDecodeProbeUnit
  | "zisk_account_at_address"   => some ziskAccountAtAddressProbeUnit
  | "zisk_slot_at_index"        => some ziskSlotAtIndexProbeUnit
  | "zisk_rlp_encode_uint_be"   => some ziskRlpEncodeUintBeProbeUnit
  | "zisk_account_encode"       => some ziskAccountEncodeProbeUnit
  | "zisk_hp_encode_nibbles"    => some ziskHpEncodeNibblesProbeUnit
  | "zisk_state_root_single_account" => some ziskStateRootSingleAccountProbeUnit
  | "zisk_rlp_field_to_u64"     => some ziskRlpFieldToU64ProbeUnit
  | "zisk_rlp_field_to_u256_be" => some ziskRlpFieldToU256BeProbeUnit
  | "zisk_tx_legacy_decode"     => some ziskTxLegacyDecodeProbeUnit
  | "zisk_tx_eip1559_decode"    => some ziskTxEip1559DecodeProbeUnit
  | "zisk_derive_chain_id_from_v" => some ziskDeriveChainIdFromVProbeUnit
  | "zisk_header_minimal_decode" => some ziskHeaderMinimalDecodeProbeUnit
  | "zisk_header_extended_decode" => some ziskHeaderExtendedDecodeProbeUnit
  | "zisk_coinbase_extract_from_header" => some ziskCoinbaseExtractFromHeaderProbeUnit
  | "zisk_header_extract_blob_gas_pair" => some ziskHeaderExtractBlobGasPairProbeUnit
  | "zisk_validate_header_basic" => some ziskValidateHeaderBasicProbeUnit
  | "zisk_check_gas_limit"      => some ziskCheckGasLimitProbeUnit
  | "zisk_tx_validate_against_block" => some ziskTxValidateAgainstBlockProbeUnit
  | "zisk_calc_excess_blob_gas" => some ziskCalcExcessBlobGasProbeUnit
  | "zisk_header_validate_post_merge" => some ziskHeaderValidatePostMergeProbeUnit
  | "zisk_header_validate_extra_data_length" => some ziskHeaderValidateExtraDataLengthProbeUnit
  | "zisk_u256_add_be"          => some ziskU256AddBeProbeUnit
  | "zisk_u256_sub_be"          => some ziskU256SubBeProbeUnit
  | "zisk_u256_eq"              => some ziskU256EqProbeUnit
  | "zisk_u256_mul_u64_be"      => some ziskU256MulU64BeProbeUnit
  | "zisk_account_charge_gas_pre_exec" => some ziskAccountChargeGasPreExecProbeUnit
  | "zisk_account_refund_gas_post_exec" => some ziskAccountRefundGasPostExecProbeUnit
  | "zisk_eip1559_calc_base_fee_per_gas" => some ziskEip1559CalcBaseFeePerGasProbeUnit
  | "zisk_header_validate_base_fee" => some ziskHeaderValidateBaseFeeProbeUnit
  | "zisk_validate_header_full" => some ziskValidateHeaderFullProbeUnit
  | "zisk_u256_from_u64_be"     => some ziskU256FromU64BeProbeUnit
  | "zisk_u256_to_u64_be"       => some ziskU256ToU64BeProbeUnit
  | "zisk_u256_is_zero"         => some ziskU256IsZeroProbeUnit
  | "zisk_u256_min"             => some ziskU256MinProbeUnit
  | "zisk_u256_max"             => some ziskU256MaxProbeUnit
  | "zisk_u256_div_u64_be"      => some ziskU256DivU64BeProbeUnit
  | "zisk_priority_fee_per_gas_eip1559" => some ziskPriorityFeePerGasEip1559ProbeUnit
  | "zisk_effective_gas_price_eip1559" => some ziskEffectiveGasPriceEip1559ProbeUnit
  | "zisk_tx_cost_compute"      => some ziskTxCostComputeProbeUnit
  | "zisk_validate_transaction_balance" => some ziskValidateTransactionBalanceProbeUnit
  | "zisk_tx_type_dispatch"     => some ziskTxTypeDispatchProbeUnit
  | "zisk_tx_eip2930_decode"    => some ziskTxEip2930DecodeProbeUnit
  | "zisk_tx_eip7702_decode"    => some ziskTxEip7702DecodeProbeUnit
  | "zisk_tx_eip4844_decode"    => some ziskTxEip4844DecodeProbeUnit
  | "zisk_tx_eip4844_compute_blob_gas" => some ziskTxEip4844ComputeBlobGasProbeUnit
  | "zisk_block_body_blob_gas_total" => some ziskBlockBodyBlobGasTotalProbeUnit
  | "zisk_block_validate_blob_gas_consistency" => some ziskBlockValidateBlobGasConsistencyProbeUnit
  | "zisk_tx_decode_dispatch"   => some ziskTxDecodeDispatchProbeUnit
  | "zisk_intrinsic_gas_legacy" => some ziskIntrinsicGasLegacyProbeUnit
  | "zisk_tx_validate_intrinsic_gas_legacy" => some ziskTxValidateIntrinsicGasLegacyProbeUnit
  | "zisk_validate_transaction_basic" => some ziskValidateTransactionBasicProbeUnit
  | "zisk_validate_transaction_full" => some ziskValidateTransactionFullProbeUnit
  | "zisk_withdrawal_decode"    => some ziskWithdrawalDecodeProbeUnit
  | "zisk_block_body_decode"    => some ziskBlockBodyDecodeProbeUnit
  | "zisk_block_validate_ommers_empty" => some ziskBlockValidateOmmersEmptyProbeUnit
  | "zisk_process_withdrawal"   => some ziskProcessWithdrawalProbeUnit
  | "zisk_process_withdrawals_block" => some ziskProcessWithdrawalsBlockProbeUnit
  | "zisk_withdrawals_sum_amounts" => some ziskWithdrawalsSumAmountsProbeUnit
  | "zisk_block_withdrawals_total" => some ziskBlockWithdrawalsTotalProbeUnit
  | "zisk_block_summary"        => some ziskBlockSummaryProbeUnit
  | "zisk_sha256_from_input"    => some ziskSha256FromInputProbeUnit
  | "zisk_ssz_pair_hash"        => some ziskSszPairHashProbeUnit
  | "zisk_ssz_zero_hashes"      => some ziskSszZeroHashesProbeUnit
  | "zisk_ssz_merkleize_pow2"   => some ziskSszMerkleizePow2ProbeUnit
  | "zisk_ssz_merkleize"        => some ziskSszMerkleizeProbeUnit
  | "zisk_ssz_pack_bytes"       => some ziskSszPackBytesProbeUnit
  | "zisk_ssz_hash_tree_root_bytes" => some ziskSszHashTreeRootBytesProbeUnit
  | "zisk_ssz_hash_tree_root_list_bytelist" => some ziskSszHashTreeRootListByteListProbeUnit
  | "zisk_ssz_hash_tree_root_execution_witness" => some ziskSszHashTreeRootExecutionWitnessProbeUnit
  | _                           => none

/-- List of known program names, for use in CLI usage strings. -/
def knownProgramNames : List String :=
  ["smoke", "evm_add", "evm_div", "evm_mod", "evm_sdiv", "evm_sdiv_v4", "input_echo",
   "evm_add_from_input", "evm_div_from_input", "evm_mod_from_input",
   "evm_sdiv_from_input", "evm_sdiv_v4_from_input",
   "evm_smod", "evm_smod_from_input",
   "evm_smod_v4", "evm_smod_v4_from_input",
   "tiny_interp_add", "tiny_interp_add2",
   "tiny_interp_dispatch_add", "tiny_interp_dispatch_add2",
   "runtime_dispatcher",
   "stateless_guest",
   "zisk_keccak_probe",
   "zisk_keccak256_empty",
   "zisk_keccak256_abc",
   "zisk_zkvm_keccak256",
   "zisk_sha256_probe_le",
   "zisk_zkvm_sha256",
   "zisk_keccak256_from_input",
   "zisk_headers_keccak_chain",
   "zisk_headers_keccak_array",
   "zisk_headers_parent_hash",
   "zisk_headers_validate_chain",
   "zisk_witness_lookup_by_hash",
   "zisk_rlp_list_nth_item",
   "zisk_rlp_list_count_items",
   "zisk_access_list_count",
   "zisk_blob_gas_used_from_versioned_hashes",
   "zisk_mpt_node_kind",
   "zisk_mpt_branch_child",
   "zisk_hp_decode_nibbles",
   "zisk_mpt_walk",
   "zisk_bytes_to_nibbles",
   "zisk_mpt_lookup_by_key",
   "zisk_account_decode",
   "zisk_account_at_address",
   "zisk_slot_at_index",
   "zisk_rlp_encode_uint_be",
   "zisk_account_encode",
   "zisk_hp_encode_nibbles",
   "zisk_state_root_single_account",
   "zisk_rlp_field_to_u64",
   "zisk_rlp_field_to_u256_be",
   "zisk_tx_legacy_decode",
   "zisk_tx_eip1559_decode",
   "zisk_derive_chain_id_from_v",
   "zisk_header_minimal_decode",
   "zisk_header_extended_decode",
   "zisk_coinbase_extract_from_header",
   "zisk_header_extract_blob_gas_pair",
   "zisk_validate_header_basic",
   "zisk_check_gas_limit",
   "zisk_tx_validate_against_block",
   "zisk_calc_excess_blob_gas",
   "zisk_header_validate_post_merge",
   "zisk_header_validate_extra_data_length",
   "zisk_u256_add_be",
   "zisk_u256_sub_be",
   "zisk_u256_eq",
   "zisk_u256_mul_u64_be",
   "zisk_account_charge_gas_pre_exec",
   "zisk_account_refund_gas_post_exec",
   "zisk_eip1559_calc_base_fee_per_gas",
   "zisk_header_validate_base_fee",
   "zisk_validate_header_full",
   "zisk_u256_from_u64_be",
   "zisk_u256_to_u64_be",
   "zisk_u256_is_zero",
   "zisk_u256_min",
   "zisk_u256_max",
   "zisk_u256_div_u64_be",
   "zisk_priority_fee_per_gas_eip1559",
   "zisk_effective_gas_price_eip1559",
   "zisk_tx_cost_compute",
   "zisk_validate_transaction_balance",
   "zisk_tx_type_dispatch",
   "zisk_tx_eip2930_decode",
   "zisk_tx_eip7702_decode",
   "zisk_tx_eip4844_decode",
   "zisk_tx_eip4844_compute_blob_gas",
   "zisk_block_body_blob_gas_total",
   "zisk_block_validate_blob_gas_consistency",
   "zisk_tx_decode_dispatch",
   "zisk_intrinsic_gas_legacy",
   "zisk_tx_validate_intrinsic_gas_legacy",
   "zisk_validate_transaction_basic",
   "zisk_validate_transaction_full",
   "zisk_withdrawal_decode",
   "zisk_block_body_decode",
   "zisk_block_validate_ommers_empty",
   "zisk_process_withdrawal",
   "zisk_process_withdrawals_block",
   "zisk_withdrawals_sum_amounts",
   "zisk_block_withdrawals_total",
   "zisk_block_summary",
   "zisk_sha256_from_input",
   "zisk_ssz_pair_hash",
   "zisk_ssz_zero_hashes",
   "zisk_ssz_merkleize_pow2",
   "zisk_ssz_merkleize",
   "zisk_ssz_pack_bytes",
   "zisk_ssz_hash_tree_root_bytes",
   "zisk_ssz_hash_tree_root_list_bytelist",
   "zisk_ssz_hash_tree_root_execution_witness"]

end EvmAsm.Codegen
