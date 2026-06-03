/-
  EvmAsm.Codegen.Programs.Evm

  M-series demo programs: smoke target, input echo, the verified-body
  end-to-end paths for ADD / DIV / MOD / SDIV / SMOD, the tiny
  interpreter scaffolding, and the runtime dispatcher.

  Extracted from `EvmAsm.Codegen.Programs` so the registry hub stays
  manageable.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Evm64.Add.Program
import EvmAsm.Evm64.AddMod.Program
import EvmAsm.Evm64.And.Program
import EvmAsm.Evm64.Byte.Program
import EvmAsm.Evm64.Calldata.LoadProgram
import EvmAsm.Evm64.Calldata.CopyProgram
import EvmAsm.Evm64.Calldata.SizeProgram
import EvmAsm.Evm64.ControlFlow.Program
import EvmAsm.Evm64.DivMod.Callable
import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Evm64.Dup.Program
import EvmAsm.Evm64.Env.Program
import EvmAsm.Evm64.Eq.Program
import EvmAsm.Evm64.Exp.Program
import EvmAsm.Evm64.Gt.Program
import EvmAsm.Evm64.IsZero.Program
import EvmAsm.Evm64.Lt.Program
import EvmAsm.Evm64.MLoad.Program
import EvmAsm.Evm64.MStore.Program
import EvmAsm.Evm64.MStore8.Program
import EvmAsm.Evm64.Multiply.Callable
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
import EvmAsm.Codegen.Programs.Clz
import EvmAsm.Codegen.Programs.Noop
import EvmAsm.Codegen.Programs.Storage

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

    **M23 addition**: also writes `halt_kind = 0` to
    `OUTPUT_ADDR + 32`. RETURN / REVERT handlers overwrite this
    cell with their own kind code (1 / 2) on their own exit path
    via `.exit_no_epilogue`, bypassing this epilogue. STOP and the
    other halts that flow through `.exit_label` inherit kind 0.

    Lives in the verified Program world: every instruction is in
    `Instr`, so it benefits from `emitInstr` totality and the round-trip
    tests. -/
def evmAddEpilogue : Program :=
  LI .x5 OUTPUT_ADDR ;;
  LD .x6 .x12 0  ;; SD .x5 .x6 0  ;;
  LD .x6 .x12 8  ;; SD .x5 .x6 8  ;;
  LD .x6 .x12 16 ;; SD .x5 .x6 16 ;;
  LD .x6 .x12 24 ;; SD .x5 .x6 24 ;;
  SD .x5 .x0 32   -- M23: halt_kind = 0 (STOP / unspecified)

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

/-- `EvmAsm.Evm64.evm_div_v5` with the NOP exit slot patched to skip the
    longer 85-instruction v5 div128 subroutine. -/
def evmDivV5Patched : Program :=
  (EvmAsm.Evm64.evm_div_v5 : List Instr).take 267 ++
  [Instr.JAL .x0 (344 : BitVec 21)] ++
  (EvmAsm.Evm64.evm_div_v5 : List Instr).drop 268

/-- `EvmAsm.Evm64.evm_mod_v5` with the same v5 NOP-splice as
    `evmDivV5Patched`. -/
def evmModV5Patched : Program :=
  (EvmAsm.Evm64.evm_mod_v5 : List Instr).take 267 ++
  [Instr.JAL .x0 (344 : BitVec 21)] ++
  (EvmAsm.Evm64.evm_mod_v5 : List Instr).drop 268

/-- `EvmAsm.Evm64.evm_sdiv_v5` with the leading save-ra block removed for
    trampoline-style handlers. -/
def evmSdivV5Patched : Program :=
  (EvmAsm.Evm64.evm_sdiv_v5 : List Instr).drop 1

/-- `EvmAsm.Evm64.evm_smod_v5` with the leading save-ra block removed for
    trampoline-style handlers. -/
def evmSmodV5Patched : Program :=
  (EvmAsm.Evm64.evm_smod_v5 : List Instr).drop 1

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

    Coverage (M6b): 82 opcodes wired —
      - **PUSH0..PUSH32** (33) via `pushHandlers`
      - **DUP1..DUP16** (16) via `dupHandlers`
      - **SWAP1..SWAP16** (16) via `swapHandlers`
      - **17 fixed-shape singletons** via `singletonHandlers`:
        SUB, MUL, SIGNEXTEND, AND, OR, XOR, NOT, LT, GT, SLT, SGT,
        EQ, ISZERO, BYTE, CLZ, SHR, POP — CLZ is currently a bounded
        raw RV64IM handler; the others are parameter-free verified
        `Program`s with the standard `<body>` + `addi x10, x10, 1` +
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

/-- Dispatcher env offset used by the concrete runtime handlers for
    active memory size in bytes. The env data block is 512 bytes, and
    offsets 472 / 480 are already used by event-log metadata. -/
private def activeMemorySizeOff : Nat := 488

/-- Inline asm that updates the runtime `MSIZE` high-water mark from
    one memory access `(offset, length)`, using low u64 limbs. If
    `length = 0`, the EVM does not expand memory even for large
    offsets. -/
private def updateActiveMemorySizeAsm
    (tag offsetReg lengthReg roundedReg currentReg maskReg : String) : String :=
  "  beqz " ++ lengthReg ++ ", .Lmemsize_" ++ tag ++ "_done\n" ++
  "  add " ++ roundedReg ++ ", " ++ offsetReg ++ ", " ++ lengthReg ++ "\n" ++
  "  addi " ++ roundedReg ++ ", " ++ roundedReg ++ ", 31\n" ++
  "  li " ++ maskReg ++ ", -32\n" ++
  "  and " ++ roundedReg ++ ", " ++ roundedReg ++ ", " ++ maskReg ++ "\n" ++
  "  ld " ++ currentReg ++ ", " ++ toString activeMemorySizeOff ++ "(x20)\n" ++
  "  bgeu " ++ currentReg ++ ", " ++ roundedReg ++ ", .Lmemsize_" ++ tag ++ "_done\n" ++
  "  sd " ++ roundedReg ++ ", " ++ toString activeMemorySizeOff ++ "(x20)\n" ++
  ".Lmemsize_" ++ tag ++ "_done:\n"

private def updateActiveMemorySizeConstAsm
    (tag offsetReg tmpLengthReg roundedReg currentReg maskReg : String) (length : Nat) : String :=
  "  li " ++ tmpLengthReg ++ ", " ++ toString length ++ "\n" ++
  updateActiveMemorySizeAsm tag offsetReg tmpLengthReg roundedReg currentReg maskReg

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
  , { label := "h_SHL"        , opcodes := [0x1b], preBody := "  mv x9, x10", body := EvmAsm.Evm64.evm_shl       , tail := x10RestoreAdvance1 }
  , { label := "h_SHR"        , opcodes := [0x1c], preBody := "  mv x9, x10", body := EvmAsm.Evm64.evm_shr       , tail := x10RestoreAdvance1 }
  , { label := "h_SAR"        , opcodes := [0x1d], preBody := "  mv x9, x10", body := EvmAsm.Evm64.evm_sar       , tail := x10RestoreAdvance1 }
  , { label := "h_CLZ"        , opcodes := [0x1e], body := []                         , tail := clzTail }
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
      preBody := "  ld x15, 0(x12)\n" ++
                 updateActiveMemorySizeConstAsm "mload" "x15" "x16" "x17" "x18" "x19" 32
      body    := EvmAsm.Evm64.evm_mload .x15 .x16 .x17 .x18 .x13
      tail    := .advanceAndRet 1 }
  , -- MSTORE: pop offset + value, write 32 bytes BE to memory.
    -- valReg=x14 (scratch; placeholder per evm_mstore docstring).
    { label   := "h_MSTORE"
      opcodes := [0x52]
      preBody := "  ld x15, 0(x12)\n" ++
                 updateActiveMemorySizeConstAsm "mstore" "x15" "x16" "x17" "x18" "x19" 32
      body    := EvmAsm.Evm64.evm_mstore .x15 .x14 .x16 .x17 .x18 .x13
      tail    := .advanceAndRet 1 }
  , -- MSTORE8: pop offset + value, write 1 byte to memory.
    { label   := "h_MSTORE8"
      opcodes := [0x53]
      preBody := "  ld x15, 0(x12)\n" ++
                 updateActiveMemorySizeConstAsm "mstore8" "x15" "x16" "x17" "x18" "x19" 1
      body    := EvmAsm.Evm64.evm_mstore8 .x15 .x14 .x18 .x13
      tail    := .advanceAndRet 1 } ]

/-- MSIZE pushes the dispatcher-maintained active memory size. It is
    updated by the concrete memory handlers in this file using the
    EVM's 32-byte rounding rule. -/
def memoryMetadataHandlers : List OpcodeHandlerSpec :=
  [ { label   := "h_MSIZE"
      opcodes := [0x59]
      body    := []
      tail    := .custom <|
        "  addi x12, x12, -32\n" ++
        "  ld x14, " ++ toString activeMemorySizeOff ++ "(x20)\n" ++
        "  sd x14, 0(x12)\n" ++
        "  sd x0, 8(x12)\n" ++
        "  sd x0, 16(x12)\n" ++
        "  sd x0, 24(x12)\n" ++
        "  addi x10, x10, 1\n" ++
        "  ret" } ]

/-- M30: GAS (0x5a) pushes the dispatcher-maintained remaining gas
    (env+568, charged per-opcode by the dispatch loop). Mirrors the
    MSIZE handler — read the env cell, push it as a 256-bit word (low
    limb = remaining gas, high limbs 0). The loop charges GAS's own
    cost (BASE = 2) *before* this handler runs, so the pushed value
    already reflects it, matching EVM semantics. -/
def gasHandlers : List OpcodeHandlerSpec :=
  [ { label   := "h_GAS"
      opcodes := [0x5a]
      body    := []
      tail    := .custom <|
        "  addi x12, x12, -32\n" ++
        "  ld x14, 568(x20)\n" ++       -- env.gasRemaining (M30)
        "  sd x14, 0(x12)\n" ++
        "  sd x0, 8(x12)\n" ++
        "  sd x0, 16(x12)\n" ++
        "  sd x0, 24(x12)\n" ++
        "  addi x10, x10, 1\n" ++
        "  ret" } ]

/-- M12 simple environment opcodes (13 of them, one record each).

    All 13 share the verified body
    `EvmAsm.Evm64.Env.evm_env_load envBaseReg tmpReg field`
    (9 instructions = 36 bytes per handler) parameterized over a
    `SimpleEnvField`. The dispatcher prologue sets `x20 = &evm_env`
    (a 416-byte = 13×32 region in `.data` initialised to zero), and
    each handler passes `.x20` as `envBaseReg` plus `.x15` as
    `tmpReg`. None of these bodies touch `x10`, so `preBody := ""`.

    `x20` was chosen over `x14` (the M8/M9/M10 save register) because
    DIV/MOD/SDIV/SMOD/ADDMOD all use `preBody := "mv x14, x10"` —
    `x14` is explicitly "outside the dispatcher's preserved set" per
    M8's docstring. `x20` is a callee-saved LP64 register with zero
    references in any `EvmAsm/Evm64/*/Program.lean` and zero uses by
    any existing handler's `preBody`/`tail`, making it the cleanest
    long-term home for the env base.

    The env region is zero-initialised; non-zero env values come
    from a future host-preload PR. The wiring correctness (each
    opcode byte routes to the right field offset, x12 advances, the
    32 bytes land on the stack) is what M12 validates. -/
def envHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_ADDRESS"    , opcodes := [0x30], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .address    , tail := .advanceAndRet 1 }
  , { label := "h_ORIGIN"     , opcodes := [0x32], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .origin     , tail := .advanceAndRet 1 }
  , { label := "h_CALLER"     , opcodes := [0x33], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .caller     , tail := .advanceAndRet 1 }
  , { label := "h_CALLVALUE"  , opcodes := [0x34], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .callValue  , tail := .advanceAndRet 1 }
  , { label := "h_GASPRICE"   , opcodes := [0x3a], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .gasPrice   , tail := .advanceAndRet 1 }
  , { label := "h_COINBASE"   , opcodes := [0x41], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .coinbase   , tail := .advanceAndRet 1 }
  , { label := "h_TIMESTAMP"  , opcodes := [0x42], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .timestamp  , tail := .advanceAndRet 1 }
  , { label := "h_NUMBER"     , opcodes := [0x43], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .number     , tail := .advanceAndRet 1 }
  , { label := "h_PREVRANDAO" , opcodes := [0x44], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .prevrandao , tail := .advanceAndRet 1 }
  , { label := "h_GASLIMIT"   , opcodes := [0x45], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .gasLimit   , tail := .advanceAndRet 1 }
  , { label := "h_CHAINID"    , opcodes := [0x46], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .chainId    , tail := .advanceAndRet 1 }
  , { label := "h_SELFBALANCE", opcodes := [0x47], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .selfBalance, tail := .advanceAndRet 1 }
  , { label := "h_BASEFEE"    , opcodes := [0x48], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .baseFee    , tail := .advanceAndRet 1 } ]

/-! ## M28 blob-context opcodes

  `BLOBBASEFEE` (0x4a) is an Amsterdam/Cancun context opcode. The
  executable spec computes it as `calculate_blob_gas_price(block_env.excess_blob_gas)`;
  this runtime dispatcher receives that already-computed 256-bit word in the
  `pack-bytecode.py --blob-base-fee` input trailer and copies it to `evm_env+512`.

  `BLOBHASH` (0x49) reads `tx_env.blob_versioned_hashes[index]` from the
  bounded `evm_blob_hashes` table. The runtime prologue copies up to 16
  entries from `pack-bytecode.py --blob-hashes` and stores the copied count at
  `evm_env+544`; indexes outside that count, or indexes with nonzero high
  limbs, push zero per execution-specs. -/
def blobContextHandlers : List OpcodeHandlerSpec :=
  let blobBaseFeeBody : Program :=
    ADDI .x12 .x12 (-32) ;;
    LD .x15 .x20 (BitVec.ofNat 12 512) ;;
    SD .x12 .x15 0 ;;
    LD .x15 .x20 (BitVec.ofNat 12 520) ;;
    SD .x12 .x15 8 ;;
    LD .x15 .x20 (BitVec.ofNat 12 528) ;;
    SD .x12 .x15 16 ;;
    LD .x15 .x20 (BitVec.ofNat 12 536) ;;
    SD .x12 .x15 24
  [ { label := "h_BLOBBASEFEE"
    , opcodes := [0x4a]
    , body := blobBaseFeeBody
    , tail := .advanceAndRet 1 } ]
  ++
  [ { label := "h_BLOBHASH"
    , opcodes := [0x49]
    , body := []
    , tail := .custom <|
        "  ld x14, 8(x12)\n" ++          -- high limbs must be zero
        "  bnez x14, .Lblobhash_zero\n" ++
        "  ld x14, 16(x12)\n" ++
        "  bnez x14, .Lblobhash_zero\n" ++
        "  ld x14, 24(x12)\n" ++
        "  bnez x14, .Lblobhash_zero\n" ++
        "  ld x14, 0(x12)\n" ++          -- x14 = low u64 index
        "  ld x15, 544(x20)\n" ++        -- x15 = copied blob_hash_count
        "  bgeu x14, x15, .Lblobhash_zero\n" ++
        "  slli x14, x14, 5\n" ++        -- 32 bytes per versioned hash
        "  la x15, evm_blob_hashes\n" ++
        "  add x15, x15, x14\n" ++
        "  ld x16, 0(x15)\n" ++
        "  sd x16, 0(x12)\n" ++
        "  ld x16, 8(x15)\n" ++
        "  sd x16, 8(x12)\n" ++
        "  ld x16, 16(x15)\n" ++
        "  sd x16, 16(x12)\n" ++
        "  ld x16, 24(x15)\n" ++
        "  sd x16, 24(x12)\n" ++
        "  addi x10, x10, 1\n" ++
        "  ret\n" ++
        ".Lblobhash_zero:\n" ++
        "  sd x0, 0(x12)\n" ++
        "  sd x0, 8(x12)\n" ++
        "  sd x0, 16(x12)\n" ++
        "  sd x0, 24(x12)\n" ++
        "  addi x10, x10, 1\n" ++
        "  ret" } ]

/-- M29 BLOCKHASH handler backed by the runtime block-history trailer.

    Runtime input supplies:
      - `env + 552`: current block number (`cur`, u64)
      - `env + 560`: number of loaded recent hashes (`count`, clamped to 256)
      - `evm_block_hashes`: `count` 32-byte hashes in increasing block-number
        order, matching execution-specs' `block_env.block_hashes`.

    The handler implements Amsterdam `block_hash` behavior for u64 targets:
      - nonzero high limbs in the target word -> zero
      - target >= cur -> zero
      - cur - target > count -> zero
      - otherwise copy `block_hashes[count - (cur - target)]` into the
        popped stack slot.

    Note: env+512..+543 is occupied by BLOBBASEFEE (M28). -/
def blockHashHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_BLOCKHASH"
    , opcodes := [0x40]
    , body := []
    , tail := .custom <|
        "  ld x14, 8(x12)\n" ++
        "  bnez x14, .Lblockhash_zero\n" ++
        "  ld x14, 16(x12)\n" ++
        "  bnez x14, .Lblockhash_zero\n" ++
        "  ld x14, 24(x12)\n" ++
        "  bnez x14, .Lblockhash_zero\n" ++
        "  ld x14, 0(x12)\n" ++       -- x14 = target block number
        "  ld x15, 552(x20)\n" ++     -- x15 = current block number (env+552)
        "  bgeu x14, x15, .Lblockhash_zero\n" ++
        "  sub x16, x15, x14\n" ++    -- x16 = cur - target, strictly positive
        "  ld x17, 560(x20)\n" ++     -- x17 = loaded hash count (env+560)
        "  bgtu x16, x17, .Lblockhash_zero\n" ++
        "  sub x17, x17, x16\n" ++    -- index = count - age
        "  slli x17, x17, 5\n" ++     -- index × 32
        "  la x18, evm_block_hashes\n" ++
        "  add x18, x18, x17\n" ++
        "  ld x19, 0(x18)\n" ++
        "  sd x19, 0(x12)\n" ++
        "  ld x19, 8(x18)\n" ++
        "  sd x19, 8(x12)\n" ++
        "  ld x19, 16(x18)\n" ++
        "  sd x19, 16(x12)\n" ++
        "  ld x19, 24(x18)\n" ++
        "  sd x19, 24(x12)\n" ++
        "  addi x10, x10, 1\n" ++
        "  ret\n" ++
        ".Lblockhash_zero:\n" ++
        "  sd x0, 0(x12)\n" ++
        "  sd x0, 8(x12)\n" ++
        "  sd x0, 16(x12)\n" ++
        "  sd x0, 24(x12)\n" ++
        "  addi x10, x10, 1\n" ++
        "  ret" } ]

/-- M13 calldata-context opcodes. Sibling to `envHandlers` — reads the
    `callDataLenOff = 424` cell from the same env block that M12
    initialises via `la x20, evm_env`.

    `evm_calldatasize` has the same 6-instruction shape as
    `evm_env_load`: load 8 bytes from `envBaseReg + 424`, decrement
    `x12` by 32, write the low limb and three zero high limbs. The
    M12 env-region size of 416 bytes is too small for offset 424;
    `Dispatch.lean`'s `evm_env:` block is bumped to 512 bytes in this
    PR (covers all `Environment/Layout.lean` fields up to
    `returnDataSizeOff = 440` + 8 with slack).

    The calldata-length cell is zero-initialised by the data section
    (same as the env fields), so `CALLDATASIZE` currently returns 0.
    Non-zero values come from a future host-preload PR.

    **M21 update**: the runtime-bytecode dispatcher's prologue now
    populates `env.callDataPtr` / `env.callDataLen` from the ziskemu
    `-i` input file. CALLDATALOAD (0x35) and CALLDATACOPY (0x37) wired
    here read real calldata bytes. The pre-M21 no-ops for both opcodes
    are removed from `popPushZeroHandlers` / `copyNoopHandlers` in
    `Programs/Noop.lean`. -/
def calldataHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_CALLDATASIZE"
    , opcodes := [0x36]
    , body    := EvmAsm.Evm64.Calldata.evm_calldatasize .x20 .x15
    , tail    := .advanceAndRet 1 }
  , -- M21 real CALLDATALOAD (0x35). The verified body
    -- `evm_calldataload_window` (94 instructions, mirrors `evm_mload`)
    -- handles the in-bounds 32-byte read: pop offset, compute
    -- `cdp + offset`, pack 4 BE u64 limbs via LBU/SLLI/OR, write the
    -- result back to the same EVM stack slot. The `preBody` loads
    -- the calldata pointer from `env.callDataPtrOff = 416` into x14
    -- (the body's `envPtrReg`).
    --
    -- Known limitation: in-bounds only. Reads past `cdp + callDataLen`
    -- yield whatever's in adjacent memory (typically zeros in the
    -- input region's padding, but undefined in general). A future PR
    -- can wrap with a bounds-check / zero-pad outer block. For
    -- trusted test programs that respect bounds, this is correct. -/
    { label   := "h_CALLDATALOAD"
    , opcodes := [0x35]
    , preBody := "  ld x14, 416(x20)\n"
    , body    := EvmAsm.Evm64.Calldata.evm_calldataload_window
                   .x15 .x16 .x17 .x18 .x14
    , tail    := .advanceAndRet 1 }
  , -- M21 real CALLDATACOPY (0x37). The verified body
    -- `evm_calldatacopy` (19 instructions) pops `(destOffset, offset,
    -- size)`, loads `cdp` and `len` from env directly, and runs a
    -- byte loop that copies up to `size` bytes from
    -- `calldata[offset..]` into `memory[destOffset..]`, zero-filling
    -- bytes whose source address falls outside the calldata window.
    -- envBaseReg = x20 (set in dispatcher prologue); memBaseReg = x13
    -- (M7); the remaining 6 args are caller-saved scratch.
    { label   := "h_CALLDATACOPY"
    , opcodes := [0x37]
    , preBody := "  ld x14, 0(x12)\n" ++
                 "  ld x15, 64(x12)\n" ++
                 updateActiveMemorySizeAsm "calldatacopy" "x14" "x15" "x16" "x17" "x18"
    , body    := EvmAsm.Evm64.Calldata.evm_calldatacopy
                   .x20 .x13 .x14 .x15 .x16 .x17 .x18 .x19
    , tail    := .advanceAndRet 1 } ]

/-- EIP-5656 MCOPY for the concrete dispatcher. The handler consumes
    low u64 limbs for `(dest, src, length)`, updates MSIZE for both
    read and write ranges, then performs `memmove`-style byte copying
    so overlapping ranges are handled correctly. Gas charging and
    256-bit overflow/OOG detection are tracked separately. -/
def mcopyHandlers : List OpcodeHandlerSpec :=
  [ { label   := "h_MCOPY"
      opcodes := [0x5e]
      body    := []
      tail    := .custom <|
        "  ld x14, 0(x12)\n" ++          -- destination offset
        "  ld x15, 32(x12)\n" ++         -- source offset
        "  ld x16, 64(x12)\n" ++         -- length
        "  addi x12, x12, 96\n" ++
        "  beqz x16, .Lmcopy_done\n" ++
        updateActiveMemorySizeAsm "mcopy_src" "x15" "x16" "x17" "x18" "x19" ++
        updateActiveMemorySizeAsm "mcopy_dst" "x14" "x16" "x17" "x18" "x19" ++
        "  add x17, x13, x14\n" ++       -- destination pointer
        "  add x18, x13, x15\n" ++       -- source pointer
        "  add x19, x15, x16\n" ++       -- source end offset
        "  bleu x14, x15, .Lmcopy_forward\n" ++
        "  bgeu x14, x19, .Lmcopy_forward\n" ++
        "  add x17, x17, x16\n" ++
        "  add x18, x18, x16\n" ++
        ".Lmcopy_backward_loop:\n" ++
        "  beqz x16, .Lmcopy_done\n" ++
        "  addi x17, x17, -1\n" ++
        "  addi x18, x18, -1\n" ++
        "  lbu x19, 0(x18)\n" ++
        "  sb x19, 0(x17)\n" ++
        "  addi x16, x16, -1\n" ++
        "  j .Lmcopy_backward_loop\n" ++
        ".Lmcopy_forward:\n" ++
        "  beqz x16, .Lmcopy_done\n" ++
        "  lbu x19, 0(x18)\n" ++
        "  sb x19, 0(x17)\n" ++
        "  addi x18, x18, 1\n" ++
        "  addi x17, x17, 1\n" ++
        "  addi x16, x16, -1\n" ++
        "  j .Lmcopy_forward\n" ++
        ".Lmcopy_done:\n" ++
        "  addi x10, x10, 1\n" ++
        "  ret" } ]

/-- Shared tail for JUMP / JUMPI: the verified body left `code[dest]`
    (or the `0x5b` sentinel for a not-taken JUMPI) in `x17`. If it
    isn't a JUMPDEST byte, route to `.exit_invalid` (M15.5 exceptional
    halt); otherwise `ret` to the dispatch loop, which re-reads the
    (now-validated) target byte. `x18` is a free scratch temp. -/
private def jumpValidityTail : HandlerTail :=
  .custom ("  li x18, 0x5b\n" ++
           "  bne x17, x18, .exit_invalid\n" ++
           "  ret")

/-- M14 / M15 control-flow opcodes.

    - **JUMPDEST (0x5b, M14)** — no-op marker. Empty body +
      `.advanceAndRet 1` tail.
    - **JUMP (0x56, M15)** — pops dest, writes `x10 := x21 + dest`.
      Tail is `.custom "  ret"`; the body has already written `x10`,
      so the dispatcher's next loop iteration reads the jump-target
      byte. No `.advanceAndRet` (would over-advance by 1).
    - **JUMPI (0x57, M15)** — pops dest + cond; if cond ≠ 0 writes
      `x10 := x21 + dest`, else advances `x10` by 1 in the body.
      Tail is `.custom "  ret"` — body handles both branches.
    - **PC (0x58, M15)** — pushes `x10 - x21` as a 256-bit word
      with the value in the low limb. Tail is `.advanceAndRet 1`.

    All three M15 handlers consume the dispatcher's preserved
    code-base register `x21` (set in the prologue via
    `la x21, evm_code` / `li x21, 0x40000010`). The scratch
    registers `x14`/`x15`/`x16` are caller-saved per the existing
    convention.

    **M15.5 JUMPDEST-validity (Level 1)**: JUMP / JUMPI now load
    `code[dest]` into `x17` (the verified bodies do this; JUMPI's
    not-taken path writes the sentinel `0x5b`). `jumpValidityTail`
    compares `x17` to `0x5b` and routes a mismatch to the
    dispatcher's `.exit_invalid` (exceptional halt, `halt_kind = 4`).
    Level 2 (pushdata-aware bitmap) is still future work — see the
    `ControlFlow/Program.lean` docstring. -/
def controlFlowHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_JUMPDEST"
    , opcodes := [0x5b]
    , body    := []
    , tail    := .advanceAndRet 1 }
  , { label := "h_JUMP"
    , opcodes := [0x56]
    , body    := EvmAsm.Evm64.ControlFlow.evm_jump .x21 .x14 .x17
    , tail    := jumpValidityTail }
  , { label := "h_JUMPI"
    , opcodes := [0x57]
    , body    := EvmAsm.Evm64.ControlFlow.evm_jumpi .x21 .x14 .x15 .x16 .x17
    , tail    := jumpValidityTail }
  , { label := "h_PC"
    , opcodes := [0x58]
    , body    := EvmAsm.Evm64.ControlFlow.evm_pc .x21 .x14
    , tail    := .advanceAndRet 1 } ]

/-- M16 hash / precompile-via-syscall opcodes. KECCAK256 (0x20) is the
    first ECALL-bridge opcode wired into the dispatcher.

    The handler does NOT have a verified body (`Instr` has no CSRS
    variant; the Zisk `csrs 0x800, a0` accelerator is encoded as a
    raw `.4byte 0x80052073` inside the `zkvm_keccak256` subroutine).
    Like `stopHandler` and the M15 JUMP/JUMPI handlers, this uses
    `body := []` + `tail := .custom "..."` with the full asm inline.

    **Calling convention.** The handler must navigate the conflict
    between LP64 (a0/a1/a2 = x10/x11/x12) and the dispatcher's
    preserved state (x10 = EVM code ptr, x12 = EVM stack ptr).
    Solution: save `x10` to `s10` and `x12` to `s11` (callee-saved
    in LP64, preserved across the keccak call), set up a0/a1/a2 as
    keccak args, then restore after the call.

    **Stack delta**: pop 2 words (offset + size, 64 B) and push 1
    word (32-byte digest). Net x12 advance = +32 (one word).

    **Tail return mechanism**: `j .dispatch_loop` (NOT `ret`),
    because the `jal x1, zkvm_keccak256` clobbers `x1`. Same fix as
    M9's `signedDivModTail`.

    **Endianness**: the keccak subroutine writes the 32-byte digest
    to `a2` in standard byte order (`digest[0]` first). The
    dispatcher's epilogue (e.g. `evmAddEpilogue`) copies x12+0..x12+31
    verbatim to OUTPUT_ADDR. So `expectedOutHex` in test cases is
    the standard keccak digest hex.

    M17+ will extend `hashHandlers` with LOG0-4 / SLOAD / SSTORE /
    other precompiles via the same ECALL bridge pattern. -/
def hashHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_KECCAK256"
    , opcodes := [0x20]
    , body    := []
    , tail    := .custom (
        "  mv s10, x10\n" ++           -- save EVM code ptr
        "  ld t0, 0(x12)\n" ++          -- t0 = offset_low (low 64 bits of top word)
        "  ld a1, 32(x12)\n" ++         -- a1 = size_low
        "  addi x12, x12, 32\n" ++      -- net stack delta: pop 2 (64), push 1 (-32) = +32
        "  add a0, x13, t0\n" ++        -- a0 = evm_memory + offset (input ptr)
        "  mv a2, x12\n" ++             -- a2 = result slot (= new EVM stack top)
        "  mv s11, x12\n" ++            -- save EVM stack ptr across the call
        "  jal x1, zkvm_keccak256\n" ++ -- call keccak (clobbers x1, a0, a1, a2)
        "  mv x10, s10\n" ++            -- restore EVM code ptr
        "  mv x12, s11\n" ++            -- restore EVM stack ptr
        "  addi x10, x10, 1\n" ++       -- advance PC by 1
        "  j .dispatch_loop") } ]

/-- Copy `topicCount` stack words into an event-log descriptor.
    Descriptor topics live at entry offsets 32, 64, 96, and 128. -/
def logTopicCopies (topicCount : Nat) : String :=
  String.intercalate "" <|
    (List.range topicCount).map fun i =>
      let stackOff := 64 + i * 32
      let entryOff := 32 + i * 32
      "  ld x21, " ++ toString stackOff ++ "(x12)\n" ++
      "  sd x21, " ++ toString entryOff ++ "(x14)\n" ++
      "  ld x21, " ++ toString (stackOff + 8) ++ "(x12)\n" ++
      "  sd x21, " ++ toString (entryOff + 8) ++ "(x14)\n" ++
      "  ld x21, " ++ toString (stackOff + 16) ++ "(x12)\n" ++
      "  sd x21, " ++ toString (entryOff + 16) ++ "(x14)\n" ++
      "  ld x21, " ++ toString (stackOff + 24) ++ "(x12)\n" ++
      "  sd x21, " ++ toString (entryOff + 24) ++ "(x14)\n"

/-- M26 LOG capture prefix. Appends a bounded 256-byte descriptor:
      +0  topic count (u64)
      +8  memory offset low u64
      +16 memory size low u64
      +24 copied data length (min(size, 32))
      +32..160 four 32-byte topic slots
      +160..192 first up to 32 data bytes
      +192..224 ADDRESS context word
      +224..256 CALLER context word

    The descriptor uses the dispatcher's current stack-word byte order
    (low limb first). A full receipt encoder can canonicalize to the
    Ethereum byte order later. Overflow writes halt_kind = 4 and exits
    via `.exit_no_epilogue` instead of silently dropping the event. -/
def logCapturePreBody (topicCount : Nat) : String :=
  "  ld x15, 472(x20)\n" ++          -- x15 = event log length
  "  li x16, 16\n" ++                -- static cap: 16 descriptors
  "  bgeu x15, x16, 9f\n" ++
  "  la x14, evm_event_logs\n" ++
  "  slli x16, x15, 8\n" ++          -- entry offset = count * 256
  "  add x14, x14, x16\n" ++         -- x14 = descriptor pointer
  -- Zero the full descriptor before filling the fields/topics/data prefix.
  "  mv x16, x14\n" ++
  "  li x17, 32\n" ++
  "1:\n" ++
  "  sd x0, 0(x16)\n" ++
  "  addi x16, x16, 8\n" ++
  "  addi x17, x17, -1\n" ++
  "  bnez x17, 1b\n" ++
  "  li x16, " ++ toString topicCount ++ "\n" ++
  "  sd x16, 0(x14)\n" ++
  "  ld x17, 0(x12)\n" ++            -- memory offset low u64
  "  ld x18, 32(x12)\n" ++           -- memory size low u64
  "  sd x17, 8(x14)\n" ++
  "  sd x18, 16(x14)\n" ++
  logTopicCopies topicCount ++
  -- Capture the local address and caller context from the env block.
  "  ld x21, 0(x20)\n" ++
  "  sd x21, 192(x14)\n" ++
  "  ld x21, 8(x20)\n" ++
  "  sd x21, 200(x14)\n" ++
  "  ld x21, 16(x20)\n" ++
  "  sd x21, 208(x14)\n" ++
  "  ld x21, 24(x20)\n" ++
  "  sd x21, 216(x14)\n" ++
  "  ld x21, 64(x20)\n" ++
  "  sd x21, 224(x14)\n" ++
  "  ld x21, 72(x20)\n" ++
  "  sd x21, 232(x14)\n" ++
  "  ld x21, 80(x20)\n" ++
  "  sd x21, 240(x14)\n" ++
  "  ld x21, 88(x20)\n" ++
  "  sd x21, 248(x14)\n" ++
  "  li x19, 32\n" ++
  "  bgeu x19, x18, 2f\n" ++
  "  mv x18, x19\n" ++
  "2:\n" ++
  "  sd x18, 24(x14)\n" ++
  "  add x22, x13, x17\n" ++         -- source = evm_memory + offset
  "  addi x23, x14, 160\n" ++        -- data-prefix destination
  "3:\n" ++
  "  beqz x18, 4f\n" ++
  "  lbu x24, 0(x22)\n" ++
  "  sb x24, 0(x23)\n" ++
  "  addi x22, x22, 1\n" ++
  "  addi x23, x23, 1\n" ++
  "  addi x18, x18, -1\n" ++
  "  j 3b\n" ++
  "4:\n" ++
  "  addi x15, x15, 1\n" ++
  "  sd x15, 472(x20)\n" ++
  "  j 8f\n" ++
  "9:\n" ++
  "  li x16, 0xa0010000\n" ++
  "  li x17, 4\n" ++                 -- LOG buffer overflow
  "  sd x17, 32(x16)\n" ++
  "  j .exit_no_epilogue\n" ++
  "8:\n"

/-- M26 LOG opcodes (LOG0..LOG4). Each handler captures a bounded
    event descriptor, pops `(2 + n)` EVM words, advances PC by one
    byte, and returns to the dispatcher. -/
def logHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_LOG0", opcodes := [0xa0]
    , preBody := logCapturePreBody 0
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 64)
    , tail := .advanceAndRet 1 }
  , { label := "h_LOG1", opcodes := [0xa1]
    , preBody := logCapturePreBody 1
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 96)
    , tail := .advanceAndRet 1 }
  , { label := "h_LOG2", opcodes := [0xa2]
    , preBody := logCapturePreBody 2
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 128)
    , tail := .advanceAndRet 1 }
  , { label := "h_LOG3", opcodes := [0xa3]
    , preBody := logCapturePreBody 3
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 160)
    , tail := .advanceAndRet 1 }
  , { label := "h_LOG4", opcodes := [0xa4]
    , preBody := logCapturePreBody 4
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 192)
    , tail := .advanceAndRet 1 } ]


/-! ## Runtime account-witness opcodes

    EXTCODEHASH (0x3f) now reads the account trie through the optional
    runtime account-witness context populated by `pack-bytecode.py` and
    `emitRuntimeDispatcherSetup`. If no witness context is present, it keeps
    the old deterministic zero behavior. -/

/-- Copy an EVM stack address word into natural 20-byte address order.

    Stack bytes 0..19 hold the low 160-bit address little-endian; trie lookup
    helpers expect the big-endian byte string whose keccak selects the account
    path. `x12` is the EVM stack pointer and `t1` points at
    `eahsr_address_scratch`. -/
private def extcodehashWitnessAddressCopy : String :=
  String.intercalate "" <|
    (List.range 20).map fun i =>
      s!"  lbu t2, {19 - i}(x12)\n  sb t2, {i}(t1)\n"

/-- Raw dispatcher handler for EXTCODEHASH backed by
    `extcodehash_at_header_state_root`.

    The EVM stack word stores the low 160-bit address little-endian; the
    helper expects the natural 20-byte address order used for
    `keccak(address)`, so the handler first reverses bytes 0..19 into
    `eahsr_address_scratch`. Net stack delta is zero: the address word is
    overwritten with the 32-byte EIP-1052 result. -/
private def extcodehashWitnessTail : HandlerTail :=
  .custom <|
    "  ld t0, 584(x20)\n" ++          -- header length; zero means no witness context
    "  beqz t0, .Lextcodehash_no_context\n" ++
    "  la t1, eahsr_address_scratch\n" ++
    extcodehashWitnessAddressCopy ++
    "  addi sp, sp, -32\n" ++
    "  sd x10, 0(sp)\n" ++
    "  sd x12, 8(sp)\n" ++
    "  ld a0, 576(x20)\n" ++         -- header ptr
    "  ld a1, 584(x20)\n" ++         -- header len
    "  la a2, eahsr_address_scratch\n" ++
    "  ld a3, 592(x20)\n" ++         -- witness.state ptr
    "  ld a4, 600(x20)\n" ++         -- witness.state len
    "  ld a5, 8(sp)\n" ++            -- saved EVM stack ptr; a2 aliases x12
    "  jal ra, extcodehash_at_header_state_root\n" ++
    "  ld x10, 0(sp)\n" ++
    "  ld x12, 8(sp)\n" ++
    "  addi sp, sp, 32\n" ++
    "  addi x10, x10, 1\n" ++
    "  j .dispatch_loop\n" ++
    ".Lextcodehash_no_context:\n" ++
    "  sd zero, 0(x12)\n" ++
    "  sd zero, 8(x12)\n" ++
    "  sd zero, 16(x12)\n" ++
    "  sd zero, 24(x12)\n" ++
    "  addi x10, x10, 1\n" ++
    "  j .dispatch_loop"

def accountWitnessHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_EXTCODEHASH"
    , opcodes := [0x3f]
    , body := []
    , tail := extcodehashWitnessTail } ]

-- M17 / M22 storage handlers (SLOAD, SSTORE, TLOAD, TSTORE) live in
-- `EvmAsm/Codegen/Programs/Storage.lean` — extracted at M22 (when
-- the inline-asm scan loops pushed this file past the per-file size
-- cap) following the same pattern as `Programs/Noop.lean` (M18).
-- The `storageHandlers` builder is brought into scope by the
-- `import EvmAsm.Codegen.Programs.Storage` near the top of this file.

-- M18 stack-pop / push-zero / halt no-op handlers (haltHandlers,
-- pushZeroHandlers, popPushZeroHandlers, copyNoopHandlers) live in
-- `EvmAsm/Codegen/Programs/Noop.lean` — extracted to respect the
-- file-size guard at the bottom of `Programs.lean`. They're brought
-- into scope here by the `import EvmAsm.Codegen.Programs.Noop`
-- statement near the top of this file.

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

    EXP (0x0a) now rides the same self-calling pattern via
    `evmExpComposed` below, using the `_fixed_fixed` body variant.
    The earlier deferral note was that `mul_callable` clobbers `x6`
    (the EXP loop's per-limb counter) — the `_fixed` variant only
    moved the `x19` cursor to a callee-saved register, leaving the
    `x6` counter to be corrupted mid-iteration. `_fixed_fixed`
    (`EvmAsm/Evm64/Exp/Program.lean`) moves the counter to `x22`
    (s6, callee-saved, untouched by `evm_mul`/`cc_ret`), so EXP now
    runs correctly through the dispatcher. (The limb pointer `x16`
    was never the problem — `evm_mul` doesn't touch it.) -/

/-- Runtime ADDMOD handler body for the dispatcher.

    The proof-facing `evm_addmod` skeleton still only reduces the truncated
    low 256-bit sum. The dispatcher needs total EVM behavior now, so this
    raw handler uses assembler labels for the internal calls and handles the
    carry-out path empirically:

      * if `N = 0`, write zero and advance by one stack word;
      * if the ADD carry is zero, reduce the truncated sum with MOD;
      * if the ADD carry is one, compute `m = 2^256 mod N`, reduce the
        truncated sum first, add `m`, then perform the single conditional
        subtract required because both addends are already `< N`.

    The carry helper uses `x12 + 224` / `x12 + 256` as its callable MOD work
    window so DivMod's negative scratch offsets do not overlap the live
    truncated sum or modulus. This wrapper exists only to avoid brittle
    hand-counted JAL offsets in the runtime dispatcher while the verified
    top-level ADDMOD assembly catches up. -/
private def evmAddmodRuntimeTail : HandlerTail :=
  .custom <| String.intercalate "\n" [
    emitProgram EvmAsm.Evm64.evm_addmod_prologue,
    emitProgram EvmAsm.Evm64.evm_addmod_phase1_carry,
    "  ld x6, 32(x12)\n  ld x5, 40(x12)\n  or x6, x6, x5\n  ld x5, 48(x12)\n  or x6, x6, x5\n  ld x5, 56(x12)\n  or x6, x6, x5\n  beq x6, x0, .Laddmod_zero\n  beq x7, x0, .Laddmod_no_carry\n  addi x5, x0, -1\n  sd x5, 224(x12)\n  sd x5, 232(x12)\n  sd x5, 240(x12)\n  sd x5, 248(x12)\n  ld x5, 32(x12)\n  sd x5, 256(x12)\n  ld x5, 40(x12)\n  sd x5, 264(x12)\n  ld x5, 48(x12)\n  sd x5, 272(x12)\n  ld x5, 56(x12)\n  sd x5, 280(x12)\n  addi x12, x12, 224\n  jal x1, .Laddmod_mod_callable\n  addi x12, x12, -256\n  ld x5, 256(x12)\n  addi x6, x5, 1\n  sltiu x7, x6, 1\n  sd x6, 224(x12)\n  ld x5, 264(x12)\n  add x6, x5, x7\n  sltu x7, x6, x7\n  sd x6, 232(x12)\n  ld x5, 272(x12)\n  add x6, x5, x7\n  sltu x7, x6, x7\n  sd x6, 240(x12)\n  ld x5, 280(x12)\n  add x6, x5, x7\n  sltu x7, x6, x7\n  sd x6, 248(x12)\n  ld x5, 32(x12)\n  sd x5, 256(x12)\n  ld x5, 40(x12)\n  sd x5, 264(x12)\n  ld x5, 48(x12)\n  sd x5, 272(x12)\n  ld x5, 56(x12)\n  sd x5, 280(x12)\n  addi x12, x12, 224\n  jal x1, .Laddmod_mod_callable\n  addi x12, x12, -256\n  ld x5, 32(x12)\n  sd x5, 64(x12)\n  ld x5, 40(x12)\n  sd x5, 72(x12)\n  ld x5, 48(x12)\n  sd x5, 80(x12)\n  ld x5, 56(x12)\n  sd x5, 88(x12)\n  jal x1, .Laddmod_mod_callable\n  addi x12, x12, -32\n  ld x5, 32(x12)\n  sd x5, 0(x12)\n  ld x5, 40(x12)\n  sd x5, 8(x12)\n  ld x5, 48(x12)\n  sd x5, 16(x12)\n  ld x5, 56(x12)\n  sd x5, 24(x12)\n  ld x5, 256(x12)\n  sd x5, 32(x12)\n  ld x5, 264(x12)\n  sd x5, 40(x12)\n  ld x5, 272(x12)\n  sd x5, 48(x12)\n  ld x5, 280(x12)\n  sd x5, 56(x12)",
    emitProgram EvmAsm.Evm64.evm_add,
    "  bne x5, x0, .Laddmod_sub_n\n  ld x6, 24(x12)\n  ld x7, 56(x12)\n  bltu x7, x6, .Laddmod_sub_n\n  bltu x6, x7, .Laddmod_done\n  ld x6, 16(x12)\n  ld x7, 48(x12)\n  bltu x7, x6, .Laddmod_sub_n\n  bltu x6, x7, .Laddmod_done\n  ld x6, 8(x12)\n  ld x7, 40(x12)\n  bltu x7, x6, .Laddmod_sub_n\n  bltu x6, x7, .Laddmod_done\n  ld x6, 0(x12)\n  ld x7, 32(x12)\n  bltu x6, x7, .Laddmod_done\n.Laddmod_sub_n:\n  ld x6, 0(x12)\n  ld x7, 32(x12)\n  sub x5, x6, x7\n  sltu x11, x6, x7\n  sd x5, 0(x12)\n  ld x6, 8(x12)\n  ld x7, 40(x12)\n  sub x5, x6, x7\n  sltu x10, x6, x7\n  sub x5, x5, x11\n  sltu x11, x5, x11\n  or x11, x10, x11\n  sd x5, 8(x12)\n  ld x6, 16(x12)\n  ld x7, 48(x12)\n  sub x5, x6, x7\n  sltu x10, x6, x7\n  sub x5, x5, x11\n  sltu x11, x5, x11\n  or x11, x10, x11\n  sd x5, 16(x12)\n  ld x6, 24(x12)\n  ld x7, 56(x12)\n  sub x5, x6, x7\n  sub x5, x5, x11\n  sd x5, 24(x12)\n  j .Laddmod_done\n.Laddmod_no_carry:\n  jal x1, .Laddmod_mod_callable\n  j .Laddmod_done\n.Laddmod_zero:",
    emitProgram EvmAsm.Evm64.evm_addmod_phase2_zero_path,
    emitProgram EvmAsm.Evm64.evm_addmod_epilogue,
    ".Laddmod_done:\n  mv x10, x14\n  addi x10, x10, 1\n  j .dispatch_loop\n.Laddmod_mod_callable:",
    emitProgram EvmAsm.Evm64.evm_mod_callable_v4]

/-- Runtime ADDMOD handler assembly. Supports the no-carry lane by reusing
    `evmAddmodComposed`'s snippets, but rejects carry-out sums explicitly.
    The full ADDMOD semantics need 257-bit reduction `(c * 2^256 + r) mod N`;
    until that lands, `x7 != 0` is an unsupported development halt
    (`halt_kind = 3`) rather than a false successful low-256-bit result. -/
private def addmodRuntimeAsm : String :=
  "  mv x14, x10\n" ++
  emitProgram EvmAsm.Evm64.evm_addmod_prologue ++ "\n" ++
  emitProgram EvmAsm.Evm64.evm_addmod_phase1_carry ++ "\n" ++
  "  bnez x7, .exit_invalid_op\n" ++
  emitProgram (EvmAsm.Evm64.evm_addmod_phase2_reduce 8) ++ "\n" ++
  emitProgram (single (Instr.JAL .x0 (1376 : BitVec 21))) ++ "\n" ++
  emitProgram EvmAsm.Evm64.evm_mod_callable_v4 ++ "\n" ++
  "  mv x10, x14\n" ++
  "  addi x10, x10, 1\n" ++
  "  j .dispatch_loop"

/-- EXP (0x0a) handler body: the double-fixed verified EXP body inlined
    with `mul_callable`, mirroring `evmAddmodComposed`.

    Composition:
      - `evm_exp_..._fixed_fixed_canonical 200 92`: 84 instr (336 B). The
        two interior `JAL .x1` MUL-call sites target `mul_callable`.
      - skip-JAL `JAL .x0 +260`: 1 instr (4 B) at byte 336 — jumps past
        the inlined callable to the handler tail (260 = 4 + 256).
      - `mul_callable`: 64 instr (256 B) at byte 340.

    **MUL-call offsets shift +4 vs the standalone `evm_exp_from_input`.**
    There, `mul_callable` sits immediately after the body (byte 336), so
    the canonical offsets are 196 / 88. Here the 4-byte skip-JAL pushes
    `mul_callable` to byte 340, so the squaring / cond-multiply JAL sites
    (at body bytes 140 / 248) need offsets `340-140 = 200` and
    `340-248 = 92`. The internal branch offsets (cond-mul skip BEQ,
    loop-back BNE) are unaffected — they stay inside the 336-byte body
    and use the canonical `_fixed` values.

    The skip-JAL is required because EXP's loop exits by *falling through*
    `exp_epilogue` (which has no trailing jump); without it, control would
    run straight into `mul_callable`. ADDMOD doesn't need this shape
    because its single MUL call is the last thing before the callable.

    Net `x12` advance: `exp_epilogue` does one `ADDI x12, x12, 32` (pops 2,
    pushes 1); the per-iteration call marshal/un-marshal nets zero. -/
def evmExpComposed : Program :=
  EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_fixed_canonical
    (200 : BitVec 21) (92 : BitVec 21) ;;
  single (Instr.JAL .x0 (260 : BitVec 21)) ;;
  EvmAsm.Evm64.mul_callable

/-- Tail for EXP (0x0a): like `signedDivModTail` (the inner `JAL .x1` into
    `mul_callable` clobbers `x1`, so `ret` would jump to garbage → use
    `j .dispatch_loop`), plus a `la sp, lp64_sp_top` to restore the LP64
    stack pointer that h_EXP's `preBody` repointed at `exp_scratch` for the
    EXP body's result accumulator. -/
private def expTail : HandlerTail :=
  .custom ("  mv x10, x14\n" ++
           "  la sp, lp64_sp_top\n" ++
           "  addi x10, x10, 1\n" ++
           "  j .dispatch_loop")

/-- M10 self-calling handlers. Currently just ADDMOD; EXP is
    deferred (see the milestone-header comment). Reuses
    `signedDivModTail` because the wrapper's inner `JAL .x1` into
    the inline callable clobbers `x1`, so the standard `ret` (=
    `jalr x0, x1, 0`) would jump to garbage. -/
def selfCallingHandlers : List OpcodeHandlerSpec :=
  [ { label         := "h_ADDMOD"
      opcodes       := [0x08]
      preBody       := "  mv x14, x10"
      body          := []
      tail          := evmAddmodRuntimeTail }
  , { label         := "h_EXP"
      opcodes       := [0x0a]
      preBody       := "  mv x14, x10\n  la x2, exp_scratch"
      body          := evmExpComposed
      tail          := expTail } ]

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
  memoryHandlers ++ memoryMetadataHandlers ++ gasHandlers ++ envHandlers ++
  blobContextHandlers ++ blockHashHandlers ++ calldataHandlers ++
  controlFlowHandlers ++ hashHandlers ++ logHandlers ++
  accountWitnessHandlers ++ storageHandlers ++ mcopyHandlers ++ haltHandlers ++ pushZeroHandlers ++
  popPushZeroHandlers ++ copyNoopHandlers ++ childFrameHandlers ++
  arithNoopHandlers ++ divModHandlers ++ signedDivModHandlers ++
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


end EvmAsm.Codegen
