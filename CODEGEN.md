# Codegen

Roadmap for emitting executable RISC-V from the verified `Program`s in this
repo and running them on the Zisk emulator (`ziskemu`). Companion to
[`PLAN.md`](PLAN.md) (the verification roadmap) and the host-I/O ADR at
[`docs/zkvm-host-io-interface.md`](docs/zkvm-host-io-interface.md).

## Locked decisions

1. **Text emitter first.** Emit a `.s` file, assemble & link with
   `riscv64-unknown-elf-as -march=rv64imac` and
   `riscv64-unknown-elf-ld -Ttext=0x80000000`, run on `ziskemu`. A Lean-native
   binary encoder (`Instr → BitVec 32` + ELF writer) is *future work*, not
   blocking; see the Zisk
   [`elf-regressions`](https://github.com/0xPolygonHermez/zisk/tree/9537bcebe414f3a2a2cbf809b3d1cd09ac1e1b68/elf-regressions)
   examples for the target shape.
2. **First smoke target.** A synthetic
   `LI a0, 42 ;; LI a1, 58 ;; ADD a2, a0, a1 ;; <halt>` — pure toolchain
   validation before touching EVM-specific memory layout. Mirrors Zisk's
   [`simple_add/test.s`](https://github.com/0xPolygonHermez/zisk/blob/pre-develop-0.17.1/elf-regressions/simple_add/test.s).
3. **Tool home: `lake exe codegen`.** A new Lean executable target declared in
   `lakefile.toml` and rooted at the existing `Main.lean`. Source of truth is
   the verified `Instr` type at `EvmAsm/Rv64/Basic.lean:113-237`.
4. **Halt convention is parametric**: `--halt={sp1,linux93}`.
   - `sp1` = `ECALL` with `t0 = 0` — matches the verified `step_ecall_halt` at
     `EvmAsm/Rv64/Execution.lean:611-615`.
   - `linux93` = `ECALL` with `a7 = 93` — matches Zisk's `simple_add`.
   - This sidesteps the still-Open
     [`docs/host-io-halt-convention.md`](docs/host-io-halt-convention.md) ADR.

## File layout

New code lives under a fresh `EvmAsm/Codegen/` tree so the verified core is
untouched. Generated artifacts go in `gen-out/` (gitignored).

| Path | Purpose |
|---|---|
| `EvmAsm/Codegen.lean` | Top-level umbrella (mirrors `EvmAsm/Rv64.lean`, `EvmAsm/Evm64.lean`). |
| `EvmAsm/Codegen/Emit.lean` | Pure `emitReg`, `emitInstr`, `emitProgram` — `Instr → String`. No `IO`. |
| `EvmAsm/Codegen/Layout.lean` | `HaltConv` enum, halt stubs, `_start` preamble, `.option norvc`, `MEM_START`/`MEM_END` constants, `BuildUnit` struct + `emitBuildUnit`/`emitDataLabel` helpers. |
| `EvmAsm/Codegen/Dispatch.lean` | M5b dispatcher scaffolding: `OpcodeHandlerSpec` (optional `preBody` for x10-clobbering handlers + optional `postBodyLabel` for M9's trampoline pattern) + `HandlerTail` types, `emitDispatcherPrologue`/`Epilogue`/`DataSection` and `buildDispatchUnit` helpers. M8.5 adds the parallel runtime-bytecode helpers (`emitRuntimeDispatcherPrologue` / `emitRuntimeDispatcherDataSection` / `buildRuntimeDispatchUnit`) that read bytecode from `INPUT_ADDR + INPUT_DATA_OFFSET` at runtime. Pure (no IO). |
| `EvmAsm/Codegen/Programs.lean` | `BuildUnit` lookup hub: `lookupProgram`, `knownProgramNames`, plus the `statelessGuestUnit` build target. Imports every `BuildUnit` defined under `Programs/`. The actual M5b opcode-handler registry (`tinyInterpRegistry`) and the `BuildUnit`s for `evm_add` / `evm_div` / `evm_mod` / `input_echo` / `runtime_dispatcher` / `tiny_interp_*` now live in `Programs/Evm.lean` (see next row). |
| `EvmAsm/Codegen/Programs/` | Execution-layer programs supporting the Stateless guest (40+ files): Account / Block / Chain / Header / Mpt / Tx / Receipt / Bloom / RLP read / SSZ / U256 / etc. Plus `Programs/Evm.lean` — the M5b opcode handler registry **`tinyInterpRegistry`** at `Programs/Evm.lean:666`, composed from `pushHandlers` (PUSH0..32), `dupHandlers` (DUP1..16), `swapHandlers` (SWAP1..16), `singletonHandlers` (19 fixed-shape opcodes incl. SHL/SAR from M11), `memoryHandlers` (MLOAD/MSTORE/MSTORE8, M7), `envHandlers` (13 simple environment opcodes ADDRESS/CALLER/.../BASEFEE, M12), `calldataHandlers` (CALLDATASIZE, M13), `controlFlowHandlers` (JUMPDEST from M14; JUMP/JUMPI/PC added in M15), `divModHandlers` (DIV/MOD, M8), `signedDivModHandlers` (SDIV/SMOD via trampoline, M9), `selfCallingHandlers` (ADDMOD via inline-callable, M10), and `stopHandler`. Total: **111 wired opcodes**. Also hosts shared helpers (`advancePc`, `copy64`, `evmAddEpilogue`, `evmDivPatched`/`evmModPatched`/`evmSdivPatched`/`evmSmodPatched` for the DIV/MOD/SDIV/SMOD NOP-splice). |
| `EvmAsm/Codegen/Proofs/` | Codegen-proofs scaffolding (post-M10). `RegistryInvariants.lean` (Phase 1) — 6 `decide`-checked theorems about `tinyInterpRegistry`'s structural well-formedness (Nodup on opcodes/labels, byte bounds, jump-table coverage). `HandlerSpecs.lean` (Phase 4) — reusable `cleanRetHandlerSpec` template + **13 concrete handler-level `cpsTripleWithin` instances** for clean-shape singletons (ADD, POP, SUB, LT, GT, SLT, SGT, EQ, ISZERO, AND, OR, XOR, NOT). Phases 2, 3, 5 + the remaining Phase 4 instances are still future work. |
| `EvmAsm/Codegen/Tests/Cases.lean` | Per-opcode regression test registry: `OpcodeTestCase` struct + `opcodeTestCases` list (**44 cases** as of M15). Wraps each bytecode through the M5b dispatcher for end-to-end ziskemu validation. |
| `EvmAsm/Codegen/Cli.lean` | Argument parsing (`--program`, `--test-case`, `--list-test-cases`, `--halt`, `--out`, `--asm-only`). |
| `EvmAsm/Codegen/Driver.lean` | `IO`: shells out to `as`/`ld` if available; `--asm-only` for CI without the cross toolchain. |
| `Main.lean` | Already exists as `import EvmAsm`; extend to call `EvmAsm.Codegen.Cli.main`. |
| `lakefile.toml` | Add `[[lean_exe]] name = "codegen"; root = "Main"; supportInterpreter = true`. |
| `scripts/codegen-*.sh` | Per-milestone round-trip checks: `codegen-smoke.sh` (M0), `codegen-evm_add-check.sh` (M2), `codegen-evm_add-from-input-check.sh` (M4), `codegen-tiny-interp-check.sh` (M5a), `codegen-tiny-interp-dispatch-check.sh` (M5b), `codegen-opcodes-check.sh` (M6a legacy per-case-ELF runner), `codegen-opcodes-runtime-check.sh` (M8.5 **canonical** runtime-bytecode runner, ~3× faster), `codegen-evm_div-check.sh` / `codegen-evm_div-cases-check.sh` / `codegen-evm_mod-check.sh` / `codegen-evm_mod-cases-check.sh` (standalone DIV/MOD wrappers — also routed through the dispatcher in M8). |
| `scripts/pack-bytecode.py` | Helper used by `codegen-opcodes-runtime-check.sh`: parses a comma-separated `0xNN` byte list and emits `<8-byte LE length><bytes><zero pad to multiple-of-8>` (ziskemu input file format). |
| `gen-out/` | Generated `.s`/`.elf`/`.input`; gitignored. |

## Milestones

### M0 — Synthetic smoke (S)

Emit `.s` for `smoke : Program := LI .x10 42 ;; LI .x11 58 ;; ADD .x12 .x10 .x11`,
assemble, link, run on `ziskemu`.

- Implement `emitInstr` for *only* the constructors needed by the smoke (`LI`,
  `ADD`, `ECALL`) plus the halt stubs.
- Wrapper:
  ```asm
  .option norvc
  .section .text
  .globl _start
  _start:
  <body>
  <halt stub>
  ```
  - Halt stub (sp1):    `li t0, 0` ; `ecall`
  - Halt stub (linux93): `li a7, 93` ; `li a0, 0` ; `ecall`
- Driver: `as -march=rv64imac -mno-relax`,
  `ld -Ttext=0x80000000 -nostdlib --no-relax`.

**Exit criteria.**
`lake exe codegen --program smoke --halt linux93 -o gen-out/smoke` produces
`gen-out/smoke.elf`; `ziskemu -e gen-out/smoke.elf` exits 0. Direct
verification that `a2 = 100` is deferred to M2 when `write_output` is wired
— for M0 we only validate that the toolchain (emitter → `as` → `ld` →
`ziskemu`) round-trips and that the halt convention works.

**Status (2026-05-18, resolved).** Toolchain validated end-to-end on
macOS 26 with Homebrew `riscv64-elf-binutils` and ZisK v0.18.0. The
SP1-vs-`ziskemu` halt experiment §Tricky bits #5 below is answered:
**`ziskemu` honors `linux93` (`ecall` + `a7 = 93`) and ignores `sp1`
(`ecall` + `t0 = 0`)**. `--halt linux93` is therefore the default for
generated ELFs; `--halt sp1` remains correct against the verified `step`
semantics but produces an ELF that runs to `--max-steps` on `ziskemu`.

### M1 — Total coverage of `Instr` (S/M)

Make `emitInstr` total for every constructor in `EvmAsm/Rv64/Basic.lean:113-237`:

- Immediates: `BitVec 12`, `BitVec 6` → signed decimal (`.toInt`).
  `BitVec 20` (LUI/AUIPC) → unsigned hex. `LI`'s `Word` → 64-bit signed `Int`
  literal — `as` handles the lowering to `lui`+`addiw`+`slli`+`addi`.
- Branches (`BEQ`, …, `JAL`) emit numeric byte offsets in M1; labels arrive in M3.
- `MV`, `NOP`, `FENCE`, `ECALL`, `EBREAK` pass through as their canonical mnemonics.
- Add `EvmAsm/Codegen/RoundTripTests.lean` — `#guard` examples covering each
  constructor once (e.g. `emitInstr (.SLTU .x5 .x7 .x6) = "sltu x5, x7, x6"`).

**Exit criteria.**
`lake exe codegen --program evm_add --asm-only` emits assembly that
`riscv64-unknown-elf-as -march=rv64imac` accepts cleanly; round-trip tests
pass under `lake build`.

### M2 — End-to-end `evm_add` (M) — **DONE (2026-05-18)**

Wire enough memory and registers so the verified `evm_add` program
(`EvmAsm/Evm64/Add/Program.lean`) computes a 256-bit sum on `ziskemu`.

**Delivered:**
- `BuildUnit` struct in `EvmAsm/Codegen/Layout.lean`: a verified
  `Program` body alongside optional raw-asm prologue, epilogue, and
  `.data` section. `emitBuildUnit` composes them into the full `.s`.
- `evm_add` wrapping in `EvmAsm/Codegen/Programs.lean`:
  - `.data` section with two 256-bit operands as eight LE doublewords.
  - Prologue (raw text, because `la` is a GNU-as pseudo not in our
    `Instr`): `la x12, operands`.
  - Body: `EvmAsm.Evm64.evm_add ++ evmAddEpilogue` where the 9-instr
    epilogue is itself a verified `Program` — every instruction lives
    in `Instr` and goes through the same totalized `emitInstr` and
    `#guard` round-trip tests as the body.
- `Driver.lean` adds `-Tdata=0xa0000000` to the link step so writable
  `.data` lands in `ziskemu`'s RAM region (`0xa0000000–0xc0000000`);
  without this, the emulator refuses the ELF with
  *"writable data section … outside RAM bounds"*.
- `scripts/codegen-evm_add-check.sh` builds, emits, links, runs, and
  diffs the first 32 bytes of `ziskemu`'s `-o` output against the
  expected 4-limb sum. **PASSES** with the M2 test case
  `A = 2^64-1, B = 1 → sum LE = [0, 1, 0, 0]`.

**Empirical surprise — `write_output` is memory-mapped, not an ecall.**
ziskemu does NOT honor the zkvm-standards `ecall + t0=0x10` write_output
syscall (the verified `step` semantics in
`EvmAsm/Rv64/Execution.lean:411` do). Instead, the public-output region
is memory-mapped at `OUTPUT_ADDR = 0xa001_0000` (constant from
`zisk/ziskos/entrypoint/src/ziskos_definitions.rs`). Guest writes u32
slots there directly; ziskemu's `-o <file>` dumps the full 256-byte
region. `MAX_OUTPUT = 0x1_0000` (64 KB) per the same file but the
default dump is `64 × 4 = 256` bytes. This mirrors the SP1/linux93
halt-convention split — the verified semantics target a different host
than ziskemu — and is now folded into M4's scope.

**Exit criteria (met).**
`ziskemu -e gen-out/evm_add.elf` halts and the post-state limbs equal
the `Word`-level sum. `scripts/codegen-evm_add-check.sh` exits 0.

### M3 — Labels (deferred)

Originally planned as two-pass emission rewriting numeric branch/jal offsets
into `Lk`-style labels. **Deferred**: the verified `Program`s in this repo
already carry branch/JAL offsets as explicit `BitVec 13` / `BitVec 21` byte
counts (see e.g. `EvmAsm/Rv64/Program.lean:104-110`); there are no symbolic
labels to resolve at codegen time, so emitting numeric offsets is exact and
readable enough through M2. Pick this milestone back up only if (a) a
verified Program starts using a symbolic branch target we'd otherwise have
to hand-compute, or (b) the M5 interpreter emission becomes unreadable
without labels.

**Exit criteria (if revisited).**
A `Program` containing a backward branch builds with `Lk`-style labels;
`riscv64-elf-objdump -d` shows the same encoded offsets as the
`--no-labels` build.

### M4 — `read_input` / `write_output` plumbing, including hint inputs (M) — **DONE (2026-05-18)**

The original M4 plan expected `read_input` (`t0 = 0xF2`) and
`write_output` (`t0 = 0x10`) to be ECALL syscalls (per the verified
`step` semantics in `EvmAsm/Rv64/Execution.lean:411,416`). M2 already
showed ziskemu uses memory-mapped output instead; M4 confirmed the
same for input. Both ECALL paths are ignored by ziskemu — everything
is memory-mapped.

**Empirical input layout** (determined by `input_echo` + a
known-pattern `ziskemu -i <file>`):
```
INPUT_ADDR + 0..8   = 8 bytes of ziskemu-side metadata (currently zero)
INPUT_ADDR + 8..16  = LE u64 length of the first record
                      (matches the first 8 bytes of the `-i` file)
INPUT_ADDR + 16..   = first record's data, packed verbatim from the
                      `-i` file after the length prefix
```
This matches `INPUT_INITIAL_OFFSET = 8` in the SDK
(`zisk/ziskos/entrypoint/src/lib.rs`).
`INPUT_DATA_OFFSET = 16` is captured as a constant in
`EvmAsm/Codegen/Programs.lean`.

**Delivered:**
- `input_echo` program: minimal probe that copies 32 bytes from
  `INPUT_ADDR + 0..32` to `OUTPUT_ADDR`, used to determine the layout
  above and as a permanent regression check.
- `copy64` Program helper (eight LE-dword load/store pairs).
- `evm_add_from_input`: same wrapping as `evm_add` but loads both
  256-bit operands at runtime from
  `INPUT_ADDR + INPUT_DATA_OFFSET`, copies them to a writable
  `.data` scratch region (`operands_ram`), runs the verified
  `evm_add` body, then writes the result via the existing
  `evmAddEpilogue`. Reuses everything from M2 — pure additive M4 work.
- `scripts/codegen-evm_add-from-input-check.sh`: builds, packs a
  72-byte input file (`8 B length || 32 B A || 32 B B`), runs
  `ziskemu -e ... -i ... -o ...`, diffs the first 32 bytes of public
  output against the expected `A + B` LE limbs. **PASSES** with the
  same test case as M2 (`A = 2^64-1, B = 1 → [0, 1, 0, 0]`),
  exercising the limb-0→limb-1 carry through the prover-input path.

**Hint inputs.** The mechanism is the *same* — both real public input
and prover-supplied non-deterministic hints share the single
`INPUT_ADDR` region; the convention is just that the prover packs
auxiliary witnesses (e.g. `(q, r)` for `DIV`) into the same
length-prefixed record after the public inputs. A full hint-driven
example will come when `evm_div` is wired into the registry; M4
infrastructure is in place to support it without further codegen
changes.

**Exit criteria (met).**
A `read_input → use → write_output → HALT` program consumes a
host-supplied input file and emits the expected bytes through
`ziskemu`'s output channel.

The `read_input` buffer carries **both** real public input **and**
prover-supplied non-deterministic hints — under the zkvm-standards I/O
ABI there is only one input channel; the host concatenates everything the
guest will need into a single buffer, and the guest decodes a structured
header (lengths, offsets) to find each section. This is the same channel
through which the prover supplies precomputed witnesses for expensive
operations: e.g. for `DIV` the prover supplies `(q, r)` and the guest
verifies `q · d + r = n ∧ r < d` instead of running long division.

M4 therefore covers three closely related concerns that share the same
syscall surface:

1. **Reading prover input** — `read_input` syscall, ELF reserves
   `__input_buf` in `.bss`/`.data` at `inputBufBase`, exposed via an
   emitted linker script template. Codegen accepts `--input <file>` and
   passes it through to `ziskemu -i <file>`.
2. **Hint inputs** — a small Lean-side helper that lets a `Program`
   declare "I expect a hint at offset N of size M (e.g. the `(q, r)` pair
   for DIV)". Codegen lays out the buffer; the host-side companion (a
   Python or Rust script under `scripts/`) packs the hints in the right
   order. Tracks the zkvm-standards hint conventions documented in
   `docs/zkvm-host-io-input-buffer-design.md`.
3. **Writing public output** — `write_output` syscall, used both by the
   smoke smoke-test (writing `a2`) and by the EVM interpreter (writing
   the final stack top / return data).

Cross-reference: the SP1-legacy streaming surface
(`HINT_LEN`/`HINT_READ`/`COMMIT`) has been retired from the Lean code; we
target only the zkvm-standards single-buffer shape.

**Exit criteria.**
- `evm_div` (when implemented) consumes a prover-supplied `(q, r)` hint
  from `read_input` and writes the verified quotient via `write_output`.
- An end-to-end `scripts/codegen-div-check.sh` packs an input, runs
  `ziskemu -i ...`, and diffs the public output against the expected
  value computed in Lean.

### M5 — Tiny EVM interpreter (L) — **DONE (2026-05-19)**

Split into two slices. **M5a** unrolls verified opcode `Program`s as a
linear chain (no runtime dispatch) to validate that the handlers
compose under `++` honoring the `x10` code-pointer convention.
**M5b** codegens the actual fetch/decode/dispatch loop from
`EvmAsm/Evm64/InterpreterLoop.lean` + `EvmAsm/Evm64/Dispatch.lean`.

#### M5a — Unrolled tiny interpreter (S) — **DONE (2026-05-19)**

Chain verified opcode `Program`s end-to-end for two hand-picked
bytecodes, no runtime dispatch. Each opcode handler reads its
operands from the conventional registers (`x10` = EVM code pointer,
`x12` = EVM stack pointer); a one-instruction `advancePc` between
handlers does the dispatcher's PC-update job inline.

**Delivered:**
- `advancePc (off : Nat) : Program` helper in
  `EvmAsm/Codegen/Programs.lean` — a single `ADDI .x10 .x10 off`
  emitted between unrolled opcode handlers. Stays in the verified
  `Program` world, so the existing `RoundTripTests.lean` already
  covers it.
- `tinyInterpAdd` / `tinyInterpAdd2` `Program`s composing
  `EvmAsm.Evm64.evm_push 1`, `EvmAsm.Evm64.evm_add`, and `advancePc`
  via `++`. STOP is handled by fall-through to the halt stub — no
  RISC-V `Program` body needed in the unrolled chain.
- `tinyInterpPrologue` + `tinyInterpDataSection` lay out the EVM
  bytecode bytes as `.byte` directives under label `evm_code`,
  followed by 256 bytes of writable scratch ending at label
  `evm_stack_top`. Prologue initializes `x10 = &evm_code` and
  `x12 = &evm_stack_top`.
- Two `BuildUnit`s (`tinyInterpAddUnit`, `tinyInterpAdd2Unit`)
  registered in `lookupProgram` and `knownProgramNames`. Both reuse
  the existing `evmAddEpilogue` for the result-to-`OUTPUT_ADDR` copy.
- `scripts/codegen-tiny-interp-check.sh`: builds, emits, links, runs
  both ELFs on `ziskemu`, and diffs the first 32 bytes of public
  output against the expected LE limbs. **PASSES** for both test
  programs.

**Test cases.**
- `tiny_interp_add`: `PUSH1 0xFF; PUSH1 0x01; ADD; STOP`
  → expected `[0x100, 0, 0, 0]` (first 8 bytes `00 01 00 00 00 00 00 00`).
- `tiny_interp_add2`: `PUSH1 0x10; PUSH1 0x20; ADD; PUSH1 0x30; ADD; STOP`
  → expected `[0x60, 0, 0, 0]` (first 8 bytes `60 00 00 00 00 00 00 00`).
  Exercises chained ADDs and a stack pointer that walks back up after
  each `evm_add`.

**Exit criteria (met).**
`scripts/codegen-tiny-interp-check.sh` exits 0; `riscv64-elf-objdump
-d` shows the inline `addi a0, a0, N` advances between unrolled opcode
handler bodies.

#### M5b — Runtime fetch/decode/dispatch loop (M) — **DONE (2026-05-19)**

A real fetch/decode/dispatch loop in RISC-V, with verified opcode
`Program`s wrapped one-by-one in subroutines. Per §Tricky bits #9
("Codegen is not verified") the loop scaffold lives as raw asm; only
the opcode bodies remain verified.

**Delivered:**
- `opcodeHandlerLabel : Nat → String` + `emitOpcodeHandlerTable`
  in `EvmAsm/Codegen/Programs.lean`: render a 256-entry jump table
  in `.data` mapping each opcode byte to a handler label. Unhandled
  bytes route to `h_invalid`.
- `tinyInterpDispatchPrologue` — `_start` init (`la x10, evm_code`,
  `la x12, evm_stack_top`) followed by `.dispatch_loop:`:
    ```
    lbu  x5, 0(x10)              # fetch opcode byte
    la   x6, opcode_handlers
    slli x5, x5, 3               # opcode * 8 (entry stride)
    add  x6, x6, x5
    ld   x7, 0(x6)               # load handler address
    jalr x1, x7, 0               # call handler
    j    .dispatch_loop
    ```
- `tinyInterpDispatchEpilogue` — handler subroutines + exit path:
  - `h_PUSH1`: `<emitProgram (evm_push 1)>` + `addi x10, x10, 2` + `ret`
  - `h_ADD`:   `<emitProgram evm_add>`     + `addi x10, x10, 1` + `ret`
  - `h_STOP`:  `j .exit_label` (no return to dispatcher)
  - `h_invalid`: `j .exit_label` (same exit path as STOP for this slice)
  - `.exit_label`: `<emitProgram evmAddEpilogue>` — falls through to
    the linux93 halt stub appended by `emitBuildUnit`.
- Two `BuildUnit`s (`tinyInterpDispatchAddUnit`,
  `tinyInterpDispatchAdd2Unit`) registered in `lookupProgram` and
  `knownProgramNames`. They reuse `tinyInterpAddBytecode` /
  `tinyInterpAdd2Bytecode` verbatim, so M5a and M5b run on identical
  inputs and produce identical expected outputs — any regression is
  isolated to the dispatcher.
- `scripts/codegen-tiny-interp-dispatch-check.sh` mirrors the M5a
  script and runs both dispatch units. **PASSES** for both bytecodes
  with `-n 200000` step budget.

**Calling convention (informal).** `x10` (EVM code pointer) is
preserved across handler calls; each handler wrapper advances it by
the opcode's byte width before returning. `x12` (EVM stack pointer)
is updated freely by handlers and persists across the loop. `x1` is
the standard return address. The dispatcher reloads its scratch
(`x5`, `x6`, `x7`) from `x10` and the jump-table base every
iteration, so the fact that verified handlers clobber them
(`evm_add` uses `x5`/`x6`/`x7`/`x11`) is by design.

**Layout note.** `evm_stack_top` and `opcode_handlers` end up at
the same address (no `.balign` padding needed since the stack
region already lands on an 8-byte boundary). Safe at the worst-case
depth of 2 (= 64 bytes) for both test programs, but worth flagging
if M5c expands to deeper bytecodes — give the stack its own
explicit reserved tail before the jump table.

**Exit criteria (met).**
`scripts/codegen-tiny-interp-dispatch-check.sh` exits 0; both M5a
and M5b produce identical bytes through `ziskemu`'s public output.

### M6a — Opcode registry + test harness (S/M) — **DONE (2026-05-20)**

Pure-infrastructure refactor of M5b's hand-written dispatcher
scaffolding into a declarative registry, plus a generic per-opcode
test harness. Zero behavior change: M5a, M5b, and M2 scripts all
still pass; the dispatcher emits the same handler subroutines in
the same order.

**Delivered:**
- New `EvmAsm/Codegen/Dispatch.lean`: `OpcodeHandlerSpec` struct
  (`label`, `opcodes : List Nat`, `body : Program`, `tail :
  HandlerTail`) plus `emitDispatcherPrologue / Epilogue /
  DataSection` helpers that consume `List OpcodeHandlerSpec`.
  `buildDispatchUnit` produces a complete `BuildUnit` from a
  registry, an exit body (`evmAddEpilogue`), and a bytecode payload.
- `EvmAsm/Codegen/Programs.lean` M5b section is now a 3-entry
  registry (`tinyInterpRegistry`):
    ```lean
    [ { label := "h_PUSH1"; opcodes := [0x60]; body := evm_push 1; tail := .advanceAndRet 2 }
    , { label := "h_ADD"  ; opcodes := [0x01]; body := evm_add    ; tail := .advanceAndRet 1 }
    , { label := "h_STOP" ; opcodes := [0x00]; body := []         ; tail := .custom "  j .exit_label" } ]
    ```
  Adding an opcode now = adding one record.
- New `EvmAsm/Codegen/Tests/Cases.lean`: `OpcodeTestCase` struct
  (`name`, `bytecode`, `expectedOutHex`) + `opcodeTestCases : List
  OpcodeTestCase` registry. Two M5b bytecodes migrated as
  `add_basic` / `add_chain`. `lookupTestCase` + `buildTestCaseUnit`
  let the CLI emit any case via the M5b dispatcher.
- `EvmAsm/Codegen/Cli.lean` extended with `--test-case <name>` and
  `--list-test-cases`. The list flag emits TSV (`name\thex`) so the
  bash runner reads expected outputs straight from Lean — single
  source of truth, no hex duplication.
- `scripts/codegen-opcodes-check.sh`: portable (bash 3.2-safe)
  runner. Calls `--list-test-cases`, iterates, emits + runs + diffs.
  Adding a regression test = appending one record to
  `opcodeTestCases`.

**Exit criteria (met).**
`scripts/codegen-opcodes-check.sh` exits 0 (both migrated cases
pass); `scripts/codegen-tiny-interp{,-dispatch}-check.sh` continue
to exit 0; M2/M4 scripts unchanged.

### M6b — Mass wire-up of fixed-shape opcodes (M) — **DONE (2026-05-20)**

Bring M5b dispatcher coverage from 3 → 82 opcodes by registering
every verified handler that matches the standard ABI (`<body>` +
`addi x10, x10, width` + `ret`). Pure registry expansion against
M6a's infrastructure; the dispatcher scaffolding (loop, jump table,
exit path) is unchanged from M6a.

**Delivered:**
- `EvmAsm/Codegen/Programs.lean` `tinyInterpRegistry` now composed
  from four builders:
  - `pushHandlers` — PUSH0..PUSH32 (33 entries, opcode bytes
    `0x5f + n`, tail `.advanceAndRet (1 + n)`).
  - `dupHandlers` — DUP1..DUP16 (16 entries, opcode bytes
    `0x7f + n`, tail `.advanceAndRet 1`).
  - `swapHandlers` — SWAP1..SWAP16 (16 entries, opcode bytes
    `0x8f + n`, tail `.advanceAndRet 1`).
  - `singletonHandlers` — 17 fixed-shape singletons: ADD, MUL, SUB,
    SIGNEXTEND, LT, GT, SLT, SGT, EQ, ISZERO, AND, OR, XOR, NOT,
    BYTE, SHR, POP.
  Plus `stopHandler` for STOP. Total: 33 + 16 + 16 + 17 + 1 =
  **83 wired opcodes**; remaining 173 bytes fall to `h_invalid`.
- **`OpcodeHandlerSpec.preBody : String`** added in
  `EvmAsm/Codegen/Dispatch.lean`. Used to inject raw asm between
  the handler's label and verified body. Required because four
  verified bodies (`evm_mul`, `evm_signextend`, `evm_byte`,
  `evm_shr`) use `x10` as a scratch accumulator, which clobbers
  our dispatcher's preserved EVM code pointer. Those handlers
  carry `preBody := "  mv x9, x10"` to stash the code pointer in
  `x9` (a register no verified opcode body touches) and a
  `x10RestoreAdvance1` tail that restores it before the standard
  advance + ret. Discovered empirically when `mul_basic` panicked
  ziskemu with `Mem::read() section not found for addr: 1` — the
  `addi x10, x10, 1` after `MULHU .x10 ...` landed at address 1.
- **`EvmAsm/Codegen/Tests/Cases.lean`** grew from 2 to 22 cases:
  16 singleton tests (one per opcode), 3 family representatives
  (`push32_basic`, `dup1_basic`, `swap1_basic`), one `arith_mix`
  kitchen sink, plus the two M6a baseline cases (`add_basic`,
  `add_chain`).

**Exit criteria (met).**
`scripts/codegen-opcodes-check.sh` exits 0 with all 22 cases
PASS; `scripts/codegen-tiny-interp{,-dispatch}-check.sh`,
`codegen-smoke.sh`, and `codegen-evm_add-check.sh` continue to
exit 0; full M6b suite runs in ~48 s (under the 60 s threshold
for considering the runtime-bytecode optimization).

### M7 — Memory opcodes (S/M) — **DONE (2026-05-20)**

Wires MLOAD / MSTORE / MSTORE8 into `tinyInterpRegistry`. First
milestone needing infrastructure beyond a stack-only ABI: the
dispatcher prologue now initialises a third persistent register
(`x13` = EVM memory base) alongside `x10` (code pointer) and `x12`
(stack pointer). MSIZE is deferred — the verified core doesn't
yet bookkeep memory expansion (`evmMemSizeIs` lives outside the
verified `Program`s; see `docs/99-mload-design.md` §4 and the
`evm_mload` docstring).

**Delivered:**
- `EvmAsm/Codegen/Dispatch.lean` — `emitDispatcherPrologue` adds
  `la x13, evm_memory`. `emitDispatcherDataSection` now declares
  a 32 KiB `evm_memory:` `.zero` block between `evm_stack_top:`
  and `opcode_handlers:`.
- `EvmAsm/Codegen/Programs.lean` — new `memoryHandlers` list with
  three entries:
    - `h_MLOAD` (0x51): `evm_mload .x15 .x16 .x17 .x18 .x13`
    - `h_MSTORE` (0x52): `evm_mstore .x15 .x14 .x16 .x17 .x18 .x13`
    - `h_MSTORE8` (0x53): `evm_mstore8 .x15 .x14 .x18 .x13`
  All three use `.advanceAndRet 1` — no `preBody` needed (none
  touch `x10`). MSTORE / MSTORE8's internal `ADDI .x12 .x12 64`
  handles the stack shrink.
- `EvmAsm/Codegen/Tests/Cases.lean` — two new cases
  (`mstore_mload`, `mstore8_basic`). Total now 24.

**Register convention.**
- `x10` = EVM code pointer (preserved across handlers)
- `x12` = EVM stack pointer (handlers update freely)
- `x13` = EVM memory base, init'd in dispatcher prologue (new in M7)
- `x14, x15, x16, x17, x18` = caller-saved scratch for memory handlers

**`.data` budget.**
The dispatcher's `.data` section starts at `0xa0000000` and must
stay under `0xa0010000` (= `OUTPUT_ADDR`). Post-M7 layout: ~50 B
bytecode + 256 B stack scratch + 32 KiB EVM memory + 2 KiB jump
table ≈ 35 KiB. Comfortably under the 64 KiB cap. A future
milestone that needs > 32 KiB of EVM memory should either grow
the budget (extending `.data` is bounded by `OUTPUT_ADDR`) or
relocate `evm_memory` to a separate section linked above
`OUTPUT_ADDR + 0x10000`.

**Exit criteria (met).**
`scripts/codegen-opcodes-check.sh` exits 0 with all 24 cases
PASS; legacy scripts (`codegen-tiny-interp{,-dispatch}-check.sh`,
`codegen-smoke.sh`, `codegen-evm_add{,-from-input}-check.sh`,
`codegen-evm_div{,-cases}-check.sh`, `codegen-evm_mod{,-cases}-check.sh`)
all still exit 0. Full M7 suite runs in **~57 s** — just under
the 60 s threshold; the next milestone that materially grows the
dispatcher ELF should consider the runtime-bytecode optimization.

### M8 — Unsigned division (DIV, MOD) through the dispatcher (M) — **DONE (2026-05-20)**

Routes the verified `evm_div` (0x04) and `evm_mod` (0x06) bodies
through `tinyInterpRegistry` using the existing `evmDivPatched` /
`evmModPatched` NOP-splice helpers (lifted out of the M2 standalone
DIV/MOD wrappers and hoisted before the M5b registry section).

**Delivered:**
- `EvmAsm/Codegen/Programs.lean`:
  - Hoisted `evmDivPatched` / `evmModPatched` above the M5b
    registry so both the M2 standalone wrappers (`evmDivUnit`,
    `evmModUnit`, etc.) and the new M8 dispatcher handlers can
    reference them.
  - New `divModHandlers : List OpcodeHandlerSpec` with two entries
    (`h_DIV`, `h_MOD`). Both use `preBody := "  mv x14, x10"` and a
    custom tail (`divModTail`) that restores via `mv x10, x14`.
    **`x14` instead of `x9`** because `evm_div` / `evm_mod` use `x9`
    as the Knuth-D loop counter `j` (94 references); the standard
    M6b `mv x9, x10` save would be destroyed mid-body.
- `EvmAsm/Codegen/Tests/Cases.lean`: two new cases — `div_basic`
  (10/2 = 5) and `mod_basic` (10%3 = 1). Total now 26.

**Discovered scope reduction.** SDIV (0x05) and SMOD (0x07) ended up
deferred. The earlier plan assumed they'd ride the same wrapping
pattern, but their verified bodies (`evm_sdiv` / `evm_smod`) end with
a "saved-ra-ret" pattern — `JALR x0, x18, 0` after the wrapper has
copied `x1` into `x18` at the start — which **bypasses the dispatcher's
standard wrapper tail entirely**. Integrating them needs a
trampoline-style wrapper: set `x18` to point at a per-handler restore
stub *before* the body runs, and splice off the body's initial
`save_ra_block` so the trampoline target sticks. That's a new
infrastructure surface; tracked as a separate codegen PR (M8.5 or
M9-prep).

**Register clobber audit lesson.** M6b's `mv x9, x10` save trick
isn't universal — it assumed `x9` was unused by the verified body.
For DIV/MOD (which use `x9` as `j`) we picked `x14` instead. **The
M7-and-beyond habit of `grep -c '\.x10\b'` before adding a handler
needs to extend to the chosen save register too:** verify
`grep -c '\.<save-reg>\b'` is zero across the body's `Program.lean`
and any callable subroutines.

**Exit criteria (met).**
`scripts/codegen-opcodes-check.sh` exits 0 with all 26 cases PASS
(24 prior + 2 new). Pre-existing scripts unchanged. Full M8 suite
runs in **~60 s** — at the threshold. The next opcode batch (M9
self-calling, or M8.5 SDIV/SMOD via trampoline) should bundle the
runtime-bytecode optimization to keep the suite snappy.

### M8.5 — Runtime-bytecode dispatcher (S/M) — **DONE (2026-05-20)**

Pure infrastructure: build the dispatcher ELF **once**; per case
the test harness packs the bytecode into a `ziskemu -i <file>`
payload instead of rebuilding the ELF per case. M8 put the suite
at ~60 s; this brings it to **~20 s** (3× speedup) and leaves
headroom for the next several opcode milestones.

**Delivered:**
- `EvmAsm/Codegen/Dispatch.lean` — new helpers:
  - `emitRuntimeDispatcherPrologue` — same fetch/decode/dispatch
    loop as the `.data`-baked variant, but `li x10, 0x40000010`
    (= `INPUT_ADDR + INPUT_DATA_OFFSET`) replaces
    `la x10, evm_code`.
  - `emitRuntimeDispatcherDataSection` — drops the `evm_code:`
    block. Stack scratch, `evm_memory:`, and the 256-entry jump
    table all stay.
  - `buildRuntimeDispatchUnit (registry, exitBody) → BuildUnit` —
    factory mirroring `buildDispatchUnit` but with no bytecode
    parameter.
- `EvmAsm/Codegen/Programs.lean` — new `runtimeDispatcherUnit`
  using `tinyInterpRegistry` + `evmAddEpilogue`. Registered as
  `"runtime_dispatcher"` in `lookupProgram` / `knownProgramNames`.
- `EvmAsm/Codegen/Cli.lean` — `--list-test-cases` extended to a
  **3-column TSV** (`name\thex\tbytecode`). The legacy
  per-case-ELF runner (`codegen-opcodes-check.sh`) updated to
  drop the 3rd column with a placeholder var; the new
  `codegen-opcodes-runtime-check.sh` reads all three.
- `scripts/pack-bytecode.py` — new helper. Parses a
  comma-separated `0xNN` list and emits `<8-byte LE u64
  length><bytecode><zero pad to multiple-of-8>`. The zero pad is
  required by ziskemu (`EmuContext::new() input size must be a
  multiple of 8`); trailing zeros are harmless because the
  dispatcher hits the bytecode's own STOP first.
- `scripts/codegen-opcodes-runtime-check.sh` — new canonical
  runner. Builds `runtime_dispatcher.elf` once, then iterates
  `--list-test-cases`, packing each per-case bytecode into
  `gen-out/<name>.input` and running ziskemu against the shared
  ELF.

**Suite runtime (validated on a macOS dev box):**
- Legacy `codegen-opcodes-check.sh`: ~60 s (26 cases, one
  assemble + link per case).
- New `codegen-opcodes-runtime-check.sh`: **~20 s** (26 cases,
  one assemble + link total). 3× speedup.

The speedup is smaller than the ~6× I predicted in the M8.5 plan;
per-case ziskemu invocation overhead (process startup, ELF load,
input parse) is bigger than I modelled (~0.5 s vs the predicted
0.1 s). Still plenty of headroom for M9 / M10 / M11 to add
handler text without forcing the suite back over the 60 s mark.

**Exit criteria (met).**
Both `codegen-opcodes-runtime-check.sh` (new canonical) and
`codegen-opcodes-check.sh` (legacy fallback, kept for
backwards-compat during the transition) exit 0 with the same 26
cases PASS. Pre-existing M2/M4/M5/M7/M8 scripts unchanged.
PROGRESS.md regenerated (program count 16 → 17, script count
14 → 15).

### M9 — SDIV / SMOD via trampoline wrapper (M) — **DONE (2026-05-21)**

Closes the M8 scope-reduction debt: SDIV (0x05) and SMOD (0x07)
now route through `tinyInterpRegistry`. New trampoline wrapper
pattern via a `postBodyLabel : Option String` field on
`OpcodeHandlerSpec` — generalisable to any future opcode whose
verified body ends with a saved-ra-ret (`JALR x0, x18, 0`).

**Delivered:**
- `EvmAsm/Codegen/Dispatch.lean` — extended `OpcodeHandlerSpec`
  with `postBodyLabel : Option String := none`. `emitSubroutine`
  emits an optional label between body and tail. Handlers that
  leave this `none` (all M5b–M8 handlers) emit byte-identical
  asm.
- `EvmAsm/Codegen/Programs.lean` — new helpers:
  - `evmSdivPatched := (evm_sdiv : List Instr).drop 1` — strips
    the leading `ADDI .x18 .x1 0` save_ra_block (413 instructions
    instead of 414).
  - `evmSmodPatched := (evm_smod : List Instr).drop 1` — same.
  - `signedDivModTail` — restores `x10` from `x14`, advances PC,
    then `j .dispatch_loop` (NOT `ret`: the wrapper's inner
    `JAL .x1` into `evm_div_callable_v4` / `evm_mod_callable_v4`
    clobbers x1, so a standard `ret` would jump to garbage).
  - `signedDivModHandlers` — two entries (`h_SDIV`, `h_SMOD`).
    Each carries `preBody := "  mv x14, x10\n  la x18, h_<NAME>_done"`,
    `postBodyLabel := some "h_<NAME>_done"`, and `tail := signedDivModTail`.
  - `tinyInterpRegistry` appends `signedDivModHandlers` between
    `divModHandlers` and `[stopHandler]`.
- `EvmAsm/Codegen/Tests/Cases.lean` — three new cases:
  `sdiv_basic` (5/2 = 2, positive path), `sdiv_negative` (NOT trick
  → −2 / 2 = −1, exercises sign-extract + conditional-negate),
  `smod_negative` (NOT trick → −2 % 5 = −2, sign(result) = sign(a)
  per EVM SMOD semantics).
- `scripts/codegen-opcodes-runtime-check.sh` — bumped per-case
  step budget from 200K to 500K. SDIV/SMOD's Knuth-D inner loop
  plus the trampoline overhead pushes beyond 200K even for small
  operands; the legacy `codegen-evm_div-check.sh` already used 500K.

**Trampoline mechanics gotcha.** First attempt used `divModTail`
(= `mv x10, x14; addi; ret`) for the SDIV/SMOD restore stub —
ziskemu hung with `EmulationNoCompleted`. Cause: the wrapper's
inner `JAL .x1` into the callable divider clobbers `x1`, so by
the time control reaches the restore stub, `x1` no longer points
at the dispatcher's continuation. Fix: replaced `ret` with
`j .dispatch_loop` (a direct jump to the dispatcher loop entry,
bypassing the `x1`-mediated return).

**SMOD v4 status.** `evm_smod` now uses the v4 modulo callable, matching
`evm_sdiv`'s v4 division path. The trampoline shape did not need to
change: both signed wrappers still end through the same saved-ra return
stub, and `signedDivModTail` still jumps directly back to `.dispatch_loop`.

**Exit criteria (met).**
`scripts/codegen-opcodes-runtime-check.sh` exits 0 with all 29
cases PASS (26 prior + 3 new). Legacy `codegen-opcodes-check.sh`
also exits 0. Pre-existing M2/M4/M5/M7/M8/M8.5 scripts unchanged.
PROGRESS.md needs only a snapshot-line bump (ignored by CI's
drift check) — no commit.

### M11 — Remaining bitwise shifts (SHL + SAR) — **DONE (2026-05-26)**

Wires the last two unwired entries from `EvmAsm/Evm64/Shift/Program.lean`
into `singletonHandlers`. SHL (0x1b) and SAR (0x1d) share the exact
shape that SHR (0x1c, wired in M6b) already uses: a `preBody :=
"mv x9, x10"` + `x10RestoreAdvance1` tail because the verified
bodies clobber `x10` as a JAL-target scratch.

**Delivered:**
- `EvmAsm/Codegen/Programs/Evm.lean` — two new entries adjacent to
  `h_SHR` in `singletonHandlers`:
  ```lean
  { label := "h_SHL", opcodes := [0x1b], preBody := "  mv x9, x10",
    body := EvmAsm.Evm64.evm_shl, tail := x10RestoreAdvance1 }
  { label := "h_SAR", opcodes := [0x1d], preBody := "  mv x9, x10",
    body := EvmAsm.Evm64.evm_sar, tail := x10RestoreAdvance1 }
  ```
  `singletonHandlers` grows from 17 → 19; `tinyInterpRegistry`'s total
  wired-opcode count grows from 91 → 93.
- `EvmAsm/Codegen/Tests/Cases.lean` — three new cases:
  `shl_basic` (`1 << 4 = 0x10`),
  `sar_basic_positive` (`0xff >>> 1 = 0x7f`, MSB clear so SAR == SHR),
  `sar_basic_negative` (`-1 >>>arith 1 = -1`, exercises sign-fill via
  PUSH32 of `2^256-1`). Total cases: 31 → 34.
- `EvmAsm/Codegen/Proofs/RegistryInvariants.lean` — bump the two
  hard-coded count theorems (`tinyInterpRegistry_wired_opcode_count`
  and `jumpTable_non_invalid_count`) from 91 → 93. Discharged by
  `decide` / `set_option maxRecDepth 2048 in decide` as before.

**MSIZE (0x59) deferred.** The verified `evm_msize` Program exists
(`EvmAsm/Evm64/MSize/Program.lean`, slice 6 of issue #99) and is a
pure read of a memory-size cell, but slices 1–5 — updating that cell
from MLOAD/MSTORE/MSTORE8 on memory expansion — have not shipped:
`evm_mload` / `evm_mstore` / `evm_mstore8` take no `sizeReg`
parameter and never reference `sizeLoc`. Wiring MSIZE today would
push a 4-limb zero regardless of EVM-memory touches. Drop into
`memoryHandlers` once issue #99 slices 1–5 land.

**EXP (0x0a) still blocked** pending the upstream
`evm_exp_msb_saved_bit_two_mul_fixed_fixed` callee-saved variant.

**Exit criteria (met).**
`scripts/codegen-opcodes-runtime-check.sh` exits 0 with all 34 cases
PASS. `scripts/check-progress.sh` exits 0 (drift gate). Legacy
`scripts/codegen-opcodes-check.sh` also exits 0. Pre-existing
M2/M4/M5/M7/M8/M8.5/M9/M10 scripts unchanged.

### M12 — Simple environment opcodes (Bucket A drain) — **DONE (2026-05-26)**

Wires the 13 `SimpleEnvField` opcodes (ADDRESS 0x30, ORIGIN 0x32,
CALLER 0x33, CALLVALUE 0x34, GASPRICE 0x3a, COINBASE 0x41,
TIMESTAMP 0x42, NUMBER 0x43, PREVRANDAO 0x44, GASLIMIT 0x45,
CHAINID 0x46, SELFBALANCE 0x47, BASEFEE 0x48) into
`tinyInterpRegistry` as `envHandlers`. Lifts wired opcode count
93 → 106 in one PR.

**Delivered:**
- `EvmAsm/Codegen/Dispatch.lean` — prologue (both `.data`-baked and
  runtime-bytecode variants) initialises **`x20 = &evm_env`**; data
  section adds a 416-byte (13 × 32 B) `evm_env:` block zero-
  initialised. `x20` was chosen over `x14` because M8/M9/M10
  DIV/MOD/SDIV/SMOD/ADDMOD handlers all save `x10` to `x14` via
  `preBody`. `x20` has zero references in any
  `EvmAsm/Evm64/*/Program.lean` and zero existing handler uses,
  making it the cleanest long-term home for the env base.
- `EvmAsm/Codegen/Programs/Evm.lean` — new `envHandlers` builder
  inserted between `memoryHandlers` and `divModHandlers` in the
  registry composition. All 13 records share the verified body
  `EvmAsm.Evm64.Env.evm_env_load .x20 .x15 <field>` (9 instructions
  per handler) parameterized over the `SimpleEnvField` enum value.
  No `preBody` needed (env body doesn't touch `x10`); all use the
  standard `.advanceAndRet 1` tail.
- `EvmAsm/Codegen/Tests/Cases.lean` — three representative cases:
  `address_zero` (routes byte 0x30 → 32 zero bytes),
  `caller_via_dup_add` (CALLER + DUP1 + ADD exercises post-ENV
  stack flow), `env_field_offset_distinct` (TIMESTAMP + NUMBER + SUB
  confirms different opcode bytes resolve to different env cells).
  Total cases: 34 → 37.
- `EvmAsm/Codegen/Proofs/RegistryInvariants.lean` — bumped the two
  hard-coded counts (`tinyInterpRegistry_wired_opcode_count` and
  `jumpTable_non_invalid_count`) from 93 → **106**.

**Env values are zero-initialised.** The dispatcher's
`evm_env:` data section is `.zero 416`. Wiring this PR validates
that the handler dispatch + field-offset arithmetic + 4-limb push
mechanism work correctly. Non-zero env values come from a future
host-preload PR that extends `INPUT_DATA_OFFSET` semantics to carry
an `EvmEnv` struct; not blocking codegen correctness today.

**Exit criteria (met).**
`scripts/codegen-opcodes-runtime-check.sh` exits 0 with all 37 cases
PASS. `scripts/check-progress.sh` exits 0. Legacy
`scripts/codegen-opcodes-check.sh` also exits 0. Pre-existing scripts
unchanged.

### M13 — CALLDATASIZE (final Bucket A drain) — **DONE (2026-05-26)**

Wires `CALLDATASIZE (0x36)` via a new `calldataHandlers` list of one
entry. Reuses M12's `x20 = &evm_env` register convention — the
calldata-length cell at `evm_env + 424` lives in the same env region.
Lifts wired opcode count 106 → 107.

**Delivered:**
- `EvmAsm/Codegen/Dispatch.lean` — `evm_env:` data block bumped from
  416 to **512 bytes**, large enough to cover all
  `Environment/Layout.lean` field offsets up to `returnDataSizeOff =
  440` + 8 with slack. Both `.data`-baked and runtime-bytecode
  variants updated.
- `EvmAsm/Codegen/Programs/Evm.lean` — new `calldataHandlers`
  builder adjacent to `envHandlers`. Single record:
  ```lean
  { label := "h_CALLDATASIZE", opcodes := [0x36],
    body := EvmAsm.Evm64.Calldata.evm_calldatasize .x20 .x15,
    tail := .advanceAndRet 1 }
  ```
  `evm_calldatasize` is a verified 6-instruction Program (parametric
  in `envBaseReg`/`tmpReg`) at
  `EvmAsm/Evm64/Calldata/SizeProgram.lean`. It reads `callDataLenOff
  = 424` from the env block (defined in
  `EvmAsm/Evm64/Environment/Layout.lean:87`), decrements `x12` by 32,
  writes the low limb plus three zero high limbs.
- `EvmAsm/Codegen/Tests/Cases.lean` — one new case
  `calldatasize_zero` (bytecode `0x36 0x00`). Total: 37 → 38.
- `EvmAsm/Codegen/Proofs/RegistryInvariants.lean` — counts bumped
  106 → 107.

**Strategic crossroad reached.** M13 drains the last opcode whose
verified body is ready AND wireable without new design surface.
Continuing to 100% coverage from 107 requires either external
unblock (issue #99 → MSIZE; upstream EXP fix), small core change
(extend `EvmEnv` for BLOBHASH/BLOBBASEFEE), verified-core
implementation (MULMOD, CALLDATACOPY, CODESIZE/COPY, RETURNDATA*,
EXTCODE*, BALANCE, BLOCKHASH), or new codegen design surface
(control flow with a `HandlerTail.writeX10` variant; host-syscall
ECALL bridge for KECCAK256/LOG/SLOAD/SSTORE/precompiles; child
frames for CALL/CREATE/RETURN/REVERT/SELFDESTRUCT/INVALID).

**Exit criteria (met).**
`scripts/codegen-opcodes-runtime-check.sh` exits 0 with all 38 cases
PASS. `scripts/check-progress.sh` exits 0. Legacy
`scripts/codegen-opcodes-check.sh` also exits 0. Pre-existing scripts
unchanged.

### M14 — JUMPDEST (control-flow no-op marker) — **DONE (2026-05-27)**

Wires JUMPDEST (0x5b) via a new `controlFlowHandlers` builder.
Smallest possible PR: an empty body (`body := []`) + the standard
`.advanceAndRet 1` tail. JUMPDEST is the EVM no-op marker that
JUMP/JUMPI use as their valid-target check; M14 makes the
dispatcher route 0x5b correctly so it stops short-circuiting to
`h_invalid`. M15 will extend `controlFlowHandlers` with JUMP /
JUMPI / PC under the same umbrella.

**Delivered:**
- `EvmAsm/Codegen/Programs/Evm.lean` — new `controlFlowHandlers`
  list with one record (`h_JUMPDEST`, opcode `0x5b`, `body := []`,
  `tail := .advanceAndRet 1`) inserted into `tinyInterpRegistry`
  between `calldataHandlers` and `divModHandlers`. The empty-body
  emission path is already exercised by `stopHandler` — no
  dispatcher changes needed.
- `EvmAsm/Codegen/Tests/Cases.lean` — one new case
  `jumpdest_basic` (bytecode `0x5b 0x60 0x42 0x00`: JUMPDEST; PUSH1
  0x42; STOP). Confirms JUMPDEST advances `x10` by 1 without
  disturbing the stack and PUSH1 lands 0x42 on the EVM stack as
  expected. Total cases: 38 → 39.
- `EvmAsm/Codegen/Proofs/RegistryInvariants.lean` — counts bumped
  107 → 108.

**Strategic note.** M14 by itself has no semantic effect (JUMPDEST
is a no-op for the dispatcher), but it eliminates one of the most
common "INVALID opcode" failures bytecode-test runners hit:
JUMPDEST appears in every EVM contract that uses loops. M15
(JUMP / JUMPI / PC) closes the control-flow loop.

**Exit criteria (met).**
`scripts/codegen-opcodes-runtime-check.sh` exits 0 with all 39 cases
PASS. `scripts/check-progress.sh` exits 0. Legacy
`scripts/codegen-opcodes-check.sh` also exits 0. Pre-existing scripts
unchanged.

### M15 — JUMP / JUMPI / PC (control-flow design surface) — **DONE (2026-05-27)**

Closes the control-flow loop: extends `controlFlowHandlers` with
**JUMP (0x56), JUMPI (0x57), PC (0x58)**. With M15 the dispatcher
can run non-trivial EVM bytecode (loops, conditionals, PC-aware
computation). Lifts wired opcode count **108 → 111** (74.5% of the
149-byte EVM space).

**Delivered:**

- **New verified file `EvmAsm/Evm64/ControlFlow/Program.lean`**
  with three parametric Programs:
  - `evm_pc codeBaseReg tmpReg` (6 instructions) — `pc = x10 -
    codeBaseReg`, pushed as a 256-bit word.
  - `evm_jump codeBaseReg destReg` (3 instructions) — `x10 :=
    codeBaseReg + dest`. Tail is `.custom "  ret"`; no advance.
  - `evm_jumpi codeBaseReg destReg condReg tmpReg`
    (13 instructions) — OR-combines the 4 cond limbs to detect
    nonzero; `BEQ +12` skips the jump path (lands at fall-through
    `ADDI x10, x10, 1`), `JAL +8` skips the fall-through on the
    cond-nonzero path (lands at the tail's `ret`).
- **`EvmAsm/Codegen/Dispatch.lean`**: dispatcher prologue (both
  `.data`-baked and runtime-bytecode variants) gains
  `la x21, evm_code` / `li x21, 0x40000010` — the **preserved
  code-base register**. `x21` was audited the same way `x20` was
  for M12 (zero references in `EvmAsm/Evm64/*/Program.lean`, zero
  uses by any existing handler `preBody`/`tail`).
- **`EvmAsm/Codegen/Programs/Evm.lean`**: `controlFlowHandlers`
  grows from 1 → 4 entries. JUMP/JUMPI use `.custom "  ret"`
  tails (body has already written `x10`); PC uses
  `.advanceAndRet 1`.
- **`EvmAsm/Codegen/Tests/Cases.lean`**: 5 new cases —
  `pc_at_zero`, `pc_after_push`, `jump_forward`, `jumpi_taken`,
  `jumpi_not_taken`. Total 39 → 44.
- **`EvmAsm/Codegen/Proofs/RegistryInvariants.lean`**: counts
  bumped 108 → 111.

**Known limitation: no JUMPDEST-validity check.** The verified
bodies in this PR unconditionally follow the popped destination.
A spec-compliant EVM rejects invalid jumps; ours doesn't. Trusted
test programs all jump to real JUMPDEST bytes. A follow-on PR
will inline the `LBU + BEQ 0x5b` check.

**Other limitations** (same trust model):
- 256-bit `dest` is truncated to its low 64 bits. EVM jumps with
  `dest >= 2^64` are technically invalid; trusted programs never
  go there.
- Out-of-bounds `dest` reads beyond the bytecode region into
  `.data` (stack, memory, env, jump table). The dispatcher's next
  iteration would read whatever byte is there. Same trust caveat.

**Exit criteria (met).**
`scripts/codegen-opcodes-runtime-check.sh` exits 0 with all 44
cases PASS. `scripts/check-progress.sh` exits 0. Legacy
`scripts/codegen-opcodes-check.sh` also exits 0. Pre-existing
scripts unchanged.

### Sequencing

M0 ✅ → M1 ✅ → M2 ✅ → M4 ✅ → M5a ✅ → M5b ✅ → M6a ✅ → M6b ✅ → M7 ✅ → M8 ✅ → M8.5 ✅ → M9 ✅ → M10 ✅ → M11 ✅ → M12 ✅ → M13 ✅ → M14 ✅ → M15 ✅.
M3 is deferred; revisit only if a future milestone (full opcode
coverage, JUMP/JUMPI, or the binary encoder) makes label-free
emission unreadable. M11 (SHL + SAR) shipped 2026-05-26; M12
(13 simple environment opcodes via `envHandlers`) shipped 2026-05-26;
M13 (CALLDATASIZE via `calldataHandlers`) shipped 2026-05-26;
M14 (JUMPDEST via `controlFlowHandlers`) shipped 2026-05-27;
M15 (JUMP/JUMPI/PC into `controlFlowHandlers`) shipped 2026-05-27.
EXP remains deferred pending upstream callee-saved register
variants; MSIZE deferred pending issue #99 slices 1–5;
BLOBHASH/BLOBBASEFEE pending `EvmEnv` struct extension;
JUMPDEST-validity check tracked as the next follow-on slice.

## Tricky bits / open questions

1. **`LI rd, imm64` lowering.** `as` chooses 1–8 instructions to materialize a
   64-bit constant. The verified specs assume specific PC arithmetic — for the
   text-first path this is fine because we never re-derive PCs at the bit
   level. The future binary encoder will need to reproduce `as`'s expansion
   exactly (or use its own).
2. **`MV`, `NOP`, `FENCE`** are accepted verbatim by `as`. No manual lowering.
3. **Branch encoding sanity.** M1 emits numeric byte offsets via `.toInt` on
   `BitVec 13`/`BitVec 21`. M3's label path is for readability; verify the
   encoded bytes match the numeric path with `objdump`.
4. **`.option norvc`** at every unit head — keeps `as` from emitting 2-byte
   compressed encodings. Required for predictable PC layout and for the future
   binary encoder.
5. **SP1 `t0=0` vs `ziskemu` HALT — RESOLVED (2026-05-18).** The verified
   `step` halts on `t0=0` (`EvmAsm/Rv64/Execution.lean:611-615`), but
   `ziskemu`'s stock examples use `a7=93`. M0 ran the experiment with
   ZisK v0.18.0 on macOS 26: **`ziskemu` halts cleanly on `linux93`
   (`ecall` + `a7=93`) and ignores `sp1` (`ecall` + `t0=0`)** — the SP1
   variant runs to `--max-steps` and errors with `EmulationNoCompleted`.
   `--halt linux93` is the codegen default; `--halt sp1` is kept for
   anyone proving against the SP1 step semantics directly.
   `docs/host-io-halt-convention.md` remains the canonical ADR.
6. **Memory bounds.** Emitted ELFs must respect
   `MEM_START=0x20` / `MEM_END=0x78000000`. Codify in `Codegen/Layout.lean` so
   the constants can't drift from `EvmAsm/Rv64/Basic.lean:244,247`.
7. **No `read_input` in M0.** Deferred to M4. M0/M1/M2 use hardcoded values
   (smoke) or `.data` seeding (`evm_add`).
8. **Toolchain availability.** Gate the assemble/link step behind a feature
   check; CI without `riscv64-unknown-elf-as` still runs `--asm-only` to catch
   emitter regressions.
9. **Codegen is mostly unverified, but the proof boundary is growing.**
   The text emitters (`emitInstr`, `emitDispatcherPrologue`, etc.)
   remain an output channel, not part of the trusted kernel surface.
   Two codegen-proofs phases have landed:
   * Phase 1 (`EvmAsm/Codegen/Proofs/RegistryInvariants.lean`) —
     6 theorems about `tinyInterpRegistry`'s structural well-formedness
     (Nodup on opcode bytes + labels, byte bounds, jump-table coverage).
   * Phase 4 (`EvmAsm/Codegen/Proofs/HandlerSpecs.lean`) — a reusable
     `cleanRetHandlerSpec` template that lifts a verified body spec
     to a full handler-subroutine `cpsTripleWithin` triple (body +
     `ADDI x10 x10 n` + `JALR x0 x1 0`). **13 concrete handler-level
     instances** cover ADD, POP, SUB, LT, GT, SLT, SGT, EQ, ISZERO,
     AND, OR, XOR, NOT — every clean-shape singleton with an empty
     `preBody` and `.advanceAndRet 1` tail.
   All proofs use only `decide`, `omega`, `bv_omega`, and the
   `cpsTripleWithin` composition lemmas — no `native_decide` /
   `bv_decide`, per [`CLAUDE.md`](CLAUDE.md). Phase 2 (parser
   round-trip), Phase 3 (dispatch-loop spec), the remaining Phase 4
   instances (other clean-shape handlers, then x10-save / trampoline
   / self-calling variants), and Phase 5 (end-to-end refinement)
   are still future work.

## Verification (per milestone)

- **M0.** `ziskemu -e gen-out/smoke.elf` exits 0 (validated 2026-05-18 with
  ZisK v0.18.0). Both halt modes exercised; result of the SP1/`ziskemu`
  experiment recorded in §Tricky bits #5 above. Direct `a2 = 100`
  verification is deferred to M2 (needs `write_output` wiring).
- **M1.** `lake build` passes (includes `RoundTripTests.lean`);
  `lake exe codegen --program evm_add --asm-only | riscv64-unknown-elf-as -march=rv64imac -o /dev/null -`
  returns 0.
- **M2.** ✅ `scripts/codegen-evm_add-check.sh` exits 0 (validated
  2026-05-18). Test case `A = 2^64-1, B = 1 → sum LE = [0, 1, 0, 0]`
  exercises the limb-0→limb-1 carry.
- **M3.** `diff <(codegen --no-labels … | as | objdump -d) <(codegen … | as | objdump -d)`
  shows only label-noise differences.
- **M4.** ✅ `scripts/codegen-evm_add-from-input-check.sh` exits 0
  (validated 2026-05-18). Same operands and expected sum as M2, but
  loaded at runtime from `ziskemu -i <file>` instead of `.data`.
- **M5a.** ✅ `scripts/codegen-tiny-interp-check.sh` exits 0
  (validated 2026-05-19). Two unrolled bytecodes
  (`PUSH1; PUSH1; ADD; STOP` and `PUSH1; PUSH1; ADD; PUSH1; ADD; STOP`)
  round-trip through verified opcode `Program`s chained with
  `advancePc`.
- **M5b.** ✅ `scripts/codegen-tiny-interp-dispatch-check.sh` exits 0
  (validated 2026-05-19). Same two bytecodes as M5a, but routed
  through a 256-entry jump table + handler subroutines (`jalr ra,
  …`) instead of an unrolled chain. Output bytes match M5a's, which
  cross-checks the dispatcher against the unrolled reference.
- **M6a.** ✅ `scripts/codegen-opcodes-check.sh` exits 0 (validated
  2026-05-20). Generic harness driven by Lean-declared
  `opcodeTestCases`; the two M5b bytecodes (`add_basic`,
  `add_chain`) migrated as the seed regression suite. `--list-test-cases`
  emits TSV with expected outputs so the bash runner stays in sync
  with `Tests/Cases.lean` automatically.
- **M6b.** ✅ `scripts/codegen-opcodes-check.sh` exits 0 with **22
  test cases** PASS (validated 2026-05-20). 83 opcodes wired through
  `tinyInterpRegistry`: PUSH0..32, DUP1..16, SWAP1..16, plus 17
  fixed-shape singletons (ADD, MUL, SUB, SIGNEXTEND, LT, GT, SLT,
  SGT, EQ, ISZERO, AND, OR, XOR, NOT, BYTE, SHR, POP) and STOP.
  Four handlers that clobber `x10` (MUL, SIGNEXTEND, BYTE, SHR)
  use the new `OpcodeHandlerSpec.preBody` field to save the EVM
  code pointer in `x9` before the body and restore it in the tail.
- **M7.** ✅ `scripts/codegen-opcodes-check.sh` exits 0 with **24
  test cases** PASS (validated 2026-05-20). Three memory opcodes
  wired (MLOAD, MSTORE, MSTORE8) plus a 32 KiB `evm_memory:`
  `.data` region and `x13` = memory-base in the dispatcher prologue.
  MSIZE deferred pending verified memory-expansion bookkeeping.
  Suite runtime: ~57 s (just under the 60 s threshold).
- **M8.** ✅ `scripts/codegen-opcodes-check.sh` exits 0 with **26
  test cases** PASS (validated 2026-05-20). DIV (0x04) and MOD (0x06)
  routed through `tinyInterpRegistry` using the
  `evmDivPatched` / `evmModPatched` NOP-splice helpers. Save register
  switched from `x9` to `x14` for these two handlers because the
  verified bodies use `x9` as the Knuth-D loop counter. SDIV/SMOD
  deferred — their bodies use a saved-ra-ret pattern that bypasses
  the dispatcher's wrapper tail.
- **M8.5.** ✅ `scripts/codegen-opcodes-runtime-check.sh` exits 0
  with **26 test cases** PASS (validated 2026-05-20). New
  `runtime_dispatcher` BuildUnit reads bytecode at
  `INPUT_ADDR + INPUT_DATA_OFFSET = 0x40000010` at runtime instead
  of baking it into `.data`. Suite runtime dropped from ~60 s to
  ~20 s (3× speedup). Legacy `codegen-opcodes-check.sh` still
  passes as the fallback.
- **M9.** ✅ `scripts/codegen-opcodes-runtime-check.sh` exits 0 with
  **29 test cases** PASS (validated 2026-05-21). SDIV (0x05) and
  SMOD (0x07) wired via the new trampoline pattern + the
  `OpcodeHandlerSpec.postBodyLabel : Option String` field.
  `signedDivModTail` uses `j .dispatch_loop` instead of `ret`
  because the wrapper's inner `JAL .x1` clobbers x1 mid-body.
- **M10.** ✅ `scripts/codegen-opcodes-runtime-check.sh` exits 0 with
  **31 test cases** PASS (validated 2026-05-21). ADDMOD (0x08)
  wired via an inline-callable composition: the handler body is
  `evm_addmod_prologue ;; phase1_carry ;; phase2_reduce 8 ;;
  skip-JAL ;; evm_mod_callable_v4`. The JAL inside `phase2_reduce`
  targets the inlined callable's first instruction; the skip-JAL
  (`JAL .x0 +1376`) jumps past the callable to the tail so the
  wrapper doesn't fall through. `evm_addmod_epilogue` is
  **deliberately omitted**: its `ADDI x12, x12, 32` would compound
  the `divK_mod_epilogue`'s own `ADDI x12, x12, 32` inside
  `evm_mod_callable_v4`, over-advancing `x12` by 32 bytes. Net
  advance: 32 (prologue) + 32 (callable) = 64 B (pop 3, push 1).
  Reuses M9's `signedDivModTail` + `mv x14, x10` preBody because
  the inner `JAL .x1` into the callable clobbers `x1`. EXP (0x0a)
  was planned for M10 but deferred — the verified
  `evm_exp_msb_saved_bit_two_mul_fixed` wrapper uses `x6` and `x16`
  as per-limb counter / limb pointer state across `mul_callable`
  calls, but those are LP64 caller-saved registers and
  `mul_callable` clobbers `x6` 39 times per call. The upstream
  "fix" only addresses `x19` (cursor) clobber, not `x6`/`x16`, so
  the bit-test reload logic produces garbage after the first
  squaring. EXP can ship once upstream lands a fully callee-saved
  variant.
- **M11.** ✅ `scripts/codegen-opcodes-runtime-check.sh` exits 0 with
  **34 test cases** PASS (validated 2026-05-26). SHL (0x1b) and SAR
  (0x1d) wired through `singletonHandlers` with the same
  `preBody := "mv x9, x10"` + `x10RestoreAdvance1` pattern as
  SHR/BYTE/MUL/SIGNEXTEND. `tinyInterpRegistry_wired_opcode_count`
  and `jumpTable_non_invalid_count` (Codegen-proofs Phase 1) bumped
  from 91 → 93. MSIZE (0x59) deferred until issue #99 slices 1–5
  wire memory-expansion bookkeeping into `evm_mload` / `evm_mstore` /
  `evm_mstore8`.
- **M12.** ✅ `scripts/codegen-opcodes-runtime-check.sh` exits 0 with
  **37 test cases** PASS (validated 2026-05-26). 13 simple
  environment opcodes (ADDRESS / ORIGIN / CALLER / CALLVALUE /
  GASPRICE / COINBASE / TIMESTAMP / NUMBER / PREVRANDAO / GASLIMIT /
  CHAINID / SELFBALANCE / BASEFEE) wired as new `envHandlers`
  builder. Dispatcher prologue extended with `la x20, evm_env` and
  the data section grows by 416 zero bytes for the 13-slot env
  region. `x20` chosen over `x14` because the M8–M10 handlers all
  clobber `x14` via `preBody := "mv x14, x10"`. Registry-invariants
  counts bumped 93 → 106. Bucket-A coverage drained except MSIZE
  (still gated on issue #99) and BLOBHASH / BLOBBASEFEE (need env
  struct extension).
- **M13.** ✅ `scripts/codegen-opcodes-runtime-check.sh` exits 0 with
  **38 test cases** PASS (validated 2026-05-26). CALLDATASIZE (0x36)
  wired via new `calldataHandlers` builder. Reuses M12's
  `x20 = &evm_env` (the calldata-length cell at offset 424 lives in
  the same env region). `evm_env:` data block bumped from 416 to
  **512 bytes** to cover all `Environment/Layout.lean` field offsets
  up to `returnDataSizeOff = 440` + 8 with slack. Registry-invariants
  counts bumped 106 → 107.
- **M14.** ✅ `scripts/codegen-opcodes-runtime-check.sh` exits 0 with
  **39 test cases** PASS (validated 2026-05-27). JUMPDEST (0x5b)
  wired via new `controlFlowHandlers` builder. Empty-body handler
  (`body := []`) + `.advanceAndRet 1` tail — same emission path as
  `stopHandler`. No dispatcher changes; no new file; no new
  `HandlerTail` variant. Registry-invariants counts bumped 107 →
  108. M15 will extend `controlFlowHandlers` with JUMP / JUMPI / PC.
- **M15.** ✅ `scripts/codegen-opcodes-runtime-check.sh` exits 0 with
  **44 test cases** PASS (validated 2026-05-27). JUMP (0x56),
  JUMPI (0x57), PC (0x58) wired via new verified Programs in
  `EvmAsm/Evm64/ControlFlow/Program.lean` (`evm_pc` 6 instr,
  `evm_jump` 3 instr, `evm_jumpi` 13 instr — the JUMPI body uses
  `BEQ +12` to skip the jump path on cond=0 and `JAL +8` to skip
  the fall-through on cond≠0). Dispatcher prologue gains
  `la x21, evm_code` / `li x21, 0x40000010` — `x21` is the
  preserved code-base register, audited free across all verified
  bodies and existing handlers. JUMP/JUMPI use `.custom "  ret"`
  tails (body writes `x10` directly); PC uses `.advanceAndRet 1`.
  Known limitation: no JUMPDEST-validity check — invalid jumps
  follow garbage. Tracked as the next follow-on slice.
  Registry-invariants counts bumped 108 → 111.
- **Codegen-proofs Phase 1.** ✅ `lake build` exits 0 (validated
  2026-05-21). New file `EvmAsm/Codegen/Proofs/RegistryInvariants.lean`
  carries 6 kernel-checked theorems about `tinyInterpRegistry`:
  `tinyInterpRegistry_opcodes_Nodup` (no two handlers fight for the
  same byte), `tinyInterpRegistry_labels_Nodup` (no duplicate asm
  labels reach the assembler), `tinyInterpRegistry_opcodes_lt_256`
  (every claimed opcode fits in a `lbu`-fetched byte),
  `jumpTargetLabel_well_formed` (every byte 0..255 routes to a
  registered label or to `"h_invalid"`),
  `tinyInterpRegistry_wired_opcode_count` (exactly 91 opcodes wired),
  and `jumpTable_non_invalid_count` (165 of 256 bytes route to
  `h_invalid`). All discharged by `decide`; the two ∀-over-`[0,256)`
  goals need `set_option maxRecDepth 2048`. Compile cost ~11 s; well
  under the 30 s budget set in the roadmap. Drift detection
  validated by manually injecting a duplicate opcode into the
  registry and confirming the build fails (then reverting).
- **Codegen-proofs Phase 4 (first instance).** ✅ `lake build` exits 0
  (validated 2026-05-22). New file
  `EvmAsm/Codegen/Proofs/HandlerSpecs.lean` adds a **reusable
  `cleanRetHandlerSpec` template** plus two concrete instances:
  `evmAddHandlerSpec` (h_ADD, opcode 0x01) and `evmPopHandlerSpec`
  (h_POP, opcode 0x50). The template lifts any verified body spec
  in `cpsTripleWithin` form (e.g. `evm_add_spec_within`,
  `evm_pop_spec_within`) through the dispatcher's
  `body ;; ADDI x10 x10 n ;; JALR x0 x1 0` wrapping, producing a
  handler-subroutine triple where `x10` is advanced by `n` and `x1`
  is frame-preserved. Composes the body spec with primitive
  `addi_spec_same_within` + `ret_spec_within'` lemmas via
  `cpsTripleWithin_seq`. The template's `hBodyLenBound : nSteps < 2^60`
  side condition is trivially `by decide` for every real handler.
  This pattern covers ~70 of the 91 wired handlers (every entry
  with empty `preBody` and `.advanceAndRet n` tail) and is the
  scaffolding for the follow-up Phase 4 PRs that will instantiate
  for SUB / comparisons / bitwise / memory / DUP / SWAP / PUSH
  via the same template (the parameterized DUP/SWAP/PUSH families
  may need a parameterized template variant). Drift detection
  validated by manually corrupting the advance width in one
  instance and confirming the build fails (then reverting).
- **Codegen-proofs Phase 4 expansion — 11 clean singletons.**
  ✅ `lake build` exits 0 (validated 2026-05-22). Extends
  `EvmAsm/Codegen/Proofs/HandlerSpecs.lean` with handler-level
  specs for the 11 remaining clean-shape singleton opcodes:
  `evmSubHandlerSpec` (0x03), `evmLtHandlerSpec` (0x10),
  `evmGtHandlerSpec` (0x11), `evmSltHandlerSpec` (0x12),
  `evmSgtHandlerSpec` (0x13), `evmEqHandlerSpec` (0x14),
  `evmIsZeroHandlerSpec` (0x15), `evmAndHandlerSpec` (0x16),
  `evmOrHandlerSpec` (0x17), `evmXorHandlerSpec` (0x18),
  `evmNotHandlerSpec` (0x19). Each is a 1-call invocation of the
  `cleanRetHandlerSpec` template against the corresponding
  `evm_<op>_spec_within` body spec. Compile cost: ~7 s for all 13
  theorems combined; per-instance overhead negligible. Handler-
  spec coverage now stands at **13 of the 91 wired opcodes** (~14%).
  Follow-up PRs extend to memory handlers (MLOAD/MSTORE/MSTORE8),
  the parameterized PUSH / DUP / SWAP families, and the
  x10-clobber / saved-ra / self-calling variants. Drift detection
  re-validated on SUB.

## Future work (post-M10)

Near-term:

- **EXP (0x0a).** Blocked on upstream: needs an
  `evm_exp_msb_saved_bit_two_mul_fixed_fixed` variant that moves
  the per-limb counter (`x6`) and limb pointer (`x16`) to
  callee-saved registers (e.g. `x20`/`x21`). Once that lands, EXP
  can drop into `selfCallingHandlers` next to ADDMOD using the
  same inline-callable + `signedDivModTail` pattern; the skip-JAL
  offset and `mulOff` / `condMulOff` derivations from this PR's
  preliminary work are recorded in the git history.

Longer-term (genuine new design surface):

- **Codegen-proofs Phases 2–5.** Phase 1 (registry invariants)
  shipped; the rest of the roadmap:
  - **Phase 2:** define `parseInstr : String → Option Instr` and
    prove `parseInstr (emitInstr i) = some i`. Bridges emitted asm
    back to the verified `Program` type so later phases can reason
    about dispatcher prologue / epilogue / tail strings.
  - **Phase 3:** encode the 7-instruction dispatch loop as a
    verified `Program` and prove its `cpsTripleWithin` spec —
    "given `mem[x10] = b` and a handler `h` at jump-table entry `b`,
    control transfers to `h` with `x1` pointing at the loop's
    re-entry point."
  - **Phase 4:** lift each `OpcodeHandlerSpec`'s spec from the body
    alone to `preBody + body + tail` — covers the ~90 wired
    handlers via ~8 templates (PUSH, DUP, SWAP, singleton, memory,
    divModTail, signedDivModTail, self-calling). **13 of 91 wired
    opcodes covered** (ADD, POP, SUB, LT, GT, SLT, SGT, EQ, ISZERO,
    AND, OR, XOR, NOT — all using `cleanRetHandlerSpec`); follow-ups
    extend to memory handlers (MLOAD/MSTORE/MSTORE8), parameterized
    PUSH / DUP / SWAP families, and add `withX10SavePreBody`
    (MUL/SIGNEXTEND/BYTE/SHR), trampoline (SDIV/SMOD), and
    self-calling (ADDMOD) variants.
  - **Phase 5:** end-to-end refinement — for every bytecode `B`,
    the runtime dispatcher's final state matches the EVM
    executable-spec interpreter's final state.
- **JUMP / JUMPI + JUMPDEST table.** Real control flow. Handlers must
  write `x10` directly (the wrapper baking in a fixed advance no longer
  works) and JUMP/JUMPI need to consult a JUMPDEST validity table built
  from the bytecode at codegen time.
- **Lean-native binary encoder** (`Instr → BitVec 32` + ELF writer) to
  drop the GNU binutils dependency. Cross-check the encoded bytes
  against the verified `step` semantics.
- **STF integration**: consume RLP-decoded transactions via `read_input`
  and drive the full interpreter loop.
- **Precompile stubs** aligned with
  `EvmAsm/Evm64/zkvm-standards/standards/c-interface-accelerators`.
- **Cross-zkVM testing** (SP1, RISC0) to validate the halt-convention
  ADR closure described in
  [`docs/host-io-halt-convention.md`](docs/host-io-halt-convention.md).

## References

- [Zisk emulator quickstart](https://0xpolygonhermez.github.io/zisk/getting_started/quickstart.html)
- [Zisk ELF regressions](https://github.com/0xPolygonHermez/zisk/tree/9537bcebe414f3a2a2cbf809b3d1cd09ac1e1b68/elf-regressions)
- [Zisk `simple_add` example](https://github.com/0xPolygonHermez/zisk/blob/pre-develop-0.17.1/elf-regressions/simple_add/test.s)
- [`docs/zkvm-host-io-interface.md`](docs/zkvm-host-io-interface.md) — I/O ABI ADR
- [`docs/host-io-halt-convention.md`](docs/host-io-halt-convention.md) — halt-convention ADR (Open)
- [`docs/zkvm-host-io-input-buffer-design.md`](docs/zkvm-host-io-input-buffer-design.md) — input-buffer design
