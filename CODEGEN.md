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
| `EvmAsm/Codegen/Programs/` | Execution-layer programs supporting the Stateless guest (40+ files): Account / Block / Chain / Header / Mpt / Tx / Receipt / Bloom / RLP read / SSZ / U256 / etc. Plus `Programs/Evm.lean` — the M5b opcode handler registry **`tinyInterpRegistry`** at `Programs/Evm.lean:666`, composed from `pushHandlers` (PUSH0..32), `dupHandlers` (DUP1..16), `swapHandlers` (SWAP1..16), `singletonHandlers` (19 fixed-shape opcodes incl. SHL/SAR from M11), `memoryHandlers` (MLOAD/MSTORE/MSTORE8, M7), `envHandlers` (13 simple environment opcodes ADDRESS/CALLER/.../BASEFEE, M12), `calldataHandlers` (CALLDATASIZE, M13), `controlFlowHandlers` (JUMPDEST from M14; JUMP/JUMPI/PC added in M15), `hashHandlers` (KECCAK256 via ECALL bridge from M16), `logHandlers` (LOG0–LOG4 as stack-pop no-ops, M17), `storageHandlers` (SLOAD/SSTORE/TLOAD/TSTORE as no-op stack ops with empty-storage semantics, M17), `haltHandlers`/`pushZeroHandlers`/`popPushZeroHandlers`/`copyNoopHandlers` (M18 — 20 trivial no-ops covering RETURN/REVERT/INVALID/SELFDESTRUCT + 5 push-zero + 6 pop+push-zero + 5 copy-no-op opcodes; defined in `Programs/Noop.lean`), `childFrameHandlers` (M19 — 6 child-frame opcodes CREATE/CALL/CALLCODE/DELEGATECALL/CREATE2/STATICCALL as pop-N + push-zero no-ops; also in `Programs/Noop.lean`), `arithNoopHandlers` (MULMOD as a pop-N + push-zero no-op; in `Programs/Noop.lean` — EXP graduated to a real body in M27), `divModHandlers` (DIV/MOD, M8), `signedDivModHandlers` (SDIV/SMOD via trampoline, M9), `selfCallingHandlers` (ADDMOD via inline-callable from M10; EXP via inline-callable `_fixed_fixed` body from M27), and `stopHandler`. Total: **149 wired opcodes — 🎯 100% of the 149-byte EVM space**. Also hosts shared helpers (`advancePc`, `copy64`, `evmAddEpilogue`, `evmDivPatched`/`evmModPatched`/`evmSdivPatched`/`evmSmodPatched` for the DIV/MOD/SDIV/SMOD NOP-splice). |
| `EvmAsm/Codegen/Proofs/` | Codegen-proofs scaffolding (post-M10). `RegistryInvariants.lean` (Phase 1) — 6 `decide`-checked theorems about `tinyInterpRegistry`'s structural well-formedness (Nodup on opcodes/labels, byte bounds, jump-table coverage). `HandlerSpecs.lean` (Phase 4) — reusable `cleanRetHandlerSpec` template + **13 concrete handler-level `cpsTripleWithin` instances** for clean-shape singletons (ADD, POP, SUB, LT, GT, SLT, SGT, EQ, ISZERO, AND, OR, XOR, NOT). Phases 2, 3, 5 + the remaining Phase 4 instances are still future work. |
| `EvmAsm/Codegen/Tests/Cases.lean` | Per-opcode regression test registry: `OpcodeTestCase` struct + `opcodeTestCases` list (**59 cases** as of M20). Wraps each bytecode through the M5b dispatcher for end-to-end ziskemu validation. |
| `EvmAsm/Codegen/Cli.lean` | Argument parsing (`--program`, `--test-case`, `--list-test-cases`, `--halt`, `--out`, `--asm-only`). |
| `EvmAsm/Codegen/Driver.lean` | `IO`: shells out to `as`/`ld` if available; `--asm-only` for CI without the cross toolchain. |
| `Main.lean` | Already exists as `import EvmAsm`; extend to call `EvmAsm.Codegen.Cli.main`. |
| `lakefile.toml` | Add `[[lean_exe]] name = "codegen"; root = "Main"; supportInterpreter = true`. |
| `scripts/codegen-*.sh` | Per-milestone round-trip checks: `codegen-smoke.sh` (M0), `codegen-evm_add-check.sh` (M2), `codegen-evm_add-from-input-check.sh` (M4), `codegen-tiny-interp-check.sh` (M5a), `codegen-tiny-interp-dispatch-check.sh` (M5b), `codegen-opcodes-runtime-check.sh` (M8.5 **canonical** runtime-bytecode runner, also reached via compatibility wrapper `codegen-opcodes-check.sh`), `codegen-evm_div-check.sh` / `codegen-evm_div-cases-check.sh` / `codegen-evm_mod-check.sh` / `codegen-evm_mod-cases-check.sh` (standalone DIV/MOD wrappers — also routed through the dispatcher in M8). |
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
- `Driver.lean` adds `-Tdata=0xa0100000` to the link step so writable
  `.data` lands in `ziskemu`'s RAM region (`0xa0000000–0xc0000000`);
  without an explicit RAM address, the emulator refuses the ELF with
  *"writable data section … outside RAM bounds"*. The data base is above
  `OUTPUT_ADDR = 0xa0010000`, so large scratch sections cannot alias the
  public output buffer.
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
The dispatcher's `.data` section starts at `0xa0100000`, deliberately above
the fixed ziskemu public-output page at `0xa0010000`. Earlier milestones kept
`.data` below `OUTPUT_ADDR`; the stateless guest's scratch data now exceeds
that old 64 KiB window, so the link layout reserves the output page instead of
treating it as the upper bound for writable data. Large multi-MiB SSZ scratch
buffers remain in the separate `.sszscratch` section at `0xa2000000`.

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

**MSIZE (0x59) runtime slice.** The dispatcher maintains an
active-memory-size cell in `evm_env` and wires MSIZE to push it as a
low-u64 EVM word. MLOAD, MSTORE, MSTORE8, CALLDATACOPY, and MCOPY
update that cell with 32-byte EVM rounding. This is a concrete
runtime path, not the verified `evm_msize` Program yet, and exact
memory gas / OOG behavior is still deferred.

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
test programs all jump to real JUMPDEST bytes. **Resolved (Level 1)
in M15.5** — the inline `LBU` + `0x5b` check; see that section.

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

### M15.5 — JUMPDEST-validity check (Level 1) — **DONE (2026-06-02)**

Closes the M15 known limitation (JUMP/JUMPI unconditionally followed the
popped destination). A spec-compliant EVM exceptionally halts on a jump to
a non-JUMPDEST byte; this adds that check. Numbered M15.5 (the follow-on the
M15 section + the `ControlFlow/Program.lean` docstring both promised) to avoid
colliding with the M26–M29 numbers reserved for the stateless-track roadmap.

**Scope — Level 1 (`code[dest] == 0x5b` byte check).** Rejects jumps to any
non-JUMPDEST byte. **Level 2 (deferred):** a `0x5b` inside PUSH immediate data
is still wrongly accepted; full compliance needs a pushdata-aware
valid-jumpdest bitmap built by scanning the bytecode at dispatch entry — a
separate, larger slice. Level 1 already eliminates the dangerous
"follow garbage past the bytecode into `.data`" cases.

**Dual-use.** The byte *load* lives in the verified `evm_jump`/`evm_jumpi`
bodies, so the stateless guest's VM (which is designed to plug in these
bodies) inherits it; only the host-specific halt *routing* is in the codegen
handler tail.

**Delivered:**
- **`EvmAsm/Evm64/ControlFlow/Program.lean`** — `evm_jump` (3→4 instr) and
  `evm_jumpi` (13→15 instr) gain a `validityReg` parameter. `evm_jump` appends
  `LBU validityReg, 0(x10)` (load `code[dest]`). `evm_jumpi` loads `code[dest]`
  on the *taken* path and writes the sentinel `0x5b` into `validityReg` on the
  *not-taken* path (so the downstream check is a no-op for fall-through); the
  two internal offsets are re-pinned (`BEQ` 12→16, `JAL` 8→12). No specs to
  update — these bodies have no `cpsTriple` proofs yet.
- **`EvmAsm/Codegen/Programs/Evm.lean`** — `controlFlowHandlers` passes `.x17`
  as `validityReg` and swaps JUMP/JUMPI's `.custom "  ret"` tails for the
  shared `jumpValidityTail` (`li x18, 0x5b ; bne x17, x18, .exit_invalid ;
  ret`). `x17`/`x18` are free scratch.
- **`EvmAsm/Codegen/Dispatch.lean`** — `emitDispatcherEpilogue` gains an
  `.exit_invalid:` label that zero-fills `OUTPUT[0..32]` and tags
  `halt_kind = 4` (distinct from 0=STOP / 1=RETURN / 2=REVERT, M23) then joins
  `.exit_no_epilogue`. Reached only via `j .exit_invalid`; placed so it never
  falls through into `exitBody`.
- **`EvmAsm/Codegen/Tests/Cases.lean`** — `jump_invalid_dest` (`PUSH1 0x00;
  JUMP` → `code[0]=0x60≠0x5b`) and `jumpi_taken_invalid` (taken JUMPI to byte 0)
  both assert `halt_kind = 4` + zero result; `jumpi_not_taken` gains a
  `halt_kind = 0` assertion confirming the sentinel path doesn't spuriously
  halt. Existing `jump_forward` / `jumpi_taken` (which jump to real JUMPDEST
  bytes) still pass. Total cases 82 → 85.

**Known limitations:** Level 2 (pushdata-aware bitmap) deferred. 256-bit `dest`
still truncated to its low 64 bits (M15 caveat, unchanged). `RegistryInvariants`
counts unchanged (149 — JUMP/JUMPI stay in `controlFlowHandlers`).

**Exit criteria (met).**
`scripts/codegen-opcodes-runtime-check.sh` exits 0 with all **85 cases PASS**
(82 prior + `jump_invalid_dest` + `jumpi_taken_invalid` + the `jumpi_not_taken`
halt-kind assertion). `scripts/check-progress.sh` exits 0. `lake build
EvmAsm.Codegen` clean.

### M16 — KECCAK256 via ECALL bridge (first precompile pattern) — **DONE (2026-05-27)**

First opcode that uses a host syscall / accelerator bridge instead
of an inline verified RV64 body. Wires **KECCAK256 (0x20)** through
a new `hashHandlers` builder that pops `offset` + `size` from the
EVM stack, calls the Zisk-accelerated keccak subroutine
(`zkvm_keccak256` in `EvmAsm/Codegen/Programs/HashBridge.lean`),
and pushes the 32-byte digest. Lifts wired count **111 → 112**
(75% of the 149-byte EVM space). Establishes the ECALL bridge
pattern that LOG0-4, SLOAD, SSTORE, and the precompile family
(ECRECOVER, SHA256, MODEXP, etc.) will reuse.

**Delivered:**

- **`EvmAsm/Codegen/Dispatch.lean`** — multiple additions:
  - Epilogue inserts `zkvmKeccak256Function` (the full ~76-line
    sponge-mode subroutine that wraps Zisk's
    `csrs 0x800, a0` accelerator at `.4byte 0x80052073`)
    **between the handler subroutines and `h_invalid:`** — so
    it's only reachable via `jal x1, zkvm_keccak256`, never via
    fall-through from exitBody.
  - Data section gains a 200-byte `zk3_state:` block (the 25 × u64
    keccak permutation state buffer).
  - Data section also gains a 512-byte `lp64_stack:` block ending
    with `lp64_sp_top:` — the keccak subroutine does `addi sp, sp,
    -32` to save its callee-saved regs, and the dispatcher had
    never initialised `sp` before M16.
  - Both prologue variants gain `la sp, lp64_sp_top` as the
    first instruction.
  - Imports `EvmAsm.Codegen.Programs.HashBridge`.
- **`EvmAsm/Codegen/Programs/Evm.lean`** — new `hashHandlers`
  list with one entry. The handler is **all raw asm** (no verified
  body; `Instr` has no CSRS variant): `body := []`, `tail :=
  .custom "..."`. The tail saves `x10`→`s10` and `x12`→`s11`,
  pops `offset`/`size` from the EVM stack, allocates a result slot
  (net stack delta +32), sets up `a0`/`a1`/`a2` as keccak args,
  `jal x1, zkvm_keccak256`, restores `x10`/`x12`, advances PC by
  1, `j .dispatch_loop` (NOT `ret` — `jal x1` clobbered `x1`).
- **`EvmAsm/Codegen/Tests/Cases.lean`** — one new case
  `keccak256_empty` (bytecode `0x60 0x00 0x60 0x00 0x20 0x00`:
  PUSH1 0; PUSH1 0; KECCAK256; STOP). Hash of empty bytes; expected
  `c5d246…5a470`. Total cases 44 → 45.
- **`EvmAsm/Codegen/Proofs/RegistryInvariants.lean`** — counts
  bumped 111 → 112.

**ECALL bridge pattern (template for M17+):**

1. Promote a `zkvm_*Function : String` (raw asm) from
   `HashBridge.lean` or a sibling file into the dispatcher epilogue
   so the label is reachable via `jal x1, …`.
2. Allocate any required scratch buffer in the dispatcher data
   section (mirrors `zk3_state`).
3. Handler tail saves dispatcher state (x10, x12) to callee-saved
   regs (s10, s11), pops EVM stack into a0/a1/a2 (LP64 args), calls
   the subroutine, restores state, advances PC, returns via
   `j .dispatch_loop`.

**Exit criteria (met).**
`scripts/codegen-opcodes-runtime-check.sh` exits 0 with all 45
cases PASS. `scripts/check-progress.sh` exits 0. Legacy
`scripts/codegen-opcodes-check.sh` also exits 0. Pre-existing
scripts unchanged.

### M17 — LOG0–LOG4 + SLOAD/SSTORE/TLOAD/TSTORE as stack-pop no-ops — **DONE (2026-05-27)**

Bundles two opcode families that share the same "no host syscall
available → stack-pop no-op" shape. Lifts wired count
**112 → 121** (81% of the 149-byte EVM space). 9 new opcodes in
one PR, all with trivial 1–4 instruction bodies + the standard
`.advanceAndRet 1` tail.

**Why no-ops.** Zisk's `zkvm_accelerators.h` has no log or storage
syscall, so an M16-style ECALL bridge has nowhere to call.
Spec-compliant log emission and persistent storage are deferred
until the host gains the relevant syscalls. Until then, LOG
events are dropped and storage always reads 0.

**Delivered:**

- **`EvmAsm/Codegen/Programs/Evm.lean`** — two new `*Handlers`
  builders adjacent to `hashHandlers`:
  - `logHandlers` (5 entries, LOG0–LOG4). Each handler's body is
    `ADDI .x12 .x12 (BitVec.ofNat 12 ((2+n)*32))` — pops the right
    number of 256-bit words for the LOGn variant (64, 96, 128,
    160, 192 bytes). Standard `.advanceAndRet 1` tail.
  - `storageHandlers` (4 entries: SLOAD, SSTORE, TLOAD, TSTORE).
    SLOAD/TLOAD overwrite the popped key with 32 zero bytes via 4 ×
    `SD .x12 .x0 …` (net stack delta 0). SSTORE/TSTORE pop both
    inputs via `ADDI .x12 .x12 64`. All use `.advanceAndRet 1`.
  - Both builders inserted into `tinyInterpRegistry` between
    `hashHandlers` and `divModHandlers`.
- **`EvmAsm/Codegen/Tests/Cases.lean`** — four new cases:
  - `log0_pop`: PUSH×2 + LOG0 + PUSH 0x33 + STOP → 0x33 (confirms
    LOG0 pops 2 words).
  - `log4_pop`: PUSH×6 + LOG4 + PUSH 0xff + STOP → 0xff (confirms
    LOG4 pops 6 words).
  - `sstore_sload_roundtrip`: SSTORE then SLOAD with key=0,
    value=0x42 → returns 0x00 (confirms the **no-op limitation** —
    spec-compliant EVM would return 0x42).
  - `tstore_tload_roundtrip`: same shape but for transient storage.
- **`EvmAsm/Codegen/Proofs/RegistryInvariants.lean`** — counts
  bumped 112 → 121.

**Known limitations** (all spec-incompliances that trusted test
programs avoid):
- LOG events are dropped (no receipt log list).
- Storage always reads 0; writes are dropped. Affects programs
  that depend on storage persistence within a transaction.
- No memory expansion costs for LOG's offset/size inputs (same
  caveat as M15's JUMP/JUMPI: trust the program).

**Exit criteria (met).**
`scripts/codegen-opcodes-runtime-check.sh` exits 0 with all 49
cases PASS. `scripts/check-progress.sh` exits 0. Legacy
`scripts/codegen-opcodes-check.sh` also exits 0. Pre-existing
scripts unchanged.

### M18 — Drain remaining trivial handlers (94.6% milestone) — **DONE (2026-05-27)**

The biggest opcode-count jump since M6b. Bundles **20 trivial
no-op handlers** in one PR across four new builders. Lifts wired
opcode count **121 → 141 (94.6% of the 149-byte EVM space)**.
Crosses the **90% coverage milestone** (135/149) and reaches
94.6%. The only remaining unwired opcodes are MULMOD (needs
verified body), EXP (blocked upstream), and the **6 child-frame
opcodes** (CALL/CREATE family — the real gap to 100%).

**Why no-ops.** Each of the remaining 16 opcodes ships with at least one
spec-incompliance because the dispatcher has no model for the
relevant state (accounts, calldata, block history, blob context,
return-data buffers). Trusted bytecode that doesn't depend on
these subsystems passes through correctly.

**Delivered:** Four new `*Handlers` builders, lifted into the
new file `EvmAsm/Codegen/Programs/Noop.lean` per the file-size
guardrail at the bottom of `Programs.lean`:

- **`haltHandlers` (4 entries)**: RETURN (0xf3), REVERT (0xfd),
  INVALID (0xfe), SELFDESTRUCT (0xff). `body := []` + `.custom`
  tail that inlines the right `addi x12, x12, …` pop and
  `j .exit_label`.
- **`pushZeroHandlers` (4 entries)**: CODESIZE (0x38),
  RETURNDATASIZE (0x3d), BLOBBASEFEE (0x4a), GAS (0x5a).
  5-instruction body: decrement `x12` by 32 (push), then
  4 × `SD .x12 .x0 …` (zero limbs).
- **`popPushZeroHandlers` (5 entries)**: BALANCE (0x31),
  EXTCODESIZE (0x3b), EXTCODEHASH (0x3f), BLOCKHASH (0x40),
  BLOBHASH (0x49). Same shape as M17 SLOAD:
  net stack delta 0; 4 × `SD .x12 .x0 …` overwrites the popped
  slot with zeros.
- **`copyNoopHandlers` (3 entries)**: CODECOPY (0x39),
  EXTCODECOPY (0x3c), RETURNDATACOPY (0x3e). 1-instruction body:
  `ADDI .x12 .x12 96` (or 128 for EXTCODECOPY's 4-pop). CALLDATACOPY
  and MCOPY have since moved to concrete runtime handlers.

`EvmAsm/Codegen/Proofs/RegistryInvariants.lean` counts bumped
121 → 141. All 6 invariant theorems now use `set_option
maxRecDepth 2048 in decide` (3 of the 6 previously used plain
`decide` which began tripping the recursion limit at 141
entries). Phase 1 recompile ~16 s, well under the 30 s budget.

`EvmAsm/Codegen/Tests/Cases.lean` adds 5 representative cases
(one per builder + INVALID smoke): `return_pop2_halt`,
`invalid_halt`, `gas_push_zero`, `balance_pop_push_zero`,
`mcopy_pop3`. Total 49 → 54.

**Known limitations** (documented per-builder in
`Programs/Noop.lean`):
- BALANCE / EXTCODESIZE / EXTCODEHASH / BLOCKHASH / BLOBHASH
  always return 0 (no account / block-history / blob-context
  state).
- CALLDATALOAD / CALLDATACOPY read empty calldata.
- CODESIZE / CODECOPY / RETURNDATASIZE / RETURNDATACOPY /
  EXTCODECOPY return / copy zero data.
- BLOBBASEFEE / GAS always 0.
- RETURN / REVERT halt with whatever's at EVM stack top after
  the pop (deterministic if the program pre-pushes a known
  value).
- SELFDESTRUCT doesn't actually destroy the account.
- INVALID is identical to the `h_invalid` catch-all but listed
  explicitly so the registry count reflects deliberate wiring.

**Exit criteria (met).**
`scripts/codegen-opcodes-runtime-check.sh` exits 0 with all 54
cases PASS. `scripts/check-progress.sh` exits 0. Legacy
`scripts/codegen-opcodes-check.sh` also exits 0. Pre-existing
scripts unchanged.

### M19 — Wire 6 child-frame opcodes as no-ops (98.7% milestone) — **DONE (2026-05-27)**

Extends M18 with one more no-op builder, `childFrameHandlers`, in
the existing `EvmAsm/Codegen/Programs/Noop.lean`. Wires the 6
child-frame opcodes (**CREATE 0xf0**, **CALL 0xf1**, **CALLCODE
0xf2**, **DELEGATECALL 0xf4**, **CREATE2 0xf5**, **STATICCALL
0xfa**) as **pop-N + push-zero no-ops**. Lifts wired count
**141 → 147 (98.7%)**. **Crosses the 95% coverage milestone**
(143) along the way. After M19 the only remaining unwired opcodes
are MULMOD (needs verified body) and EXP (blocked upstream).

**Why no-ops.** The 6 child-frame opcodes don't actually require
a "large multi-PR design surface" when shipped as no-ops — they
all fit the same shape as M18's `popPushZeroHandlers`, just with
bigger pop counts. Push 0 = "call failed" / "create returned
address 0", which is spec-compliant for trusted bytecode that
handles call-failure paths (the common ISZERO + JUMPI pattern).
A future PR can replace these with real sub-frame execution once
the frame-stack design lands (likely tied to STF integration).

**Delivered:** new `childFrameHandlers` builder in
`Programs/Noop.lean`. Uses a 4-arg `mkHandler` helper to
factor out the boilerplate, then six `mkHandler` calls — one per
child-frame opcode with its net-pop byte count.

| Opcode | Byte | Pops | Net pops × 32 |
|---|---|---|---|
| CREATE | 0xf0 | 3 | 64 |
| CALL | 0xf1 | 7 | 192 |
| CALLCODE | 0xf2 | 7 | 192 |
| DELEGATECALL | 0xf4 | 6 | 160 |
| CREATE2 | 0xf5 | 4 | 96 |
| STATICCALL | 0xfa | 6 | 160 |

Body (5 instructions per entry): `ADDI .x12 .x12 (netPopBytes)`
+ 4 × `SD .x12 .x0 …` (zero the new top slot). Standard
`.advanceAndRet 1` tail.

`EvmAsm/Codegen/Proofs/RegistryInvariants.lean` counts bumped
141 → 147. Phase 1 `decide` recompile ~20 s (under the 30 s
budget; `maxRecDepth 2048` already set across all 6 theorems
from M18).

Three representative test cases added (54 → 57):
`create_pop3_push_zero` (smallest net pop = 2),
`call_pop7_push_zero` (largest = 6),
`staticcall_pop6_push_zero` (mid = 5). The three cover the
distinct ADDI immediates (64, 192, 160); DELEGATECALL/CALLCODE/
CREATE2 share net pops with the tested opcodes.

**Known limitations** (documented in `Programs/Noop.lean`):
- **CALL / CALLCODE / DELEGATECALL / STATICCALL**: always return
  0 (= "call failed"). No actual sub-frame execution; no
  return-data buffer.
- **CREATE / CREATE2**: always return address 0 (= "deployment
  failed"). The would-be deployed code is not executed.
- **No frame stack / recursion**. The dispatcher doesn't push a
  sub-frame, run called code, and resume. Real frame-stack
  design deferred (likely tied to STF integration).
- **GASLEFT-style calculations** for CALL's gas arg not modelled
  (GAS itself is a push-zero no-op from M18).

Trusted bytecode that handles call-failure paths via
`ISZERO + JUMPI` (the standard revert-on-error pattern)
continues to work correctly.

**Exit criteria (met).**
`scripts/codegen-opcodes-runtime-check.sh` exits 0 with all 57
cases PASS. `scripts/check-progress.sh` exits 0. Legacy
`scripts/codegen-opcodes-check.sh` also exits 0. Pre-existing
scripts unchanged.

### M20 — Wire MULMOD + EXP as no-ops — **🎯 100% OPCODE COVERAGE** (DONE 2026-05-27)

The 100% coverage milestone PR. Wires the last two unwired
opcodes — **MULMOD (0x09)** and **EXP (0x0a)** — as no-ops via a
new `arithNoopHandlers` builder in
`EvmAsm/Codegen/Programs/Noop.lean`. Lifts wired count
**147 → 149 (100%)**. **Every EVM byte-code now routes through
a `tinyInterpRegistry` handler instead of `h_invalid`.**

**Why no-ops for these two:**
- **MULMOD**: the verified body is still a placeholder in
  `EvmAsm/Evm64/MulMod/Program.lean` (slice evm-asm-m4wu is
  unscheduled). No real body to wire.
- **EXP**: the verified body
  `evm_exp_msb_saved_bit_two_mul_fixed` actually exists in
  `EvmAsm/Evm64/Exp/Program.lean` (x19-callee-saved cursor
  design, 84 instructions, fully proven). The M10 "upstream
  blocker" doc note was stale. Wiring it requires ~300–500 LOC
  of M10-style inline-callable composition (embed
  `mul_callable` in the dispatcher epilogue, pin JAL offsets
  for the squaring + cond-multiply calls, use M9-style
  trampoline tail). M21 (the next planned PR) will do that
  upgrade.

**Delivered:**

- **`EvmAsm/Codegen/Programs/Noop.lean`** — new `arithNoopHandlers`
  builder adjacent to `childFrameHandlers`:

  | Opcode | Byte | Pops | Pushes | Net pops × 32 |
  |---|---|---|---|---|
  | MULMOD | 0x09 | 3 (a, b, N) | 1 | 64 |
  | EXP    | 0x0a | 2 (base, exp) | 1 | 32 |

  Same 5-instruction body shape (`ADDI .x12 .x12 N` + 4 × SD)
  as the rest of the M17/M18/M19 no-op family.

- **`EvmAsm/Codegen/Proofs/RegistryInvariants.lean`** — counts
  bumped 147 → 149. Phase 1 `decide` recompile ~20 s (under
  the 30 s budget; `maxRecDepth 2048` already set from M18).
  **Every byte 0..255 now either routes to a registered handler
  (149 bytes) or falls through to `h_invalid` (107 bytes —
  bytes never assigned a real opcode by the EVM spec).**

- **`EvmAsm/Codegen/Tests/Cases.lean`** — two new cases
  (`mulmod_pop3`, `exp_pop2`) confirming dispatch and net-pop
  arithmetic. Total cases: 57 → 59.

**Known limitations** (documented in `Programs/Noop.lean`):

- **MULMOD** always returns 0. Future upgrade: real body
  (Knuth-style 512-bit intermediate + reduce-by-N using the
  existing div/mod callables) when slice evm-asm-m4wu lands.
- **EXP** always returns 0. M21 = real body wiring (the
  verified body exists; just needs M10-style inline-callable
  wiring).

Trusted bytecode that doesn't depend on MULMOD/EXP results
continues to work correctly.

**Coverage trajectory (final):**

- M11–M16: 91 → 112 (75.2%)
- M17: 121 (81%)
- M18: 141 (94.6%) ✅ crosses 90%
- M19: 147 (98.7%) ✅ crosses 95%
- **M20: 149 (100%) 🎯**

**Exit criteria (met).**
`scripts/codegen-opcodes-runtime-check.sh` exits 0 with all 59
cases PASS. `scripts/check-progress.sh` exits 0. Legacy
`scripts/codegen-opcodes-check.sh` also exits 0. Pre-existing
scripts unchanged.

### M21 — Real calldata wiring (first step on the EEST path) — **DONE (2026-05-27)**

The first PR after the 100% coverage milestone, deliberately
pivoting the track from "wire opcodes" to "run real test
suites". M21 picks the cheapest first step on the EEST
(Ethereum Execution Spec Tests) ladder: **real calldata**.
CALLDATALOAD (0x35) and CALLDATACOPY (0x37) graduate from
M18 no-ops to real semantics; CALLDATASIZE (0x36) — already
wired in M13 against an unpopulated env cell — now reads a
real length. All three opcodes now read bytes from the
`ziskemu -i` input file, extending its layout to carry
calldata alongside bytecode.

**The strategic case for calldata first:** every EVM contract
is called *with* calldata, so most pure-computation EEST
fixtures exercise this path. Calldata is also mechanically
trivial — extend the input format, add a dispatcher-prologue
preamble that populates two env cells, point the existing
verified bodies at the env cells. No new design surface
(storage, witnesses, harness) is touched. After M21, the
dispatcher can run any single-contract pure-computation
bytecode given (bytecode, calldata). M22+ adds storage,
state-witness unpacking, the post-state serializer, and the
EEST fixture loader.

**Delivered:**

- **`scripts/pack-bytecode.py`** — gains a `--calldata
  <hex-string>` flag. The packed input layout extends from
  one length-prefixed segment to two:

  ```
  bytes 0..8       <8B LE u64 bytecode length>
  bytes 8..        <bytecode bytes><zero pad to 8B>
  next 8 bytes     <8B LE u64 calldata length>
  following        <calldata bytes><zero pad to 8B>
  ```

  Calldata accepts either CSV form (`0x60, 0x42`) or a hex
  blob (`0xdeadbeef`). Empty calldata produces a zero-length
  calldata segment — pre-M21 callers that omit `--calldata`
  see exactly the M17 no-op behavior (CALLDATASIZE returns 0).

- **`EvmAsm/Codegen/Dispatch.lean`** — both dispatcher
  prologues populate `env.callDataPtrOff (416)` and
  `env.callDataLenOff (424)`:
  - **`emitRuntimeDispatcherPrologue`** (runtime-bytecode
    path used by the M8.5 runner): 10 new instructions
    compute the calldata segment's start address from the
    bytecode-length cell at `INPUT_ADDR+8`, round up to an
    8-byte boundary, load the 8-byte calldata length, and
    write the pointer + length into the env region.
  - **`emitDispatcherPrologue`** (legacy .data-baked path):
    points `callDataPtrOff` at `evm_memory` (a safe zero
    region) and writes 0 to `callDataLenOff`. This preserves
    pre-M21 behavior for the 7 legacy programs that don't
    take a `-i` input file.

- **`EvmAsm/Codegen/Programs/Evm.lean`** —
  `calldataHandlers` grows from 1 to 3 entries:

  | Opcode | Byte | Body | Notes |
  |---|---|---|---|
  | CALLDATASIZE | 0x36 | `evm_calldatasize` (M13) | env cell now populated |
  | CALLDATALOAD | 0x35 | `evm_calldataload_window` | preBody loads `cdp` from env into x14 |
  | CALLDATACOPY | 0x37 | `evm_calldatacopy` | reads `cdp`/`len` from env directly |

  Both new bodies are verified Programs already shipped in
  `EvmAsm/Evm64/Calldata/{LoadProgram,CopyProgram}.lean`.
  M21 only wires them; no body changes.

- **`EvmAsm/Codegen/Programs/Noop.lean`** — removes
  CALLDATALOAD from `popPushZeroHandlers` and CALLDATACOPY
  from `copyNoopHandlers`. Registry size unchanged (149 —
  same opcodes, different builders).

- **`EvmAsm/Codegen/Tests/Cases.lean`** —
  `OpcodeTestCase` gains an optional `calldata : String :=
  ""` field. 3 new cases (`calldatasize_with_input`,
  `calldataload_basic`, `calldatacopy_basic`) confirm
  end-to-end wiring; the 59 pre-M21 cases default to empty
  calldata and remain green. Total cases: 59 → 62.

- **`EvmAsm/Codegen/Cli.lean`** — `--list-test-cases` emits a
  4-column TSV (`name\thex\tbytecode\tcalldata`).

- **`scripts/codegen-opcodes-runtime-check.sh`** — reads the
  4th TSV column and passes it through to
  `pack-bytecode.py --calldata` when non-empty.

**Known limitations** (documented in the handler builders):

- **CALLDATALOAD** is in-bounds only. Reads past
  `cdp + callDataLen` yield whatever's in adjacent memory
  (typically zeros from the input region's padding, but
  formally undefined). A future PR can wrap with an outer
  bounds-check / zero-pad block. Trusted programs that
  respect bounds work correctly.
- **CALLDATACOPY** correctly zero-fills source bytes outside
  the calldata window (handled by the verified body's
  byte-loop bounds check). The destination side is
  unbounded — copies into very-large memory offsets are
  governed by the same caveats as MSTORE.

**Exit criteria (met).**
`scripts/codegen-opcodes-runtime-check.sh` exits 0 with all
**62 cases PASS** (59 pre-M21 + 3 new). The 59 pre-M21 cases
pass empty calldata and continue to work unchanged.
`scripts/check-progress.sh` exits 0. Build clean
(`lake build EvmAsm.Codegen` exits 0).

### M22 — Real storage (SLOAD/SSTORE) via pre-loaded slot table — **DONE (2026-05-28)**

Next step on the EEST ladder after M21 real calldata. SLOAD
(0x54) and SSTORE (0x55) graduate from M17 no-ops to real
persistent storage via a **pre-loaded slot table** extension
to the `ziskemu -i` input format. TLOAD (0x5c) and TSTORE
(0x5d) remain M17 no-ops (transient storage is per-tx scoped
and orthogonal; deferred).

**Architecture (pre-loaded slot table, not in-dispatcher hash):**
state arrives via a third length-prefixed segment in the input
file, alongside the M21 bytecode and calldata segments. The
dispatcher prologue copies it into a writable `.data` region
(`evm_slot_table`, 16 KiB = 256 slots × 64 bytes) and records
the count at `env.slotTableCountOff = 448`. SLOAD / SSTORE
inline-asm bodies scan the table linearly. State leaves the
dispatcher only via stack values that SLOAD pushes back — the
M22 ABI surface is "read your own writes within a tx"; full
post-state serialization is M24's job.

**Why pre-loaded over in-dispatcher hash table:** keeps the
dispatcher stateless across invocations (a fresh ELF run with
no input still produces the same `.data` initial conditions),
matches a witness-style flow without committing to a specific
witness format, and isolates the storage-architecture choice
from the dispatcher's opcode-table machinery.

**Delivered:**

- **`scripts/pack-bytecode.py`** — new `--storage <hex>` flag.
  Format: parenthesized hex pairs `"(0xKEY, 0xVAL) (0xKEY2,
  0xVAL2)"`. Each key / value is interpreted as a u256
  integer and serialized in EVM-stack byte order (the LE
  limb order PUSH32 + SSTORE deposits on the stack). Empty
  default appends `slot_count = 0` and zero-byte slot data,
  preserving pre-M22 input bytes.

  Input layout grows to:
  ```
  <u64 bytecode-len><bytecode><pad>
  <u64 calldata-len><calldata><pad>
  <u64 slot_count><slot_count × 64B (key, value)><pad>
  ```

- **`EvmAsm/Codegen/Dispatch.lean`** —
  - `emitRuntimeDispatcherPrologue` gains ~20 instructions:
    compute slot-segment start past the calldata pad, read
    `slot_count`, dword-loop-copy bytes into `evm_slot_table`,
    write count to env+448.
  - `emitDispatcherPrologue` (.data-baked path) writes 0 to
    env+448 (no input).
  - Both `.data` sections now declare `evm_slot_table: .zero
    0x4000` (16 KiB). The block sits between `evm_env` and
    `zk3_state`; the total `.data` footprint goes from
    ~36 KiB to ~52 KiB, well under the ~64 KiB cap before
    `OUTPUT_ADDR = 0xa0010000`.

- **`EvmAsm/Evm64/Environment/Layout.lean`** — adds
  `slotTableCountOff : Nat := 448`. Bumps `envSize` 448 → 456
  and extends the `envSize_covers` `decide` chain through the
  new cell. `envCells` in `Environment/Assertion.lean` bumped
  56 → 57.

- **`EvmAsm/Codegen/Programs/Storage.lean`** — **NEW
  submodule**. The M22 inline-asm scan loops pushed
  `Programs/Evm.lean` past the per-file size cap, so the
  `storageHandlers` cluster moves into its own file
  (mirrors the M18 `Noop.lean` extraction). Real SLOAD /
  SSTORE bodies use GNU AS numeric local labels (`1:`,
  `1b`, `1f`, …) which are unique-per-use across the
  emitted file, so SLOAD and SSTORE can reuse the same
  label numbers without colliding. TLOAD / TSTORE entries
  carry over as M17 no-ops.

- **`EvmAsm/Codegen/Programs/Evm.lean`** — adds
  `import EvmAsm.Codegen.Programs.Storage`; the inline
  `storageHandlers` def is removed (now sourced from the
  new submodule).

- **`EvmAsm/Codegen/Tests/Cases.lean`** + `Cli.lean` +
  bash runner — `OpcodeTestCase` gains an optional
  `storage : String := ""` field. `--list-test-cases` emits
  a 5-column TSV; runner uses `cut -f` per-field (POSIX
  `read -r` with `IFS=$'\t'` collapses adjacent tab
  separators because tab is IFS-whitespace, silently
  shifting the storage column into the calldata slot when
  calldata is empty — `cut` preserves empty fields).

  4 new test cases:
  - `sstore_then_sload_round_trip` — store, read back.
  - `sload_preloaded_match` — read a preloaded slot.
  - `sload_preloaded_no_match` — read an absent slot → 0.
  - `sstore_overwrites_preload` — overwrite a preloaded
    slot in place (does not append).

  The pre-M22 `sstore_sload_roundtrip` test (M17-era,
  asserted no-op behavior) was removed — it's redundant
  with the new `sstore_then_sload_round_trip` (same
  bytecode) and its expected value of 0 is now wrong
  under M22 real semantics.

  Total cases: **62 → 65** (-1 redundant + 4 new).

**Inline-asm scan loops (illustrative SLOAD body):**

```
h_SLOAD:
  ld   x15, 448(x20)       # x15 = slot_count
  la   x14, evm_slot_table # x14 = base
  beqz x15, 2f             # empty → zero result
1: # scan loop iteration
  ld   x16, 0(x14); ld x17, 0(x12); bne x16, x17, 3f
  ld   x16, 8(x14); ld x17, 8(x12); bne x16, x17, 3f
  ld   x16, 16(x14); ld x17, 16(x12); bne x16, x17, 3f
  ld   x16, 24(x14); ld x17, 24(x12); bne x16, x17, 3f
  # match: copy value into stack top, jump to tail
  ld   x16, 32(x14); sd x16, 0(x12)
  ld   x16, 40(x14); sd x16, 8(x12)
  ld   x16, 48(x14); sd x16, 16(x12)
  ld   x16, 56(x14); sd x16, 24(x12)
  j    4f
3: # no match this entry — advance
  addi x14, x14, 64
  addi x15, x15, -1
  bnez x15, 1b
2: # no match anywhere — write zeros
  sd x0, 0(x12); sd x0, 8(x12); sd x0, 16(x12); sd x0, 24(x12)
4: # tail
  addi x10, x10, 1
  ret
```

**Known limitations:**

- **Capacity cap**: 256 slots. Programs that touch more keys
  overflow the `.data` block; a future PR can grow the table
  or swap in a hash-table backend.
- **Linear scan**: O(slot_count) per access. Fine for tests
  (<10 slots typical); a bottleneck for proving real blocks.
  Hash upgrade ships without ABI / env changes.
- **TLOAD / TSTORE remain no-ops**: transient storage uses a
  separate per-tx-scoped table; future PR.
- **No gas accounting** for SLOAD / SSTORE: M22 doesn't touch
  gas (still absent across the dispatcher).
- **No post-state surfacing**: modified slots are visible to
  in-tx SLOADs but not emitted at `OUTPUT_ADDR+32..`. M24's
  job in the original roadmap.
- **Inline asm, not verified body**: the scan loop is loop-
  based and would need a verified-loop pattern. M22 ships
  correct asm with comprehensive tests; verified bodies
  follow in a separate PR.

**Exit criteria (met).**
`scripts/codegen-opcodes-runtime-check.sh` exits 0 with all
**65 cases PASS** (61 pre-M22 + 4 new; one pre-M22 case
removed as redundant). `scripts/check-progress.sh` exits 0.
Build clean (`lake build EvmAsm.Codegen` exits 0).

### M23 — Real RETURN/REVERT with returndata buffer + halt-kind status — **DONE (2026-05-28)**

After M22 shipped real SLOAD/SSTORE, issue **#7130 ("Decide on
memory layout of storage")** flagged that M22's slot-table is
the **first version** of storage and will be redesigned soon
to handle arbitrary 256-bit addresses and align with the EVM
gas model. The original M23 (pre-state witness unpacking) and
M24 (post-state serializer) both bake in M22's specific layout,
so picking either as the next PR would risk burning work that
gets thrown away when #7130 lands.

M23 therefore pivots to a **storage-orthogonal** milestone:
real RETURN (0xf3) and REVERT (0xfd). These graduate from M18
halt no-ops to real bodies that surface the returndata at
`OUTPUT_ADDR` and tag the halt kind so external callers (and
EEST tests) can distinguish successful return from revert.
Zero coupling to the M22 slot table — survives #7130 redesign
untouched.

### OUTPUT layout extension (post-M23)

```
OUTPUT_ADDR (0xa0010000):
  +0..32    <32 bytes of result>
              STOP            → first 32 bytes of EVM stack top (unchanged)
              RETURN / REVERT → first min(size, 32) bytes of
                                memory[offset..], zero-padded if size < 32
  +32..40   <u64 LE halt_kind>
              0 = STOP / unspecified (set by evmAddEpilogue)
              1 = RETURN
              2 = REVERT
              3 = INVALID (0xfe)            — M23.5
              4 = invalid JUMP/JUMPI dest   — M15.5
              5 = SELFDESTRUCT (0xff)       — M23.5
              6 = out-of-gas                — M30
              (M23 originally left INVALID/SELFDESTRUCT at 0; M15.5 added
               4, M23.5 added 3/5, M30 added 6 — all distinct.)
  +40..256  <unused, room for future surfaces>
```

The 256-byte ziskemu output region has plenty of room past
byte 40 for future extensions (returndata-length prefix,
modified-slot list, etc.).

### The new `.exit_no_epilogue` exit path

`evmAddEpilogue` (the existing exit body emitted at
`.exit_label`) copies 32 bytes from the EVM stack top to
`OUTPUT_ADDR[0..32]`. For STOP that's correct. For RETURN /
REVERT we want the **returndata** at `OUTPUT_ADDR[0..32]`
instead — running `evmAddEpilogue` afterward would clobber
it.

M23 adds a new label `.exit_no_epilogue:` between
`emitProgram exitBody` and the halt stub in
`emitDispatcherEpilogue`. RETURN / REVERT handler tails do
their own OUTPUT writes and `j .exit_no_epilogue` to skip
the epilogue. STOP, INVALID, and SELFDESTRUCT continue to
flow through `.exit_label → evmAddEpilogue → halt stub`:

```
.exit_label:
  <evmAddEpilogue>   (writes stack top to OUTPUT[0..32] + halt_kind=0 to OUTPUT[32..40])
.exit_no_epilogue:   (M23: handlers that surface their own output target this)
  <halt stub>        (linux93: li x17, 93; li x10, 0; ecall)
```

### Delivered

- **`EvmAsm/Codegen/Dispatch.lean`** — emit
  `.exit_no_epilogue:` between `emitProgram exitBody` and the
  halt stub in `emitDispatcherEpilogue`. Single surgical
  insertion.

- **`EvmAsm/Codegen/Programs/Evm.lean`** — `evmAddEpilogue`
  gains a final `SD .x5 .x0 32` instruction (writes
  `halt_kind = 0` to `OUTPUT_ADDR + 32`). Still pure
  verified `Program` — stays in `Instr`-only world.

- **`EvmAsm/Codegen/Programs/Noop.lean::haltHandlers`** —
  RETURN (0xf3) and REVERT (0xfd) tails replaced with real
  inline asm (~25 instructions each) that:
  1. Reads `offset_low` / `size_low` (low u64 limbs) from
     stack at `[x12+0..]` / `[x12+32..]`.
  2. Zero-fills `OUTPUT_ADDR[0..32]`.
  3. Clamps `size_low` to 32 (M23 cap).
  4. Byte-loop copies clamped bytes from
     `evm_memory + offset_low` to `OUTPUT_ADDR`.
  5. Writes halt_kind (1 = RETURN, 2 = REVERT) at
     `OUTPUT_ADDR + 32`.
  6. `j .exit_no_epilogue`.

  Bodies use GNU AS numeric local labels (`1:`, `2:`, `3:`,
  `1b`, `1f`, …) — unique-per-use, so RETURN and REVERT
  reuse the same label numbers without colliding (same
  convention M22 storage scan loops established).

  INVALID (0xfe) and SELFDESTRUCT (0xff) tails untouched —
  still flow through `.exit_label`, inheriting
  `halt_kind = 0`.

- **`EvmAsm/Codegen/Tests/Cases.lean`** — `OpcodeTestCase`
  gains optional `expectedHaltKind : String := ""` (8-byte
  LE hex; empty = don't assert).

- **`EvmAsm/Codegen/Cli.lean`** — `--list-test-cases` emits
  a 6-column TSV (appending halt-kind after storage).

- **`scripts/codegen-opcodes-runtime-check.sh`** — reads the
  6th column via `cut -f6`. When non-empty, asserts
  `OUTPUT_ADDR + 32..40` matches via `xxd -s 32 -l 8`. Both
  the output mismatch and the halt-kind mismatch are
  surfaced separately in the failure list.

- **3 new test cases:**
  - `return_word_basic` — `PUSH1 0x42; PUSH1 0x00; MSTORE;
    PUSH1 0x20; PUSH1 0x00; RETURN`. Writes BE(0x42) to
    memory[0..32]; RETURN(0, 32) copies it out. Expected:
    `0000…0042`, halt_kind `0100000000000000`.
  - `return_small_pads_zeros` — `PUSH1 0xff; PUSH1 0x00;
    MSTORE8; PUSH1 0x01; PUSH1 0x00; RETURN`. RETURN(0, 1)
    copies 1 byte; zero-fill covers OUTPUT[1..32]. Expected:
    `ff00…00`, halt_kind = 1.
  - `revert_word_basic` — same bytecode as
    `return_word_basic` but byte 0xfd. Same returndata;
    halt_kind `0200000000000000`. **This is the test that
    proves RETURN and REVERT are observably distinguishable.**

- Pre-existing `return_pop2_halt` test was updated: it
  previously asserted the M18 no-op surfacing behavior
  (top-of-stack 0xff via evmAddEpilogue). Under M23 real
  RETURN it reads uninitialized memory[0x22..0x33] = zeros,
  so the expected output flips to 32 zeros + halt_kind = 1.

**Known limitations:**

- **Returndata clamped to 32 bytes.** Larger payloads
  silently truncate. Future PR can extend the OUTPUT layout
  with a length prefix or wider region.
- **INVALID / SELFDESTRUCT inherit halt_kind = 0** from the
  default exit path. Distinct kinds (3 / 4) are a small
  follow-up.
- **Offset / size > u64** silently use only the low u64.
  Trivially safe for any test that fits in evm_memory's
  32 KiB. Future PR can add an upper-limb-zero check.
- **No gas accounting** for RETURN / REVERT.
- **RETURNDATASIZE / RETURNDATACOPY** still no-ops — they
  read the caller's return-data buffer
  (`returnDataPtrOff = 432` / `returnDataSizeOff = 440`),
  meaningful only with nested call frames (still no-ops).

**Exit criteria (met).**
`scripts/codegen-opcodes-runtime-check.sh` exits 0 with all
**68 cases PASS** (64 pre-M23 + 4 updated/new; 3 new RETURN/
REVERT cases all assert halt_kind). `scripts/check-progress.sh`
exits 0. Build clean (`lake build EvmAsm.Codegen` exits 0).

### M23.5 — distinct INVALID / SELFDESTRUCT halt kinds — **DONE (2026-06-02)**

Completes the exceptional-halt-tagging story started by M23 (RETURN/REVERT
halt kinds) and M15.5 (invalid-jump `halt_kind = 4`). INVALID (0xfe) and
SELFDESTRUCT (0xff) previously routed through `.exit_label → evmAddEpilogue`,
surfacing the EVM stack top + `halt_kind = 0` — indistinguishable from STOP.
Now they surface zero result data (no return data) and a distinct kind, so a
caller / EEST-style check can tell all six halt outcomes apart.

**halt_kind scheme (finalized, `OUTPUT + 32`):** `0` STOP · `1` RETURN ·
`2` REVERT · `3` INVALID (M23.5) · `4` invalid JUMP/JUMPI dest (M15.5) ·
`5` SELFDESTRUCT (M23.5). INVALID is an exceptional halt (success=false);
SELFDESTRUCT is a normal halt (success=true); both have empty return data.

**Delivered:**
- **`EvmAsm/Codegen/Dispatch.lean`** — factor M15.5's inline `.exit_invalid`
  block into a reusable `emitExceptionalExit (label) (kind)` helper (zero-fill
  `OUTPUT[0..32]` + tag `halt_kind` + `j .exit_no_epilogue`), and emit three
  labels via it: `.exit_invalid` (4), `.exit_invalid_op` (3), `.exit_selfdestruct`
  (5). No behavior change for the existing `.exit_invalid`.
- **`EvmAsm/Codegen/Programs/Noop.lean`** — `haltHandlers`: INVALID tail
  `j .exit_invalid_op`; SELFDESTRUCT tail `addi x12, x12, 32 ; j .exit_selfdestruct`
  (keeps the 1-word pop). Docstring updated.
- **`EvmAsm/Codegen/Tests/Cases.lean`** — `invalid_halt` updated (result was the
  leaked stack-top `0x42`; now zero + `halt_kind = 3`); new `selfdestruct_halt`
  (`PUSH1 0xff; SELFDESTRUCT` → zero + `halt_kind = 5`).

**Exit criteria (met).**
`scripts/codegen-opcodes-runtime-check.sh` exits 0 with all **90 cases PASS**
(all six halt kinds asserted distinct: RETURN=1, REVERT=2, INVALID=3,
invalid-jump=4, SELFDESTRUCT=5, STOP=0). `scripts/check-progress.sh` exits 0.
`lake build EvmAsm.Codegen` clean; `RegistryInvariants` unchanged (149).

### M30 — Gas metering (first slice: static base costs) — **DONE (2026-06-02)**

The first real gas metering in the dispatcher — the cross-cutting feature both
tracks need (it lets out-of-gas reuse the M23.5 exceptional-halt machinery and
is the bridge toward the `Stateless/VM/Interpreter.lean` integration).
**Scope = static base costs only**; dynamic costs (memory expansion, cold/warm
SLOAD, call stipend, per-word/byte/topic, SSTORE refunds) are deferred.

**Design:** the gas counter is an env cell (`env+568`), not a register — every
high register is transiently clobbered by some handler. The dispatch loop (both
prologue variants) charges each opcode's static base cost before executing it;
underflow routes to `.exit_outofgas` (`halt_kind = 6`). Charge-then-execute
matches the spec's `charge_gas` order (so GAS reflects its own cost).

**Delivered:**
- **`Dispatch.lean`** — `staticGasCost : Nat → Nat` (EVM base-cost tiers from
  `execution-specs/.../prague/vm/gas.py`; halts + unwired bytes = 0) emitted as
  a 256-`.dword` `opcode_gas_costs:` table in both data sections; the
  `.dispatch_loop` body looks up `cost = opcode_gas_costs[op]`, `bltu`s to
  `.exit_outofgas` on underflow, else charges `env+568`. New gas cell at
  `env+568` (`.zero 568→576`); runtime prologue reads the gas limit from the
  input trailer, `.data`-baked prologue seeds 30,000,000.
  `emitExceptionalExit ".exit_outofgas" 6`.
- **`pack-bytecode.py`** — `--gas N` appends an 8-byte LE gas-limit trailer
  (default 30,000,000; back-compatible).
- **`Programs/Evm.lean`** — real `gasHandlers` (GAS 0x5a reads `env+568` and
  pushes it); removed from `pushZeroHandlers`. `RegistryInvariants` unchanged
  (149 — GAS only moved lists).
- **Tests** — `gas_opcode_sufficient` (`GAS; STOP`, limit 1000 → 998 after the
  charge), `gas_opcode_out_of_gas` (`PUSH1`, limit 2 → `halt_kind = 6`); new
  `gasLimit` TSV column threaded through `Cli.lean` + the bash runner.

**Limitations** (documented in `staticGasCost`): static base only — state ops
(SLOAD/SSTORE/CALL/EXTCODE*/KECCAK/LOG/EXP/copies) under-charge; per-iteration
cost lookup adds ~6 instrs/op; gas-used not yet surfaced at OUTPUT; MSIZE/memory
gas unchanged. `Layout.lean`'s `envSize` remains stale vs the dispatcher's
raw-offset env cells (pre-existing; a sync is a separate cleanup).

**Exit criteria (met).**
`scripts/codegen-opcodes-runtime-check.sh`: the two new gas cases pass and no
prior case regresses. (Two BLOCKHASH cases — `blockhash_parent`,
`blockhash_historical` — fail identically on pristine `upstream/main`; they are
a **pre-existing** env-offset drift in the BLOCKHASH handler, unrelated to this
PR.) `lake build EvmAsm.Codegen` clean.

### M24 — Storage on Option A: append-log + journal + real TLOAD/TSTORE — **DONE (2026-05-29)**

The storage memory-layout decision (issue **#7130**) landed
with consensus to **start with Option A** — an append-only
`(addrHash, slotKey, original, current)` log in
`STATE_TRACKER_AREA = 0xa0630000` (4 MiB), with revert = log-
length truncation (the log *is* the journal). Possible upgrade
to **C** (direct-mapped hint index over the same log) later.

M24 brings M22's transitional storage into alignment with the
Option A spec, and extends the same architecture to **real
TLOAD/TSTORE** (graduated from M17 no-ops). It also adds
**REVERT rollback** (REVERT now truncates the log to a
checkpoint captured at the dispatcher prologue's end).

**What M22 had that M24 changes:**

| Concern | M22 | M24 |
|---|---|---|
| Entry shape | `(slotKey:32, value:32)` = 64 B | `(addrHash:32, slotKey:32, original:32, current:32)` = 128 B |
| Semantics | In-place update on key match | Always append; scan from end (last-write-wins) |
| Location | Dispatcher `.data` `evm_slot_table` (16 KiB) | `STATE_TRACKER_AREA = 0xa0630000` (4 MiB) |
| Revert | None — SSTORE-then-REVERT committed | Log-length truncation to checkpoint |
| Transient (TLOAD/TSTORE) | M17 no-ops | Same Option A structure at `0xa0830000` |
| Original-value tracking | Absent | Captured on first-touch; preserved across SSTOREs |

**OUTPUT layout (post-M24):**

```
OUTPUT_ADDR (0xa0010000):
  +0..32    <result>                       (M21/M23: stack top or returndata)
  +32..40   <u64 LE halt_kind>             (M23)
  +40..48   <u64 LE persistentLogLength>   (NEW M24)
  +48..56   <u64 LE transientLogLength>    (NEW M24)
  +56..256  <unused>
```

Surfaced by 6 instructions appended to `.exit_no_epilogue:`
in `emitDispatcherEpilogue` — runs for **every** halt path.

**Delivered:**

- **`EvmAsm/Evm64/Environment/Layout.lean`** — `slotTableCountOff`
  renamed to `persistentLogLengthOff` (same offset 448; semantic
  shift from count-of-64B-entries to count-of-128B-entries). Two
  new cells: `persistentLogCheckpointOff = 456`,
  `transientLogLengthOff = 464`. `envSize` 456 → 472.
  `envSize_covers` chain extended; `Assertion.lean`'s `envCells`
  bumped 57 → 59.

- **`EvmAsm/Codegen/Dispatch.lean`** —
  - Removed `evm_slot_table: .zero 0x4000` from both `.data`
    sections (~16 KiB reclaimed). Storage now lives in
    `STATE_TRACKER_AREA`, accessed directly via
    `li xN, 0xa0630000` / `0xa0830000`.
  - **Runtime prologue:** the M22 slot-table copy loop became
    an **expansion loop** that turns each 64-byte input entry
    `(key, value)` into a 128-byte Option A entry
    `(addrHash=0, slotKey=key, original=value, current=value)`
    at `0xa0630000 + i*128`. Writes preload count to both
    `env+448` (live length) and `env+456` (checkpoint).
    Initializes `env+464` (transient length) to 0.
  - **`.data`-baked prologue:** initializes all three log-state
    cells (448, 456, 464) to 0.
  - **Epilogue:** appends 6 instructions after
    `.exit_no_epilogue:` to copy `env+448`/`env+464` to
    `OUTPUT+40`/`OUTPUT+48`. Universal exit join — works for
    STOP / RETURN / REVERT / INVALID / SELFDESTRUCT.

- **`EvmAsm/Codegen/Programs/Storage.lean`** — complete
  rewrite. Four real handler bodies, all using GNU AS numeric
  local labels for scan loops (idioms unchanged from M22):
  - **SLOAD (0x54):** scan persistent log from end (last-write-
    wins); copy `current` to stack top; zero on miss.
  - **SSTORE (0x55):** scan from end, save `&found.original`
    in x18 if matched; then **always append** a new 128-byte
    entry preserving `original` (or 0 on miss). Increment
    `env+448`.
  - **TLOAD (0x5c):** same as SLOAD against `env+464` /
    `0xa0830000`.
  - **TSTORE (0x5d):** skip scan; append `(addrHash=0,
    slotKey, original=0, current=new)` to transient log.

- **`EvmAsm/Codegen/Programs/Noop.lean::haltHandlers`** —
  REVERT body gains 3 instructions before `j .exit_no_epilogue`:
  ```
  ld  x17, 456(x20)      # persistentLogCheckpointOff
  sd  x17, 448(x20)      # restore persistent log_length
  sd  x0,  464(x20)      # transient log_length = 0
  ```
  RETURN / STOP / INVALID / SELFDESTRUCT untouched (commit
  semantics).

- **`EvmAsm/Codegen/Tests/Cases.lean`** + `Cli.lean` + bash
  runner — two new optional `OpcodeTestCase` fields:
  `expectedPersistentLogLength` and `expectedTransientLogLength`
  (16 hex chars = 8-byte LE u64). `--list-test-cases` emits an
  8-column TSV; runner asserts `OUTPUT[40..48]` / `OUTPUT[48..56]`
  via `xxd -s 40 -l 8` / `-s 48 -l 8` when the corresponding
  field is non-empty.

- **3 new M24 test cases:**
  - **`sstore_revert_rolls_back`** — `PUSH1 0x42; PUSH1 0x00;
    SSTORE; PUSH1 0x00; PUSH1 0x00; REVERT`. SSTORE appends
    (length 0→1); REVERT truncates back to checkpoint = 0.
    Expected persistent log_length = 0. **Proves the journal
    rollback works.**
  - **`sstore_no_revert_commits`** — same SSTORE then STOP.
    No rollback; persistent log_length stays at 1.
  - **`tstore_tload_round_trip`** — TSTORE + TLOAD + STOP.
    Returns stored value via TLOAD; transient log_length = 1.
    **Proves TLOAD/TSTORE moved off the M17 no-op.**

- **Pre-existing `tstore_tload_roundtrip` test** (M17-era,
  asserted TLOAD returned 0 as no-op): removed as redundant
  with the new `tstore_tload_round_trip`. Same bytecode,
  different naming (`round_trip` matches the M22 convention).

- **`scripts/codegen-opcodes-runtime-check.sh`** — gains
  `cut -f7` and `cut -f8` for the new columns + two more
  conditional `xxd` reads. Pre-M24 tests unaffected (empty
  fields → no assertion).

**Inline-asm conventions** (unchanged from M22/M23): GNU AS
numeric local labels (`1:`, `1b`, `1f`, …) — unique-per-use,
reusable across handlers. Scratch registers x14–x18 are
caller-saved.

**Known limitations** (documented in `Programs/Storage.lean`
docstring):

- **Single-contract only** — `addrHash = 0` for every entry.
  Multi-contract is M25.
- **Cold reads of non-preloaded slots return `original = 0`**.
  Real EVM reads the slot's pre-tx value from the trie; we
  don't have a witness MPT yet (deferred). For preloaded
  slots, `original` is correctly captured at preload.
- **4 MiB / log cap** = ~32K entries each. Well past any
  realistic test workload; no observable limit today.
- **Single-frame journal.** Checkpoint captured once at
  prologue end; REVERT restores. No CALL/CREATE frames yet
  (those would need push/pop journaling — future PR).
- **No gas accounting.** The `original` cell is tracked for
  forward-compatibility but never consulted yet.
- **Inline asm, not verified bodies.** Verified-loop bodies
  follow later.

**Migration cost preview:**

The post-M24 path to **C** (direct-mapped index over the same
log) is **low** (~1 PR additive — log structure and semantics
don't change; the index is a non-authoritative hint). The
path to **D + flat overlay** (sparse trie as authoritative)
is significant (~3–5 PRs replacing the storage architecture),
but ~30–40% of M24 carries over (handler EVM contracts, test
infra). User is doing independent analysis on the C vs D-flat
choice; M24 is the foundation either way.

**Exit criteria (met).**
`scripts/codegen-opcodes-runtime-check.sh` exits 0 with all
**70 cases PASS** (67 pre-M24 + 3 new; one pre-M24
`tstore_tload_roundtrip` removed as redundant under M24's
real semantics). `scripts/check-progress.sh` exits 0. Build
clean (`lake build EvmAsm.Codegen` exits 0).

### M25 — Post-state slot serializer: modified slots → OUTPUT — **DONE (2026-05-29)**

M24 surfaced storage log **lengths** at `OUTPUT[40..56]` but
not the actual slot data. Tests could only assert "the
persistent log has N entries" — they couldn't ask "which
slots changed, and to what values". M25 closes that gap by
walking the persistent log from end (last-write-wins),
deduping, and emitting up to 3 `(slotKey, current)` pairs at
`OUTPUT[64..256]` with a count cell at `OUTPUT[56..64]`.

After M25, an EEST-style post-state assertion ("after this
bytecode + preload, slot K has value V") is directly
expressible via the new `expectedPostStorage` test field —
the load-bearing piece for running real EEST fixtures.

The OUTPUT contract is layout-agnostic: the dedup+emit
mechanism produces a flat list of modified slots regardless
of which storage architecture sits behind it. If/when
storage migrates from Option A to D+flat overlay, the inner
walk changes but the OUTPUT layout stays stable.

### OUTPUT layout (post-M25)

```
OUTPUT_ADDR (0xa0010000):
  +0..32    <result>                              (M21/M23)
  +32..40   <u64 LE halt_kind>                    (M23)
  +40..48   <u64 LE persistentLogLength>          (M24 — raw count, with duplicates)
  +48..56   <u64 LE transientLogLength>           (M24)
  +56..64   <u64 LE numModifiedPersistentSlots>   (NEW M25 — deduped count, ≤ 3)
  +64..(64 + N*64)
            <modified slots: (slotKey:32, current:32) × N>  (NEW M25)
  +...      <zero-padded to 256 B by ziskemu init>
```

The 3-slot cap follows from the 256-byte ziskemu OUTPUT
region: `256 - 64 = 192 = 3 × 64`. Sufficient for pure-
computation EEST tests that modify ≤ 3 slots. Larger
workloads need a future PR to extend OUTPUT or switch to a
hash digest.

### Why dedup (and why reverse-write order)

Under Option A, SSTORE always appends, so the log can hold
multiple entries for the same slotKey. For an EEST-style
post-state assertion, what matters is the **final** value
per unique key. The dedup walks the log from end (newest
entries first), checks each slotKey against the
already-emitted output list, and emits only on first sight.
Result: slots appear in **reverse write order** (most-
recently-modified first). Documented; test authors construct
expected strings accordingly.

### Delivered

- **`EvmAsm/Codegen/Dispatch.lean`** —
  `emitDispatcherEpilogue` gains ~60 instructions after the
  M24 log-length writes. Walks `evm_persistent_log` (base
  `0xa0630000`, length `env+448`) from end, dedups in an
  inner O(N²) scan against the already-emitted slot list,
  emits `(slotKey, current)` pairs at `OUTPUT[64 +
  i*64..]`, updates the count cell. Numeric local labels
  `1:`–`6:` reused within the block; no collision with
  handler bodies (unique-per-use across the file).

- **`EvmAsm/Codegen/Tests/Cases.lean`** — `OpcodeTestCase`
  gains an optional `expectedPostStorage : String := ""`
  field. Hex string starts at `OUTPUT[56]`; runner reads
  exactly `len/2` bytes.

- **`EvmAsm/Codegen/Cli.lean`** — `--list-test-cases` emits
  9-column TSV (append `expectedPostStorage` after
  `expectedTransientLogLength`).

- **`scripts/codegen-opcodes-runtime-check.sh`** — reads
  column 9 via `cut -f9`. When non-empty, computes
  `post_len_bytes = ${#expected_post_storage}/2` and reads
  via `xxd -p -c 256 -s 56 -l <bytes>`. Mismatch added to
  the per-test failure list separately from output /
  halt-kind / log-length failures.

- **4 new test cases** exercising the new surface:
  - `sstore_post_state_single_slot` — basic single-slot
    emission (count=1, slotKey=0, value=0x42).
  - `sstore_revert_post_state_empty` — after REVERT, the
    rollback truncates the log, so dedup-and-emit produces
    just count=0. **Proves rollback also clears the
    surfaced slot data.**
  - `sstore_two_slots_post_state` — two distinct slots
    SSTORE'd; output entries appear in reverse write order
    (slot 0x02 first, then 0x01). **Asserts the ordering
    convention.**
  - `sstore_dup_keeps_latest` — same slotKey written twice;
    dedup picks the most-recent value. **Proves dedup.**

**Known limitations** (documented in CODEGEN.md / dispatcher
asm comments):

- **3-slot cap** from the 256-byte OUTPUT region. Silent
  truncation: when > 3 unique slots are modified, only the
  3 most-recently-written keys appear. Future PR can extend
  OUTPUT or use a hash digest.
- **Persistent only.** Transient post-state isn't surfaced
  (would need another OUTPUT region; observability via
  `OUTPUT[48..56]` transient log length is what we have).
- **Reverse write order.** Test authors must know this.
- **Layout-dependent asm.** The dispatcher asm hard-codes
  the 128-byte Option A entry shape (offset 32 = slotKey,
  offset 96 = current). If layout changes to D+flat, the
  asm needs updating. The OUTPUT contract (count + entries
  at +56) stays.
- **Dedup is O(N²).** For each scanned log entry, the inner
  dedup loop iterates the emitted-so-far list (≤ 3
  entries). With raw log length L, that's ≤ 3L compares.
  Negligible for tests; future PR can address at scale.
- **Inline asm**, not a verified body.

**Exit criteria (met).**
`scripts/codegen-opcodes-runtime-check.sh` exits 0 with all
**74 cases PASS** (70 pre-M25 + 4 new; existing tests
unchanged — they don't assert on `OUTPUT[56..]` and the
dedup-and-emit only writes within that previously-unused
range). `scripts/check-progress.sh` exits 0. Build clean
(`lake build EvmAsm.Codegen` exits 0).

### M27 — Real EXP (0x0a): graduate from no-op to verified body — **DONE (2026-06-02)**

(Numbered M27 to leave room for the real LOG-event-capture work that
landed after M25 in git — commit `7a160eec2` — but was not given its own
doc milestone.)

EXP (0x0a) graduates from the M20 `arithNoopHandlers` no-op to its real
verified body, routed through `selfCallingHandlers` with the same
inline-callable pattern as ADDMOD (M10).

**The blocker was a real bug, not an upstream gap.** The `_fixed` EXP body
(`EvmAsm/Evm64/Exp/Program.lean`) moved the exponent *cursor* to
callee-saved `x19`, but left the per-limb *counter* in `x6` — which
`mul_callable` (= `evm_mul ;; cc_ret`) clobbers ~51× per call. Since the
squaring / conditional-multiply blocks call `mul_callable` mid-iteration,
`x6` was garbage on the next bit-test, producing wrong results / an
infinite reload loop (documented in `scripts/codegen-evm_exp-property-check.sh`).
The earlier "x16 is also unsafe" note was stale — `evm_mul` touches none
of `x16/x18/x19/x22`.

**Delivered:**
- **`EvmAsm/Evm64/Exp/Program.lean`** — new `_fixed_fixed` family
  (`exp_prologue_fixed_fixed`, `exp_msb_bit_test_block_fixed_fixed`,
  `exp_iter_body_full_msb_saved_bit_two_mul_fixed_fixed`,
  `evm_exp_msb_saved_bit_two_mul_fixed_fixed[_canonical]` + length
  theorems). Pure register substitution `x6 → x22` (s6, callee-saved); all
  instruction counts and byte offsets identical to `_fixed`, so the
  canonical branch/MUL offsets carry over.
- **`EvmAsm/Codegen/Programs/Evm.lean`** — `evmExpComposed` =
  `evm_exp_..._fixed_fixed_canonical 200 92 ;; JAL x0 +260 ;; mul_callable`,
  mirroring `evmAddmodComposed`. MUL-call offsets shift +4 (196→200,
  88→92) because the 4-byte skip-JAL pushes `mul_callable` to body byte
  340; the skip-JAL (260 = 4 + 256) carries the loop-exit fall-through
  past the callable to the tail (`exp_epilogue` has no trailing jump). New
  `h_EXP` entry in `selfCallingHandlers` with
  `preBody := "mv x14, x10\n  la x2, exp_scratch"` and a custom `expTail`
  (`mv x10, x14; la sp, lp64_sp_top; addi x10, x10, 1; j .dispatch_loop`).
  Removed EXP from `arithNoopHandlers` (MULMOD stays).
- **`EvmAsm/Codegen/Dispatch.lean`** — both data sections gain a 32-byte
  `exp_scratch:` region. The EXP body uses `x2`(sp)+0..24 as its result
  accumulator; the dispatcher's `sp = lp64_sp_top` is the top of a
  down-growing stack immediately followed by the jump table, so `sp+0..24`
  would corrupt opcode-handler entries 0–3 (incl. STOP). `h_EXP` repoints
  `x2` at `exp_scratch` and its tail restores `sp`.
- **`EvmAsm/Codegen/Programs/ExpProperty.lean`** — `evm_exp_from_input`
  upgraded to the `_fixed_fixed` body + skip-JAL (it was doubly broken: the
  x6 clobber *and* `exp_epilogue` falling straight into `mul_callable`).
  `scripts/codegen-evm_exp-property-check.sh` now validates random
  `(base, exponent)` pairs against Python `pow(base, exp, 2**256)`.
- **`EvmAsm/Codegen/Tests/Cases.lean`** — replaced the `exp_pop2` no-op
  case with two real cases: `exp_basic` (2³=8, exercises cond-multiply)
  and `exp_zero` (5⁰=1, exercises the per-limb counter reload across all
  4 limbs via 256 squarings). Total cases 76 → 77.

**Known limitation (documented in `evmExpComposed`):** the verified EXP
body uses `x12+64..120` (deeper-stack direction) as MUL factor scratch —
fine when EXP's operands are the shallowest live elements (true for the
test cases and the standalone harness's reserved `operands_ram+64..127`),
but it overwrites deeper stack slots if EXP runs with a deeper stack. A
full-domain dispatcher fix would give the body a dedicated MUL-scratch
base register instead of reusing `x12`. `RegistryInvariants` counts are
unchanged (149) — EXP was already counted; it only moved lists.

**Exit criteria (met).**
`scripts/codegen-opcodes-runtime-check.sh` exits 0 with all **77 cases
PASS** (`exp_basic`, `exp_zero` included). `scripts/codegen-evm_exp-property-check.sh
--count=30` exits 0 (all 30 random cases match Python `pow`).
`scripts/check-progress.sh` exits 0. Build clean (`lake build EvmAsm.Codegen`
exits 0).

### Sequencing

M0 ✅ → M1 ✅ → M2 ✅ → M4 ✅ → M5a ✅ → M5b ✅ → M6a ✅ → M6b ✅ → M7 ✅ → M8 ✅ → M8.5 ✅ → M9 ✅ → M10 ✅ → M11 ✅ → M12 ✅ → M13 ✅ → M14 ✅ → M15 ✅ → M16 ✅ → M17 ✅ → M18 ✅ → M19 ✅ → M20 ✅ 🎯 100% → M21 ✅ → M22 ✅ → M23 ✅ → M24 ✅ → **M25 ✅**.
M3 is deferred; revisit only if a future milestone (full opcode
coverage, JUMP/JUMPI, or the binary encoder) makes label-free
emission unreadable. M11 (SHL + SAR) shipped 2026-05-26; M12
(13 simple environment opcodes via `envHandlers`) shipped 2026-05-26;
M13 (CALLDATASIZE via `calldataHandlers`) shipped 2026-05-26;
M14 (JUMPDEST via `controlFlowHandlers`) shipped 2026-05-27;
M15 (JUMP/JUMPI/PC into `controlFlowHandlers`) shipped 2026-05-27;
M16 (KECCAK256 via ECALL bridge in `hashHandlers`) shipped 2026-05-27;
M17 (LOG0–LOG4 + SLOAD/SSTORE/TLOAD/TSTORE as no-ops) shipped
2026-05-27; M18 (20 trivial no-ops in `Noop.lean` — 94.6%
coverage) shipped 2026-05-27; M19 (6 child-frame opcodes as
no-ops — 98.7% coverage) shipped 2026-05-27; M20 (MULMOD + EXP
no-ops — 🎯 100% coverage) shipped 2026-05-27; M21 (real
calldata wiring — CALLDATALOAD/COPY graduate from no-ops; first
step on the EEST path) shipped 2026-05-27; M22 (real SLOAD/
SSTORE via pre-loaded slot table — second step on the EEST
path; `Programs/Storage.lean` extracted) shipped 2026-05-28;
M23 (real RETURN/REVERT with returndata buffer + halt-kind
status; new `.exit_no_epilogue` exit path — storage-orthogonal
pivot prompted by #7130) shipped 2026-05-28;
M24 (storage on Option A — append-log + journal + real
TLOAD/TSTORE; supersedes M22's slot-table v1) shipped
2026-05-29; **M25 (post-state slot serializer — modified
slots at OUTPUT+56; unlocks EEST-style post-state
assertions) shipped 2026-05-29.**

**The codegen track is in "spec-compliance upgrades" mode,
building toward EEST tests.** Storage architecture is now
locked at Option A v1 (#7130 consensus); design re-evaluation
of C vs D-flat overlay is ongoing in parallel. Status:
- M21 ✅ real calldata
- M22 ✅ real persistent storage (slot-table v1, superseded by M24)
- M23 ✅ real RETURN/REVERT with halt-kind
- M24 ✅ storage on Option A + real TLOAD/TSTORE + REVERT rollback
- M25 ✅ post-state slot serializer (modified slots at OUTPUT+56)

**Storage-coupled candidates for M26+** (all build on M24's
Option A layout; each will need rework if/when #7130's design
re-evaluation lands on D+flat overlay — but ~30-40% of work
carries over):
- M26 — `addrHash` dimension (multi-contract storage keying)
- M27 — Nested call frames + multi-frame journal push/pop
- M28 — Witness MPT integration (cold reads + commit sweep)
- M29 — EEST fixture harness + CI — 🟡 stateless harness **landed**:
  `scripts/eest-fetch-fixtures.sh` (download `fixtures_zkevm.tar.gz`),
  `scripts/eest-stateless-to-input.py` (fixture → ziskemu `-i` input +
  manifest), `scripts/codegen-eest-stateless-check.sh` (build ELF, run on
  ziskemu, compare vs `statelessOutputBytes`). Targets EEST
  `zkevm@v0.4.0` (Amsterdam/Glamsterdam); baseline in PROGRESS.md Axis F.
  CI job (smoke subset on PRs) still TODO.

**Storage-orthogonal candidates** (any order, interleave anywhere):
- Real EXP body wiring (verified body exists complete; M10-
  style inline-callable composition)
- INVALID/SELFDESTRUCT distinct halt-kind tagging
- Gas-metering scaffolding
- ECRecover precompile via ECALL bridge
- Returndata > 32 bytes (extend OUTPUT layout)
- Real RETURNDATASIZE / RETURNDATACOPY (needs nested call
  frames)

**Storage-redesign-dependent work** (deferred until #7130
lands):
- Pre-state witness unpacking
- Post-state serializer (modified slots → OUTPUT)
- EEST fixture loader + CI

Ultimately PLAN.md Phase 11 (STF integration —
RLP-decoded transactions through the dispatcher to a
state-root output) is the project's real end goal.

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
- **M16.** ✅ `scripts/codegen-opcodes-runtime-check.sh` exits 0 with
  **45 test cases** PASS (validated 2026-05-27). KECCAK256 (0x20)
  wired via new `hashHandlers` builder. All-raw-asm handler:
  `body := []`, `tail := .custom "..."` with stack-pop / arg-marshal /
  `jal x1, zkvm_keccak256` / stack-restore / `j .dispatch_loop`.
  Dispatcher epilogue gained the full `zkvm_keccak256` subroutine
  (from `EvmAsm/Codegen/Programs/HashBridge.lean`) between handler
  subroutines and `h_invalid:`. Data section gained `zk3_state`
  (200 B keccak state) and `lp64_stack` / `lp64_sp_top` (512 B
  LP64 stack region; both prologues now do `la sp, lp64_sp_top`
  first thing so the keccak subroutine's frame saves don't write
  to a negative address). Test case `keccak256_empty` hashes
  empty bytes; output matches the standard digest
  `c5d246…5a470`. Establishes the ECALL bridge pattern for
  M17+ (LOG / SLOAD / SSTORE / precompiles). Registry-invariants
  counts bumped 111 → 112.
- **M17.** ✅ `scripts/codegen-opcodes-runtime-check.sh` exits 0
  with **49 test cases** PASS (validated 2026-05-27). 9 opcodes
  wired as **stack-pop no-ops**: LOG0–LOG4 via new
  `logHandlers` builder (each a 1-instruction `ADDI .x12 .x12 N`
  body popping `(2+n) × 32` bytes); SLOAD/SSTORE/TLOAD/TSTORE via
  new `storageHandlers` builder (SLOAD/TLOAD overwrite the popped
  key with 32 zero bytes via 4 × SD; SSTORE/TSTORE pop both
  inputs via single ADDI). No host syscall exists for LOG or
  storage (per `zkvm_accelerators.h`); the ECALL bridge pattern
  from M16 can't be used. Known limitations: LOG events dropped,
  storage always reads 0. Registry-invariants counts bumped
  112 → 121.
- **M18.** ✅ `scripts/codegen-opcodes-runtime-check.sh` exits 0
  with **54 test cases** PASS (validated 2026-05-27). **20
  opcodes** wired across 4 new no-op builders in
  `EvmAsm/Codegen/Programs/Noop.lean` (extracted per the
  file-size guardrail): `haltHandlers` (RETURN/REVERT/INVALID/
  SELFDESTRUCT), `pushZeroHandlers` (CODESIZE/RETURNDATASIZE/
  BLOBBASEFEE/MSIZE/GAS), `popPushZeroHandlers` (BALANCE/
  CALLDATALOAD/EXTCODESIZE/EXTCODEHASH/BLOCKHASH/BLOBHASH),
  `copyNoopHandlers` (CALLDATACOPY/CODECOPY/EXTCODECOPY/
  RETURNDATACOPY/MCOPY). **Crosses 90% coverage (135) and
  reaches 94.6% (141)** — the biggest opcode-count jump since
  M6b. All 20 ship with documented spec-incompliances (return
  zero / drop side effects) since the dispatcher has no model
  for accounts / block history / blob context / return-data
  buffers. Registry-invariants counts bumped 121 → 141; 3 of
  the 6 invariant theorems gained `set_option maxRecDepth 2048`
  to handle the larger registry. **Remaining gap to 100%**:
  MULMOD (1 verified-body PR), EXP (external unblock), 6
  child-frame opcodes (CREATE / CALL family — multi-PR design
  surface).
- **M19.** ✅ `scripts/codegen-opcodes-runtime-check.sh` exits 0
  with **57 test cases** PASS (validated 2026-05-27). **6 child-
  frame opcodes** (CREATE 0xf0, CALL 0xf1, CALLCODE 0xf2,
  DELEGATECALL 0xf4, CREATE2 0xf5, STATICCALL 0xfa) wired as
  pop-N + push-zero no-ops via a new `childFrameHandlers`
  builder in `EvmAsm/Codegen/Programs/Noop.lean`. Same shape as
  M18's `popPushZeroHandlers` with bigger pop counts: ADDI
  immediates 64 / 96 / 160 / 192 covering net pops 2 / 3 / 5 / 6.
  **Crosses 95% coverage** (143) and reaches **98.7% (147)**.
  Registry-invariants counts bumped 141 → 147; Phase 1
  recompile ~20 s, under 30 s budget. Known limitations: no
  actual sub-frame execution (always "call failed" / "address
  0"); trusted bytecode that handles call-failure paths via
  ISZERO+JUMPI continues to work. **Remaining gap to 100%**:
  MULMOD (verified body) and EXP (external unblock).
- **M20.** ✅ `scripts/codegen-opcodes-runtime-check.sh` exits 0
  with **59 test cases** PASS (validated 2026-05-27). **MULMOD
  (0x09)** and **EXP (0x0a)** — the last 2 unwired opcodes —
  wired as no-ops via a new `arithNoopHandlers` builder in
  `EvmAsm/Codegen/Programs/Noop.lean`. MULMOD: net pop 2 →
  ADDI +64; EXP: net pop 1 → ADDI +32. Both share the same
  `ADDI + 4 × SD` body shape as M17–M19. Registry-invariants
  counts bumped 147 → 149; Phase 1 recompile ~20 s, under
  budget. **🎯 100% opcode coverage** — every EVM byte-code now
  routes through `tinyInterpRegistry` instead of `h_invalid`.
  MULMOD ships as a placeholder (slice evm-asm-m4wu's verified
  body unscheduled). EXP's verified body
  (`evm_exp_msb_saved_bit_two_mul_fixed`) exists; M21 will wire
  it via M10-style inline-callable composition. The codegen
  track now pivots from "wire opcodes" to "spec-compliance
  upgrades" and "STF integration".
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
