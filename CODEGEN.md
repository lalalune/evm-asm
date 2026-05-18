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
| `EvmAsm/Codegen/Layout.lean` | `HaltConv` enum, halt stub, `_start`, `.option norvc`, `MEM_START`/`MEM_END` constants. |
| `EvmAsm/Codegen/Programs.lean` | Registry: `"smoke"`, `"evm_add"`, `"interp_tiny"`, … → `Program`. |
| `EvmAsm/Codegen/Cli.lean` | Argument parsing (`--program`, `--halt`, `--out`, `--asm-only`). |
| `EvmAsm/Codegen/Driver.lean` | `IO`: shells out to `as`/`ld` if available; `--asm-only` for CI without the cross toolchain. |
| `Main.lean` | Already exists as `import EvmAsm`; extend to call `EvmAsm.Codegen.Cli.main`. |
| `lakefile.toml` | Add `[[lean_exe]] name = "codegen"; root = "Main"; supportInterpreter = true`. |
| `scripts/codegen-smoke.sh` | One-liner driving the M0 round-trip. |
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
`gen-out/smoke.elf`; `ziskemu -e gen-out/smoke.elf` exits 0 and reports
`a2 = 100`. Test both halt modes; *record which signals are honored by
`ziskemu`* — this answers a real open question (see §Tricky bits).

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

### M2 — End-to-end `evm_add` (M)

Wire enough memory and registers so the verified `evm_add` program
(`EvmAsm/Evm64/Add/Program.lean`) computes a 256-bit sum on `ziskemu`.

- Emit a `.data` section seeding two 256-bit operands as eight LE doublewords
  inside `[MEM_START, MEM_END) = [0x20, 0x78000000)` (`EvmAsm/Rv64/Basic.lean:244,247`).
- Prologue: `li sp, <stack_top>` ; `li x12, <evm_sp>` pointing into the seeded region.
- Epilogue: copy the destination limbs to `a0`–`a3` (or via `write_output`,
  deferred to M4) before halting.

**Exit criteria.**
`ziskemu -e gen-out/evm_add.elf` halts and the post-state limbs equal the
`Word`-level sum computed via `#eval` in Lean.
`scripts/codegen-evm_add-check.sh` codifies the comparison.

### M3 — Labels (S)

Two-pass emission replaces numeric branch/jal offsets with `Lk`-style labels.
Keep numeric mode behind `--no-labels` so we can cross-check the eventual
binary encoder against `as`'s output.

**Exit criteria.**
A loop program (hand-rolled `BNE` countdown) builds with labels; `objdump -d`
shows the same encoded offsets as the `--no-labels` build.

### M4 — `read_input` / `write_output` plumbing (M)

Match the verified `Execution.lean` syscall handlers:
- `t0 = 0xF2` → `read_input` (writes `(inputBufBase, privateInput.length)` to
  `[a0]`/`[a1]`). See `EvmAsm/Rv64/Execution.lean` ~line 416.
- `t0 = 0x10` → `write_output` (concatenating). See ~line 411.

Codegen reserves `__input_buf` in a `.bss`/`.data` region exposed via an
emitted linker script template. The driver writes a Zisk prover-input file
(`--input gen-out/<prog>.input.bin`) when the program needs one.

**Exit criteria.**
A `read_input → use → write_output → HALT` program consumes a host-supplied
input file and emits the expected bytes through `ziskemu`'s output channel.

### M5 — Tiny EVM interpreter (L)

Codegen `EvmAsm/Evm64/InterpreterLoop.lean` + `EvmAsm/Evm64/Dispatch.lean` and
run small bytecodes (`PUSH1 a; PUSH1 b; ADD; STOP`, a two-op branch, …). A
reference oracle in Lean or Python diffs the expected stack against
`ziskemu`'s public output.

**Exit criteria.**
2–3 hand-picked bytecodes round-trip end-to-end against an oracle; smoke +
`evm_add` + tiny-interp all in a single CI-runnable script.

### Sequencing

M0 → M1 → (M2 ‖ M3) → M4 → M5. M2/M3 are independent; M4 unblocks M5.

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
5. **SP1 `t0=0` vs `ziskemu` HALT.** The verified `step` halts on `t0=0`
   (`EvmAsm/Rv64/Execution.lean:611-615`), but `ziskemu`'s stock examples use
   `a7=93`. M0 is the experiment that empirically answers whether `ziskemu`
   honors `t0=0`. If it doesn't, `linux93` is the default for `ziskemu` while
   `sp1` remains correct against the verified semantics. Either way
   `docs/host-io-halt-convention.md` is not pre-empted.
6. **Memory bounds.** Emitted ELFs must respect
   `MEM_START=0x20` / `MEM_END=0x78000000`. Codify in `Codegen/Layout.lean` so
   the constants can't drift from `EvmAsm/Rv64/Basic.lean:244,247`.
7. **No `read_input` in M0.** Deferred to M4. M0/M1/M2 use hardcoded values
   (smoke) or `.data` seeding (`evm_add`).
8. **Toolchain availability.** Gate the assemble/link step behind a feature
   check; CI without `riscv64-unknown-elf-as` still runs `--asm-only` to catch
   emitter regressions.
9. **Codegen is not verified.** It's an output channel, not part of the trusted
   kernel surface. The `native_decide` / `bv_decide` restrictions in
   [`CLAUDE.md`](CLAUDE.md) and [`AGENTS.md`](AGENTS.md) do not apply because
   the codegen code carries no proofs.

## Verification (per milestone)

- **M0.** `ziskemu -e gen-out/smoke.elf` exits 0; `a2` reads 100. Both halt
  modes exercised; result of the SP1/`ziskemu` experiment recorded in
  §Tricky bits above.
- **M1.** `lake build` passes (includes `RoundTripTests.lean`);
  `lake exe codegen --program evm_add --asm-only | riscv64-unknown-elf-as -march=rv64imac -o /dev/null -`
  returns 0.
- **M2.** `scripts/codegen-evm_add-check.sh` exits 0 against the `#eval`-derived
  expected limbs.
- **M3.** `diff <(codegen --no-labels … | as | objdump -d) <(codegen … | as | objdump -d)`
  shows only label-noise differences.
- **M4.** End-to-end `read_input → write_output` test: prover input file in,
  expected bytes out via `ziskemu`.
- **M5.** Per-bytecode regression script under `scripts/`; each test compares
  `ziskemu`'s `write_output` against the reference oracle.

## Future work (post-M5)

- Lean-native binary encoder (`Instr → BitVec 32` + ELF writer) to drop the
  GNU binutils dependency. Cross-check the encoded bytes against the verified
  `step` semantics.
- STF integration: consume RLP-decoded transactions via `read_input` and drive
  the full interpreter loop.
- Precompile stubs aligned with
  `EvmAsm/Evm64/zkvm-standards/standards/c-interface-accelerators`.
- Cross-zkVM testing (SP1, RISC0) to validate the halt-convention ADR closure
  described in [`docs/host-io-halt-convention.md`](docs/host-io-halt-convention.md).

## References

- [Zisk emulator quickstart](https://0xpolygonhermez.github.io/zisk/getting_started/quickstart.html)
- [Zisk ELF regressions](https://github.com/0xPolygonHermez/zisk/tree/9537bcebe414f3a2a2cbf809b3d1cd09ac1e1b68/elf-regressions)
- [Zisk `simple_add` example](https://github.com/0xPolygonHermez/zisk/blob/pre-develop-0.17.1/elf-regressions/simple_add/test.s)
- [`docs/zkvm-host-io-interface.md`](docs/zkvm-host-io-interface.md) — I/O ABI ADR
- [`docs/host-io-halt-convention.md`](docs/host-io-halt-convention.md) — halt-convention ADR (Open)
- [`docs/zkvm-host-io-input-buffer-design.md`](docs/zkvm-host-io-input-buffer-design.md) — input-buffer design
