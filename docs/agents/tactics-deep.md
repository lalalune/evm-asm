# EvmAsm — Deep Tactics & Architecture

Moved out of `AGENTS.md` to keep the agent guide compact. Load this when:
- writing or restructuring frame-automation (`runBlock`, `seqFrame`, `xperm`, `xcancel`),
- using the LP64 calling convention or designing a callable shim,
- working on a three-level opcode proof (limb → composition → semantic stack spec),
- splitting Compose files in parallel or working with the file-size guardrail,
- consuming the `benchmark-history` orphan branch.

See also `TACTICS.md` (user-facing tactic reference) and `GRIND.md` (grindset definitions).

## Frame-automation Tactics

**Primary reference:** [`TACTICS.md`](TACTICS.md) is the user guide for
`runBlock`, `seqFrame`, `xperm`, `xcancel`, the `@[spec_gen]` registry,
and the domain-specific grindsets (`divmod_addr`, `rv64_addr`, `reg_ops`,
`byte_alg`). Read it before hand-writing a `cpsTriple_seq_*` chain or
wiring a new `@[...]` equality-closing attribute from scratch.

## Separation Conjunction Permutation Tactic

The `sep_perm` tactic (defined in `SepLogic.lean`) closes goals that require rearranging `sepConj` (`**`) chains. It works by AC-normalizing both the hypothesis and goal using `simp` with three equality lemmas:

- `sepConj_assoc'` : `((P ** Q) ** R) = (P ** (Q ** R))`
- `sepConj_comm'` : `(P ** Q) = (Q ** P)`
- `sepConj_left_comm'` : `(P ** (Q ** R)) = (Q ** (P ** R))`

**Usage**: Given a hypothesis `h : (A ** B ** C) s` and goal `⊢ (C ** A ** B) s`:
```lean
sep_perm h
```

This handles arbitrary permutations of any number of assertions in a `sepConj` chain.

Additional equality lemmas for `empAssertion` elimination:
- `sepConj_emp_right'` : `(P ** empAssertion) = P`
- `sepConj_emp_left'` : `(empAssertion ** P) = P`

When rearranging involves `memBufferIs` (which unfolds to `... ** empAssertion`), combine all rules in one `simp`:
```lean
simp only [memBufferIs, addr_100_plus_4, addr_104_plus_4,
  sepConj_emp_right', sepConj_emp_left',
  sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hab ⊢
exact hab
```

## Calling Convention (LP64)

New functions **must** follow the LP64 calling convention defined in
`Evm64/CallingConvention.lean`. This applies to opcode handlers, the
interpreter dispatch loop, RLP routines, and any new subroutines.

**Register roles** (per zkvm-standards):

| Register | ABI | Role | Saved by |
|----------|-----|------|----------|
| x1 | ra | Return address | Caller |
| x2 | sp | Call stack (grows down) | **Callee** |
| x5-x7 | t0-t2 | Temporaries | Caller |
| x10-x11 | a0-a1 | Args / return values | Caller |
| x12 | a2 | EVM stack pointer | Caller |

**Reusable snippets** (use these, don't hand-roll):

| Snippet | Purpose |
|---------|---------|
| `cc_ret` | Return: `JALR x0, x1, 0` |
| `cc_prologue` | Non-leaf prologue: `ADDI sp, sp, -16 ;; SD sp, ra, 8` |
| `cc_epilogue` | Non-leaf epilogue: `LD ra, sp, 8 ;; ADDI sp, sp, 16 ;; JALR x0, ra, 0` |

**Proved specs** — use these instead of reproving from scratch:

- `callNear_spec` / `callFar_spec` — JAL/JALR call saves return address
- `ret_spec` / `ret_spec'` — JALR x0 x1 0 returns to caller
- `cc_prologue_spec` — prologue block spec (2 instructions)
- `cc_epilogue_spec` — epilogue block spec (3 instructions)
- `callNear_function_spec` — compose JAL + function callable spec → round-trip
- `nonleaf_function_spec` — compose prologue + body + epilogue → full function

**Pattern for a new leaf function:**
```lean
def my_func : Program := body ;; cc_ret
```

**Pattern for a new non-leaf function:**
```lean
def my_func : Program := cc_prologue ;; body ;; cc_epilogue
```

The existing DivMod subroutine uses an older ad-hoc convention (x2 as return
address). New code should **not** copy that pattern — use the LP64 convention.

## Three-Level Opcode Proof Architecture

Each EVM opcode follows a three-level proof hierarchy:

1. **Limb-level specs** (`LimbSpec.lean`, `ShlSpec.lean`, `SarSpec.lean`): Per-instruction specs composed with `runBlock`. These operate on raw 64-bit memory cells (`↦ₘ`).
2. **Composition** (`Compose.lean`, `ShlCompose.lean`, `SarCompose.lean`): Hierarchical composition of limb specs into full-program theorems. Includes:
   - `xyzCode` definition (`CodeReq.unionAll` of per-phase `CodeReq.ofProg` blocks)
   - Subsumption lemmas (structural `skipBlock` + `union_mono_left`, no `native_decide` on full programs)
   - Address normalization lemmas (`bv_addr` proofs — see Build Performance section)
   - Path composition (zero-path/sign-fill for shift >= 256, body-path for shift < 256)
   - Bridge lemmas connecting per-limb results to `getLimb (result) i`
3. **Semantic** (`Semantic.lean`, `ShlSemantic.lean`, `SarSemantic.lean`): Stack-level `evmWordIs` spec. Lifts composition to `EvmWord` assertions using `cpsTriple_weaken` + `xperm_hyp`.

### Composition File Pattern (for shift opcodes)

Each shift Compose file (~1000-1200 lines) follows this structure:
1. **Section 1**: `xyzCode` definition as `CodeReq.unionAll` of per-phase `ofProg` blocks + length lemmas + `skipBlock` macro + helpers (`singleton_sub_ofProg`, `CodeReq_union_sub_both`, `regIs_to_regOwn`)
2. **Section 2**: Subsumption lemmas — structural reasoning via `skipBlock` + `union_mono_left` (following the DivMod pattern). For union-chain `_code` definitions (Phase A, Phase C, sign-fill), split into bridge sub-lemma (`chain_code ⊆ ofProg small_block`) + structural sub-lemma (`ofProg small_block ⊆ xyzCode`)
3. **Section 3**: Address normalization — `bv_addr` proofs for all offset arithmetic (see Build Performance section)
4. **Section 4**: Zero-path or sign-fill composition — instruction-by-instruction Phase A chain + branch elimination + path composition
5. **Section 5**: Phase C dispatch — `cpsNBranch` with cascade steps
6. **Section 6**: Bridge lemmas — connect limb formulas to `getLimb (operation value n)`
7. **Section 7**: Body path composition — Phase A(ntaken) + B + C + body_L + exit with bridge application

### Bridge Lemma Pattern

Bridge lemmas in `Evm64/Basic.lean` connect per-limb arithmetic to 256-bit operations:
- **SHR**: `getLimb_ushiftRight` (single lemma covering all cases via `getLimbN`)
- **SHL**: `getLimb_shiftLeft`, `getLimb_shiftLeft_eq_div`, `getLimb_shiftLeft_low`
- **SAR**: `getLimb_sshiftRight_eq_ushiftRight` (merge case, delegates to ushiftRight), `getLimb_sshiftRight_last` (SRA on MSB limb), `getLimb_sshiftRight_sign'` (sign extension)

### Key Learnings for Shift Composition

- **SAR sign-fill path** uses `sar_sign_fill_path_spec` which takes `.x5` and `.x10` in its precondition (unlike `shr_zero_path_spec` which only takes `.x12`). This means the frame for sign-fill is smaller than for zero-path.
- **Address normalization direction matters**: The sign-fill path spec uses `sp + 40` directly, not `(sp + 32) + 8`. Don't apply `ha40 : sp + 40 = (sp + 32) + 8` in permutation callbacks if the assertions already use `sp + 40`. Use `xperm_hyp` directly — it handles both forms.
- **Subsumption via unionAll (preferred pattern)**: Define `xyzCode` as `CodeReq.unionAll` of per-phase `ofProg` blocks (not a flat `ofProg base evm_xyz`). Then subsumption is structural: `skipBlock` skips disjoint blocks, `union_mono_left` matches the target block. For union-chain `_code` definitions, add a bridge sub-lemma using `singleton_sub_ofProg`/`ofProg_mono_sub` on the **small** sub-program (5-25 elements). Never use `native_decide` on the full 90-95 instruction program — that's the old pattern and requires 4-8M heartbeats. See `DivMod/Compose.lean` for the canonical reference.
- **`local macro` for file-scoped tactics**: When defining `skipBlock` (or similar) in multiple Compose files, use `local macro` not `macro`. Without `local`, importing multiple files causes "environment already contains" errors.
- **`sshiftRight (sshiftRight x n) 63 = sshiftRight x 63`**: This identity (sign extension is idempotent under further shifting by 6

... [OUTPUT TRUNCATED - 5696 chars omitted out of 55696 total] ...

ng and per-domain extensions.

**Do not** introduce a new opcode subtree without an `AddrNorm` pair on the
first commit that adds non-trivial address arithmetic — see
[`EvmAsm/Evm64/OPCODE_TEMPLATE.md`](EvmAsm/Evm64/OPCODE_TEMPLATE.md) §2.5.
Retrofitting the grindset later is the tax that issue #263 documents.

### Parallel file splitting for Compose files

Large composition files (>1000 lines) should be split into independent sub-files under a `Compose/` directory:
- `Compose/Base.lean`: shared definitions (`divCode`, `modCode`, `skipBlock`, length lemmas)
- Independent sub-files (PhaseAB, CLZ, Norm, NormA, Div128, Epilogue) that all import only Base
- `Compose.lean`: lightweight re-export of all sub-files

This enables parallel kernel checking. The split reduced DivMod/Compose from 87s (monolithic) to 55s (critical path through Norm.lean).

### File-size guardrail

The advice above is enforced mechanically by `scripts/check-file-size.sh`, which runs as the first step of the Build CI workflow:

| Path | Hard cap |
|---|---|
| `EvmAsm/Evm64/**/Compose/**/*.lean` | 1200 lines (soft cap 1000) |
| `EvmAsm/Evm64/**/*.lean` (everything else) | 1500 lines |
| `Program.lean` (any directory) | exempt — concrete bytecode + tests, no proof cost |

A file over cap **must** be split. Do not add opt-out comments or approve
oversized proof modules; the guardrail intentionally has no per-file override.

To run the check locally:

```sh
scripts/check-file-size.sh           # exit 1 on any violation
scripts/check-file-size.sh --report  # always exit 0; summarize over-cap files and forbidden exemption markers
```

### Benchmark history (`benchmark-history` orphan branch)

The Monday `benchmark.yml` cron appends one JSON object per successful
run to `history.jsonl` on the long-lived `benchmark-history` orphan
branch (created on first push by the workflow itself). Each row carries
`commit`, `timestamp`, `wall_seconds`, `peak_rss_kb`, `runner_os`,
`runner_cores`, … — see `docs/benchmark-workflow-design.md` for the
full schema and rationale.

To inspect the historical series locally:

```bash
git fetch origin benchmark-history
git show origin/benchmark-history:history.jsonl | tail -n 20
# project a single metric over time:
git show origin/benchmark-history:history.jsonl \
  | jq -r '[.timestamp, .commit[:12], .wall_seconds] | @tsv'
```

When chasing a build-time regression, correlate adjacent `wall_seconds`
jumps with `git log --oneline <prev-sha>..<curr-sha>` between the two
recorded `commit` values. Files that have historically driven the
largest deltas live under `EvmAsm/Evm64/DivMod/` (compose chains; see
the `xperm` notes above) and `EvmAsm/Evm64/Shift/` (composition files
where bumping `set_option maxHeartbeats` is permitted per the Critical
Rules).
