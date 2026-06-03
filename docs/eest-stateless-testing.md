# EEST Stateless Guest Testing

This runbook covers the fixture-driven stateless guest harness:

```bash
scripts/codegen-eest-stateless-check.sh [options]
```

The harness builds `stateless_guest`, converts EEST `zkevm` fixture blocks
into `ziskemu -i` inputs, runs each selected input, and compares the 105-byte
guest output with the fixture's `statelessOutputBytes`.

For missing-feature scheduling, see
[`docs/eest-feature-surfaces.md`](eest-feature-surfaces.md). It maps EEST
fixture classes to the active transaction, gas, state, opcode, call/create,
precompile, and receipt/log feature beads.

## Prerequisites

Install the normal codegen requirements from the README: Lean/Lake,
`riscv64-elf-binutils`, and `ziskemu`.

Fetch the EEST fixture tarball once:

```bash
scripts/eest-fetch-fixtures.sh zkevm@v0.4.0
```

By default the harness reads:

```text
gen-out/eest-fixtures/zkevm@v0.4.0/fixtures/fixtures
```

Override that with `EEST_FIXTURES_DIR=/path/to/fixtures` when needed. Use
`EEST_FIXTURE_TAG=...` or `--tag ...` to select a different cached release.

## Common Commands

Run the default smoke subset:

```bash
scripts/codegen-eest-stateless-check.sh
```

Run a focused fixture subset:

```bash
scripts/codegen-eest-stateless-check.sh \
  --filter bal_7002_partial_sweep \
  --limit 2 \
  --jobs 32 \
  --steps 200000000
```

Run the complete `random_statetest` regression class for `zkevm@v0.4.0`:

```bash
scripts/codegen-eest-random-statetest-check.sh --jobs 8
```

This wrapper first counts the selected `random_statetest` blocks for the active
fixture tag, then loops over every block in fixed-size windows with
`--min-full` set to the actual chunk size and `--max-failures 1`. Set
`EEST_RANDOM_WINDOW=N` to change the default 200-case window size.

Run a focused simple value-transfer transaction frontier:

```bash
scripts/codegen-eest-simple-value-transfer-frontier-check.sh --jobs 1
```

This wrapper loops over the simple transaction/value-transfer fixture filters
from the feature-surface report and forwards `--skip`, `--limit`, `--jobs`, and
`--max-failures` to the stateless harness. It is a baseline probe today: it does
not claim the selected fixtures pass until the value-transfer validation,
state-effect, gas-settlement, and post-state integration children under bead
`evm-asm-fhsxz.2.4.2.56` land.

Run the literal EXTCODEHASH missing-code regression filters:

```bash
scripts/codegen-eest-literal-extcodehash-check.sh --jobs 4
```

This wrapper counts and runs the `witness_codes_extcodehash_only` and
`witness_codes_extcode_delegated_eoa` filters with `--min-full` set to each
filter's current selected count, so future cases added to those filters are
covered automatically.

Run the 1,000-block windows immediately after `random_statetest`:

```bash
scripts/codegen-eest-post-random-window-check.sh --jobs 8
scripts/codegen-eest-post-random-window-2-check.sh --jobs 8
scripts/codegen-eest-post-random-window-3-check.sh --jobs 8
scripts/codegen-eest-post-random-window-4-check.sh --jobs 8
```

The first starts at `--skip 17085` (`16582 + 503`), the second starts at
`--skip 18085`, the third starts at `--skip 19085`, and the fourth starts at
`--skip 20085`. Each checks `--limit 1000` with a `--min-full 1000`
regression threshold.

Run the focused EXP opcode regression:

```bash
scripts/codegen-eest-exp-power256-check.sh
```

This checks the Amsterdam `exp_power256` state-test fixture and requires a full
105-byte stateless output match. Override `EEST_EXP_POWER256_JOBS` or
`EEST_EXP_POWER256_STEPS` for this wrapper without changing the broader harness
defaults.

Run a fast EIP-2929 precompile-warming frontier:

```bash
scripts/codegen-eest-precompile-warming-frontier-check.sh
```

This selects the first `precompile_warming` fixture. The executable-spec source
is `execution-specs/tests/berlin/eip2929_gas_cost_increases/test_precompile_warming.py`:
it runs a transaction whose contract measures `BALANCE` gas for precompile
addresses across a fork transition, then checks the resulting storage. The
current guest gets the stateless root and tail correct for this case, but the
success bit is still `0` instead of the expected `1`, making it a quick
transaction/opcode frontier distinct from the BAL large-witness non-completion.
Override `EEST_PRECOMPILE_WARMING_JOBS` or `EEST_PRECOMPILE_WARMING_STEPS`
for this wrapper without changing the broader harness defaults.

To see the broader precompile fixture frontier, including families not selected
by the narrow warming probe, run:

```bash
scripts/eest-precompile-frontier-report.py --markdown
```

After any `scripts/codegen-eest-stateless-check.sh` run, the same command also
reads the latest `manifest.tsv` and `*.result.tsv` files under `gen-out/eest-run`
(including the harness's `run-*` subdirectories) and groups completed
full/root/success/tail outcomes by precompile family. The report is a coverage
matrix, not a success claim: today
`EvmAsm/Stateless/VM/Precompiles.lean` still routes precompile dispatch to the
unimplemented frontier, while the reusable accelerator payload/ECALL bridges
are tracked from [`docs/zkvm-accelerators-interface.md`](zkvm-accelerators-interface.md).

Run the current BAL replay frontier around the EIP-7002 withdrawal-request
cluster:

```bash
scripts/codegen-eest-bal-replay-frontier-check.sh --jobs 4
```

This filters to `withdrawal_requests`, starts at local `--skip 83`, checks
`--limit 20`, and stops after the two known conservative misses. With parallel
jobs, the number of completed passes before the stop point depends on
scheduling. Use `scripts/eest-bal-replay-report.py --details` after a run to
inspect the BAL row shape for the selected inputs.

To inspect only the completed frontier misses from the latest run:

```bash
uv run --directory execution-specs --quiet python3 \
  ../scripts/eest-bal-replay-report.py --failures-only --details
```

The report includes `state_witness_bytes`, `over_bsr_cap`, `bal_rows`, and
`over_bsr_bal_cap`; the cap columns mark inputs whose state witness or BAL row
count exceeds the current `block_state_root` caps. Pass `--bsr-cap N` and
`--bsr-bal-cap N` to model different proposed arena caps in those columns. The
guest default is a 64 KiB state-witness cap. That is an implementation cap for
the current EEST harness, not a protocol maximum.

The BSR scratch layout was reviewed against the local `execution-specs`
checkout. The hard protocol/test limits that matter for the current layout are:
Prague/Amsterdam withdrawal requests cap at 16 per payload
(`execution-specs/src/ethereum/forks/amsterdam/stateless_ssz.py`), Osaka block
RLP size caps at 8,388,608 bytes
(`execution-specs/src/ethereum/forks/osaka/fork.py`), Osaka transaction gas
caps at 16,777,216 (`execution-specs/src/ethereum/forks/osaka/transactions.py`),
and EVM code/initcode caps are 24 KiB / 48 KiB
(`execution-specs/src/ethereum/forks/osaka/vm/interpreter.py`). Amsterdam BAL
validation is gas-derived rather than a fixed row count: the accepted item count
is at most `block_gas_limit / 2000`, where items are account addresses plus
unique storage keys
(`execution-specs/src/ethereum/forks/amsterdam/block_access_lists.py` and
`execution-specs/src/ethereum/forks/amsterdam/vm/gas.py`).

The guest uses bounded arenas rather than dynamic host memory. `block_state_root`
first applies the Amsterdam gas-derived BAL budget, then applies its current
static layout sized for the execution-specs default 120,000,000 block gas limit.
The harness reads the block gas limit from the converted SSZ input manifest and
errors before launching `ziskemu` when a fixture needs a larger layout/ELF.
Larger gas-valid BALs need a streaming/chunked replay path or a separately built
larger static layout.

To run a focused harness experiment with different guest-side replay caps, pass
`--bsr-witness-cap N` for the block-state-root witness-byte cap or
`--bsr-bal-cap N` to add a lower BAL-row cap after the Amsterdam gas-derived
budget. The harness patches the emitted assembly and relinks only for that run:

```bash
scripts/codegen-eest-bal-replay-frontier-check.sh \
  --steps 400000000
```

The checked version of that experiment is:

```bash
scripts/codegen-eest-bal-replay-frontier-64k-check.sh
```

It requires the current `19/20` full-match frontier and leaves the large
170 KiB witness case as the remaining conservative miss.

To expose the next blocker behind that conservative miss, run:

```bash
scripts/codegen-eest-bal-large-witness-frontier-check.sh
```

This selects the single large-witness withdrawal-request case, raises the
experimental block-state-root witness cap to 256 KiB, and stops after the first
reported failure or error. The current blocker is an emulator non-completion
before the guest writes stateless output, even with a 2B-step cap.

To probe the large remaining case past both known caps:

```bash
scripts/codegen-eest-stateless-check.sh \
  --filter withdrawal_requests \
  --skip 83 \
  --limit 20 \
  --jobs 4 \
  --quiet-passes \
  --bsr-witness-cap 262144 \
  --bsr-bal-cap 1024 \
  --steps 400000000
```

The same cap experiment can be run against the focused verdict probe, which
emits debug counters instead of the full stateless output:

```bash
scripts/codegen-zisk-stateless-verdict-check.sh \
  --filter withdrawal_requests \
  --skip 87 \
  --limit 1 \
  --bsr-witness-cap 262144 \
  --bsr-bal-cap 1024 \
  --steps 2000000000
```

Each verdict line prints the fixture's block gas limit separately from the
path, followed by named debug counters from fixed 8-byte output slots:

```text
dbg=[bv_fail=... header=... state=... bal_count=... bsr_fail=... change_count=... witness_len=... baacd_fail=... bacv_fail=... baap_fail=... sri_index=... sri_mode=... sri_status=...]
```

The main EEST harness uses the same fixed-size probe automatically on
`successful_validation` mismatches and appends its decoded slots to the `FAIL`
line. Disable that rerun with `--no-verdict-debug` or `EEST_VERDICT_DEBUG=0`
when only the canonical 105-byte stateless output comparison is wanted.

`bv_fail` is the top-level block-verdict failure code. `bsr_fail` and
`bal_count` classify the block-state-root replay path, while the `baacd`,
`bacv`, `baap`, and `sri` fields expose the lower-level account, storage, and
state-read helpers.

For receipt/log-specific misses, generate a triage map that links likely
blockers to focused beads:

```bash
scripts/eest-receipt-log-frontier-report.py --run-dir gen-out/eest-run --limit 100
```

See [`eest-receipt-log-frontier.md`](eest-receipt-log-frontier.md) for the
class definitions and owner beads.

Run a large batch:

```bash
scripts/codegen-eest-stateless-check.sh \
  --limit 1000 \
  --jobs 32 \
  --steps 200000000
```

Resume from a later offset by skipping the first selected cases:

```bash
scripts/codegen-eest-stateless-check.sh \
  --skip 1000 \
  --limit 1000 \
  --jobs 32 \
  --steps 200000000
```

Collect only the first few failures from a large or highly parallel run:

```bash
scripts/codegen-eest-stateless-check.sh \
  --all \
  --jobs 32 \
  --quiet-passes \
  --max-failures 20 \
  --steps 200000000
```

Run every selected stateless block:

```bash
scripts/codegen-eest-stateless-check.sh \
  --all \
  --jobs 32 \
  --steps 200000000
```

`--filter` is applied first, `--skip N` skips the first N stateless blocks in
that filtered order, and `--limit N` caps how many remaining blocks are emitted.
With `--all`, `--skip` still applies but no limit is added.

`--max-failures N` stops the harness once N `FAIL` or `ERROR` results have been
classified. `--stop-after-failures N` is an alias. With parallel jobs, workers
that already finished before the stop point may also be reported, but the
harness stops scheduling new cases and cleans up active workers once the cap is
observed.

Use `--quiet-passes` (or `EEST_QUIET_PASSES=1`) to suppress per-case
`PASS(full)` lines while still printing every `FAIL` and `ERROR` plus the final
summary. This is useful for large `--jobs 32 --max-failures N` searches after a
long passing prefix. `--show-passes` restores the default verbose pass output.

## Focused Verdict Probe

For verdict-only debugging, use the smaller probe harness:

```bash
scripts/codegen-zisk-stateless-verdict-check.sh \
  --filter validation_codes_missing \
  --limit 100 \
  --max-failures 5 \
  --steps 200000000
```

In this probe, `--max-failures N` stops after N `ERROR`, false-positive, or
unexpected `DIFF` rows. Conservative misses (`verdict=0 exp=1`) are still
reported, but they do not count toward this cap because they are not unsound
acceptances.

## Outputs

Each harness invocation writes to a fresh run directory so concurrent EEST
searches do not clobber each other's manifests or case outputs:

```text
gen-out/eest-run/run-<timestamp>-<pid>/
```

Set `EEST_RUN_DIR=/path/to/dir` to force a stable directory for a single
reproducible run; that directory is recreated at the start of the invocation.

Important files:

- `manifest.tsv`: one row per selected guest invocation.
- `<case>.input`: ziskemu input for that fixture block.
- `<case>.output`: raw guest output.
- `<case>.emu.log`: ziskemu stdout/stderr.
- `<case>.result.tsv`: per-case harness status and output hex.
- `stateless_guest.{s,o,elf}`: guest artifacts for this invocation.
- `eest-baseline.txt`: run summary for this invocation.
- `gen-out/eest-baseline.txt`: copy of the latest harness summary.

The summary reports:

- `full match`: all 105 output bytes match.
- `root match`: bytes 0:32 match `new_payload_request_root`.
- `succ match`: byte 32 matches `successful_validation`.
- `tail match`: bytes 33:105 match the offset and chain config tail.
- `root-only diff`: success and tail match, but the root field differs.

Use `--min-full`, `--min-root`, or `--min-succ` to turn a batch into a
regression gate. For example:

```bash
scripts/codegen-eest-stateless-check.sh --limit 1000 --min-full 1000
```

## Useful Knobs

- `ZISKEMU=/path/to/ziskemu`: choose a specific emulator binary.
- `EEST_STEPS=N` or `--steps N`: set the ziskemu step cap.
- `EEST_JOBS=N` or `--jobs N`: set parallel guest jobs.
- `--max-failures N` or `--stop-after-failures N`: stop after N failures/errors.
- `EEST_QUIET_PASSES=1` or `--quiet-passes`: hide per-case pass lines.
- `EEST_MEM_RESERVE_MIB=N`: reserve host memory when auto-sizing jobs.
- `EEST_FIXTURES_DIR=/path`: point at an already extracted fixture directory.
