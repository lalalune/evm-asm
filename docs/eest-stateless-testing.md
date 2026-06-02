# EEST Stateless Guest Testing

This runbook covers the fixture-driven stateless guest harness:

```bash
scripts/codegen-eest-stateless-check.sh [options]
```

The harness builds `stateless_guest`, converts EEST `zkevm` fixture blocks
into `ziskemu -i` inputs, runs each selected input, and compares the 105-byte
guest output with the fixture's `statelessOutputBytes`.

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

The report includes `state_witness_bytes` and `over_bsr_cap`; the latter marks
inputs whose state witness exceeds the current 32 KiB `block_state_root` cap.
Pass `--bsr-cap N` to model a different proposed cap in that column.

To run a focused harness experiment with a proposed guest-side witness cap,
pass `--bsr-witness-cap N`. The default guest remains unchanged; the harness
patches the emitted assembly and relinks only for that run:

```bash
scripts/codegen-eest-bal-replay-frontier-check.sh \
  --bsr-witness-cap 65536 \
  --steps 400000000
```

The checked version of that experiment is:

```bash
scripts/codegen-eest-bal-replay-frontier-64k-check.sh
```

It requires the current `19/20` full-match frontier and leaves the large
170 KiB witness case as the remaining conservative miss.

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

The current run directory is recreated each time:

```text
gen-out/eest-run/
```

Important files:

- `manifest.tsv`: one row per selected guest invocation.
- `<case>.input`: ziskemu input for that fixture block.
- `<case>.output`: raw guest output.
- `<case>.emu.log`: ziskemu stdout/stderr.
- `<case>.result.tsv`: per-case harness status and output hex.
- `gen-out/eest-baseline.txt`: run summary for the latest harness execution.

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
