# EEST Scenario Frontier

The Amsterdam blockchain-test fixture reported by the user is generated at:

```text
gen-out/eest-fixtures/zkevm@v0.4.0/fixtures/fixtures/blockchain_tests/for_amsterdam/frontier/scenarios/scenarios/scenarios.json
```

It comes from `execution-specs/tests/frontier/scenarios/test_scenarios.py` and
the generators under `execution-specs/tests/frontier/scenarios/scenarios/`.
The current cached fixture contains 34 test-program entries and 1,258 stateless
blocks.

This is a broad feature-completeness frontier, not a narrow opcode fixture. The
scenario generator combines CALL, CREATE, revert, double-call, and static-context
execution shapes, then runs many operation programs through those shapes. A
failure here can point at several existing surfaces at once: call/create frame
execution, revert propagation, environment opcodes, storage/log/selfdestruct
effects, returndata, gas, receipts, and post-state root computation.

The owning bead is `evm-asm-fhsxz.2.4.2.60.11`. Use this fixture filter when
probing it through the stateless harness:

```bash
scripts/codegen-eest-stateless-check.sh \
  --filter frontier/scenarios/scenarios/scenarios \
  --skip 0 \
  --limit 40 \
  --jobs 1 \
  --quiet-passes \
  --max-failures 1 \
  --steps 200000000
```

## Program Windows

The fixture is ordered by test-program id. Each program contributes 37 stateless
blocks, so targeted `--skip` windows are stable for this cached fixture:

| Skip | Count | Program |
| ---: | ---: | --- |
| 0 | 37 | `program_ADDRESS` |
| 37 | 37 | `program_ALL_FRONTIER_OPCODES` |
| 74 | 37 | `program_BALANCE` |
| 111 | 37 | `program_BASEFEE` |
| 148 | 37 | `program_BLOBBASEFEE` |
| 185 | 37 | `program_BLOBHASH` |
| 222 | 37 | `program_BLOCKHASH` |
| 259 | 37 | `program_CALLDATACOPY` |
| 296 | 37 | `program_CALLDATALOAD` |
| 333 | 37 | `program_CALLDATASIZE` |
| 370 | 37 | `program_CALLER` |
| 407 | 37 | `program_CALLVALUE` |
| 444 | 37 | `program_CHAINID` |
| 481 | 37 | `program_CODECOPY_CODESIZE` |
| 518 | 37 | `program_COINBASE` |
| 555 | 37 | `program_DIFFICULTY` |
| 592 | 37 | `program_EXTCODECOPY_EXTCODESIZE` |
| 629 | 37 | `program_EXTCODEHASH` |
| 666 | 37 | `program_GASLIMIT` |
| 703 | 37 | `program_GASPRICE` |
| 740 | 37 | `program_INVALID` |
| 777 | 37 | `program_LOGS` |
| 814 | 37 | `program_MCOPY` |
| 851 | 37 | `program_NUMBER` |
| 888 | 37 | `program_ORIGIN` |
| 925 | 37 | `program_PUSH0` |
| 962 | 37 | `program_RETURNDATACOPY` |
| 999 | 37 | `program_RETURNDATASIZE` |
| 1036 | 37 | `program_SELFBALANCE` |
| 1073 | 37 | `program_SSTORE_SLOAD` |
| 1110 | 37 | `program_SUICIDE` |
| 1147 | 37 | `program_TIMESTAMP` |
| 1184 | 37 | `program_TLOAD` |
| 1221 | 37 | `program_TSTORE_TLOAD` |

## Current Triage

A bounded prefix run on 2026-06-02 passed the first 40 selected blocks fully:
all 37 `program_ADDRESS` blocks plus the first 3 `program_ALL_FRONTIER_OPCODES`
blocks.

```bash
scripts/codegen-eest-stateless-check.sh \
  --filter frontier/scenarios/scenarios/scenarios \
  --limit 40 \
  --jobs 1 \
  --max-failures 5 \
  --quiet-passes \
  --steps 200000000 \
  --no-build \
  --run-dir /tmp/eest-scenarios-triage-run
```

The next bounded continuation run started at `--skip 105`, after the already
observed passing prefix. It stopped on the first concrete failure cluster:
`program_BALANCE` blocks `b31` through `b36` returned
`successful_validation = 0`, while the fixture expects `1`. The NPR root and
chain-config tail matched; only the success bit differed.

```bash
scripts/codegen-eest-stateless-check.sh \
  --filter frontier/scenarios/scenarios/scenarios \
  --skip 105 \
  --limit 300 \
  --jobs auto \
  --max-failures 5 \
  --quiet-passes \
  --steps 200000000 \
  --no-build \
  --no-verdict-debug \
  --run-dir /tmp/eest-scenarios-skip105-run
```

Observed failing cases:

| Global index | Program case | Expected succ | Guest succ | Root | Tail |
| ---: | --- | ---: | ---: | --- | --- |
| 105 | `program_BALANCE` `b31` | 1 | 0 | match | match |
| 106 | `program_BALANCE` `b32` | 1 | 0 | match | match |
| 107 | `program_BALANCE` `b33` | 1 | 0 | match | match |
| 108 | `program_BALANCE` `b34` | 1 | 0 | match | match |
| 109 | `program_BALANCE` `b35` | 1 | 0 | match | match |
| 110 | `program_BALANCE` `b36` | 1 | 0 | match | match |

The execution-specs source for this program is
`execution-specs/tests/frontier/scenarios/programs/context_calls.py`:
`ProgramBalance` deploys an external account with balance `123`, then returns
`BALANCE(external_address)`. This failure cluster is therefore covered by the
existing P0 implementation bead `evm-asm-fhsxz.2.4.2.60.5.3`, which wires
`BALANCE`, `EXTCODESIZE`, `EXTCODEHASH`, and `EXTCODECOPY` through witness-backed
account/code reads.

When triaging later failures, continue from the window table above and first
identify the test-program id in the fixture name. If the failure belongs to an
already-open implementation bead, add the concrete case there instead of filing
a duplicate.
