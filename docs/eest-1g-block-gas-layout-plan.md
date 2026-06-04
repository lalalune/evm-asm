# EEST 1G Block-Gas Layout Plan

This is the implementation plan for bead
`evm-asm-fhsxz.2.4.2.57.9.1.1`. It replaces the PR #8044 direction of
classifying high-gas EIP-8037 fixtures as `ERROR(layout)`: the desired behavior
is to make those fixtures launch and expose semantic verdict failures or passes.

## Target

The full EEST log at `/tmp/eest-all-2026-06-03.txt` shows
`ERROR(layout)` for EIP-8037 `state_gas_pricing` fixtures at these block gas
limits:

- 200,000,000
- 300,000,000
- 500,000,000
- 1,000,000,000

Use 1,000,000,000 as the next static-layout target. Amsterdam BAL validation is
gas-derived:

```text
bal_items <= block_gas_limit / 2000
```

So the target BAL budget is 500,000 items. `block_state_root` also starts with
two modeled system changes, so any top-level change-count cap must cover at
least 500,002 rows.

## Current Blocker

Current `BlockVerdict.lean` guards are sized for the execution-specs default
120,000,000 block gas limit:

```asm
li t0, 120000000; bgtu a0, t0, .Lbsr_cons_change_cap
...
add t0, s1, t6; li t1, 60018; bgtu t0, t1, .Lbsr_cons_change_cap
```

The EEST shell harness mirrors this with
`EEST_BSR_MAX_BLOCK_GAS_LIMIT=120000000`, so the 1G cases currently fail before
ziskemu launches.

## Static Sizing

For a direct 1G static layout, scale every arena indexed by `bsr_bal_count` or
state-change count together. Do not only raise the gas guard.

| Arena | Current bytes | Current capacity | 1G capacity | 1G bytes |
| --- | ---: | ---: | ---: | ---: |
| `basr_records` | 1,440,432 | 60,018 * 24 | 500,002 | 12,000,048 |
| `basr_paths` | 3,841,152 | 60,018 * 64 | 500,002 | 32,000,128 |
| `basr_values` | 15,364,608 | 60,018 * 256 | 500,002 | 128,000,512 |
| `basr_accounts` | 15,364,608 | 60,018 * 256 | 500,002 | 128,000,512 |

The per-account storage replay arrays in `BlockVerdict.lean` also need scaling
for the opposite BAL shape: one or a few accounts with many storage keys. Their
current hard caps are effectively 60,000 storage paths/values and 100,000
storage descriptors:

| Arena | Current bytes | Current capacity | Minimum 1G capacity | Minimum 1G bytes |
| --- | ---: | ---: | ---: | ---: |
| `baap_storage_desc` | 2,400,000 | 60,000 * 40 | 500,000 | 20,000,000 |
| `baap_storage_paths` | 3,840,000 | 60,000 * 64 | 500,000 | 32,000,000 |
| `baap_storage_delete_paths` | 3,840,000 | 60,000 * 64 | 500,000 | 32,000,000 |
| `baap_storage_values` | 3,840,000 | 60,000 * 64 | 500,000 | 32,000,000 |

`BalAccountApplyPostFields.lean` has matching hard-coded `60000` guards for
storage-output and deletion counts. The `BlockVerdict.lean` embedded copy must
be kept consistent with those guards if the implementation remains static.

The straightforward static increase adds about 344 MiB over the current BSR/BAL
arena sizes before unrelated `.data` objects.

## Memory Map

The current stateless layout is:

```text
0xa0010000 .. 0xa0020000   OUTPUT_ADDR
0xa0020000 .. 0xa5000000   working RAM
0xa5000000 .. 0xb0000000   .data
0xb0000000 .. 0xb2000000   .sszscratch
0xb2000000 .. 0xc0000000   remaining verified RAM headroom
```

A direct 1G static layout does not fit comfortably in the current
`0xa5000000..0xb0000000` `.data` window, and it must not collide with
`.sszscratch`. The implementation should move `.sszscratch` upward and enlarge
or relocate `.data` while staying inside verified RAM `0xa0000000..0xc0000000`.

Recommended PR-sized static map:

```text
0xa0010000 .. 0xa0020000   OUTPUT_ADDR
0xa0020000 .. 0xa5000000   working RAM, unchanged
0xa5000000 .. 0xb9000000   .data, enough for 1G BSR/BAL static arenas
0xba000000 .. 0xbc000000   .sszscratch, 32 MiB NOBITS
0xbc000000 .. 0xc0000000   guard/headroom
```

This keeps all regions in the existing verified RAM range and preserves a gap
between `.data` and `.sszscratch`. Update all linker invocations together:

- `EvmAsm/Codegen/Driver.lean`
- `scripts/codegen-eest-stateless-check.sh`
- `scripts/codegen-zisk-stateless-verdict-check.sh`
- `EvmAsm/Stateless/MemoryLayout.lean`
- any docs that spell out the stateless memory map

## Implementation Checklist

1. Introduce named layout constants in `BlockVerdict.lean` before changing
   assembly strings, at least:
   - `bsrMaxBlockGasLimit = 1000000000`
   - `bsrBalItemGasCost = 2000`
   - `bsrMaxBalItems = 500000`
   - `bsrMaxStateChanges = 500002`
2. Replace hard-coded `120000000`, `60018`, and `60000` values in the BSR/BAL
   path with values derived from those constants.
3. Resize all `basr_*` and `baap_storage_*` static arenas consistently.
4. Move `.sszscratch` to the selected high address and update
   `SSZ_SCRATCH_BASE` docs/constants.
5. Update the EEST harness default max gas limit to 1,000,000,000 and update
   `patch_bsr_caps_asm` so experimental caps still patch the new constants.
6. Replace the PR #8044 regression with a launch-coverage test: the high-gas
   EIP-8037 fixtures should run ziskemu and produce semantic pass/fail output,
   not `ERROR(layout)`.
7. Run focused EEST with `--filter eip8037_state_creation_gas_cost_increase`
   and an explicit `--max-failures` to capture the next semantic blockers.

## Static vs Streaming

A streaming/chunked replay design would be better long-term because memory would
scale with actual fixture contents instead of worst-case gas. However, the next
implementation PR can be a larger static layout if it keeps the ELF map disjoint
and documents the supported maximum as 1G. Do not keep the pre-launch layout
error for these observed EEST gas limits.
