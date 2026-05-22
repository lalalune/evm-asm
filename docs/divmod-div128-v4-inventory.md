# DivMod div128 v4 migration inventory

This is the Step 1 inventory for bead `evm-asm-9iqmw.4.3`.

Inventory command for the bead acceptance scope:

```bash
rg -n "divK_div128\b|div128_spec\b|div128SpecPost\b" \
  EvmAsm/Evm64/DivMod/Compose \
  EvmAsm/Evm64/DivMod/LimbSpec \
  EvmAsm/Evm64/DivMod/Spec
```

## Acceptance-Scope Hits

### `Compose/Offsets.lean`

Category: documentation/constants for the legacy v1 layout.

The hits name the original `divK_div128` placement and call-return offsets.
They should stay until the old v1/v2 code surfaces are deleted or renamed,
because current legacy definitions still use those offsets. They are not proof
dependencies on `div128_spec`.

### `Compose/Div128Post.lean`

Category: legacy v1 postcondition surface.

`div128SpecPost` is the bundled postcondition for the old `divK_div128`
subroutine. Its v4 counterpart is `div128V4SpecPost` in
`Compose/Div128V4.lean`. This file is a deletion candidate after all remaining
legacy v1/v2 specs and callers are retired.

### `Compose/Div128.lean`

Category: legacy v1/v2 composition layer.

This file contains the old `div128_spec`-family surfaces over `divK_div128` and
`div128SpecPost`. The v4 replacement is already present in
`Compose/Div128V4.lean`, including lifted specs over `sharedDivModCode_v4` and
`sharedDivModCodeNoNop_v4`. Remaining migration work should move downstream
callers to the v4 surfaces, then delete or quarantine this legacy layer.

### `Compose/Base.lean`

Category: mixed legacy and v4 code-handle plumbing.

The file still defines legacy `divCode`, `modCode`, `sharedDivModCode`, and
no-NOP variants over `divK_div128`. It also already contains v4 mirrors such as
`sharedDivModCode_v4` and v4/no-NOP code handles. Remaining migration work is
not to rewrite the legacy handles in place, but to move downstream specs to the
existing v4 code handles and then remove the legacy handles when no longer used.

## Nearby Follow-On Surface

The broader search

```bash
rg -n "\bdiv128_spec\b|\bdiv128SpecPost\b|\bdiv128_v4_spec\b|\bdiv128V4SpecPost\b" \
  EvmAsm/Evm64/DivMod
```

also finds legacy `div128SpecPost` consumers in:

- `LoopBody/TrialCall.lean`
- `LoopBody/TrialCallPath.lean`

Those are outside the bead's acceptance-scope command, but they are the next
real proof-layer migration candidates. Both files already contain v4 siblings
using `div128V4SpecPost`, so the practical next slice is to replace or retire
the remaining legacy trial-call surfaces rather than introducing new v4
postconditions.
