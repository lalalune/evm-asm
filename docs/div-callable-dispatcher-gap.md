# DIV Callable Dispatcher Exact-Frame Gap

This note records the current no-NOP DIV dispatcher surface for
`evm-asm-9iqmw.2.1`.

## Target Shape

SDIV Phase 0 needs a DIV body theorem over the callable-ready precondition

```lean
divModStackDispatchPreNoX1 sp a b x9Val raVal ...
```

whose postcondition preserves both caller-framed registers exactly:

```lean
divStackDispatchPostCallableExactFrame sp a b raVal x9Val
```

Equivalently, after unfolding the named post, the proof must end in:

```lean
((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) ** (.x9 ↦ᵣ x9Val))
```

## Existing Usable Surfaces

- `EvmAsm.Evm64.DivMod.Spec.CallablePost`
  defines `divStackDispatchPostCallableExactFrame` and the unfold lemma
  `divStackDispatchPostCallableExactFrame_unfold`.
- `EvmAsm.Evm64.DivMod.Spec.N1ExactNoNop`
  has an exact-frame v4 surface for the n=1 call/max/max/max subcase:
  `evm_div_n1_call_maxmaxmax_stack_spec_within_word_noNop_v4_preNoX1_callableExtra_x9In_exactFrame_unified`.
- `EvmAsm.Evm64.DivMod.Spec.N2DivStackSpec`
  and `N3DivStackSpec` already provide conversion helpers from an exact
  no-`x1` post plus `(.x1 ↦ᵣ raVal)` into
  `divStackDispatchPostCallableExactFrame`.
- PR #5839 adds a thin zero-divisor wrapper named
  `evm_div_stack_spec_bzero_noNop_preNoX1_callableExactFrame`, exposing the
  existing bzero no-NOP dispatcher proof through the named exact-frame post.

## Remaining Proof Gap

The public n=1/n=2/n=3 callable-ready dispatcher wrappers currently stop at
the ownership-only shape:

```lean
((divStackDispatchPostCallable sp a b ** regOwn .x1) **
  (.x9 ↦ᵣ (signExtend12 4095 : Word)))
```

The relevant theorem names are:

- `evm_div_n1_stack_spec_within_word_noNop_preNoX1_callableOwnPost`
- `evm_div_n2_stack_spec_within_word_noNop_preNoX1_callableOwnPost`
- `evm_div_n3_stack_spec_within_word_noNop_preNoX1_callableOwnPost`
- `evm_div_stack_spec_noNop_preNoX1_callableOwnPost`

For n=2 and n=3, the loss happens in the precondition weakening step that
turns `(.x1 ↦ᵣ raVal)` from `divModStackDispatchPreNoX1` into `regOwn .x1`
before calling the older `divModStackDispatchPre` theorem. Once this happens,
the exact `raVal` cannot be recovered by a postcondition wrapper.

The next proof slice should therefore avoid the ownership-only theorem and
instead prove a branch-level no-NOP theorem that starts from
`divModStackDispatchPreNoX1` and feeds an exact `(.x1 ↦ᵣ raVal)` into the
existing exact-frame conversion helper for that branch.
