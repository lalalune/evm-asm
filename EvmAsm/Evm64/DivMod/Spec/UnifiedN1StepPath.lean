/-
  EvmAsm.Evm64.DivMod.Spec.UnifiedN1StepPath

  N1 unified stack wrappers that consume the step-conservation path surface
  directly.
-/

import EvmAsm.Evm64.DivMod.Spec.N1FinalCarryZero
import EvmAsm.Evm64.DivMod.Spec.UnifiedN1Normalized

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Shape-specialized n=1 no-NOP DIV callable wrapper from the
    step-conservation path surface plus quotient overestimate. -/
theorem evm_div_n1_stack_spec_within_word_noNop_preNoX1_callableOwnPost_shape_step_conservation_overestimate_uni
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (hpath : ∀ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 true bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 true bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      Carry2NzAll
        (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
        ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 0 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
        ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 1 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
        ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 2 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))) ∧
      fullDivN1R3CarryZero true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN1R2CarryZero true bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN1R1CarryZero true bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN1QuotientOverestimate true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      ((divStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  have hbnzGet :
      b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
        b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  obtain ⟨bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    n1_trial_witnesses_call_first_of_getLimbN_shape_shift_nz
      a b hbnzGet hb3z hb2z hb1z hshift_nz
  obtain ⟨hcarry2, hr3_zero, hr2_zero, hr1_zero, hge⟩ :=
    hpath bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have hdivWord :
      fullDivN1QuotientWord true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b :=
    fullDivN1QuotientWord_eq_div_of_getLimbN_step_conservation_overestimate_final
      true bltu_2 bltu_1 bltu_0 hbnzGet hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hge
  exact evm_div_n1_stack_spec_within_word_noNop_preNoX1_callableOwnPost_uni
    true bltu_2 bltu_1 bltu_0 sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 raVal
    rfl rfl rfl rfl rfl rfl rfl rfl hbnzGet hb3z hb2z hb1z
    hshift_nz halign hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2 hdivWord

/-- Shape-specialized n=1 no-NOP DIV wrapper from the step-conservation path
    surface plus quotient overestimate. -/
theorem evm_div_n1_stack_spec_within_word_noNop_shape_step_conservation_overestimate_uni
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (hpath : ∀ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 true bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 true bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      Carry2NzAll
        (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
        ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 0 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
        ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 1 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
        ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 2 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))) ∧
      fullDivN1R3CarryZero true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN1R2CarryZero true bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN1R1CarryZero true bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN1QuotientOverestimate true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) := by
  have hbnzGet :
      b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
        b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  obtain ⟨bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    n1_trial_witnesses_call_first_of_getLimbN_shape_shift_nz
      a b hbnzGet hb3z hb2z hb1z hshift_nz
  obtain ⟨hcarry2, hr3_zero, hr2_zero, hr1_zero, hge⟩ :=
    hpath bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have hfinal_zero : fullDivN1FinalCarryZero true bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
    fullDivN1FinalCarryZero_of_raw_step_conservation_overestimate
      true bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hbnzGet hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hge
  have hmulsub : fullDivN1NormalizedMulSubEq true bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
    fullDivN1NormalizedMulSubEq_of_raw_step_conservation
      true bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hbnzGet hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hfinal_zero
  exact evm_div_n1_stack_spec_within_word_noNop_uni_of_normalized_mulsub_overestimate
    true bltu_2 bltu_1 bltu_0 sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    rfl rfl rfl rfl rfl rfl rfl rfl hbnzGet hb3z hb2z hb1z
    hshift_nz halign hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2 hmulsub hge

/-- Shape-specialized n=1 exact-x1/no-NOP DIV wrapper from the
    step-conservation path surface plus quotient overestimate. -/
theorem evm_div_n1_stack_spec_within_word_exact_x1_noNop_shape_step_conservation_overestimate_uni
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (hpath : ∀ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 true bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 true bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      Carry2NzAll
        (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
        ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 0 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
        ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 1 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
        ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 2 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))) ∧
      fullDivN1R3CarryZero true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN1R2CarryZero true bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN1R1CarryZero true bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN1QuotientOverestimate true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPostNoX1 sp a b **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  have hbnzGet :
      b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
        b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  obtain ⟨bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    n1_trial_witnesses_call_first_of_getLimbN_shape_shift_nz
      a b hbnzGet hb3z hb2z hb1z hshift_nz
  obtain ⟨hcarry2, hr3_zero, hr2_zero, hr1_zero, hge⟩ :=
    hpath bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have hfinal_zero : fullDivN1FinalCarryZero true bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
    fullDivN1FinalCarryZero_of_raw_step_conservation_overestimate
      true bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hbnzGet hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hge
  have hmulsub : fullDivN1NormalizedMulSubEq true bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
    fullDivN1NormalizedMulSubEq_of_raw_step_conservation
      true bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hbnzGet hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hfinal_zero
  exact evm_div_n1_stack_spec_within_word_exact_x1_noNop_uni_of_normalized_mulsub_overestimate
    true bltu_2 bltu_1 bltu_0 sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    rfl rfl rfl rfl rfl rfl rfl rfl hbnzGet hb3z hb2z hb1z
    hshift_nz halign hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2 hmulsub hge

/-- Shape-specialized n=1 exact-x1 DIV wrapper from the step-conservation
    path surface plus quotient overestimate. -/
theorem evm_div_n1_stack_spec_within_word_exact_x1_shape_step_conservation_overestimate_uni
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (hpath : ∀ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 true bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 true bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      Carry2NzAll
        (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
        ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 0 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
        ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 1 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
        ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 2 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))) ∧
      fullDivN1R3CarryZero true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN1R2CarryZero true bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN1R1CarryZero true bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN1QuotientOverestimate true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPostNoX1 sp a b **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  have hbnzGet :
      b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
        b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  obtain ⟨bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    n1_trial_witnesses_call_first_of_getLimbN_shape_shift_nz
      a b hbnzGet hb3z hb2z hb1z hshift_nz
  obtain ⟨hcarry2, hr3_zero, hr2_zero, hr1_zero, hge⟩ :=
    hpath bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have hfinal_zero : fullDivN1FinalCarryZero true bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
    fullDivN1FinalCarryZero_of_raw_step_conservation_overestimate
      true bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hbnzGet hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hge
  have hmulsub : fullDivN1NormalizedMulSubEq true bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
    fullDivN1NormalizedMulSubEq_of_raw_step_conservation
      true bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hbnzGet hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hfinal_zero
  exact evm_div_n1_stack_spec_within_word_exact_x1_uni_of_normalized_mulsub_overestimate
    true bltu_2 bltu_1 bltu_0 sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    rfl rfl rfl rfl rfl rfl rfl rfl hbnzGet hb3z hb2z hb1z
    hshift_nz halign hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2 hmulsub hge

end EvmAsm.Evm64
