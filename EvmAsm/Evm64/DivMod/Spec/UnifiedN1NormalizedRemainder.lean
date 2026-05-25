/-
  EvmAsm.Evm64.DivMod.Spec.UnifiedN1NormalizedRemainder

  Normalized-remainder n=1 wrappers over the unified DIV code path.
-/

import EvmAsm.Evm64.DivMod.Spec.UnifiedN1Normalized

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Trial-bundled n=1 DIV wrapper from normalized mulsub plus
    normalized final-remainder obligations. -/
theorem evm_div_n1_stack_spec_within_word_trial_normalized_remainder_uni
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (htrial : N1TrialWitnesses a b)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hpath : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1NormalizedRemainderLt bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) := by
  obtain ⟨bltu_3, bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    N1TrialWitnesses.exists htrial
  obtain ⟨hmulsub, hrem_lt⟩ :=
    hpath bltu_3 bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  exact evm_div_n1_stack_spec_within_word_uni_of_normalized_mulsub_overestimate
    bltu_3 bltu_2 bltu_1 bltu_0 sp base a b
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
    hshift_nz halign
    (by simpa [ha3, hb0] using hbltu_3)
    (by simpa [ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_2)
    (by simpa [ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_1)
    (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_0)
    hcarry2
    (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hmulsub)
    (by
      exact fullDivN1QuotientOverestimate_of_normalized_mulsub_remainder_lt
        bltu_3 bltu_2 bltu_1 bltu_0
        (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hmulsub)
        (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hrem_lt))

/-- Shape-specialized n=1 DIV wrapper from normalized mulsub plus
    normalized final-remainder obligations. -/
theorem evm_div_n1_stack_spec_within_word_shape_normalized_remainder_uni
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
    (hcarry2 : Carry2NzAll
      (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
      ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 0 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 1 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 2 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))))
    (hpath : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1NormalizedRemainderLt bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
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
  have htrial : N1TrialWitnesses a b :=
    n1TrialWitnesses_of_getLimbN_shape_shift_nz
      a b hbnzGet hb3z hb2z hb1z hshift_nz
  exact evm_div_n1_stack_spec_within_word_trial_normalized_remainder_uni
    sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    rfl rfl rfl rfl rfl rfl rfl rfl hbnzGet hb3z hb2z hb1z
    hshift_nz halign htrial hcarry2 hpath

end EvmAsm.Evm64
