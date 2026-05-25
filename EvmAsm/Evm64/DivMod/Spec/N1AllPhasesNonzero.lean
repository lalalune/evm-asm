import EvmAsm.Evm64.DivMod.Spec.N1AllPhasesGetLimb

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Selected all-call path evidence for the n=1 DIV wrapper. This is not the
    old universal `Carry2NzAll` target: callers provide evidence only after the
    concrete all-true branch facts have been established. -/
abbrev N1AllTruePathEvidence (a b : EvmWord) : Prop :=
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
  Div128AllPhasesNoWrapInv
    (fullDivN1NormU
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0)).2.2.2.2
    (fullDivN1NormU
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0)).2.2.2.1
    (fullDivN1NormV
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
  Div128AllPhasesNoWrapInv
    (fullDivN1R3 true
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
    (fullDivN1NormU
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0)).2.2.1
    (fullDivN1NormV
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
  Div128AllPhasesNoWrapInv
    (fullDivN1R2 true true
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
    (fullDivN1NormU
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0)).2.1
    (fullDivN1NormV
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
  Div128AllPhasesNoWrapInv
    (fullDivN1R1 true true true
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
    (fullDivN1NormU
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0)).1
    (fullDivN1NormV
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
  fullDivN1NormalizedRemainderLt true true true true
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

/-- Callback form of `N1AllTruePathEvidence`, gated by the actual selected
    all-true branch facts. -/
abbrev N1AllTruePathCallback (a b : EvmWord) : Prop :=
  isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) →
  isTrialN1_j2 true true
    (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
  isTrialN1_j1 true true true
    (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
  isTrialN1_j0 true true true true
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
  N1AllTruePathEvidence a b

/-- `b ≠ 0` surface for the all-call n=1 path-level quotient-word wrapper. -/
theorem n1_quotient_word_true_true_true_true_of_path_remainders_lt_all_phases_no_wrap_ne_zero
    (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hr3_lt :
      EvmWord.val256
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr2_lt :
      EvmWord.val256
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr1_lt :
      EvmWord.val256
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hpath :
      isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 true true
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 true true true
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 true true true true
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
      Div128AllPhasesNoWrapInv
        (fullDivN1NormU
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0)).2.2.2.2
        (fullDivN1NormU
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormV
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      Div128AllPhasesNoWrapInv
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormU
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0)).2.2.1
        (fullDivN1NormV
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      Div128AllPhasesNoWrapInv
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormU
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0)).2.1
        (fullDivN1NormV
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      Div128AllPhasesNoWrapInv
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormU
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0)).1
        (fullDivN1NormV
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      fullDivN1NormalizedRemainderLt true true true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    fullDivN1QuotientWord true true true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
      EvmWord.div a b :=
  n1_quotient_word_true_true_true_true_of_path_remainders_lt_all_phases_no_wrap
    a b ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz) hb3z hb2z hb1z hshift_nz
    hr3_lt hr2_lt hr1_lt hpath

end EvmAsm.Evm64
