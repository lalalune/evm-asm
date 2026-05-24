import EvmAsm.Evm64.DivMod.Spec.N1QuotientStackBridgeGetLimbStep

namespace EvmAsm.Evm64

open EvmAsm.Rv64

private theorem finalCarryZero_of_conservation_bound
    {a b q r carry : Nat}
    (hbpos : 0 < b)
    (hcons : a = q * b + r + carry * 2 ^ 256)
    (hge : a / b ≤ q)
    (hb_lt : b < 2 ^ 256) :
    carry = 0 := by
  have hcons' : a = q * b + (r + carry * 2 ^ 256) := by
    omega
  have hrem_lt : r + carry * 2 ^ 256 < b :=
    (EvmWord.remainder_lt_of_ge_floor hbpos hcons' hge).2
  by_contra hcarry_nz
  have hcarry_pos : 0 < carry := by omega
  have hrem_ge : 2 ^ 256 ≤ r + carry * 2 ^ 256 := by
    nlinarith
  omega

/-- The raw normalized n=1 conservation equation plus the legacy quotient
    overestimate forces the final overflow carry to be zero. -/
theorem fullDivN1FinalCarryZero_of_conservation_overestimate
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0)
    (hcons : fullDivN1NormalizedConservation bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN1FinalCarryZero bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  have hpow : 0 < 2 ^ (fullDivN1Shift b0).toNat := by
    positivity
  have hbScaled_pos :
      0 < EvmWord.val256 b0 b1 b2 b3 * 2 ^ (fullDivN1Shift b0).toNat := by
    have hbpos : 0 < EvmWord.val256 b0 b1 b2 b3 :=
      EvmWord.val256_pos_of_or_ne_zero hbnz
    positivity
  have hgeScaled :
      (EvmWord.val256 a0 a1 a2 a3 * 2 ^ (fullDivN1Shift b0).toNat) /
        (EvmWord.val256 b0 b1 b2 b3 * 2 ^ (fullDivN1Shift b0).toNat) ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat := by
    rw [Nat.mul_div_mul_right _ _ hpow]
    exact hge
  have hs_le64 : (fullDivN1Shift b0).toNat ≤ 64 := by
    rw [fullDivN1Shift_unfold]
    have hle := clzResult_fst_toNat_le b0
    omega
  have hb3_bound :
      b3.toNat < 2 ^ (64 - (fullDivN1Shift b0).toNat) := by
    rw [hb3z]
    simp
  have hbVal_lt :
      EvmWord.val256 b0 b1 b2 b3 <
        2 ^ (256 - (fullDivN1Shift b0).toNat) :=
    EvmWord.val256_lt_of_b3_bound b0 b1 b2 b3 hs_le64 hb3_bound
  have hbScaled_lt :
      EvmWord.val256 b0 b1 b2 b3 * 2 ^ (fullDivN1Shift b0).toNat <
        2 ^ 256 := by
    calc
      EvmWord.val256 b0 b1 b2 b3 * 2 ^ (fullDivN1Shift b0).toNat
          < 2 ^ (256 - (fullDivN1Shift b0).toNat) *
              2 ^ (fullDivN1Shift b0).toNat :=
            (Nat.mul_lt_mul_right hpow).mpr hbVal_lt
      _ = 2 ^ 256 := by
            rw [← pow_add]
            congr 1
            omega
  have hcarry_toNat_zero :
      ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2).toNat = 0 := by
    unfold fullDivN1NormalizedConservation at hcons
    exact finalCarryZero_of_conservation_bound
      (hbpos := hbScaled_pos)
      (hcons := hcons)
      (hge := hgeScaled)
      (hb_lt := hbScaled_lt)
  unfold fullDivN1FinalCarryZero
  exact BitVec.eq_of_toNat_eq hcarry_toNat_zero

/-- Step-conservation wrapper for the final n=1 carry-zero fact. -/
theorem fullDivN1FinalCarryZero_of_step_conservation_overestimate
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2)
    (hr3_zero : fullDivN1R3CarryZero bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr2_zero : fullDivN1R2CarryZero bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr1_zero : fullDivN1R1CarryZero bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN1FinalCarryZero bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  have hcons :
      fullDivN1NormalizedConservation bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 :=
    fullDivN1NormalizedConservation_of_step_conservation
      bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero
  exact fullDivN1FinalCarryZero_of_conservation_overestimate
    bltu_3 bltu_2 bltu_1 bltu_0 hbnz hb3z hcons hge

/-- Raw dispatcher-surface carry form of
    `fullDivN1FinalCarryZero_of_step_conservation_overestimate`. -/
theorem fullDivN1FinalCarryZero_of_raw_step_conservation_overestimate
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
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
    (hr3_zero : fullDivN1R3CarryZero bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr2_zero : fullDivN1R2CarryZero bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr1_zero : fullDivN1R1CarryZero bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN1FinalCarryZero bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  have hcarry2Norm : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2 := by
    unfold fullDivN1NormV fullDivN1Shift fullDivN1AntiShift
    rw [fullDivN1Shift_unfold]
    exact hcarry2
  exact fullDivN1FinalCarryZero_of_step_conservation_overestimate
    bltu_3 bltu_2 bltu_1 bltu_0
    a0 a1 a2 a3 b0 b1 b2 b3
    hbnz hb1z hb2z hb3z hshift_nz hcarry2Norm
    hr3_zero hr2_zero hr1_zero hge

/-- Step-conservation bridge to the normalized n=1 Euclidean equation,
    deriving the final carry-zero witness internally from the legacy quotient
    overestimate. -/
theorem fullDivN1NormalizedMulSubEq_of_step_conservation_overestimate_final
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2)
    (hr3_zero : fullDivN1R3CarryZero bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr2_zero : fullDivN1R2CarryZero bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr1_zero : fullDivN1R1CarryZero bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  have hfinal_zero : fullDivN1FinalCarryZero bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 :=
    fullDivN1FinalCarryZero_of_step_conservation_overestimate
      bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hge
  exact fullDivN1NormalizedMulSubEq_of_step_conservation
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    hbnz hb1z hb2z hb3z hshift_nz hcarry2
    hr3_zero hr2_zero hr1_zero hfinal_zero

/-- Raw dispatcher-surface carry form of
    `fullDivN1NormalizedMulSubEq_of_step_conservation_overestimate_final`. -/
theorem fullDivN1NormalizedMulSubEq_of_raw_step_conservation_overestimate_final
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
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
    (hr3_zero : fullDivN1R3CarryZero bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr2_zero : fullDivN1R2CarryZero bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr1_zero : fullDivN1R1CarryZero bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  have hfinal_zero : fullDivN1FinalCarryZero bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 :=
    fullDivN1FinalCarryZero_of_raw_step_conservation_overestimate
      bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hge
  exact fullDivN1NormalizedMulSubEq_of_raw_step_conservation
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    hbnz hb1z hb2z hb3z hshift_nz hcarry2
    hr3_zero hr2_zero hr1_zero hfinal_zero

/-- Raw step-conservation bridge to the normalized n=1 final-remainder bound,
    deriving the final carry-zero and normalized mulsub facts internally from
    the legacy quotient overestimate. -/
theorem fullDivN1NormalizedRemainderLt_of_raw_step_conservation_overestimate_final
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
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
    (hr3_zero : fullDivN1R3CarryZero bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr2_zero : fullDivN1R2CarryZero bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr1_zero : fullDivN1R1CarryZero bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN1NormalizedRemainderLt bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  have hmulsub : fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 :=
    fullDivN1NormalizedMulSubEq_of_raw_step_conservation_overestimate_final
      bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hge
  exact fullDivN1NormalizedRemainderLt_of_mulsub_overestimate
    bltu_3 bltu_2 bltu_1 bltu_0 hbnz hmulsub hge

/-- GetLimb-level n=1 hdiv witness from raw step conservation plus the
    legacy quotient overestimate, deriving the final carry-zero fact
    internally. -/
theorem fullDivN1_getLimbN_of_getLimbN_step_conservation_overestimate_final
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hb1z : b.getLimbN 1 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb3z : b.getLimbN 3 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hcarry2 : Carry2NzAll
      (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
      ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult (b.getLimbN 0)).1).toNat % 64))))
    (hr3_zero : fullDivN1R3CarryZero bltu_3
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hr2_zero : fullDivN1R2CarryZero bltu_3 bltu_2
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hr1_zero : fullDivN1R1CarryZero bltu_3 bltu_2 bltu_1
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hge :
      EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) /
        EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3) ≤
        ((fullDivN1R3 bltu_3
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN1R1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN1R2 bltu_3 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 3 =
      (fullDivN1R3 bltu_3
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  have hfinal_zero : fullDivN1FinalCarryZero bltu_3 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
    fullDivN1FinalCarryZero_of_raw_step_conservation_overestimate
      bltu_3 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hge
  exact fullDivN1_getLimbN_of_getLimbN_step_conservation_overestimate
    bltu_3 bltu_2 bltu_1 bltu_0 hbnz hb1z hb2z hb3z hshift_nz hcarry2
    hr3_zero hr2_zero hr1_zero hfinal_zero hge

/-- Explicit-limb n=1 hdiv witness from raw step conservation plus the
    legacy quotient overestimate, deriving the final carry-zero fact
    internally. -/
theorem fullDivN1_getLimbN_of_step_conservation_overestimate_final
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
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
    (hr3_zero : fullDivN1R3CarryZero bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr2_zero : fullDivN1R2CarryZero bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr1_zero : fullDivN1R1CarryZero bltu_3 bltu_2 bltu_1
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 3 =
      (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  subst a0
  subst a1
  subst a2
  subst a3
  subst b0
  subst b1
  subst b2
  subst b3
  exact fullDivN1_getLimbN_of_getLimbN_step_conservation_overestimate_final
    bltu_3 bltu_2 bltu_1 bltu_0 hbnz hb1z hb2z hb3z hshift_nz hcarry2
    hr3_zero hr2_zero hr1_zero hge

end EvmAsm.Evm64
