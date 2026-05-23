/-
  EvmAsm.Evm64.DivMod.Spec.N3RemainderWordV4

  Packed n=3 MOD remainder word for the v4 call/max final computation.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V4
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN4V4NoNop
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN3LoopUnified
import EvmAsm.Evm64.DivMod.Spec.CallablePost
import EvmAsm.Evm64.DivMod.Spec.N3QuotientStackBridge
import EvmAsm.Evm64.EvmWordArith.DivAccumulate
import EvmAsm.Evm64.EvmWordArith.KnuthTheoremB

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero se12_32 se12_40 se12_48 se12_56)

/-- v4 n=3 MOD remainder word, using the v4 call-path `fullDivN3R0V4`
computation before the usual denormalization shift. -/
@[irreducible]
def fullModN3RemainderWordV4 (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 =>
        (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
    | 1 =>
        (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
    | 2 =>
        (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
    | 3 =>
        ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)))

/-- `val256` view of `fullModN3RemainderWordV4`.  This is the arithmetic
target needed to discharge the current word-level MOD path predicate. -/
@[irreducible]
def fullModN3RemainderVal256V4 (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Nat :=
  EvmWord.val256
    (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
        ((fullDivN3Shift b2).toNat % 64)) |||
      ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
        ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
    (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
        ((fullDivN3Shift b2).toNat % 64)) |||
      ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
        ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
    (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
        ((fullDivN3Shift b2).toNat % 64)) |||
      ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
        ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
    ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
      ((fullDivN3Shift b2).toNat % 64))

/-- Turn the `val256` denormalized-remainder equality into the public
`EvmWord.mod` word equality for the n=3 v4 final computation. -/
theorem fullModN3RemainderWordV4_eq_mod_of_val256_eq_mod
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hval : fullModN3RemainderVal256V4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.val256
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        EvmWord.val256
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    fullModN3RemainderWordV4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.mod a b := by
  let r0 :=
    (((fullDivN3R0V4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1 >>>
        ((fullDivN3Shift (b.getLimbN 2)).toNat % 64)) |||
      ((fullDivN3R0V4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1 <<<
        ((signExtend12 (0 : BitVec 12) - fullDivN3Shift (b.getLimbN 2)).toNat % 64)))
  let r1 :=
    (((fullDivN3R0V4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1 >>>
        ((fullDivN3Shift (b.getLimbN 2)).toNat % 64)) |||
      ((fullDivN3R0V4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1 <<<
        ((signExtend12 (0 : BitVec 12) - fullDivN3Shift (b.getLimbN 2)).toNat % 64)))
  let r2 :=
    (((fullDivN3R0V4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1 >>>
        ((fullDivN3Shift (b.getLimbN 2)).toNat % 64)) |||
      ((fullDivN3R0V4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <<<
        ((signExtend12 (0 : BitVec 12) - fullDivN3Shift (b.getLimbN 2)).toNat % 64)))
  let r3 :=
    ((fullDivN3R0V4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 >>>
      ((fullDivN3Shift (b.getLimbN 2)).toNat % 64))
  have hraw := EvmWord.mod_of_val256_eq_mod
    (a0 := a.getLimbN 0) (a1 := a.getLimbN 1)
    (a2 := a.getLimbN 2) (a3 := a.getLimbN 3)
    (b0 := b.getLimbN 0) (b1 := b.getLimbN 1)
    (b2 := b.getLimbN 2) (b3 := b.getLimbN 3)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3)
    hbnz (by
      subst r0; subst r1; subst r2; subst r3
      delta fullModN3RemainderVal256V4 at hval
      exact hval)
  dsimp only at hraw
  have haFold : (EvmWord.fromLimbs fun i : Fin 4 => match i with
      | 0 => a.getLimbN 0 | 1 => a.getLimbN 1
      | 2 => a.getLimbN 2 | 3 => a.getLimbN 3) = a :=
    EvmWord.fromLimbs_match_getLimbN_id a
  have hbFold : (EvmWord.fromLimbs fun i : Fin 4 => match i with
      | 0 => b.getLimbN 0 | 1 => b.getLimbN 1
      | 2 => b.getLimbN 2 | 3 => b.getLimbN 3) = b :=
    EvmWord.fromLimbs_match_getLimbN_id b
  have hmodFold :
      EvmWord.mod
        (EvmWord.fromLimbs fun i : Fin 4 => match i with
          | 0 => a.getLimbN 0 | 1 => a.getLimbN 1
          | 2 => a.getLimbN 2 | 3 => a.getLimbN 3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with
          | 0 => b.getLimbN 0 | 1 => b.getLimbN 1
          | 2 => b.getLimbN 2 | 3 => b.getLimbN 3) =
        EvmWord.mod a b := by
    rw [haFold, hbFold]
  subst r0; subst r1; subst r2; subst r3
  delta fullModN3RemainderWordV4
  exact hraw.trans hmodFold

/-- MOD-specific N3 v4 path predicate for caller-facing bridges. The first
component is the shared DIV quotient/path predicate; the second records that
the packed denormalized remainder is the EVM MOD result. -/
abbrev fullModN3PathConditionsWordV4 (bltu_1 bltu_0 : Bool)
    (a b : EvmWord) : Prop :=
  fullDivN3PathConditionsWordV4 bltu_1 bltu_0 a b ∧
  fullModN3RemainderWordV4 bltu_1 bltu_0
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
      EvmWord.mod a b

/-- MOD-specific N3 v4 path predicate with the remaining arithmetic obligation
stated at `val256` level. This is the preferred shape for closing the current
N3 MOD semantic gap, since it can be discharged by normalized-remainder
arithmetic and then bridged to `EvmWord.mod`. -/
abbrev fullModN3PathConditionsVal256V4 (bltu_1 bltu_0 : Bool)
    (a b : EvmWord) : Prop :=
  fullDivN3PathConditionsWordV4 bltu_1 bltu_0 a b ∧
  fullModN3RemainderVal256V4 bltu_1 bltu_0
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
      EvmWord.val256
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
      EvmWord.val256
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

/-- MOD-specific N3 v4 path predicate at the normalized-remainder level.
This is the shape expected from the remaining loop arithmetic proof: the
normalized final remainder is the true EVM remainder scaled by `2^shift`. -/
abbrev fullModN3PathConditionsScaledV4 (bltu_1 bltu_0 : Bool)
    (a b : EvmWord) : Prop :=
  fullDivN3PathConditionsWordV4 bltu_1 bltu_0 a b ∧
  EvmWord.val256
    (fullDivN3R0V4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
    (fullDivN3R0V4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
    (fullDivN3R0V4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
    (fullDivN3R0V4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 =
    EvmWord.val256
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
      EvmWord.val256
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
      2 ^ (fullDivN3Shift (b.getLimbN 2)).toNat

/-- Normalized Euclidean equation expected from the remaining N3 v4 loop
arithmetic proof. The final normalized remainder `fullDivN3R0V4` is paired
with the two accumulated quotient limbs. -/
abbrev fullDivN3NormalizedMulSubEqV4 (bltu_1 bltu_0 : Bool)
    (a b : EvmWord) : Prop :=
  EvmWord.val256
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
      2 ^ (fullDivN3Shift (b.getLimbN 2)).toNat =
    (((fullDivN3R1V4 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1).toNat *
        2 ^ 64 +
      ((fullDivN3R0V4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1).toNat) *
      (EvmWord.val256
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ (fullDivN3Shift (b.getLimbN 2)).toNat) +
    EvmWord.val256
      (fullDivN3R0V4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN3R0V4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN3R0V4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
      (fullDivN3R0V4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1

/-- Normalized remainder bound paired with
`fullDivN3NormalizedMulSubEqV4`. Together these are the standard Euclidean
facts needed to recover the EVM MOD remainder. -/
abbrev fullDivN3NormalizedRemainderLtV4 (bltu_1 bltu_0 : Bool)
    (a b : EvmWord) : Prop :=
  EvmWord.val256
      (fullDivN3R0V4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN3R0V4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN3R0V4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
      (fullDivN3R0V4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
    EvmWord.val256
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
      2 ^ (fullDivN3Shift (b.getLimbN 2)).toNat

theorem fullModN3PathConditionsScaledV4_of_normalized_euclidean
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hdivPath : fullDivN3PathConditionsWordV4 bltu_1 bltu_0 a b)
    (hmulsub : fullDivN3NormalizedMulSubEqV4 bltu_1 bltu_0 a b)
    (hrlt : fullDivN3NormalizedRemainderLtV4 bltu_1 bltu_0 a b) :
    fullModN3PathConditionsScaledV4 bltu_1 bltu_0 a b := by
  refine ⟨hdivPath, ?_⟩
  exact EvmWord.normalized_remainder_eq_mod_mul_pow
    ((fullDivN3Shift (b.getLimbN 2)).toNat) hmulsub hrlt

theorem fullModN3PathConditionsWordV4_of_val256
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hpath : fullModN3PathConditionsVal256V4 bltu_1 bltu_0 a b) :
    fullModN3PathConditionsWordV4 bltu_1 bltu_0 a b := by
  obtain ⟨hdivPath, hval⟩ := hpath
  exact ⟨hdivPath,
    fullModN3RemainderWordV4_eq_mod_of_val256_eq_mod
      bltu_1 bltu_0 a b hbnz hval⟩

theorem fullDivN3Shift_toNat_pos_of_ne {b2 : Word}
    (hshift_nz : fullDivN3Shift b2 ≠ 0) :
    0 < (fullDivN3Shift b2).toNat := by
  exact Nat.pos_of_ne_zero (by
    intro h_zero
    exact hshift_nz (BitVec.eq_of_toNat_eq h_zero))

theorem fullDivN3Shift_toNat_le_63 (b2 : Word) :
    (fullDivN3Shift b2).toNat ≤ 63 := by
  delta fullDivN3Shift
  exact clzResult_fst_toNat_le b2

theorem fullDivN3Shift_toNat_mod_eq (b2 : Word) :
    (fullDivN3Shift b2).toNat % 64 = (fullDivN3Shift b2).toNat :=
  Nat.mod_eq_of_lt (by
    have h_le := fullDivN3Shift_toNat_le_63 b2
    omega)

theorem fullDivN3AntiShift_toNat_mod_eq_of_shift_ne {b2 : Word}
    (hshift_nz : fullDivN3Shift b2 ≠ 0) :
    (signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64 =
      64 - (fullDivN3Shift b2).toNat := by
  have h1 : 1 ≤ (fullDivN3Shift b2).toNat := by
    have h_pos := fullDivN3Shift_toNat_pos_of_ne hshift_nz
    omega
  have h63 := fullDivN3Shift_toNat_le_63 b2
  exact antiShift_toNat_mod_eq h1 h63

/-- Reduce the N3 v4 MOD `val256` remainder obligation to the normalized
scaled-remainder equality produced before denormalization. -/
theorem fullModN3RemainderVal256V4_eq_mod_of_scaled_remainder
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    {s : Nat} (hs0 : 0 < s) (hs : s < 64)
    (hshift : (fullDivN3Shift (b.getLimbN 2)).toNat % 64 = s)
    (hanti :
      (signExtend12 (0 : BitVec 12) - fullDivN3Shift (b.getLimbN 2)).toNat % 64 =
        64 - s)
    (hscaled :
      EvmWord.val256
        (fullDivN3R0V4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN3R0V4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN3R0V4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN3R0V4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 =
      EvmWord.val256
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        EvmWord.val256
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) * 2 ^ s) :
    fullModN3RemainderVal256V4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.val256
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        EvmWord.val256
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  let r0 := (fullDivN3R0V4 bltu_1 bltu_0
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
  let r1 := (fullDivN3R0V4 bltu_1 bltu_0
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
  let r2 := (fullDivN3R0V4 bltu_1 bltu_0
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
  let r3 := (fullDivN3R0V4 bltu_1 bltu_0
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1
  have hdenorm := EvmWord.val256_denormalize hs0 hs r0 r1 r2 r3
  subst r0; subst r1; subst r2; subst r3
  delta fullModN3RemainderVal256V4
  rw [hshift, hanti, hdenorm, hscaled]
  exact Nat.mul_div_cancel _ (by positivity : 0 < 2 ^ s)

/-- Version of `fullModN3RemainderVal256V4_eq_mod_of_scaled_remainder` with
the CLZ shift side conditions discharged from `fullDivN3Shift b2 ≠ 0`. -/
theorem fullModN3RemainderVal256V4_eq_mod_of_scaled_remainder_shift_ne
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hshift_nz : fullDivN3Shift (b.getLimbN 2) ≠ 0)
    (hscaled :
      EvmWord.val256
        (fullDivN3R0V4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN3R0V4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN3R0V4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN3R0V4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 =
      EvmWord.val256
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        EvmWord.val256
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ (fullDivN3Shift (b.getLimbN 2)).toNat) :
    fullModN3RemainderVal256V4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.val256
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        EvmWord.val256
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  fullModN3RemainderVal256V4_eq_mod_of_scaled_remainder
    bltu_1 bltu_0 a b
    (fullDivN3Shift_toNat_pos_of_ne hshift_nz)
    (by
      have h_le := fullDivN3Shift_toNat_le_63 (b.getLimbN 2)
      omega)
    (fullDivN3Shift_toNat_mod_eq (b.getLimbN 2))
    (fullDivN3AntiShift_toNat_mod_eq_of_shift_ne hshift_nz)
    hscaled

theorem fullModN3PathConditionsVal256V4_of_scaled
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hshift_nz : fullDivN3Shift (b.getLimbN 2) ≠ 0)
    (hpath : fullModN3PathConditionsScaledV4 bltu_1 bltu_0 a b) :
    fullModN3PathConditionsVal256V4 bltu_1 bltu_0 a b := by
  obtain ⟨hdivPath, hscaled⟩ := hpath
  exact ⟨hdivPath,
    fullModN3RemainderVal256V4_eq_mod_of_scaled_remainder_shift_ne
      bltu_1 bltu_0 a b hshift_nz hscaled⟩

theorem fullModN3RemainderWordV4_eq_mod_of_mod_path_conditions
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullModN3PathConditionsWordV4 bltu_1 bltu_0 a b) :
    fullModN3RemainderWordV4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.mod a b :=
  hpath.2

/-- N3 MOD denorm post paired with the v4 call-path final computation. -/
@[irreducible]
def fullModN3DenormPostV4 (bltu_1 bltu_0 : Bool)
    (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := fullDivN3Shift b2
  let r1 := fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  denormModPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + signExtend12 4088) ↦ₘ r0.1) **
  ((sp + signExtend12 4080) ↦ₘ r1.1) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4064) ↦ₘ (0 : Word))

/-- N3 MOD unified post with caller `x1` outside the assertion and the v4
div128 scratch cell framed explicitly. -/
@[irreducible]
def fullModN3UnifiedPostNoX1V4 (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  fullModN3DenormPostV4 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
  fullDivN3FrameNoX1V4 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
    retMem dMem dloMem scratchUn0 **
  ((sp + signExtend12 3936) ↦ₘ
    fullDivN3ScratchMemV4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)

/-- N3 denormalization and MOD epilogue over the v4/no-NOP dispatcher body,
    using the v4 callable-trial final computation family. -/
theorem evm_mod_n3_denorm_epilogue_bundled_spec_v4_noNop_v4Final
    (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hshift_nz : fullDivN3Shift b2 ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff) (modCode_noNop_v4 base)
      (fullDivN3DenormPreV4 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3)
      (fullModN3DenormPostV4 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := fullDivN3Shift b2
  let v := fullDivN3NormV b0 b1 b2 b3
  let r1 := fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let c3 := fullDivN3C3V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  have h := evm_mod_preamble_denorm_epilogue_spec_within_noNop_v4 sp base
    r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 shift
    r0.2.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3 v.1 v.2.1 v.2.2.1 v.2.2.2 hshift_nz
  have hF := cpsTripleWithin_frameR
    (((sp + signExtend12 4088) ↦ₘ r0.1) **
     ((sp + signExtend12 4080) ↦ₘ r1.1) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)))
    (by pcFree) h
  exact cpsTripleWithin_weaken
    (fun h hp => by
      subst shift; subst v; subst r1; subst r0; subst c3
      delta fullDivN3DenormPreV4 at hp
      simp only [se12_32, se12_40, se12_48, se12_56] at hp
      xperm_hyp hp)
    (fun h hq => by
      subst shift; subst r1; subst r0
      delta fullModN3DenormPostV4
      xperm_hyp hq)
    hF

/-- N3 denormalization and MOD epilogue over v4/no-NOP for the v4 final
    computation family, preserving exact caller `x1` and the final v4 div128
    scratch cell. -/
theorem evm_mod_n3_denorm_epilogue_bundled_spec_v4_noNop_v4Final_exact_x1_scratch_frame
    (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hshift_nz : fullDivN3Shift b2 ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff)
      (modCode_noNop_v4 base)
      (fullDivN3DenormPreV4 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
       fullDivN3FrameNoX1V4 bltu_1 bltu_0 sp base
         a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ
         fullDivN3ScratchMemV4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
       (.x1 ↦ᵣ raVal))
      (fullModN3UnifiedPostNoX1V4 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem **
       (.x1 ↦ᵣ raVal)) := by
  have hDenorm := evm_mod_n3_denorm_epilogue_bundled_spec_v4_noNop_v4Final
    bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3 hshift_nz
  have hFramed := cpsTripleWithin_frameR
    (fullDivN3FrameNoX1V4 bltu_1 bltu_0 sp base
     a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN3ScratchMemV4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal))
    (by
      delta fullDivN3FrameNoX1V4 fullDivN3ScratchNoX1V4
      pcFree) hDenorm
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      delta fullModN3UnifiedPostNoX1V4
      xperm_hyp hq)
    hFramed

/-- Project a packed v4 n=3 MOD remainder equality into limb equalities. -/
theorem fullModN3V4_hmods_of_word_eq
    (bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hmod : fullModN3RemainderWordV4 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b) :
    (EvmWord.mod a b).getLimbN 0 =
      (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)) |||
        ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 1 =
      (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)) |||
        ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 2 =
      (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)) |||
        ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 3 =
      ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
        ((fullDivN3Shift b2).toNat % 64)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hmod]
    delta fullModN3RemainderWordV4
    exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hmod]
    delta fullModN3RemainderWordV4
    exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hmod]
    delta fullModN3RemainderWordV4
    exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hmod]
    delta fullModN3RemainderWordV4
    exact EvmWord.getLimbN_fromLimbs_3

/-- Convert the n=3 MOD v4 final post plus exact caller `x1` to the
    exact-register concrete MOD callable surface, preserving the v4 trial-call
    scratch cell that is not part of the public callable post. -/
theorem fullModN3UnifiedPostNoX1V4_frame_to_modConcretePostNoX1ExactRegsFrame_scratch
    (bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hmod0 : (EvmWord.mod a b).getLimbN 0 =
      (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)) |||
        ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))))
    (hmod1 : (EvmWord.mod a b).getLimbN 1 =
      (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)) |||
        ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))))
    (hmod2 : (EvmWord.mod a b).getLimbN 2 =
      (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)) |||
        ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))))
    (hmod3 : (EvmWord.mod a b).getLimbN 3 =
      ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
        ((fullDivN3Shift b2).toNat % 64))) :
    ∀ h,
      (fullModN3UnifiedPostNoX1V4 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      (modConcretePostNoX1ExactRegsFrame sp a b
        (signExtend12 4095) raVal
        (signExtend12 (0 : BitVec 12) - fullDivN3Shift b2)
        (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
        (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
        (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
        ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64))
        (fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
        (0 : Word)
        (0 : Word)
        (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
        (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
        (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
        ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64))
        (fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2
        (fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2
        (0 : Word)
        (0 : Word)
        (fullDivN3Shift b2) (3 : Word) (0 : Word)
        (if bltu_0 then (base + div128CallRetOff)
          else if bltu_1 then (base + div128CallRetOff) else retMem)
        (if bltu_0 then (fullDivN3NormV b0 b1 b2 b3).2.2.1
          else if bltu_1 then (fullDivN3NormV b0 b1 b2 b3).2.2.1 else dMem)
        (if bltu_0 then divKTrialCallV4DLo (fullDivN3NormV b0 b1 b2 b3).2.2.1
          else if bltu_1 then divKTrialCallV4DLo
            (fullDivN3NormV b0 b1 b2 b3).2.2.1 else dloMem)
        (if bltu_0 then divKTrialCallV4Un0
            (fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
          else if bltu_1 then divKTrialCallV4Un0
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
          else scratchUn0) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV4 bltu_1 bltu_0
          a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)) h := by
  intro h hq
  let shift := fullDivN3Shift b2
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let r1 := fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let v := fullDivN3NormV b0 b1 b2 b3
  let u := fullDivN3NormU a0 a1 a2 a3 b2
  let scratchRet := if bltu_0 then (base + div128CallRetOff)
    else if bltu_1 then (base + div128CallRetOff) else retMem
  let scratchD := if bltu_0 then v.2.2.1
    else if bltu_1 then v.2.2.1 else dMem
  let scratchDLo := if bltu_0 then divKTrialCallV4DLo v.2.2.1
    else if bltu_1 then divKTrialCallV4DLo v.2.2.1 else dloMem
  let scratchUn0' := if bltu_0 then divKTrialCallV4Un0 r1.2.2.1
    else if bltu_1 then divKTrialCallV4Un0 u.2.2.2.1 else scratchUn0
  let u0' := (r0.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.1 <<< (antiShift.toNat % 64))
  let u1' := (r0.2.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.2.1 <<< (antiShift.toNat % 64))
  let u2' := (r0.2.2.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.2.2.1 <<< (antiShift.toNat % 64))
  let u3' := r0.2.2.2.2.1 >>> (shift.toNat % 64)
  rw [modConcretePostNoX1ExactRegsFrame_unfold]
  change
    ((((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ u0') ** (.x10 ↦ᵣ u3') **
      (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.mod a b)) **
     ((.x9 ↦ᵣ (signExtend12 4095 : Word)) ** (.x1 ↦ᵣ raVal) **
      (.x2 ↦ᵣ antiShift) ** (.x6 ↦ᵣ u1') ** (.x7 ↦ᵣ u2') **
      (.x11 ↦ᵣ r0.1) ** evmWordIs sp a **
      divScratchValuesCallNoX1 sp r0.1 r1.1 (0 : Word) (0 : Word)
        u0' u1' u2' u3' r0.2.2.2.2.2 r1.2.2.2.2.2
        (0 : Word) (0 : Word) shift (3 : Word) (0 : Word)
        scratchRet scratchD scratchDLo scratchUn0')) **
     ((sp + signExtend12 3936) ↦ₘ
      fullDivN3ScratchMemV4 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)) h
  delta fullModN3UnifiedPostNoX1V4 fullModN3DenormPostV4 fullDivN3FrameNoX1V4
    fullDivN3ScratchNoX1V4 at hq
  simp only [denormModPost_unfold] at hq
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3))
      from by rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3]]
  rw [show evmWordIs (sp + 32) (EvmWord.mod a b) =
      (((sp + 32) ↦ₘ u0') ** ((sp + 40) ↦ₘ u1') **
       ((sp + 48) ↦ₘ u2') ** ((sp + 56) ↦ₘ u3'))
      from by
        rw [evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b) _ _ _ _
          hmod0 hmod1 hmod2 hmod3]]
  rw [divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

/-- Named callable-frame version of
    `fullModN3UnifiedPostNoX1V4_frame_to_modConcretePostNoX1ExactRegsFrame_scratch`. -/
theorem fullModN3UnifiedPostNoX1V4_frame_to_modStackDispatchPostCallableExactFrame_scratch
    (bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hmod0 : (EvmWord.mod a b).getLimbN 0 =
      (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)) |||
        ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))))
    (hmod1 : (EvmWord.mod a b).getLimbN 1 =
      (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)) |||
        ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))))
    (hmod2 : (EvmWord.mod a b).getLimbN 2 =
      (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)) |||
        ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))))
    (hmod3 : (EvmWord.mod a b).getLimbN 3 =
      ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
        ((fullDivN3Shift b2).toNat % 64))) :
    ∀ h,
      (fullModN3UnifiedPostNoX1V4 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      (((modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ signExtend12 4095)) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV4 bltu_1 bltu_0
          a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)) h := by
  intro h hp
  have hExact :=
    fullModN3UnifiedPostNoX1V4_frame_to_modConcretePostNoX1ExactRegsFrame_scratch
      bltu_1 bltu_0 sp base a b
      a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem
      raVal ha0 ha1 ha2 ha3 hmod0 hmod1 hmod2 hmod3 h hp
  exact sepConj_mono_left
    (fun h hp => modConcretePostNoX1ExactRegs_weaken_callable_frame sp a b h hp)
    h hExact

/-- Remainder-word form of
    `fullModN3UnifiedPostNoX1V4_frame_to_modStackDispatchPostCallableExactFrame_scratch`. -/
theorem fullModN3UnifiedPostNoX1V4_frame_to_modStackDispatchPostCallableExactFrame_scratch_word
    (bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hmodWord : fullModN3RemainderWordV4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.mod a b) :
    ∀ h,
      (fullModN3UnifiedPostNoX1V4 bltu_1 bltu_0 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      (modStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem)) h := by
  obtain ⟨hmod0, hmod1, hmod2, hmod3⟩ :=
    fullModN3V4_hmods_of_word_eq bltu_1 bltu_0 a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hmodWord
  intro h hp
  rw [modStackDispatchPostCallableExactFrame_unfold]
  exact fullModN3UnifiedPostNoX1V4_frame_to_modStackDispatchPostCallableExactFrame_scratch
    bltu_1 bltu_0 sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    retMem dMem dloMem scratchUn0 scratchMem raVal
    rfl rfl rfl rfl hmod0 hmod1 hmod2 hmod3 h hp

end EvmAsm.Evm64
