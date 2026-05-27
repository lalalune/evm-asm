/-
  EvmAsm.Evm64.DivMod.HalignFromBaseEven

  Discharge of the DIV `halign` precondition from the standard
  "base is 2-byte aligned" hypothesis (`base &&& 1 = 0`).
-/

import EvmAsm.Evm64.DivMod.Compose.Offsets
import EvmAsm.Evm64.EvmWordArith.CLZLemmas
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4NoNopCallMax

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- For `y < 2^64` with `y % 2 = 0`, `y &&& (2^64 - 2) = y`. -/
private theorem nat_and_pow_sub_two_eq_self
    (y : Nat) (hy_lt : y < 2^64) (hy_even : y % 2 = 0) :
    y &&& (2^64 - 2) = y := by
  have h_mask : (2^64 - 1 : Nat) = (2^64 - 2) ||| 1 := by decide
  have h_y_full : y &&& (2^64 - 1) = y := by
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt hy_lt
  have h_y_and_1 : y &&& 1 = 0 := by
    rw [Nat.and_one_is_mod]
    exact hy_even
  have h_distrib : y &&& ((2^64 - 2) ||| 1) = (y &&& (2^64 - 2)) ||| (y &&& 1) :=
    Nat.and_or_distrib_left y (2^64 - 2) 1
  rw [h_mask, h_distrib, h_y_and_1, Nat.or_zero] at h_y_full
  exact h_y_full

/-- If `base` is 2-byte aligned, then so is `base + div128CallRetOff`. -/
theorem halign_from_base_even (base : Word)
    (hbase_even : base &&& (1 : Word) = 0) :
    ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
      ~~~(1 : Word) = base + div128CallRetOff := by
  have h_se0 : (signExtend12 (0 : BitVec 12) : Word) = (0 : Word) := by decide
  rw [h_se0]
  have h_add_zero : (base + (div128CallRetOff : Word)) + (0 : Word) =
      base + (div128CallRetOff : Word) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add]
    show ((base + (div128CallRetOff : Word)).toNat + (0:Word).toNat) % 2^64 =
         (base + (div128CallRetOff : Word)).toNat
    have : ((0:Word).toNat : Nat) = 0 := by decide
    rw [this, Nat.add_zero]
    exact Nat.mod_eq_of_lt (base + (div128CallRetOff : Word)).isLt
  rw [h_add_zero]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have h_not1 : (~~~(1 : Word)).toNat = 2^64 - 2 := by decide
  rw [h_not1]
  have h_sum : (base + (div128CallRetOff : Word)).toNat = (base.toNat + 516) % 2^64 := by
    show (base + (516 : Word)).toNat = (base.toNat + 516) % 2^64
    rw [BitVec.toNat_add]
    have h_516 : ((516 : Word)).toNat = 516 := by decide
    rw [h_516]
  rw [h_sum]
  have hbase_mod : base.toNat % 2 = 0 := by
    have h_and : (base &&& (1 : Word)).toNat = 0 := by rw [hbase_even]; rfl
    rw [BitVec.toNat_and] at h_and
    have h1_toNat : ((1 : Word)).toNat = 1 := by decide
    rw [h1_toNat] at h_and
    have hbit : base.toNat &&& 1 = base.toNat % 2 := Nat.and_one_is_mod _
    omega
  have h_sum_even : ((base.toNat + 516) % 2^64) % 2 = 0 := by
    have h_dvd : (2 : Nat) ∣ 2^64 := by
      refine ⟨2^63, ?_⟩
      show (2:Nat)^64 = 2 * 2^63
      have h_eq : (2:Nat) * 2^63 = 2^64 := by
        rw [show (64 : Nat) = 1 + 63 from rfl, pow_add, pow_one]
      omega
    rw [Nat.mod_mod_of_dvd _ h_dvd]
    omega
  have h_lt : (base.toNat + 516) % 2^64 < 2^64 :=
    Nat.mod_lt _ (by positivity)
  exact nat_and_pow_sub_two_eq_self _ h_lt h_sum_even

/-- Bundled-form alignment from `base &&& 1 = 0`: produces the
    `fullDivN1CallMaxmaxmaxExactInputAligned` predicate the N1 callable
    wrappers require. -/
theorem fullDivN1CallMaxmaxmaxExactInputAligned_of_base_even
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbase_even : base &&& (1 : Word) = 0) :
    fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  unfold fullDivN1CallMaxmaxmaxExactInputAligned
  unfold loopN1CallMaxmaxmaxExactInputAligned
  show ((_ + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
    ~~~(1 : Word) = _ + div128CallRetOff
  exact halign_from_base_even base hbase_even

end EvmAsm.Evm64
