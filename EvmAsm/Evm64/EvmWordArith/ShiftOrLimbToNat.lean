/-
  EvmAsm.Evm64.EvmWordArith.ShiftOrLimbToNat

  Foundational building block for the val256-normalize identity: the
  disjoint shift-OR of two 64-bit words, as it appears in the per-limb
  normalization `Bi' = (bi <<< s) ||| (b(i-1) >>> (64 - s))`, equals an
  addition at the `toNat` level.

  The two operands are bit-disjoint — `(x <<< s)` occupies bits `[s, 64)`
  and `(y >>> (64 - s))` occupies bits `[0, s)` — so `|||` is `+`. This is
  the leaf lemma that lets `val256` of the shift-OR normalized limbs
  telescope to `val256 · 2^s` (bead `evm-asm-wbc4i.13`), which in turn
  feeds the n4 Knuth-B Word-level wrapper toward `evm_div_stack_spec`.
-/

import EvmAsm.Evm64.Basic

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Disjoint shift-OR as addition at the `toNat` level: for `0 < s < 64`,
    `((x <<< s) ||| (y >>> (64 - s))).toNat = (x.toNat % 2^(64-s)) * 2^s +
    y.toNat / 2^(64-s)`. The `<<< s` keeps the low `64-s` bits of `x`
    (shifted up by `s`); the `>>> (64-s)` keeps the top `s` bits of `y`;
    the two bit-ranges are disjoint so the `|||` is an addition. -/
theorem shiftOr_disjoint_toNat (x y : Word) (s : Nat) (hs : 0 < s) (hs64 : s < 64) :
    ((x <<< s) ||| (y >>> (64 - s))).toNat
      = (x.toNat % 2^(64-s)) * 2^s + y.toNat / 2^(64-s) := by
  have hsle : 64 - s + s = 64 := by omega
  have hpow : (2:Nat)^64 = 2^(64-s) * 2^s := by rw [← Nat.pow_add, hsle]
  have hpos : (0:Nat) < 2^(64-s) := Nat.two_pow_pos (64-s)
  have h2s : (2:Nat)^s ≤ 2^64 := Nat.pow_le_pow_right (by decide) (by omega)
  have hmulmod : (x.toNat * 2^s) % 2^64 = (x.toNat % 2^(64-s)) * 2^s := by
    rw [hpow, Nat.mul_mod_mul_right]
  have hydiv : y.toNat / 2^(64-s) < 2^s := by
    have h := Nat.div_lt_div_of_lt_of_dvd (⟨2^s, hpow⟩ : 2^(64-s) ∣ 2^64) y.isLt
    rwa [hpow, Nat.mul_div_cancel_left _ (by omega)] at h
  -- Bit-disjointness at the Nat level.
  have hdisjNat : ((x.toNat % 2^(64-s)) * 2^s) &&& (y.toNat / 2^(64-s)) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit]
    simp only [Nat.testBit_and, Bool.and_eq_false_iff]
    by_cases hi : i < s
    · left
      rw [Nat.mul_comm, Nat.testBit_two_pow_mul]
      simp [Nat.not_le.mpr hi]
    · right
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hydiv (Nat.pow_le_pow_right (by decide) (by omega)))
  -- Lift disjointness to BitVec, turning `|||` into `+`.
  have hdisj : (x <<< s) &&& (y >>> (64 - s)) = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, hmulmod]
    exact hdisjNat
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hdisj, BitVec.toNat_add,
    BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, hmulmod]
  have hmod : x.toNat % 2^(64-s) ≤ 2^(64-s) - 1 :=
    Nat.le_sub_one_of_lt (Nat.mod_lt x.toNat hpos)
  have hkey : (x.toNat % 2^(64-s)) * 2^s ≤ 2^64 - 2^s := by
    have h := Nat.mul_le_mul_right (2^s) hmod
    rwa [Nat.sub_mul, Nat.one_mul, ← Nat.pow_add, hsle] at h
  rw [Nat.mod_eq_of_lt (by omega)]

end EvmAsm.Evm64
