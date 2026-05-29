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
import EvmAsm.Evm64.EvmWordArith.MultiLimb

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

/-- **val256-normalize identity (divisor / no-overflow case).** Left-shifting
    a 4-limb value by `0 < s < 64` via the per-limb shift-OR limbs
    `Bi' = (bi <<< s) ||| (b(i-1) >>> (64-s))` (with `B0' = b0 <<< s`) gives
    `val256 B' = val256 b · 2^s`, provided the top limb does not overflow
    (`b3.toNat / 2^(64-s) = 0`, which holds when `s = clz(b3)` for `b3 ≠ 0`).

    Telescopes `shiftOr_disjoint_toNat` across the 4 limbs: each `bi`'s top
    `s` bits carry into the next limb, the carries cancel via `2^(64-s)·2^s
    = 2^64`, and the top carry vanishes by hypothesis. -/
theorem val256_normalize_divisor (b0 b1 b2 b3 : Word) (s : Nat)
    (hs : 0 < s) (hs64 : s < 64) (htop : b3.toNat / 2^(64-s) = 0) :
    EvmWord.val256 (b0 <<< s) ((b1 <<< s) ||| (b0 >>> (64-s)))
      ((b2 <<< s) ||| (b1 >>> (64-s))) ((b3 <<< s) ||| (b2 >>> (64-s)))
      = EvmWord.val256 b0 b1 b2 b3 * 2^s := by
  have hsle : 64 - s + s = 64 := by omega
  have hpow : (2:Nat)^64 = 2^(64-s) * 2^s := by rw [← Nat.pow_add, hsle]
  have hb0 : (b0 <<< s).toNat = (b0.toNat % 2^(64-s)) * 2^s := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hpow, Nat.mul_mod_mul_right]
  unfold EvmWord.val256
  rw [hb0, shiftOr_disjoint_toNat b1 b0 s hs hs64,
      shiftOr_disjoint_toNat b2 b1 s hs hs64, shiftOr_disjoint_toNat b3 b2 s hs hs64]
  have e0 := Nat.div_add_mod b0.toNat (2^(64-s))
  have e1 := Nat.div_add_mod b1.toNat (2^(64-s))
  have e2 := Nat.div_add_mod b2.toNat (2^(64-s))
  have e3 := Nat.div_add_mod b3.toNat (2^(64-s))
  have h128 : (2:Nat)^128 = 2^64 * 2^64 := by rw [← Nat.pow_add]
  have h192 : (2:Nat)^192 = 2^64 * 2^64 * 2^64 := by rw [← Nat.pow_add, ← Nat.pow_add]
  rw [h128, h192, hpow]
  set M := 2^(64-s)
  set T := 2^s
  set p0 := b0.toNat % M; set q0 := b0.toNat / M
  set p1 := b1.toNat % M; set q1 := b1.toNat / M
  set p2 := b2.toNat % M; set q2 := b2.toNat / M
  set p3 := b3.toNat % M; set q3 := b3.toNat / M
  rw [htop] at e3
  rw [← e0, ← e1, ← e2, ← e3]
  ring

/-- **val256-normalize identity (dividend / overflow case).** Same per-limb
    shift-OR normalization as `val256_normalize_divisor`, but the top limb's
    high `s` bits overflow into a 5th "limb" `U4 = a3 >>> (64-s)`:
    `U4 · 2^256 + val256 U' = val256 a · 2^s`. No `htop` hypothesis — the top
    carry `a3 / 2^(64-s)` is exactly `U4` and contributes the `2^256` term. -/
theorem val256_normalize_dividend (a0 a1 a2 a3 : Word) (s : Nat)
    (hs : 0 < s) (hs64 : s < 64) :
    (a3 >>> (64-s)).toNat * 2^256
    + EvmWord.val256 (a0 <<< s) ((a1 <<< s) ||| (a0 >>> (64-s)))
        ((a2 <<< s) ||| (a1 >>> (64-s))) ((a3 <<< s) ||| (a2 >>> (64-s)))
      = EvmWord.val256 a0 a1 a2 a3 * 2^s := by
  have hsle : 64 - s + s = 64 := by omega
  have hpow : (2:Nat)^64 = 2^(64-s) * 2^s := by rw [← Nat.pow_add, hsle]
  have hb0 : (a0 <<< s).toNat = (a0.toNat % 2^(64-s)) * 2^s := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hpow, Nat.mul_mod_mul_right]
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  unfold EvmWord.val256
  rw [hb0, shiftOr_disjoint_toNat a1 a0 s hs hs64,
      shiftOr_disjoint_toNat a2 a1 s hs hs64, shiftOr_disjoint_toNat a3 a2 s hs hs64]
  have e0 := Nat.div_add_mod a0.toNat (2^(64-s))
  have e1 := Nat.div_add_mod a1.toNat (2^(64-s))
  have e2 := Nat.div_add_mod a2.toNat (2^(64-s))
  have e3 := Nat.div_add_mod a3.toNat (2^(64-s))
  have h128 : (2:Nat)^128 = 2^64 * 2^64 := by rw [← Nat.pow_add]
  have h192 : (2:Nat)^192 = 2^64 * 2^64 * 2^64 := by rw [← Nat.pow_add, ← Nat.pow_add]
  have h256 : (2:Nat)^256 = 2^64 * 2^64 * 2^64 * 2^64 := by
    rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
  rw [h128, h192, h256, hpow]
  set M := 2^(64-s)
  set T := 2^s
  set p0 := a0.toNat % M; set q0 := a0.toNat / M
  set p1 := a1.toNat % M; set q1 := a1.toNat / M
  set p2 := a2.toNat % M; set q2 := a2.toNat / M
  set p3 := a3.toNat % M; set q3 := a3.toNat / M
  rw [← e0, ← e1, ← e2, ← e3]
  ring

end EvmAsm.Evm64
