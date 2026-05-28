/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1cLB

  Knuth-A lower bound for V5's Phase-1a-corrected quotient in the
  wide-uHi case (the V4 exclusion zone): `Q1c ≥ q_true_1` when
  `uHi ≥ dHi * 2^32`.

  The narrow case (`uHi < dHi * 2^32`) reduces to the v2 Knuth-A LB
  `algorithmQ1Prime_ge_q_true_1`; the wide case here is the V5-specific
  half that wasn't accessible under v4 (because v4's q1c = q1 - 1 in
  the wide regime could undershoot, motivating the wide-uHi
  counterexamples in PR #7077).

  Bead `evm-asm-wbc4i.5.4` (V5.5.0.1). Prerequisite for V5.5.1.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1ddBound

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- In the wide-uHi regime (`uHi ≥ dHi*2^32`), the V5 cap forces
    `Q1c = 2^32 - 1`. Combined with `q_true_1 < 2^32` (from `uHi < vTop`),
    this gives the Knuth-A LB unconditionally for the wide case. -/
theorem algorithmQ1cV5_ge_q_true_1_of_uHi_ge_dHi_pow32
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_ge_dHi_pow32 : uHi.toNat ≥ (divKTrialCallV5DHi vTop).toNat * 2^32) :
    (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat ≤
      (algorithmQ1cV5 uHi vTop).toNat := by
  -- Q1c = 2^32 - 1 in this case (cap fires).
  have h_dHi_lt : (divKTrialCallV5DHi vTop).toNat < 2^32 :=
    divKTrialCallV5DHi_lt_pow32 vTop
  have h_dHi_ge : (divKTrialCallV5DHi vTop).toNat ≥ 2^31 := by
    unfold divKTrialCallV5DHi
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    omega
  have h_dHi_ne : divKTrialCallV5DHi vTop ≠ 0 := by
    intro h
    have : (divKTrialCallV5DHi vTop).toNat = 0 := by rw [h]; rfl
    omega
  -- q1 = uHi / dHi.
  have h_q1_eq : (rv64_divu uHi (divKTrialCallV5DHi vTop)).toNat =
      uHi.toNat / (divKTrialCallV5DHi vTop).toNat := by
    unfold rv64_divu
    have : ¬ (divKTrialCallV5DHi vTop == 0#64) := by simpa using h_dHi_ne
    rw [if_neg this, BitVec.toNat_udiv]
  -- uHi ≥ dHi*2^32 ⇒ q1 = uHi/dHi ≥ 2^32 ⇒ hi1 = q1>>>32 ≠ 0.
  have h_q1_ge : (rv64_divu uHi (divKTrialCallV5DHi vTop)).toNat ≥ 2^32 := by
    rw [h_q1_eq]
    have h_div : uHi.toNat / (divKTrialCallV5DHi vTop).toNat ≥
        ((divKTrialCallV5DHi vTop).toNat * 2^32) / (divKTrialCallV5DHi vTop).toNat :=
      Nat.div_le_div_right huHi_ge_dHi_pow32
    have h_eq : ((divKTrialCallV5DHi vTop).toNat * 2^32) /
        (divKTrialCallV5DHi vTop).toNat = 2^32 :=
      Nat.mul_div_cancel_left _ (by omega)
    omega
  have h_hi1_ne : (rv64_divu uHi (divKTrialCallV5DHi vTop)) >>>
      (32 : BitVec 6).toNat ≠ (0 : Word) := by
    intro h
    have h_nat : ((rv64_divu uHi (divKTrialCallV5DHi vTop)) >>>
        (32 : BitVec 6).toNat).toNat = 0 := by rw [h]; rfl
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32,
        Nat.shiftRight_eq_div_pow] at h_nat
    have h_div : (rv64_divu uHi (divKTrialCallV5DHi vTop)).toNat / 2^32 = 0 := h_nat
    omega
  -- Q1c = q1cCap = 2^32 - 1.
  have h_q1c : (algorithmQ1cV5 uHi vTop).toNat = 2^32 - 1 := by
    rw [algorithmQ1cV5_unfold]
    dsimp only
    rw [if_neg h_hi1_ne]
    decide
  -- q_true_1 < 2^32 (from uHi < vTop and vTop ≥ 1).
  have h_vTop_pos : vTop.toNat ≥ 1 := by omega
  have h_un1_lt : (divKTrialCallV5Un1 uLo).toNat < 2^32 :=
    divKTrialCallV5Un1_lt_pow32 uLo
  have h_num_lt : uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat <
      vTop.toNat * 2^32 := by
    have h_uHi_le : uHi.toNat ≤ vTop.toNat - 1 := by omega
    have h_uHi_mul : uHi.toNat * 2^32 ≤ (vTop.toNat - 1) * 2^32 :=
      Nat.mul_le_mul_right _ h_uHi_le
    -- vTop ≥ 2^63 ⇒ vTop * 2^32 ≥ 2^95 ≫ uHi * 2^32 + un1 < (vTop-1)*2^32 + 2^32.
    have h_vTop_mul_ge : vTop.toNat * 2^32 ≥ 2^32 := by
      have : vTop.toNat ≥ 1 := h_vTop_pos
      nlinarith
    have h1 : (vTop.toNat - 1) * 2^32 + 2^32 = vTop.toNat * 2^32 := by
      have hv_eq : vTop.toNat = (vTop.toNat - 1) + 1 := by omega
      calc (vTop.toNat - 1) * 2^32 + 2^32
          = ((vTop.toNat - 1) + 1) * 2^32 := by ring
        _ = vTop.toNat * 2^32 := by rw [← hv_eq]
    linarith
  have h_q_true_lt : (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) /
      vTop.toNat < 2^32 :=
    Nat.div_lt_of_lt_mul h_num_lt
  -- Combine.
  rw [h_q1c]
  omega

end EvmAsm.Evm64
