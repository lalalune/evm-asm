/-
  EvmAsm.Evm64.EvmWordArith.KnuthAFloorWindow

  The abstract Knuth Theorem A floor inequality (the "trial does not
  underestimate" direction) and its v5 n=2 per-digit specialization.

  `knuth_a_floor_window_le` is the position-independent core extracted from the
  n=4 `val256_ratio_le_u_total_div_b3_prime` (CallSkipLowerBoundV2): for a
  normalized window where the divisor's value is at least its top part times the
  place value (`Vtop·K ≤ V`) and the dividend splits as `U = Utop·K + Ulow` with
  `Ulow < K`, the full quotient `U/V` is at most the top-window quotient
  `Utop/Vtop`.

  `n2_window_val256_div_le_trial_v5` instantiates it at the n=2 limb positions
  (divisor `(v0,v1,0,0)`, window `(u0,u1,u2,0)`, trial on `u2,u1,v1`) and chains
  the v5 trial lower bound `div128Quot_v5_ge_q_true` to give the per-digit
  no-underestimate `val256 u / val256 v ≤ divKTrialCallV5QHat u2 u1 v1` — the
  `hq_ge` input of `iterWithDoubleAddback_remainder_lt_of_plus_two` for the v5
  n=2 lane.  Bead `evm-asm-wbc4i.9.2`.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.LowerBound
import EvmAsm.Evm64.EvmWordArith.DivV5TrialOverestimate

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- **Abstract Knuth-A floor inequality.** For a normalized window — divisor
    value at least its top part times the place value (`Vtop·K ≤ V`) and dividend
    `U = Utop·K + Ulow` with `Ulow < K` — the full quotient is at most the
    top-window quotient.  Position-independent core of
    `val256_ratio_le_u_total_div_b3_prime`. -/
theorem knuth_a_floor_window_le {U V Utop Ulow Vtop K : Nat}
    (hV : Vtop * K ≤ V) (hVtop : 0 < Vtop) (hK : 0 < K)
    (hU : U = Utop * K + Ulow) (hUlow : Ulow < K) :
    U / V ≤ Utop / Vtop := by
  have hpos : 0 < Vtop * K := Nat.mul_pos hVtop hK
  calc U / V ≤ U / (Vtop * K) := Nat.div_le_div_left hV hpos
    _ = (Utop * K + Ulow) / (Vtop * K) := by rw [hU]
    _ = Utop / Vtop := nat_trunc_div_add_lt Utop Vtop K Ulow hK hVtop hUlow

/-- **v5 n=2 per-digit no-underestimate.** The full window quotient is at most
    the v5 trial quotient (which divides the top two window limbs `u2,u1` by the
    divisor's top limb `v1`).  Needs normalization (`v1 ≥ 2^63`) and the call
    regime (`u2 < v1`).  This is the `hq_ge` ingredient for the n=2 per-digit
    remainder bound. -/
theorem n2_window_val256_div_le_trial_v5
    (v0 v1 u0 u1 u2 : Word)
    (hv1 : v1.toNat ≥ 2^63)
    (hcall : u2.toNat < v1.toNat) :
    val256 u0 u1 u2 0 / val256 v0 v1 0 0 ≤
      (divKTrialCallV5QHat u2 u1 v1).toNat := by
  rw [divKTrialCallV5QHat_eq_div128Quot_v5]
  have h0 : (0 : Word).toNat = 0 := rfl
  have hVtop : 0 < v1.toNat := by omega
  have hV : v1.toNat * 2^64 ≤ val256 v0 v1 0 0 := by
    simp only [EvmWord.val256, h0]; omega
  have hU : val256 u0 u1 u2 0 = (u2.toNat * 2^64 + u1.toNat) * 2^64 + u0.toNat := by
    simp only [EvmWord.val256, h0]; ring
  have hUlow : u0.toNat < 2^64 := u0.isLt
  have hknuth := knuth_a_floor_window_le hV hVtop (by positivity) hU hUlow
  have hge := div128Quot_v5_ge_q_true u2 u1 v1 hv1 hcall
  omega

end EvmAsm.Evm64
