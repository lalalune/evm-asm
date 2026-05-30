/-
  EvmAsm.Evm64.DivMod.Spec.N2V5CallCarryOfCallShape

  The per-digit call-carry discharge for the n=2 lane: from the call regime
  (`u2 < v1`, i.e. `bltu = true`) + the normalized divisor (`v1 ≥ 2^63`,
  `v2 = v3 = 0`) + the runtime borrow, derive `callAddbackCarry2NzV5` on a
  `v2 = v3 = 0`, `u3 = 0` window.  Composes the +2 overestimate (#7425, valid in
  the call regime), the small-divisor bound (#7453), and the borrow-case carry
  discharge (#7431).  Applied per call digit by the lane (the call regime comes
  from that digit's `bltu` being true; `u3 = 0` from the per-digit remainder
  collapse).
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5TrialOverestimate
import EvmAsm.Evm64.DivMod.Spec.N2V5HvSmall
import EvmAsm.Evm64.DivMod.Spec.N2V5CallCarryBorrowN2

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- `callAddbackCarry2NzV5` on a `v2=v3=0`, `u3=0` window, from the call regime,
    the normalized top divisor limb, and the runtime borrow. -/
theorem callAddbackCarry2NzV5_of_borrow_of_call_shape
    (v0 v1 u0 u1 u2 uTop : Word)
    (hv1_norm : v1.toNat ≥ 2 ^ 63)
    (hcall : u2.toNat < v1.toNat)
    (hborrow : BitVec.ult uTop
      (mulsubN4_c3 (divKTrialCallV5QHat u2 u1 v1) v0 v1 0 0 u0 u1 u2 0) = true) :
    callAddbackCarry2NzV5 v0 v1 0 0 u0 u1 u2 0 uTop := by
  have hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    have h3 := (BitVec.or_eq_zero_iff.mp h2).1
    have hv1z : v1 = 0 := (BitVec.or_eq_zero_iff.mp h3).2
    rw [hv1z] at hv1_norm
    simp at hv1_norm
  exact callAddbackCarry2NzV5_of_borrow_n2 v0 v1 0 0 u0 u1 u2 0 uTop hbnz
    (divKTrialCallV5QHat_le_window_div_plus_two_of_call u0 u1 u2 v0 v1 hv1_norm hcall)
    (n2_two_val256_v_lt_pow256 v0 v1) hborrow

end EvmAsm.Evm64
