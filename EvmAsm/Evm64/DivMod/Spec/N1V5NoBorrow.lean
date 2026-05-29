/-
  EvmAsm.Evm64.DivMod.Spec.N1V5NoBorrow

  The v5 single-limb mulsub leaves no top borrow — `mulsubN4NoBorrow` for the
  exact v5 trial `div128Quot_v5`, discharged from the divisor shape alone.

  This is the `hborrow` hypothesis that the v5 n=1 loop-body skip spec
  (`divK_loop_body_n1_call_skip_*_v5`, brick 6 of bead `evm-asm-wbc4i.7.2`) and
  the loop-iteration layer consume.  In v4 this had to be supplied as a
  reachable-carry certificate; under v5 it follows unconditionally because the
  trial is the exact 128/64 floor (`div128Quot_v5 = floor`), so the single-limb
  mulsub's top limb `c3` is zero (the same fact behind
  `iterN1V5_true_carry_zero_of_v0_norm_call`), and `mulsubN4NoBorrow` is then
  immediate (`ult uTop 0 = false`).
-/

import EvmAsm.Evm64.DivMod.Spec.N1V5CarryZero

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **v5 single-limb no-borrow, from shape.** For a normalized one-limb divisor
    (`v0 ≥ 2^63`) in the call regime (`u1 < v0`), the v5 trial's single-limb
    mulsub leaves no top borrow, for any top accumulator `uTop`.  No
    `Carry2NzAll` / reachability — the exact floor bound forces `c3 = 0`. -/
theorem mulsubN4NoBorrow_div128Quot_v5_of_norm_call
    (v0 u0 u1 uTop : Word)
    (hv0_norm : v0.toNat ≥ 2 ^ 63)
    (hcall : u1.toNat < v0.toNat) :
    mulsubN4NoBorrow (div128Quot_v5 u1 u0 v0) v0 0 0 0 u0 u1 0 0 uTop := by
  have hc3 : (mulsubN4 (div128Quot_v5 u1 u0 v0) v0 0 0 0 u0 u1 0 0).2.2.2.2 = 0 := by
    apply c3_un_zero_of_qHat_mul_le
    have hq_le := div128Quot_v5_le_q_true u1 u0 v0 hv0_norm hcall
    have h_product : (div128Quot_v5 u1 u0 v0).toNat * v0.toNat ≤
        u1.toNat * 2 ^ 64 + u0.toNat :=
      le_trans (Nat.mul_le_mul_right v0.toNat hq_le) (Nat.div_mul_le_self _ _)
    simp [EvmWord.val256]
    omega
  unfold mulsubN4NoBorrow
  rw [hc3]
  simp [BitVec.ult]

end EvmAsm.Evm64
