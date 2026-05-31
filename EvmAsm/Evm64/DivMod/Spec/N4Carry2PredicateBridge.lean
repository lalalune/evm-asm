/-
  EvmAsm.Evm64.DivMod.Spec.N4Carry2PredicateBridge

  The n=4 v5 call-addback carry-2 predicate equals the generic double-addback
  progress predicate at the v5 call trial:
    `loopBodyN4CallAddbackCarry2NzV5 v u uTop
       = isAddbackCarry2Nz (divKTrialCallV5QHat uTop u3 v3) v u uTop`.

  Both unfold to the identical `mulsubN4`/`addbackN4` carry structure with the v5
  call-trial quotient `divKTrialCallV5QHat uTop u3 v3` in the `qHat` slot, so this
  is definitional (`rfl`).  Kept over plain `Word` variables (not the huge
  normalized n=4 limb terms) so it stays kernel-cheap; the n=4 `h_carry2` discharge
  rewrites with it and then applies the generic
  `isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero`
  (the `+2` from #7574, the divisor `≠ 0`, and the `c3 = 1`-of-carry-zero invariant).
  Bead `evm-asm-wbc4i.8.2.2`.
-/

import EvmAsm.Evm64.DivMod.Spec.CallAddbackV5
import EvmAsm.Evm64.DivMod.LoopDefs.Iter

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The v5 call-addback carry-2 predicate is the generic `isAddbackCarry2Nz` at the
    v5 call trial. -/
theorem loopBodyN4CallAddbackCarry2NzV5_eq_isAddbackCarry2Nz
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    loopBodyN4CallAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop =
      isAddbackCarry2Nz (divKTrialCallV5QHat uTop u3 v3)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold loopBodyN4CallAddbackCarry2NzV5 isAddbackCarry2Nz
  rfl

end EvmAsm.Evm64
