/-
  EvmAsm.Evm64.DivMod.LoopIterN1.LoopAtShapeBridgeR0V5

  The fourth (j=0) digit equality for the loop-post → denorm bridge, completing the
  set in `LoopAtShapeBridgeV5` (which provides R3 / R2-via-S2 / R1-via-S1).  Defines
  the j=0 iteration chain `fullN1S0` (one `iterN1Call_v5` past `fullN1S1`) and proves
  it equals the schoolbook final digit `fullDivN1R0V5 true true true true` at the
  normalized inputs.  Proven in a SMALL context (no surrounding assertion) so it
  avoids the deep-recursion blowup that defeats unfolding the digits inside the
  25-atom loop post.  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.LoopAtShapeBridgeV5

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- j=0-entry iteration state (after the j=3, j=2, j=1 digits). -/
def fullN1S0 (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1 u0_orig_0 : Word) :=
  let s1 := fullN1S1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1
  iterN1Call_v5 v0 v1 v2 v3 u0_orig_0 s1.2.1 s1.2.2.1 s1.2.2.2.1 s1.2.2.2.2.1

/-- `fullN1S0` at the normalized inputs equals the schoolbook final digit
    `fullDivN1R0V5 true true true true`. -/
theorem fullN1S0_eq_fullDivN1R0V5 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullN1S0 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).1
    = fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3 := by
  unfold fullN1S0 fullN1S1 fullN1S2 fullDivN1R0V5 fullDivN1R1V5 fullDivN1R2V5 fullDivN1R3V5
  simp only [iterN1V5_true]

end EvmAsm.Evm64
