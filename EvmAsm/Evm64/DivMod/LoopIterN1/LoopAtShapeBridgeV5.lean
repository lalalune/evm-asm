/-
  EvmAsm.Evm64.DivMod.LoopIterN1.LoopAtShapeBridgeV5

  Bridge equations connecting the v5 full-loop's per-digit helper states
  (`fullN1S2`/`fullN1S1`, raw `iterN1Call_v5` nestings) to the schoolbook model
  digits (`fullDivN1R2V5`/`fullDivN1R1V5 true`, irreducible) at the normalized
  inputs.  These let the loop-at-shape instantiation discharge the full loop's
  `hbltu_1`/`hbltu_0`/`hborrow_1`/`hborrow_0` hypotheses (over `fullN1S*`) using
  the shape lemmas (over `fullDivN1R*V5`).  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.UnifiedCallV5

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- `fullN1S2` at the normalized inputs equals the schoolbook j=1-entry digit
    `fullDivN1R2V5 true true`. -/
theorem fullN1S2_eq_fullDivN1R2V5 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullN1S2 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
    = fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3 := by
  unfold fullN1S2 fullDivN1R2V5 fullDivN1R3V5
  simp only [iterN1V5_true]

/-- `fullN1S1` at the normalized inputs equals the schoolbook j=0-entry digit
    `fullDivN1R1V5 true true true`. -/
theorem fullN1S1_eq_fullDivN1R1V5 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullN1S1 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
    = fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3 := by
  unfold fullN1S1 fullN1S2 fullDivN1R1V5 fullDivN1R2V5 fullDivN1R3V5
  simp only [iterN1V5_true]

/-- The first schoolbook digit `fullDivN1R3V5 true` equals the raw `iterN1Call_v5`
    over the normalized top window — the form the full loop's `hbltu_2`/`hborrow_3`
    hypotheses use. -/
theorem fullDivN1R3V5_eq_iterN1Call_v5 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3
    = iterN1Call_v5 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0 := by
  unfold fullDivN1R3V5
  simp only [iterN1V5_true]

end EvmAsm.Evm64
