/-
  EvmAsm.Evm64.DivMod.Spec.N4V5CallAddbackQOutReconcile

  Reconciles the two n=4 v5 call-addback corrected-quotient defs: the lane
  skeleton's `fullDivN4CallAddbackQuotientV5` (built on `divKTrialCallV5QHat`) and
  the runtime/word-equality's `n4CallAddbackBeqQOutV5` (built on `div128Quot_v5`).
  They differ only in the trial-quotient name, and `divKTrialCallV5QHat =
  div128Quot_v5`, so they are equal.  This lets the call-addback word equality
  (#7609, `… = n4CallAddbackBeqQOutV5`) feed the call-addback lane skeleton
  (#7603, `hdiv0 : … = fullDivN4CallAddbackQuotientV5 …`).  Bead `evm-asm-wbc4i.8`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneCallAddback
import EvmAsm.Evm64.DivMod.Spec.CallAddbackV5

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The lane-skeleton corrected quotient equals the runtime corrected quotient. -/
theorem fullDivN4CallAddbackQuotientV5_eq_QOutV5 (a b : EvmWord) :
    fullDivN4CallAddbackQuotientV5
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
      n4CallAddbackBeqQOutV5 a b := by
  rw [n4CallAddbackBeqQOutV5_raw_unfold]
  unfold fullDivN4CallAddbackQuotientV5
  simp only [divKTrialCallV5QHat_eq_div128Quot_v5]

end EvmAsm.Evm64
