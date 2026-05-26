/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V4CallMaxSelectedIfBorrow

  Selected-if-borrow input hypotheses for the n=1 v4 call/max/max/max path.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4CallMaxSelected

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Selected-if-borrow assumptions for the bundled N1 call/max/max/max input
    path. This package replaces unconditional max carry facts with facts
    needed only when each max step takes the addback branch. -/
@[irreducible]
def loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses
    (I : LoopN1CallMaxmaxmaxExactInputs) : Prop :=
  BitVec.ult I.u1 I.v0 ∧
  loopN1CallMaxmaxmaxBranchFacts
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1 ∧
  loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0

/-- Compatibility projection from selected-only inputs to selected-if-borrow
    inputs. -/
theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_of_selected
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I := by
  unfold loopN1CallMaxmaxmaxSelectedInputHypotheses at hh
  unfold loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses
  exact ⟨hh.1, hh.2.1,
    loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts_of_selected
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      I.u0Orig2 I.u0Orig1 I.u0Orig0 hh.2.2⟩

/-- Build selected-if-borrow bundled N1 call/max/max/max hypotheses from
    bundled branch facts and conditional selected carry facts. -/
theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_of_branches
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hbltu3 : BitVec.ult I.u1 I.v0)
    (hbranches : loopN1CallMaxmaxmaxBranchFacts
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1)
    (hselected : loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      I.u0Orig2 I.u0Orig1 I.u0Orig0) :
    loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I := by
  unfold loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses
  exact ⟨hbltu3, hbranches, hselected⟩

theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu3
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    BitVec.ult I.u1 I.v0 := by
  unfold loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses at hh
  exact hh.1

theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_branches
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    loopN1CallMaxmaxmaxBranchFacts
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1 := by
  unfold loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses at hh
  exact hh.2.1

theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu2
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop).2.1
      I.v0 := by
  exact loopN1CallMaxmaxmaxBranchFacts_hbltu2
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1
    (loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_branches I hh)

theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu1
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2).2.1 I.v0 := by
  exact loopN1CallMaxmaxmaxBranchFacts_hbltu1
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1
    (loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_branches I hh)

theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu0
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2 I.u0Orig1).2.1 I.v0 := by
  exact loopN1CallMaxmaxmaxBranchFacts_hbltu0
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1
    (loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_branches I hh)

theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_selectedCarryIfBorrow
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      I.u0Orig2 I.u0Orig1 I.u0Orig0 := by
  unfold loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses at hh
  exact hh.2.2

theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowCall
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    isAddbackCarry2NzN1CallV4
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop := by
  exact loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts_call
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0
    (loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_selectedCarryIfBorrow I hh)

theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax2
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    selectedN1MaxCarryIfBorrow
      I.v0 I.v1 I.v2 I.v3 I.u0Orig2
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop).2.1
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop).2.2.1
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop).2.2.2.1
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop).2.2.2.2.1 := by
  exact loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts_max2
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0
    (loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_selectedCarryIfBorrow I hh)

theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax1
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    selectedN1MaxCarryIfBorrow
      I.v0 I.v1 I.v2 I.v3 I.u0Orig1
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2).2.1
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2).2.2.1
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2).2.2.2.1
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2).2.2.2.2.1 := by
  exact loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts_max1
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0
    (loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_selectedCarryIfBorrow I hh)

theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax0
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    selectedN1MaxCarryIfBorrow
      I.v0 I.v1 I.v2 I.v3 I.u0Orig0
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2 I.u0Orig1).2.1
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2 I.u0Orig1).2.2.1
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2 I.u0Orig1).2.2.2.1
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2 I.u0Orig1).2.2.2.2.1 := by
  exact loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts_max0
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0
    (loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_selectedCarryIfBorrow I hh)

end EvmAsm.Evm64
