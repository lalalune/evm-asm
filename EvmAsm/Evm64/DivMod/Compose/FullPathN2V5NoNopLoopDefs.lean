/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopLoopDefs

  Foundation defs for the unified n=2 v5/no-NOP loop: the branch-selected
  iteration `loopN2IterSelectedV5`, the selected-carry bundle
  `loopN2SelectedCarryV5`, and the unified postcondition
  `loopN2UnifiedPostV5NoX1` (8-arm match over `bltu_2 × bltu_1 × bltu_0`).
  Mirror of the v4 defs in `FullPathN2V4NoNopLoopUnified`, using the v5 trial
  accessors, the v5 direct carry2 form (`callAddbackCarry2NzV5`), and the v5
  per-prefix aliases (r2CCC/r1CCC/r1TMM/r2MTT/r1MTT/r2MMT/r1MMT) chosen in the
  8 combo files.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboMMM

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Branch-selected n=2 v5 loop iteration. -/
def loopN2IterSelectedV5 (bltu : Bool)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  if bltu then
    iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
  else
    iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop

@[simp] theorem loopN2IterSelectedV5_false
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    loopN2IterSelectedV5 false v0 v1 v2 v3 u0 u1 u2 u3 uTop =
      iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold loopN2IterSelectedV5; simp

@[simp] theorem loopN2IterSelectedV5_true
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    loopN2IterSelectedV5 true v0 v1 v2 v3 u0 u1 u2 u3 uTop =
      iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold loopN2IterSelectedV5; simp

/-- Selected-carry bundle for the n=2 v5 loop: the three carry facts picked out
    by the actual `bltu_2 × bltu_1 × bltu_0` path (call digits use the v5 direct
    double-addback carry2, max digits use `isAddbackCarry2NzN2Max`). -/
def loopN2SelectedCarryV5 (bltu_2 bltu_1 bltu_0 : Bool)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word) : Prop :=
  let r2 := loopN2IterSelectedV5 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r1 := loopN2IterSelectedV5 bltu_1 v0 v1 v2 v3
    u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  (if bltu_2 then
    callAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
   else
    isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) ∧
  (if bltu_1 then
    callAddbackCarry2NzV5 v0 v1 v2 v3
      u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
   else
    isAddbackCarry2NzN2Max v0 v1 v2 v3
      u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1) ∧
  (if bltu_0 then
    callAddbackCarry2NzV5 v0 v1 v2 v3
      u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
   else
    isAddbackCarry2NzN2Max v0 v1 v2 v3
      u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1)

theorem loopN2SelectedCarryV5_unfold (bltu_2 bltu_1 bltu_0 : Bool)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word) :
    loopN2SelectedCarryV5 bltu_2 bltu_1 bltu_0
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 =
    (let r2 := loopN2IterSelectedV5 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop
     let r1 := loopN2IterSelectedV5 bltu_1 v0 v1 v2 v3
       u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
     (if bltu_2 then
       callAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      else
       isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) ∧
     (if bltu_1 then
       callAddbackCarry2NzV5 v0 v1 v2 v3
         u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
      else
       isAddbackCarry2NzN2Max v0 v1 v2 v3
         u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1) ∧
     (if bltu_0 then
       callAddbackCarry2NzV5 v0 v1 v2 v3
         u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
      else
       isAddbackCarry2NzN2Max v0 v1 v2 v3
         u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1)) := by
  delta loopN2SelectedCarryV5; rfl

end EvmAsm.Evm64
