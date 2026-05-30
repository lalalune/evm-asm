/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboMMM

  Three-iteration max×max×max composition for the n=2 v5/no-NOP source path.
  All three digits take the max-trial branch.  Reuses r2MMTN2V5/r1MMTN2V5
  (both iterN2Max) + the max×max prefix (#7395).  Mirror of
  FullPathN2V4NoNopMaxMaxMax.  Completes the 8-way combo dispatch for the n=2 v5
  loop.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboMMT

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Compact final postcondition for the n=2 v5 max×max×max source path.  No
    digit calls div128, so the original scratch cells persist unchanged. -/
@[irreducible]
def loopN2MaxMaxMaxSourceFinalPostNoX1V5 (sp : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal
     retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  let r2 := r2MMTN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r1 := r1MMTN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
  let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  ((loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3
    u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
    (sp + signExtend12 3968 ↦ₘ retMem) **
    (sp + signExtend12 3960 ↦ₘ dMem) **
    (sp + signExtend12 3952 ↦ₘ dloMem) **
    (sp + signExtend12 3944 ↦ₘ scratchUn0) **
    (sp + signExtend12 3936 ↦ₘ scratchMem) **
    (.x1 ↦ᵣ raVal)) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
      (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) **
      (qAddr2 ↦ₘ r2.1))))

theorem loopN2MaxMaxMaxSourceFinalPostNoX1V5_unfold (sp : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal
     retMem dMem dloMem scratchUn0 scratchMem : Word) :
    loopN2MaxMaxMaxSourceFinalPostNoX1V5 sp
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal
      retMem dMem dloMem scratchUn0 scratchMem =
    (let r2 := r2MMTN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
     let r1 := r1MMTN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
     let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
     let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
     let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
     let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
     ((loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3
       u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) **
       (.x1 ↦ᵣ raVal)) **
       (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
         (qAddr1 ↦ₘ r1.1)) **
        ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) **
         (qAddr2 ↦ₘ r2.1))))) := by
  delta loopN2MaxMaxMaxSourceFinalPostNoX1V5
  rfl

/-- Bundled runtime conditions for the n=2 v5 max×max×max source path. -/
@[irreducible]
def loopN2MaxMaxMaxSourceCondsV5
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word) : Prop :=
  let r2 := r2MMTN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r1 := r1MMTN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
  ¬BitVec.ult u2 v1 ∧
  isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop ∧
  ¬BitVec.ult r2.2.2.1 v1 ∧
  isAddbackCarry2NzN2Max v0 v1 v2 v3
    u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 ∧
  ¬BitVec.ult r1.2.2.1 v1 ∧
  isAddbackCarry2NzN2Max v0 v1 v2 v3
    u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1

theorem loopN2MaxMaxMaxSourceCondsV5_unfold
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word) :
    loopN2MaxMaxMaxSourceCondsV5
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 =
    (let r2 := r2MMTN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
     let r1 := r1MMTN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
     ¬BitVec.ult u2 v1 ∧
     isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop ∧
     ¬BitVec.ult r2.2.2.1 v1 ∧
     isAddbackCarry2NzN2Max v0 v1 v2 v3
       u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 ∧
     ¬BitVec.ult r1.2.2.1 v1 ∧
     isAddbackCarry2NzN2Max v0 v1 v2 v3
       u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) := by
  delta loopN2MaxMaxMaxSourceCondsV5
  rfl

/-- The n=2 v5/no-NOP source path whose three iterations all take the max-trial
    branch. -/
theorem divK_loop_n2_max_max_max_from_source_exact_loopIterScratch_v5_noNop
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hconds :
      loopN2MaxMaxMaxSourceCondsV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig1 u0Orig0) :
    cpsTripleWithin (152 + 152 + 152) (base + loopBodyOff) (base + denormOff)
      (divCode_noNop_v5 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN2MaxMaxMaxSourceFinalPostNoX1V5 sp
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal
        retMem dMem dloMem scratchUn0 scratchMem) := by
  rw [loopN2MaxMaxMaxSourceCondsV5_unfold] at hconds
  simp only [r2MMTN2V5_eq, r1MMTN2V5_eq] at hconds
  obtain ⟨hbltu_2, hcarry2_nz_2, hbltu_1, hcarry2_nz_1, hbltu_0, hcarry2_nz_0⟩ := hconds
  have JMM := divK_loop_n2_max_max_from_source_exact_loopIterScratch_v5_noNop
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem
    hbltu_2 hcarry2_nz_2 hbltu_1 hcarry2_nz_1
  have J0 := divK_loop_body_n2_max_j0_exact_loopIterScratch_v5_noNop sp base
    (1 : Word) ((1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0Orig1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1)
    (iterN2Max v0 v1 v2 v3 u0Orig1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).1
    (iterN2Max v0 v1 v2 v3 u0Orig1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1
    v0 v1 v2 v3 u0Orig0
    (iterN2Max v0 v1 v2 v3 u0Orig1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
    (iterN2Max v0 v1 v2 v3 u0Orig1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
    (iterN2Max v0 v1 v2 v3 u0Orig1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
    (iterN2Max v0 v1 v2 v3 u0Orig1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1
    q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem
    hbltu_0 hcarry2_nz_0
  have J0f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
      (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.2) **
      ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
      (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).1)) **
     (((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
      ((sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
       (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)))
    (by pcFree) J0
  have hcomp := cpsTripleWithin_seq_perm_same_cr
    (loopIterPostN2MaxScratchX1_j1_to_max_j0_pre_with_j2_frame
      sp retMem dMem dloMem scratchUn0 scratchMem
      v0 v1 v2 v3 u0Orig1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
      u0Orig0 q0Old raVal
      (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat)
      (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat)
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
    JMM J0f
  have hsteps : (152 + 152) + 152 = 152 + 152 + 152 := by decide
  rw [hsteps] at hcomp
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hcomp
  intro h hp
  rw [loopN2MaxMaxMaxSourceFinalPostNoX1V5_unfold]
  simp only [r2MMTN2V5_eq, r1MMTN2V5_eq] at hp ⊢
  xperm_hyp hp

end EvmAsm.Evm64
