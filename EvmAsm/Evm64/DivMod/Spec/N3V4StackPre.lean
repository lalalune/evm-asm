/-
  EvmAsm.Evm64.DivMod.Spec.N3V4StackPre

  Stack-level wrappers for n=3 DIV v4 preloop+loop paths.
-/

import EvmAsm.Evm64.DivMod.Spec.Dispatcher
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V4

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- EvmWord-level wrapper around the n=3 exact-x1/scratch v4 preloop+loop
    path. It exposes the proof over the full `divCode_v4` bundle while keeping
    the stack precondition bundled as `evmWordIs` plus the v4 scratch cell. -/
theorem evm_div_n3_preloop_loop_stack_pre_spec_v4 (sp base : Word)
    (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 =
      BitVec.ult (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hbltu_0 : bltu_0 =
      match bltu_1, hbltu_1 with
      | false, _ =>
        BitVec.ult
          (iterN3Max
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      | true, _ =>
        BitVec.ult
          (iterWithDoubleAddback
            (divKTrialCallV4QHat
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
              (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hcarry2 : Carry2NzAll
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 448)
      base (base + denormOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      ((loopN3UnifiedPostV4NoX1 bltu_1 bltu_0 sp base
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 2)).2.1
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 2)).2.2.1
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 2)).2.2.2.1
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 2)).2.2.2.2
        (0 : Word)
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 2)).1
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
        ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult (b.getLimbN 2)).1))) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hrawNoNop := fullDivN3_preloop_loop_unified_exact_x1_scratch_v4_noNop
    bltu_1 bltu_0 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz' hb3z hb2nz hshift_nz halign hbltu_1
    (by cases bltu_1 <;> simpa using hbltu_0) hcarry2
  have hraw := fullDivN3_preloop_loop_unified_exact_x1_scratch_v4 base hrawNoNop
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [divModStackDispatchPreNoX1_unfold, divScratchValuesCallNoX1_unfold] at hp
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Compose the n=3 v4 stack preloop+loop path through denormalization to the
    v4 final no-`x1` post, preserving the exact caller `x1`. -/
theorem evm_div_n3_stack_pre_to_unified_post_v4 (sp base : Word)
    (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 =
      BitVec.ult (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hbltu_0 : bltu_0 =
      match bltu_1, hbltu_1 with
      | false, _ =>
        BitVec.ult
          (iterN3Max
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      | true, _ =>
        BitVec.ult
          (iterWithDoubleAddback
            (divKTrialCallV4QHat
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
              (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hcarry2 : Carry2NzAll
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2) :
    cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 448) + (2 + 23 + 10))
      base (base + nopOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (fullDivN3UnifiedPostNoX1V4 bltu_1 bltu_0 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem **
       (.x1 ↦ᵣ raVal)) := by
  have hA := evm_div_n3_preloop_loop_stack_pre_spec_v4
    sp base a b v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2nz hshift_nz halign hbltu_1 hbltu_0 hcarry2
  have hshift_nz' : fullDivN3Shift (b.getLimbN 2) ≠ 0 := by
    rw [fullDivN3Shift_unfold]
    exact hshift_nz
  have hBNoNop := evm_div_n3_denorm_epilogue_bundled_spec_v4_noNop_v4Final_exact_x1_scratch_frame
    bltu_1 bltu_0 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    retMem dMem dloMem scratchUn0 scratchMem raVal hshift_nz'
  have hB := cpsTripleWithin_divCode_noNop_v4_to_divCode_v4 hBNoNop
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      cases bltu_1 <;> cases bltu_0
      · exact loopN3UnifiedPostV4NoX1_to_fullDivN3DenormPreV4_frame_FF
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN3UnifiedPostV4NoX1_to_fullDivN3DenormPreV4_frame_FT
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN3UnifiedPostV4NoX1_to_fullDivN3DenormPreV4_frame_TF
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN3UnifiedPostV4NoX1_to_fullDivN3DenormPreV4_frame_TT
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp)
    hA hB
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hq => hq)
    hFull

end EvmAsm.Evm64
