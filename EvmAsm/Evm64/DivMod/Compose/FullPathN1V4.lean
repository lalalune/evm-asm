import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4NoNopLoopBody
import EvmAsm.Evm64.DivMod.Compose.V4Code

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Loop body n=1, max+skip, j=0 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n1_max_skip_j0_norm_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u1 v0) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopBodyN1MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN1SkipPost sp (0 : Word) (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_max_skip_j0_norm_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hborrow)

/-- Loop body n=1, max+skip, j>0 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n1_max_skip_jgt0_norm_v4 (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u1 v0) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN1MaxSkipJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN1SkipPost sp j (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_max_skip_jgt0_norm_v4_noNop j sp base hpos
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hborrow)

/-- Loop body n=1, max path, j=3 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n1_max_j3_exact_loopIter_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN1MaxSkipJgt0NormPreV4 (3 : Word)
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1Max sp (3 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_max_j3_exact_loopIter_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal hbltu hcarry2_nz)

/-- Loop body n=1, max path, j=2 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n1_max_j2_exact_loopIter_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN1MaxSkipJgt0NormPreV4 (2 : Word)
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1Max sp (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_max_j2_exact_loopIter_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal hbltu hcarry2_nz)

/-- Loop body n=1, max path, j=1 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n1_max_j1_exact_loopIter_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN1MaxSkipJgt0NormPreV4 (1 : Word)
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1Max sp (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_max_j1_exact_loopIter_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal hbltu hcarry2_nz)

/-- Loop body n=1, max path, j=0 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n1_max_j0_exact_loopIter_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopBodyN1MaxSkipJ0NormPreV4
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1Max sp (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_max_j0_exact_loopIter_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal hbltu hcarry2_nz)

/-- Exact-`x1` N1 two-iteration max/max path over the full `divCode_v4` bundle. -/
theorem divK_loop_n1_iter10_maxmax_exact_x1_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 raVal : Word)
    (hbltu_1 : ¬BitVec.ult u1 v0)
    (hbltu_0 : ¬BitVec.ult (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 404 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopN1Iter10PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal))
      (loopN1Iter10PostNoX1 false false sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
        retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_n1_iter10_maxmax_exact_x1_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 raVal hbltu_1 hbltu_0 hcarry2)

/-- Exact-`x1` N1 three-iteration all-max path over the full `divCode_v4` bundle. -/
theorem divK_loop_n1_iter210_maxmaxmax_exact_x1_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 raVal : Word)
    (hbltu_2 : ¬BitVec.ult u1 v0)
    (hbltu_1 : ¬BitVec.ult (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu_0 : ¬BitVec.ult
      (iterN1Max v0 v1 v2 v3 u0Orig1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1 v0)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 556 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopN1Iter210PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal))
      (loopN1Iter210PostNoX1 false false false sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig1 u0Orig0 retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_n1_iter210_maxmaxmax_exact_x1_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 raVal hbltu_2 hbltu_1 hbltu_0 hcarry2)

/-- Exact-`x1` N1 four-iteration all-max path over the full `divCode_v4` bundle. -/
theorem divK_loop_n1_maxmaxmaxmax_exact_x1_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 raVal : Word)
    (hbltu_3 : ¬BitVec.ult u1 v0)
    (hbltu_2 : ¬BitVec.ult (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu_1 : ¬BitVec.ult
      (iterN1Max v0 v1 v2 v3 u0Orig2
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1 v0)
    (hbltu_0 : ¬BitVec.ult
      (iterN1Max v0 v1 v2 v3 u0Orig1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1).2.1 v0)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 758 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopN1PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal))
      (loopN1UnifiedPostNoX1 false false false false sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1 u0Orig0 retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_n1_maxmaxmaxmax_exact_x1_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 raVal
      hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2)

/-- Loop body n=1, call+skip, j=0 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n1_call_skip_j0_norm_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : loopBodyN1CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopBodyN1CallSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN1CallSkipJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_call_skip_j0_norm_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow)

/-- Loop body n=1, call+skip, j>0 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n1_call_skip_jgt0_norm_v4 (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN1CallSkipJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN1CallSkipJgt0PostV4 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_call_skip_jgt0_norm_v4_noNop j sp base hpos
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow)

end EvmAsm.Evm64
