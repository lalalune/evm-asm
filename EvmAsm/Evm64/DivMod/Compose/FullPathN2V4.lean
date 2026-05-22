import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNop
import EvmAsm.Evm64.DivMod.Compose.V4Code

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Loop body n=2, max+skip, j=0 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n2_max_skip_j0_norm_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u2 v1) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopBodyN2MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN2SkipPost sp (0 : Word) (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n2_max_skip_j0_norm_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hborrow)

/-- Loop body n=2, max+skip, j>0 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n2_max_skip_jgt0_norm_v4 (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u2 v1) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN2MaxSkipJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN2SkipPost sp j (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n2_max_skip_jgt0_norm_v4_noNop j sp base hpos
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hborrow)

/-- Loop body n=2, max+addback (BEQ double-addback), j>0 over the full
    `divCode_v4` bundle. -/
theorem divK_loop_body_n2_max_addback_jgt0_beq_norm_v4 (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN2MaxSkipJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN2AddbackBeqPost sp j (signExtend12 4095 : Word)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n2_max_addback_jgt0_beq_norm_v4_noNop j sp base hpos
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hcarry2_nz hborrow)

/-- Loop body n=2, call+skip, j=0 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n2_call_skip_j0_norm_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : loopBodyN2CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopBodyN2CallSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN2CallSkipJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n2_call_skip_j0_norm_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu hborrow)

/-- Loop body n=2, call+skip, j>0 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n2_call_skip_jgt0_norm_v4 (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN2CallSkipJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN2CallSkipJgt0PostV4 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n2_call_skip_jgt0_norm_v4_noNop j sp base hpos
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu hborrow)

/-- Loop body n=2, call+addback (BEQ double-addback), j>0 over the full
    `divCode_v4` bundle. -/
theorem divK_loop_body_n2_call_addback_jgt0_beq_norm_v4 (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : loopBodyN2CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN2CallAddbackJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN2CallAddbackJgt0PostV4 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n2_call_addback_jgt0_beq_norm_v4_noNop j sp base hpos
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu hborrow hcarry2_nz)

/-- Loop body n=2, max+addback (BEQ double-addback), j=0 over the full
    `divCode_v4` bundle. -/
theorem divK_loop_body_n2_max_addback_j0_beq_norm_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopBodyN2MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN2AddbackBeqPost sp (0 : Word) (signExtend12 4095 : Word)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n2_max_addback_j0_beq_norm_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hcarry2_nz hborrow)

/-- Loop body n=2, call+addback (BEQ double-addback), j=0 over the full
    `divCode_v4` bundle. -/
theorem divK_loop_body_n2_call_addback_j0_beq_norm_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : loopBodyN2CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopBodyN2CallSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN2CallAddbackJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n2_call_addback_j0_beq_norm_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu hborrow hcarry2_nz)

end EvmAsm.Evm64
