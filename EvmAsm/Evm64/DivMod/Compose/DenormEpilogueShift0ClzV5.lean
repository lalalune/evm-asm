/-
  EvmAsm.Evm64.DivMod.Compose.DenormEpilogueShift0ClzV5

  Convenience specialization of `evm_div_shift0_epilogue_spec_v5_noNop` to
  `shift = (clzResult b0).1`, the value the v5 n=1 loop leaves in the `sp+3992`
  shift cell.  On the shift=0 branch `(clzResult b0).1 = 0`, so the BEQ is taken
  and the DIV epilogue copies the four quotient digits to the output slots.

  This packages the `shift` argument so the full shift=0 path composition
  (`to_denorm_shift0` + epilogue) can apply the epilogue without separately
  threading `shift = 0`.  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- `evm_div_shift0_epilogue_spec_v5_noNop` with `shift` fixed to `(clzResult b0).1`
    (the loop's `sp+3992` shift value), discharged from `(clzResult b0).1 = 0`. -/
theorem evm_div_shift0_epilogue_clz_spec_v5_noNop (sp base b0 : Word)
    (_u0 _u1 _u2 _u3 v2 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 m0 m8 m16 m24 : Word)
    (hclz : (clzResult b0).1 = 0) :
    cpsTripleWithin 12 (base + denormOff) (base + nopOff) (divCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ q0) ** (.x6 ↦ᵣ q1) ** (.x7 ↦ᵣ q2) **
       (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ q3) **
       ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + 32) ↦ₘ q0) ** ((sp + 40) ↦ₘ q1) **
       ((sp + 48) ↦ₘ q2) ** ((sp + 56) ↦ₘ q3)) :=
  evm_div_shift0_epilogue_spec_v5_noNop sp base _u0 _u1 _u2 _u3 (clzResult b0).1
    v2 v5 v6 v7 v10 q0 q1 q2 q3 m0 m8 m16 m24 hclz

end EvmAsm.Evm64
