import EvmAsm.Evm64.DivMod.Spec.N4V4StackPre

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- EVM-stack-level DIV spec on the n=4 v4 max+skip sub-path. -/
theorem evm_div_n4_max_skip_stack_spec_v4 (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hbltu : isMaxTrialN4Evm a b)
    (hborrow : isSkipBorrowN4MaxEvm a b)
    (hsem : n4MaxSkipSemanticHolds a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 76 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPre sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem)
      (divN4MaxSkipStackPost sp a b) := by
  have h_pre := evm_div_n4_full_max_skip_stack_pre_spec_bundled_v4
    sp base a b v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 nMem shiftMem jMem
    hbnz hb3nz hshift_nz hbltu hborrow
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3, _, _, _, _⟩ :=
    n4_max_skip_div_mod_getLimbN a b hb3nz hsem
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ h_pre
  intro h hq
  simp only [fullDivN4MaxSkipPost_unfold, denormDivPost_unfold] at hq
  apply div_n4_max_skip_stack_weaken sp a b h
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
      from evmWordIs_sp_unfold]
  rw [show evmWordIs (sp + 32) (EvmWord.div a b) =
      (((sp + 32) ↦ₘ (signExtend12 4095 : Word)) **
       ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) **
       ((sp + 56) ↦ₘ (0 : Word)))
      from by rw [evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _
                  hdiv0 hdiv1 hdiv2 hdiv3]]
  rw [divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

end EvmAsm.Evm64
