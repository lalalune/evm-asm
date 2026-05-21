import EvmAsm.Evm64.DivMod.Callable

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Legacy LP64-callable DIV wrapper pinned to the original one-correction
    `divK_div128` subroutine. This gives existing v1 no-NOP specs a stable
    target when the default callable name migrates to v4. -/
def evm_div_callable_v1 : Program :=
  divK_phaseA 1020 ;;
  divK_phaseB ;;
  divK_clz ;;
  divK_phaseC2 172 ;;
  divK_normB ;;
  divK_normA 40 ;;
  divK_copyAU ;;
  divK_loopSetup 464 ;;
  divK_loopBody 560 7736 ;;
  divK_denorm ;;
  divK_div_epilogue 24 ;;
  divK_zeroPath ;;
  cc_ret ;;
  divK_div128

/-- Legacy LP64-callable MOD wrapper pinned to the original one-correction
    `divK_div128` subroutine. -/
def evm_mod_callable_v1 : Program :=
  divK_phaseA 1020 ;;
  divK_phaseB ;;
  divK_clz ;;
  divK_phaseC2 172 ;;
  divK_normB ;;
  divK_normA 40 ;;
  divK_copyAU ;;
  divK_loopSetup 464 ;;
  divK_loopBody 560 7736 ;;
  divK_denorm ;;
  divK_mod_epilogue 24 ;;
  divK_zeroPath ;;
  cc_ret ;;
  divK_div128

/-- Legacy v1 CodeReq layout for `evm_div_callable_v1`. -/
abbrev evm_div_callable_code_v1 (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,
    CodeReq.ofProg (base + clzOff)        divK_clz,
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),
    CodeReq.ofProg (base + normBOff)      divK_normB,
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),
    CodeReq.ofProg (base + denormOff)     divK_denorm,
    CodeReq.ofProg (base + epilogueOff)   (divK_div_epilogue 24),
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,
    cc_ret_code   (base + nopOff),
    CodeReq.ofProg (base + div128Off)     divK_div128
  ]

/-- Legacy v1 CodeReq layout for `evm_mod_callable_v1`. -/
abbrev evm_mod_callable_code_v1 (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,
    CodeReq.ofProg (base + clzOff)        divK_clz,
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),
    CodeReq.ofProg (base + normBOff)      divK_normB,
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),
    CodeReq.ofProg (base + denormOff)     divK_denorm,
    CodeReq.ofProg (base + epilogueOff)   (divK_mod_epilogue 24),
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,
    cc_ret_code   (base + nopOff),
    CodeReq.ofProg (base + div128Off)     divK_div128
  ]

theorem evm_div_callable_v1_eq_current :
    evm_div_callable_v1 = evm_div_callable := by
  rfl

theorem evm_mod_callable_v1_eq_current :
    evm_mod_callable_v1 = evm_mod_callable := by
  rfl

theorem evm_div_callable_code_v1_eq_current (base : Word) :
    evm_div_callable_code_v1 base = evm_div_callable_code base := by
  rfl

theorem evm_mod_callable_code_v1_eq_current (base : Word) :
    evm_mod_callable_code_v1 base = evm_mod_callable_code base := by
  rfl

-- ----------------------------------------------------------------------------
-- Legacy v1 code subsumption lemmas
-- ----------------------------------------------------------------------------

private theorem callable_b0_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left
private theorem callable_b1_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; exact CodeReq.union_mono_left
private theorem callable_b2_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b3_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b4_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b5_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b6_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b7_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left
private theorem callable_b8_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left
private theorem callable_b9_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; exact CodeReq.union_mono_left
private theorem callable_b10_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + epilogueOff) (divK_div_epilogue 24)) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b11_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b12_div_v1 {b : Word} :
    ∀ a i, (cc_ret_code (b + nopOff)) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC
  skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC
  exact CodeReq.union_mono_left
private theorem callable_b13_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons, cc_ret_code]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlockCC; exact CodeReq.union_mono_left

private theorem callable_b0_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left
private theorem callable_b1_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; exact CodeReq.union_mono_left
private theorem callable_b2_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b3_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b4_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b5_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b6_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b7_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left
private theorem callable_b8_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left
private theorem callable_b9_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; exact CodeReq.union_mono_left
private theorem callable_b10_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + epilogueOff) (divK_mod_epilogue 24)) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b11_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b12_mod_v1 {b : Word} :
    ∀ a i, (cc_ret_code (b + nopOff)) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC
  skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC
  exact CodeReq.union_mono_left
private theorem callable_b13_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons, cc_ret_code]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlockCC; exact CodeReq.union_mono_left

theorem divCode_noNop_sub_div_callable_code_v1 {base : Word} :
    ∀ a i, (divCode_noNop base) a = some i →
           (evm_div_callable_code_v1 base) a = some i := by
  unfold divCode_noNop; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono callable_b0_div_v1
    (CodeReq.union_split_mono callable_b1_div_v1
    (CodeReq.union_split_mono callable_b2_div_v1
    (CodeReq.union_split_mono callable_b3_div_v1
    (CodeReq.union_split_mono callable_b4_div_v1
    (CodeReq.union_split_mono callable_b5_div_v1
    (CodeReq.union_split_mono callable_b6_div_v1
    (CodeReq.union_split_mono callable_b7_div_v1
    (CodeReq.union_split_mono callable_b8_div_v1
    (CodeReq.union_split_mono callable_b9_div_v1
    (CodeReq.union_split_mono callable_b10_div_v1
    (CodeReq.union_split_mono callable_b11_div_v1
    (CodeReq.union_split_mono callable_b13_div_v1
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h)))))))))))))

theorem modCode_noNop_sub_mod_callable_code_v1 {base : Word} :
    ∀ a i, (modCode_noNop base) a = some i →
           (evm_mod_callable_code_v1 base) a = some i := by
  unfold modCode_noNop; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono callable_b0_mod_v1
    (CodeReq.union_split_mono callable_b1_mod_v1
    (CodeReq.union_split_mono callable_b2_mod_v1
    (CodeReq.union_split_mono callable_b3_mod_v1
    (CodeReq.union_split_mono callable_b4_mod_v1
    (CodeReq.union_split_mono callable_b5_mod_v1
    (CodeReq.union_split_mono callable_b6_mod_v1
    (CodeReq.union_split_mono callable_b7_mod_v1
    (CodeReq.union_split_mono callable_b8_mod_v1
    (CodeReq.union_split_mono callable_b9_mod_v1
    (CodeReq.union_split_mono callable_b10_mod_v1
    (CodeReq.union_split_mono callable_b11_mod_v1
    (CodeReq.union_split_mono callable_b13_mod_v1
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h)))))))))))))

theorem evm_div_callable_code_v1_ret_sub {base : Word} :
    ∀ a i, (CodeReq.singleton (base + nopOff) (.JALR .x0 .x1 0)) a = some i →
      (evm_div_callable_code_v1 base) a = some i := by
  intro a i h
  apply callable_b12_div_v1
  unfold cc_ret_code cc_ret
  simpa [CodeReq.ofProg] using h

theorem evm_mod_callable_code_v1_ret_sub {base : Word} :
    ∀ a i, (CodeReq.singleton (base + nopOff) (.JALR .x0 .x1 0)) a = some i →
      (evm_mod_callable_code_v1 base) a = some i := by
  intro a i h
  apply callable_b12_mod_v1
  unfold cc_ret_code cc_ret
  simpa [CodeReq.ofProg] using h

theorem evm_div_callable_v1_spec_from_noNop (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : DivStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
        (divModStackDispatchPre sp a b
          branch.x1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (divStackDispatchPost sp a b)) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v1 base)
      (divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** (.x1 ↦ᵣ raVal))
      (divStackDispatchPost sp a b ** (.x1 ↦ᵣ raVal)) := by
  have hpcFreePost : (divStackDispatchPost sp a b).pcFree := by
    rw [divStackDispatchPost_unfold]
    rw [divScratchOwnCall_unfold, divScratchOwn_unfold]
    pcFree
  have hStackCall :=
    cpsTripleWithin_extend_code (hmono := divCode_noNop_sub_div_callable_code_v1) hStack
  have hStackFramed :=
    cpsTripleWithin_frameR (.x1 ↦ᵣ raVal) (by pcFree) hStackCall
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_div_callable_code_v1_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL (divStackDispatchPost sp a b) hpcFreePost hRet
  exact cpsTripleWithin_seq_same_cr hStackFramed hRetFramed

theorem evm_div_callable_v1_spec_from_branch_noNop (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : DivStackSpecCase base a b) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v1 base)
      (divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** (.x1 ↦ᵣ raVal))
      (divStackDispatchPost sp a b ** (.x1 ↦ᵣ raVal)) := by
  exact evm_div_callable_v1_spec_from_noNop
    sp base raVal a b v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch
    (evm_div_stack_spec_noNop
      sp base a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch)

theorem evm_div_callable_v1_spec_from_noNop_preserving_x1 (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : DivStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
        (divModStackDispatchPre sp a b
          branch.x1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal))) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v1 base)
      (divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal)) := by
  have hpcFreePost : (divStackDispatchPostNoX1 sp a b).pcFree := by
    rw [divStackDispatchPostNoX1_unfold]
    rw [divScratchOwnCall_unfold, divScratchOwn_unfold]
    pcFree
  have hStackCall :=
    cpsTripleWithin_extend_code (hmono := divCode_noNop_sub_div_callable_code_v1) hStack
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_div_callable_code_v1_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL (divStackDispatchPostNoX1 sp a b) hpcFreePost hRet
  exact cpsTripleWithin_seq_same_cr hStackCall hRetFramed

theorem evm_div_callable_v1_spec_from_noNop_branch_return_x1 (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : DivStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
        (divModStackDispatchPre sp a b
          branch.returnX1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ branch.returnX1))) :
    cpsTripleWithin (unifiedDivBound + 1) base (branch.returnX1 &&& ~~~1)
      (evm_div_callable_code_v1 base)
      (divModStackDispatchPre sp a b
        branch.returnX1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ branch.returnX1)) := by
  have hpcFreePost : (divStackDispatchPostNoX1 sp a b).pcFree := by
    rw [divStackDispatchPostNoX1_unfold]
    rw [divScratchOwnCall_unfold, divScratchOwn_unfold]
    pcFree
  have hStackCall :=
    cpsTripleWithin_extend_code (hmono := divCode_noNop_sub_div_callable_code_v1) hStack
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_div_callable_code_v1_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) branch.returnX1)
  have hRetFramed :=
    cpsTripleWithin_frameL (divStackDispatchPostNoX1 sp a b) hpcFreePost hRet
  exact cpsTripleWithin_seq_same_cr hStackCall hRetFramed

theorem evm_div_callable_v1_spec_from_noNop_branch_return_x1_framed
    {F : Assertion} [Assertion.PCFree F] (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : DivStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
        (divModStackDispatchPre sp a b
          branch.returnX1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ branch.returnX1))) :
    cpsTripleWithin (unifiedDivBound + 1) base (branch.returnX1 &&& ~~~1)
      (evm_div_callable_code_v1 base)
      (divModStackDispatchPre sp a b
        branch.returnX1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      ((divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ branch.returnX1)) ** F) := by
  exact
    cpsTripleWithin_frameR F (by pcFree)
      (evm_div_callable_v1_spec_from_noNop_branch_return_x1
        sp base a b v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch hStack)

theorem evm_mod_callable_v1_spec_from_noNop_preserving_x1 (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : ModStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop base)
        (divModStackDispatchPre sp a b
          branch.x1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (modStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal))) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v1 base)
      (divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (modStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal)) := by
  have hpcFreePost : (modStackDispatchPostNoX1 sp a b).pcFree :=
    modStackDispatchPostNoX1_pcFree sp a b
  have hStackCall :=
    cpsTripleWithin_extend_code (hmono := modCode_noNop_sub_mod_callable_code_v1) hStack
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_mod_callable_code_v1_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL (modStackDispatchPostNoX1 sp a b) hpcFreePost hRet
  exact cpsTripleWithin_seq_same_cr hStackCall hRetFramed

theorem evm_mod_callable_v1_spec_from_noNop (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : ModStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop base)
        (divModStackDispatchPre sp a b
          branch.x1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (modStackDispatchPost sp a b)) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v1 base)
      (divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** (.x1 ↦ᵣ raVal))
      (modStackDispatchPost sp a b ** (.x1 ↦ᵣ raVal)) := by
  have hpcFreePost : (modStackDispatchPost sp a b).pcFree := by
    rw [modStackDispatchPost_unfold]
    rw [divScratchOwnCall_unfold, divScratchOwn_unfold]
    pcFree
  have hStackCall :=
    cpsTripleWithin_extend_code (hmono := modCode_noNop_sub_mod_callable_code_v1) hStack
  have hStackFramed :=
    cpsTripleWithin_frameR (.x1 ↦ᵣ raVal) (by pcFree) hStackCall
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_mod_callable_code_v1_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL (modStackDispatchPost sp a b) hpcFreePost hRet
  exact cpsTripleWithin_seq_same_cr hStackFramed hRetFramed

end EvmAsm.Evm64
