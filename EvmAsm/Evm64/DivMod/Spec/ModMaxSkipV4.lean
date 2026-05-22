import EvmAsm.Evm64.DivMod.Spec.ModN4V4StackPre

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- Stack-level postcondition shape for the n=4 MOD max+skip path. -/
@[irreducible]
def modN4MaxSkipStackPost (sp : Word) (a b : EvmWord) : Assertion :=
  (.x12 ↦ᵣ (sp + 32)) ** regOwn .x9 ** regOwn .x2 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.mod a b) **
  divScratchOwn sp

theorem modN4MaxSkipStackPost_unfold {sp : Word} {a b : EvmWord} :
    modN4MaxSkipStackPost sp a b =
    ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x9 ** regOwn .x2 **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
     evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.mod a b) **
     divScratchOwn sp) := by
  delta modN4MaxSkipStackPost
  rfl

theorem pcFree_modN4MaxSkipStackPost (sp : Word) (a b : EvmWord) :
    (modN4MaxSkipStackPost sp a b).pcFree := by
  rw [modN4MaxSkipStackPost_unfold, divScratchOwn_unfold]
  pcFree

instance (sp : Word) (a b : EvmWord) :
    Assertion.PCFree (modN4MaxSkipStackPost sp a b) :=
  ⟨pcFree_modN4MaxSkipStackPost sp a b⟩

/-- MOD counterpart of `div_n4_max_skip_stack_weaken`. -/
theorem mod_n4_max_skip_stack_weaken
    (sp : Word) (a b : EvmWord)
    {v1_p v2_p v5_p v6_p v7_p v10_p v11_p : Word}
    {q0P q1P q2_p q3_p u0P u1P u2P u3P u4_p u5_p u6_p u7_p
     shift_p n_p j_p : Word} :
    ∀ h,
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x9 ↦ᵣ v1_p) ** (.x2 ↦ᵣ v2_p) **
       (.x5 ↦ᵣ v5_p) ** (.x6 ↦ᵣ v6_p) ** (.x7 ↦ᵣ v7_p) **
       (.x10 ↦ᵣ v10_p) ** (.x11 ↦ᵣ v11_p) **
       (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.mod a b) **
       divScratchValues sp q0P q1P q2_p q3_p u0P u1P u2P u3P u4_p
         u5_p u6_p u7_p shift_p n_p j_p) h →
      modN4MaxSkipStackPost sp a b h := by
  intro h hp
  delta modN4MaxSkipStackPost
  refine sepConj_mono_right ?_ h hp
  iterate 7 apply sepConj_mono (regIs_implies_regOwn _)
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  exact divScratchValues_implies_divScratchOwn
    sp q0P q1P q2_p q3_p u0P u1P u2P u3P u4_p u5_p u6_p u7_p
    shift_p n_p j_p

/-- EVM-stack-level MOD spec on the n=4 v4 max+skip sub-path. -/
theorem evm_mod_n4_max_skip_stack_spec_within_v4 (sp base : Word)
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
      base (base + nopOff) (modCode_v4 base)
      (modN4StackPre sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem)
      (modN4MaxSkipStackPost sp a b) := by
  have h_pre := evm_mod_n4_full_max_skip_stack_pre_spec_bundled_within_v4
    sp base a b v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 nMem shiftMem jMem
    hbnz hb3nz hshift_nz hbltu hborrow
  have hshift_pos : 0 < (clzResult (b.getLimbN 3)).1.toNat := by
    by_contra h
    push Not at h
    apply hshift_nz
    apply BitVec.eq_of_toNat_eq
    rw [show (0 : Word).toNat = 0 from rfl]
    omega
  have hshift_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by
    have := clzResult_fst_toNat_le (b.getLimbN 3)
    omega
  have hmod_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have h0se12 : signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1 =
      -((clzResult (b.getLimbN 3)).1) := by
    rw [signExtend12_0]
    simp
  have hanti_toNat_mod :
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat := by
    rw [h0se12, BitVec.toNat_neg]
    have : ((clzResult (b.getLimbN 3)).1).toNat ≤ 2^64 := by
      have := ((clzResult (b.getLimbN 3)).1).isLt
      omega
    omega
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  rw [isSkipBorrowN4MaxEvm] at hborrow
  have hc3_le := EvmWord.c3_le_u_top_of_skip_borrow hborrow
  simp only [hmod_eq, hanti_toNat_mod] at hc3_le
  have h_slot := EvmWord.output_slot_to_evmWordIs_mod_n4_max_skip_denorm
    sp a b hb3nz (clzResult (b.getLimbN 3)).1.toNat hshift_pos hshift_lt_64
    hb3_bound hsem hc3_le
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ h_pre
  intro h hq
  rw [fullModN4MaxSkipPost_unfold] at hq
  simp only [denormModPost_unfold] at hq
  apply mod_n4_max_skip_stack_weaken sp a b h
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
      from evmWordIs_sp_unfold]
  rw [show evmWordIs (sp + 32) (EvmWord.mod a b) = _ from h_slot.symm]
  rw [divScratchValues_unfold]
  rw [word_add_zero] at hq
  simp only [hmod_eq, hanti_toNat_mod] at hq ⊢
  xperm_hyp hq

end EvmAsm.Evm64
