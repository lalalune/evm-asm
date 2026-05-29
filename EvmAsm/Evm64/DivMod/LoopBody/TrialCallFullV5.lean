/-
  EvmAsm.Evm64.DivMod.LoopBody.TrialCallFullV5

  v5 trial-quotient call path, pre-call half: save-j + trial-load over the
  **v5** loop-body code (`sharedDivModCodeNoNop_v5`).

  This is the v5 analog of the private `divK_save_trial_load_v4_spec_within_noNop`
  (TrialCall.lean).  The instructions executed here (save the current `j`, load
  the trial-window limbs `uHi`/`uLo`/`vTop` into registers) are IDENTICAL in v4
  and v5 — only the later `div128` subroutine differs — so the proof is a
  mechanical mirror, swapping the loop-body code-subsumption lemma
  `lb_sub_noNop_v4` → `lb_sub_noNop_v5` and the code surface
  `sharedDivModCodeNoNop_v4` → `_v5`.  The underlying single-instruction specs
  (`divK_save_j_spec_within`, `divK_trial_load_spec_within`) are version-agnostic.

  This is the first brick of the v5 n=1 loop-body execution layer (bead
  `evm-asm-wbc4i.7.2`): it feeds `divK_trial_call_full_v5` (next), which composes
  it with the BLTU taken-path and the existing v5 trial-call-path
  (`divK_trial_call_path_v5_spec_within_noNop_exact_x1`, #7210).
-/

import EvmAsm.Evm64.DivMod.LoopBody.TrialCall
import EvmAsm.Evm64.DivMod.Compose.V5Code

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 save-j + trial-load over `sharedDivModCodeNoNop_v5`.  Mechanical mirror of
    `divK_save_trial_load_v4_spec_within_noNop` with the v5 code subsumption. -/
theorem divK_save_trial_load_v5_spec_within_noNop
    (sp j n jOld v5Old v6Old v7Old v10Old uHi uLo vTop : Word)
    (base : Word) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 13 (base + loopBodyOff) (base + trialCallOff) (sharedDivModCodeNoNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) **
       (sp + signExtend12 3976 ↦ₘ jOld) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop))
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
       (sp + signExtend12 3976 ↦ₘ j) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop)) := by
  intro uAddr vtopBase
  have SJ := divK_save_j_spec_within sp j jOld (base + loopBodyOff)
  rw [show (base + loopBodyOff : Word) + 4 = base + (loopBodyOff + 4) from by
    simp [BitVec.add_assoc]] at SJ
  have SJe := cpsTripleWithin_extend_code (hmono :=
    lb_sub_noNop_v5 0 _ _ (by decide) (by bv_addr) (by decide)) SJ
  have SJf := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
     (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop))
    (by pcFree) SJe
  have TL := divK_trial_load_spec_within sp j n v5Old v6Old v7Old v10Old uHi uLo vTop
    (base + (loopBodyOff + 4))
  dsimp only [] at TL
  rw [show (base + (loopBodyOff + 4) : Word) + 48 = base + trialCallOff from by bv_addr] at TL
  have TLe := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub_noNop_v5 1 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 2 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 3 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 4 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 5 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 6 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 7 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 8 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 9 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 10 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 11 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub_noNop_v5 12 _ _ (by decide) (by bv_addr) (by decide))))))))))))) TL
  seqFrame SJf TLe
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    SJfTLe

end EvmAsm.Evm64
