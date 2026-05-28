/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128Phase2bV5

  v5 div128 Phase-2b 2nd-D3 block (instrs [71]-[80] of `divK_div128_v5`):
  the guarded second Knuth-D3 correction on `q0`.

    * Phase-2b 2nd-D3 guard — [71..72]: `SRLI x9 x11 32 ; BNE x9 x0 36`.
      When `rhat2' ≥ 2^32` the guard fires and skips the mul-check.
    * prodcheck2 mul-check — [73..80]:
      `LD x9 x12 3952 ; MUL x7 x5 x9 ; SLLI x9 x11 32 ; LD x11 x12 3944 ;
       OR x9 x9 x11 ; BLTU x9 x7 8 ; JAL x0 8 ; ADDI x5 x5 4095`.

  This is the Phase-2b analogue of `divK_div128_prodcheck1b_merged_spec_within`
  (`Div128ProdCheck1b.lean`) — the building block the v4 step2 spec lacked
  (v4 inlined Phase-2b via `phase_D`/`phase_E` over the full step2 code).
  Both Phase-2b D3 corrections are identical between v4 and v5; only the
  Phase-2a cap differs. Composed via the disjoint guard + body sequencing
  lemma `cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr`, so no
  flat-CR subsumption is needed beyond the standard code extensions.

  Bead `evm-asm-wbc4i.6.9` (V5.6.10); a building block of the full
  `step2_v5` spec (bead `.6`).
-/

import EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck2

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Bundled CodeReq for `divK_div128_prodcheck2b_v5_merged_spec_within`
    (10 singletons, instrs [71..80]). `@[irreducible]` to keep the
    let-chain out of the theorem signature. -/
@[irreducible]
def divKDiv128Prodcheck2bV5MergedCode (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.SRLI .x9 .x11 32))
  (CodeReq.union (CodeReq.singleton (base + 4) (.BNE .x9 .x0 36))
  (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x9 .x12 3952))
  (CodeReq.union (CodeReq.singleton (base + 12) (.MUL .x7 .x5 .x9))
  (CodeReq.union (CodeReq.singleton (base + 16) (.SLLI .x9 .x11 32))
  (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x11 .x12 3944))
  (CodeReq.union (CodeReq.singleton (base + 24) (.OR .x9 .x9 .x11))
  (CodeReq.union (CodeReq.singleton (base + 28) (.BLTU .x9 .x7 8))
  (CodeReq.union (CodeReq.singleton (base + 32) (.JAL .x0 8))
   (CodeReq.singleton (base + 36) (.ADDI .x5 .x5 4095))))))))))

/-- Bundled precondition. -/
@[irreducible]
def divKDiv128Prodcheck2bV5MergedPre (sp q0' rhat2' v7Old v9Old dlo un0 : Word) :
    Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0') ** (.x11 ↦ᵣ rhat2') ** (.x7 ↦ᵣ v7Old) **
  (.x9 ↦ᵣ v9Old) ** (.x0 ↦ᵣ 0) **
  (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)

/-- Bundled taken-leg postcondition (rhat2'Hi ≠ 0: guard fires, body skipped). -/
@[irreducible]
def divKDiv128Prodcheck2bV5MergedTakenPost
    (sp q0' rhat2' v7Old dlo un0 : Word) : Assertion :=
  let rhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0') ** (.x11 ↦ᵣ rhat2') ** (.x7 ↦ᵣ v7Old) **
  (.x9 ↦ᵣ rhat2'Hi) ** (.x0 ↦ᵣ 0) ** ⌜rhat2'Hi ≠ 0⌝ **
  (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)

/-- Bundled fall-through-leg postcondition (rhat2'Hi = 0: body runs the
    2nd D3 mul-check). -/
@[irreducible]
def divKDiv128Prodcheck2bV5MergedFTPost (sp q0' rhat2' dlo un0 : Word) :
    Assertion :=
  let q0Dlo := q0' * dlo
  let rhat2'Un0 := (rhat2' <<< (32 : BitVec 6).toNat) ||| un0
  let rhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
  let q0'' := if BitVec.ult rhat2'Un0 q0Dlo then q0' + signExtend12 4095 else q0'
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0'') ** (.x11 ↦ᵣ un0) ** (.x7 ↦ᵣ q0Dlo) **
  (.x9 ↦ᵣ rhat2'Un0) ** (.x0 ↦ᵣ 0) ** ⌜rhat2'Hi = 0⌝ **
  (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)

/-- div128 v5 Phase-2b 2nd-D3 block (instrs [71]-[80]): the guard
    `SRLI;BNE` then the prodcheck2 mul-check. Both guard branches and both
    BLTU paths merge at `base + 40`. The taken leg (rhat2'Hi ≠ 0) skips the
    body, leaving `.x5 = q0'`, `.x9 = rhat2'Hi`. The fall-through leg
    (rhat2'Hi = 0) executes the mul-check, producing `.x5 = q0''`,
    `.x11 = un0`, `.x7 = q0'*dlo`, `.x9 = rhat2'*2^32|un0`.

    Phase-2b analogue of `divK_div128_prodcheck1b_merged_spec_within`. -/
theorem divK_div128_prodcheck2b_v5_merged_spec_within
    (sp q0' rhat2' v7Old v9Old dlo un0 : Word) (base : Word) :
    cpsBranchWithin 10 base (divKDiv128Prodcheck2bV5MergedCode base)
      (divKDiv128Prodcheck2bV5MergedPre sp q0' rhat2' v7Old v9Old dlo un0)
      (base + 40)
        (divKDiv128Prodcheck2bV5MergedTakenPost sp q0' rhat2' v7Old dlo un0)
      (base + 40)
        (divKDiv128Prodcheck2bV5MergedFTPost sp q0' rhat2' dlo un0) := by
  unfold divKDiv128Prodcheck2bV5MergedCode divKDiv128Prodcheck2bV5MergedPre
    divKDiv128Prodcheck2bV5MergedTakenPost divKDiv128Prodcheck2bV5MergedFTPost
  let rhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
  let cr :=
    CodeReq.union (CodeReq.singleton base (.SRLI .x9 .x11 32))
    (CodeReq.union (CodeReq.singleton (base + 4) (.BNE .x9 .x0 36))
    (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x9 .x12 3952))
    (CodeReq.union (CodeReq.singleton (base + 12) (.MUL .x7 .x5 .x9))
    (CodeReq.union (CodeReq.singleton (base + 16) (.SLLI .x9 .x11 32))
    (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x11 .x12 3944))
    (CodeReq.union (CodeReq.singleton (base + 24) (.OR .x9 .x9 .x11))
    (CodeReq.union (CodeReq.singleton (base + 28) (.BLTU .x9 .x7 8))
    (CodeReq.union (CodeReq.singleton (base + 32) (.JAL .x0 8))
     (CodeReq.singleton (base + 36) (.ADDI .x5 .x5 4095))))))))))
  have hcr_eq : cr =
      CodeReq.union (CodeReq.singleton base (.SRLI .x9 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 4) (.BNE .x9 .x0 36))
      (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x9 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 12) (.MUL .x7 .x5 .x9))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SLLI .x9 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x11 .x12 3944))
      (CodeReq.union (CodeReq.singleton (base + 24) (.OR .x9 .x9 .x11))
      (CodeReq.union (CodeReq.singleton (base + 28) (.BLTU .x9 .x7 8))
      (CodeReq.union (CodeReq.singleton (base + 32) (.JAL .x0 8))
       (CodeReq.singleton (base + 36) (.ADDI .x5 .x5 4095)))))))))) := rfl
  -- Guard [71..72] at base: cpsBranchWithin, taken→base+40, ft→base+8.
  have h1_raw := divK_div128_phase2b_guard_spec_within sp rhat2' v9Old base (36 : BitVec 13)
  have ha_t : (base + 4 : Word) + signExtend13 (36 : BitVec 13) = base + 40 := by rv64_addr
  rw [ha_t] at h1_raw
  have h1 : cpsBranchWithin 2 base cr _ _ _ _ _ :=
    cpsBranchWithin_extend_code (h := h1_raw) (hmono := by
      rw [hcr_eq]; intro a i
      simp only [CodeReq.union_singleton_apply, CodeReq.singleton]; intro h
      split at h
      · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all
      · split at h
        · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left]
        · simp at h)
  have h1f := cpsBranchWithin_frameR
    ((.x5 ↦ᵣ q0') ** (.x7 ↦ᵣ v7Old) **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) h1
  -- Body [73..80] at base+8: prodcheck2 mul-check (x9 input = rhat2'Hi, dead).
  have h2_raw := divK_div128_prodcheck2_merged_spec_within sp q0' rhat2' rhat2'Hi v7Old dlo un0
    (base + 8)
  have hb4 : (base + 8 : Word) + 4 = base + 12 := by bv_addr
  have hb8 : (base + 8 : Word) + 8 = base + 16 := by bv_addr
  have hb12 : (base + 8 : Word) + 12 = base + 20 := by bv_addr
  have hb16 : (base + 8 : Word) + 16 = base + 24 := by bv_addr
  have hb20 : (base + 8 : Word) + 20 = base + 28 := by bv_addr
  have hb24 : (base + 8 : Word) + 24 = base + 32 := by bv_addr
  have hb28 : (base + 8 : Word) + 28 = base + 36 := by bv_addr
  have hb32 : (base + 8 : Word) + 32 = base + 40 := by bv_addr
  simp only [hb4, hb8, hb12, hb16, hb20, hb24, hb28, hb32] at h2_raw
  have h2 : cpsTripleWithin 8 (base + 8) (base + 40) cr _ _ :=
    cpsTripleWithin_extend_code (h := h2_raw) (hmono := by
      rw [hcr_eq]; intro a i
      simp only [CodeReq.union_singleton_apply, CodeReq.singleton]; intro h
      split at h
      · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
      · split at h
        · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
        · split at h
          · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
          · split at h
            · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
            · split at h
              · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
              · split at h
                · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
                · split at h
                  · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
                  · split at h
                    · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
                    · simp at h)
  have h2f := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ 0) ** ⌜rhat2'Hi = 0⌝)
    (by pcFree) h2
  -- Compose: guard fall-through ⨾ body.
  have composed := cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    (h1 := h1f)
    (hperm := fun h hp => by xperm_hyp hp)
    (h2 := h2f)
    (ht1 := fun h hp => hp)
  exact cpsBranchWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed

end EvmAsm.Evm64
