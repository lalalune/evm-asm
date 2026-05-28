/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128Step1V5

  Step-1 composition for the v5 `divK_div128_v5` subroutine.

  This file builds the v5 Phase-1 block specs bottom-up. The first piece
  is the straight-line prefix `init + cap_q1` (instrs [10]-[20]):

    * step-1 init (DIVU + MUL + SUB) — instrs [10..12]: q1 = uHi / dHi,
      rhat = uHi - q1*dHi.
    * Phase-1a cap block — instrs [13..20]
      (`divK_div128_cap_q1_v5_merged_spec_within`): caps q1c at 0xFFFFFFFF
      and recomputes rhatc when q1 ≥ 2^32.

  Output `q1c`/`rhatc` match the Phase-1a portion of `div128Quot_v5`.
  This is the foundation of the full `step1_v5` spec (which additionally
  threads the Phase-1b leading guard + the two D3 corrections).

  Bead `evm-asm-wbc4i.6.4` (V5.6.4), part of `div128_v5_spec` (bead `.6`).
-/

import EvmAsm.Evm64.DivMod.LimbSpec.Div128CapV5

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- div128 v5 step-1 prefix: trial division `q1` then the Phase-1a cap.
    Instrs [10]-[20]. Input: uHi in x7, dHi in x6. Output: capped `q1c`
    in x10, recomputed `rhatc` in x7. -/
theorem divK_div128_step1_initcap_v5_spec_within
    (uHi dHi v10Old v5Old v9Old : Word) (base : Word) :
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi := q1 >>> (32 : BitVec 6).toNat
    let q1cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
    let q1c := if hi = 0 then q1 else q1cCap
    let rhatc := if hi = 0 then rhat else rhat + (q1 - q1cCap) * dHi
    let x5o := if hi = 0 then hi else q1cCap
    let x9o := if hi = 0 then v9Old else (q1 - q1cCap) * dHi
    let cr :=
      CodeReq.union (CodeReq.singleton base (.DIVU .x10 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x5 .x10 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x7 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x5 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x5 .x0 28))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x5 .x0 4095))
      (CodeReq.union (CodeReq.singleton (base + 24) (.SRLI .x5 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 28) (.SUB .x9 .x10 .x5))
      (CodeReq.union (CodeReq.singleton (base + 32) (.MUL .x9 .x9 .x6))
      (CodeReq.union (CodeReq.singleton (base + 36) (.ADD .x7 .x7 .x9))
       (CodeReq.singleton (base + 40) (.ADDI .x10 .x5 0)))))))))))
    cpsTripleWithin 11 base (base + 44) cr
      ((.x7 ↦ᵣ uHi) ** (.x6 ↦ᵣ dHi) ** (.x10 ↦ᵣ v10Old) **
       (.x5 ↦ᵣ v5Old) ** (.x9 ↦ᵣ v9Old) ** (.x0 ↦ᵣ 0))
      ((.x10 ↦ᵣ q1c) ** (.x7 ↦ᵣ rhatc) ** (.x6 ↦ᵣ dHi) **
       (.x5 ↦ᵣ x5o) ** (.x9 ↦ᵣ x9o) ** (.x0 ↦ᵣ 0)) := by
  intro q1 rhat hi q1cCap q1c rhatc x5o x9o cr
  have hcr_eq : cr =
      CodeReq.union (CodeReq.singleton base (.DIVU .x10 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x5 .x10 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x7 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x5 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x5 .x0 28))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x5 .x0 4095))
      (CodeReq.union (CodeReq.singleton (base + 24) (.SRLI .x5 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 28) (.SUB .x9 .x10 .x5))
      (CodeReq.union (CodeReq.singleton (base + 32) (.MUL .x9 .x9 .x6))
      (CodeReq.union (CodeReq.singleton (base + 36) (.ADD .x7 .x7 .x9))
       (CodeReq.singleton (base + 40) (.ADDI .x10 .x5 0))))))))))) := rfl
  -- Block 1: step-1 init [10..12] (DIVU + MUL + SUB).
  have h1_raw : cpsTripleWithin 3 base (base + 12)
      (CodeReq.union (CodeReq.singleton base (.DIVU .x10 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x5 .x10 .x6))
       (CodeReq.singleton (base + 8) (.SUB .x7 .x7 .x5))))
      ((.x7 ↦ᵣ uHi) ** (.x6 ↦ᵣ dHi) ** (.x10 ↦ᵣ v10Old) ** (.x5 ↦ᵣ v5Old))
      ((.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ dHi) ** (.x10 ↦ᵣ q1) ** (.x5 ↦ᵣ q1 * dHi)) := by
    have I0 := divu_spec_gen_within .x10 .x7 .x6 v10Old uHi dHi base (by nofun)
    have I1 := mul_spec_gen_within .x5 .x10 .x6 v5Old q1 dHi (base + 4) (by nofun)
    have I2 := sub_spec_gen_rd_eq_rs1_within .x7 .x5 uHi (q1 * dHi) (base + 8) (by nofun)
    runBlock I0 I1 I2
  have h1 : cpsTripleWithin 3 base (base + 12) cr _ _ :=
    cpsTripleWithin_extend_code (h := h1_raw) (hmono := by
      rw [hcr_eq]
      exact CodeReq.union_mono_tail (CodeReq.union_mono_tail (CodeReq.union_mono_left)))
  have h1f := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ v9Old) ** (.x0 ↦ᵣ 0))
    (by pcFree) h1
  -- Block 2: Phase-1a cap [13..20].
  have h2_raw := divK_div128_cap_q1_v5_merged_spec_within q1 rhat dHi (q1 * dHi) v9Old (base + 12)
  have hb4 : (base + 12 : Word) + 4 = base + 16 := by bv_addr
  have hb8 : (base + 12 : Word) + 8 = base + 20 := by bv_addr
  have hb12 : (base + 12 : Word) + 12 = base + 24 := by bv_addr
  have hb16 : (base + 12 : Word) + 16 = base + 28 := by bv_addr
  have hb20 : (base + 12 : Word) + 20 = base + 32 := by bv_addr
  have hb24 : (base + 12 : Word) + 24 = base + 36 := by bv_addr
  have hb28 : (base + 12 : Word) + 28 = base + 40 := by bv_addr
  have hb32 : (base + 12 : Word) + 32 = base + 44 := by bv_addr
  simp only [hb4, hb8, hb12, hb16, hb20, hb24, hb28, hb32] at h2_raw
  have h2 : cpsTripleWithin 8 (base + 12) (base + 44) cr _ _ :=
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
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1f h2
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    h12

end EvmAsm.Evm64
