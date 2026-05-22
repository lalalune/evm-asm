/-
  EvmAsm.Codegen.Proofs.HandlerSpecs

  Phase 4 of the codegen-proofs roadmap: lift verified body specs from
  `Evm64/<Op>/Spec.lean` to **dispatcher-handler-level** specs that
  also account for the M5b dispatcher's wrapping (preBody + tail).

  This file delivers the **first** Phase 4 instance: a reusable template
  `cleanRetHandlerSpec` covering all handlers that use the standard
  `.advanceAndRet n` tail with an empty `preBody`, plus concrete
  instances for ADD (0x01) and POP (0x50).

  The template applies to ~70 of the 91 wired handlers today (every
  "clean-shape" entry: empty `preBody`, `tail := .advanceAndRet n`).
  Future PRs can add:
    * a `withX10SavePreBody` variant for MUL/SIGNEXTEND/BYTE/SHR;
    * a `signedDivModTail` variant for SDIV/SMOD;
    * a self-calling variant for ADDMOD;
    * parameterized templates for the PUSH/DUP/SWAP families.

  See `CODEGEN.md` for the full roadmap.
-/

import EvmAsm.Codegen.Programs
import EvmAsm.Evm64.Add.Spec
import EvmAsm.Evm64.Pop.Spec
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Rv64.InstructionSpecs

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Evm64 (cc_ret)
open EvmAsm.Rv64.Tactics

-- ============================================================================
-- 1. The clean-ret handler Program + CodeReq
-- ============================================================================

/-- Wrap a verified body in the M5b dispatcher's "clean-ret" handler
    ABI: run the body, then advance the EVM code pointer `x10` by `n`
    bytes (the opcode's byte width), then return via `JALR x0, x1, 0`
    to the dispatcher's `j .dispatch_loop` continuation. -/
def cleanRetHandlerProgram (body : Program) (n : BitVec 12) : Program :=
  body ;; (Rv64.ADDI .x10 .x10 n) ;; cc_ret

/-- CodeReq for a clean-ret handler at base address `base`. -/
abbrev cleanRetHandlerCode (base : Word) (body : Program) (n : BitVec 12) : CodeReq :=
  CodeReq.ofProg base (cleanRetHandlerProgram body n)

theorem cleanRetHandlerProgram_length (body : Program) (n : BitVec 12) :
    (cleanRetHandlerProgram body n).length = body.length + 2 := by
  simp [cleanRetHandlerProgram, seq, Rv64.ADDI, cc_ret, Rv64.JALR, single]

-- ============================================================================
-- 2. The handler-level spec template
-- ============================================================================

/-- Helper: 4 * (nSteps : Nat) as a 64-bit Word. -/
private def fourTimes (nSteps : Nat) : Word := BitVec.ofNat 64 (4 * nSteps)

/-- Lift a verified body spec to a handler subroutine spec.

    Given:
    * `h_body` — the body's verified `cpsTripleWithin` spec from
      `Evm64/<Op>/Spec.lean`. Its exit PC must be `base + 4*body.length`
      and its CodeReq must be `CodeReq.ofProg base body` (the standard
      shape produced by the `*_code` abbreviations);
    * `hQpcFree` — the body's postcondition `Q` is pcFree. Satisfied
      automatically by any sepConj of `regIs` / `memCellIs` cells
      (true for every body spec in `Evm64/`);
    * `n` — the opcode's byte width (typically `1`; up to `33` for PUSH32);

    we get a Hoare triple for the full handler subroutine
    `body ;; ADDI x10 x10 n ;; JALR x0 x1 0` that says:
    * x10 is incremented by `signExtend12 n` (= `n` as a Word, for `n < 2048`);
    * x1 is preserved;
    * the body's frame `P → Q` carries through.

    The exit PC is `x1_init &&& ~~~1` — the standard JALR mask. In the
    M5b dispatcher, x1 was set by the loop's `jalr x1, x7, 0` to the
    address of the `j .dispatch_loop` instruction (always 4-byte
    aligned), so the mask is a no-op there. -/
theorem cleanRetHandlerSpec
    {nSteps : Nat} {base : Word} {body : Program} {P Q : Assertion}
    (hQpcFree : Q.pcFree)
    (hBodyLen : body.length = nSteps)
    (hBodyLenBound : nSteps < 2 ^ 60)
    (h_body : cpsTripleWithin nSteps base (base + fourTimes nSteps)
                (CodeReq.ofProg base body) P Q)
    (n : BitVec 12)
    (x10_init x1_init : Word) :
    cpsTripleWithin (nSteps + 2) base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base body n)
      (P ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (Q ** (.x10 ↦ᵣ (x10_init + signExtend12 n)) ** (.x1 ↦ᵣ x1_init)) := by
  -- Set up code-region addresses.
  set addiAddr : Word := base + fourTimes nSteps with haddiAddr
  set jalrAddr : Word := addiAddr + 4 with hjalrAddr
  -- Frame blocks (open formulas so `pcFree` can see the structure):
  -- pre-tail `F = (x10 ↦ x10_init) ** (x1 ↦ x1_init)`
  -- post-tail `F' = (x10 ↦ x10_init + n) ** (x1 ↦ x1_init)`
  -- Framing order is chosen so that all three pieces compose with no
  -- associativity dance: body's post and ADDI's pre are syntactically
  -- `Q ** F`; ADDI's post and JALR's pre/post are syntactically `Q ** F'`.
  -- Step 1: body, framed with F on the right.
  have h_body_framed :=
    cpsTripleWithin_frameR
      ((.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (by pcFree) h_body
  -- Step 2: ADDI x10 x10 n at addiAddr. Frame x1 on the right (giving
  -- F / F' as combined frame), then Q on the left.
  have h_addi := addi_spec_same_within .x10 x10_init n addiAddr (by decide)
  have h_addi_x1 :=
    cpsTripleWithin_frameR (.x1 ↦ᵣ x1_init) pcFree_regIs h_addi
  have h_addi_framed :=
    cpsTripleWithin_frameL Q hQpcFree h_addi_x1
  -- Step 3: JALR x0 x1 0 (= cc_ret) at jalrAddr. Frame `(x10 ↦ +n)` on
  -- the left (giving F'), then Q on the left.
  have h_jalr := EvmAsm.Evm64.ret_spec_within' jalrAddr x1_init
  have h_jalr_x10 :=
    cpsTripleWithin_frameL (.x10 ↦ᵣ (x10_init + signExtend12 n))
      pcFree_regIs h_jalr
  have h_jalr_framed :=
    cpsTripleWithin_frameL Q hQpcFree h_jalr_x10
  -- Disjointness #1: body code vs ADDI singleton.
  have hNStepsBound64 : (4 * nSteps : Nat) < 2 ^ 64 := by
    have : (2 : Nat) ^ 60 * 4 ≤ 2 ^ 64 := by decide
    omega
  have h_disj_body_addi :
      (CodeReq.ofProg base body).Disjoint
        (CodeReq.singleton addiAddr (.ADDI .x10 .x10 n)) := by
    intro a
    by_cases ha : a = addiAddr
    · left
      apply CodeReq.ofProg_none_range
      intro k hk heq
      subst ha
      simp only [addiAddr, fourTimes, ← hBodyLen] at heq
      have hk_bound : (4 * k : Nat) < 4 * body.length := by omega
      have hbody_bound : (4 * body.length : Nat) < 2 ^ 64 := by
        rw [hBodyLen]; exact hNStepsBound64
      have hk_bound' : (4 * k : Nat) < 2 ^ 64 := by omega
      bv_omega
    · right
      simp [CodeReq.singleton, ha]
  -- Compose body ;; ADDI.
  have h_body_addi :=
    cpsTripleWithin_seq h_disj_body_addi h_body_framed h_addi_framed
  -- Disjointness #2: (body ∪ ADDI) vs JALR singleton.
  have h_disj_bodyaddi_jalr :
      ((CodeReq.ofProg base body).union
          (CodeReq.singleton addiAddr (.ADDI .x10 .x10 n))).Disjoint
        (CodeReq.singleton jalrAddr (.JALR .x0 .x1 0)) := by
    apply CodeReq.Disjoint.union_left
    · -- body vs JALR
      intro a
      by_cases ha : a = jalrAddr
      · left
        apply CodeReq.ofProg_none_range
        intro k hk heq
        subst ha
        simp only [jalrAddr, addiAddr, fourTimes, ← hBodyLen] at heq
        have hk_bound : (4 * k : Nat) < 4 * body.length := by omega
        have hbody_bound : (4 * body.length : Nat) < 2 ^ 64 := by
          rw [hBodyLen]; exact hNStepsBound64
        have hk_bound' : (4 * k : Nat) < 2 ^ 64 := by omega
        bv_omega
      · right; simp [CodeReq.singleton, ha]
    · -- ADDI vs JALR: singletons at addiAddr vs addiAddr + 4.
      apply CodeReq.Disjoint.singleton
      intro heq
      -- addiAddr ≠ addiAddr + 4 (since 4 ≠ 0 in Word).
      have : (4 : Word) = 0 := by
        have h := heq
        bv_omega
      exact absurd this (by decide)
  -- Compose (body ;; ADDI) ;; JALR. Bound: (nSteps + 1) + 1 = nSteps + 2.
  have h_full :=
    cpsTripleWithin_seq h_disj_bodyaddi_jalr h_body_addi h_jalr_framed
  -- Align the CodeReq with cleanRetHandlerCode. Mirrors the pattern from
  -- `mul_callable_code_eq_ofProg`: unfold seq, then apply ofProg_append
  -- twice to peel off the two tail instructions. Note `;;` is
  -- right-associative, so `body ;; ADDI ;; cc_ret = body ++ (ADDI ++ cc_ret)`.
  have hCodeEq :
      ((CodeReq.ofProg base body).union
          (CodeReq.singleton addiAddr (.ADDI .x10 .x10 n))).union
            (CodeReq.singleton jalrAddr (.JALR .x0 .x1 0)) =
        cleanRetHandlerCode base body n := by
    unfold cleanRetHandlerCode cleanRetHandlerProgram
    unfold seq
    -- Goal: `... = ofProg base (body ++ (Rv64.ADDI x10 x10 n ++ cc_ret))`
    -- Outer split: peel `body` off the front.
    have hOuter :
        CodeReq.ofProg base (body ++ (Rv64.ADDI .x10 .x10 n ++ cc_ret)) =
          (CodeReq.ofProg base body).union
            (CodeReq.ofProg (base + BitVec.ofNat 64 (4 * body.length))
              (Rv64.ADDI .x10 .x10 n ++ cc_ret)) :=
      CodeReq.ofProg_append
    rw [hOuter]
    -- Inner split: peel ADDI off the front of (ADDI ++ cc_ret).
    have hInner :
        CodeReq.ofProg (base + BitVec.ofNat 64 (4 * body.length))
            (Rv64.ADDI .x10 .x10 n ++ cc_ret) =
          (CodeReq.ofProg (base + BitVec.ofNat 64 (4 * body.length))
              (Rv64.ADDI .x10 .x10 n)).union
            (CodeReq.ofProg
              (base + BitVec.ofNat 64 (4 * body.length)
                + BitVec.ofNat 64 (4 * (Rv64.ADDI .x10 .x10 n).length))
              cc_ret) :=
      CodeReq.ofProg_append
    rw [hInner]
    -- Reduce single-instr ofProgs.
    rw [show CodeReq.ofProg (base + BitVec.ofNat 64 (4 * body.length))
              (Rv64.ADDI .x10 .x10 n)
            = CodeReq.singleton (base + BitVec.ofNat 64 (4 * body.length))
                (Instr.ADDI .x10 .x10 n) from
        CodeReq.ofProg_singleton]
    rw [show CodeReq.ofProg
              (base + BitVec.ofNat 64 (4 * body.length)
                + BitVec.ofNat 64 (4 * (Rv64.ADDI .x10 .x10 n).length))
              cc_ret
            = CodeReq.singleton
                (base + BitVec.ofNat 64 (4 * body.length)
                  + BitVec.ofNat 64 (4 * (Rv64.ADDI .x10 .x10 n).length))
                (Instr.JALR .x0 .x1 0) from
        CodeReq.ofProg_singleton]
    -- Reassociate union: ofProg_append produces right-nested
    -- `A ∪ (B ∪ C)` but h_full's CodeReq is `(A ∪ B) ∪ C`.
    rw [← CodeReq.union_assoc]
    -- Resolve address offsets to `addiAddr` / `jalrAddr`.
    have h_addi_len : (Rv64.ADDI .x10 .x10 n).length = 1 := by
      simp [Rv64.ADDI, single]
    have h_addi_off :
        base + BitVec.ofNat 64 (4 * body.length) = addiAddr := by
      simp only [addiAddr, fourTimes, hBodyLen]
    rw [h_addi_off]
    -- After the addi rewrite, the jalr address is
    -- `addiAddr + BitVec.ofNat 64 (4 * (Rv64.ADDI ...).length)`.
    have h_jalr_off :
        addiAddr + BitVec.ofNat 64 (4 * (Rv64.ADDI .x10 .x10 n).length) = jalrAddr := by
      rw [h_addi_len]
      simp only [jalrAddr]
      bv_omega
    rw [h_jalr_off]
  -- Align step bound and finish.
  rw [← hCodeEq, show nSteps + 2 = (nSteps + 1) + 1 from by omega]
  exact h_full

-- ============================================================================
-- 3. Concrete instance — ADD (0x01)
-- ============================================================================

/-- Handler-level spec for `h_ADD` (opcode 0x01). The verified
    `evm_add_spec_within` body spec gets lifted through the dispatcher's
    `.advanceAndRet 1` tail. After the handler runs, the EVM stack is
    one word smaller (per evm_add), `x10` (EVM code pointer) advances
    by 1, and `x1` (dispatcher's return address) is preserved. -/
theorem evmAddHandlerSpec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (v7 v6 v5 v11 : Word)
    (x10_init x1_init : Word) :
    let sum0 := a0 + b0
    let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
    let psum1 := a1 + b1
    let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
    let result1 := psum1 + carry0
    let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
    let carry1 := carry1a ||| carry1b
    let psum2 := a2 + b2
    let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
    let result2 := psum2 + carry1
    let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
    let carry2 := carry2a ||| carry2b
    let psum3 := a3 + b3
    let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
    let result3 := psum3 + carry2
    let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
    let carry3 := carry3a ||| carry3b
    cpsTripleWithin 32 base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base EvmAsm.Evm64.evm_add 1)
      (((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
       ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ carry3b) ** (.x5 ↦ᵣ carry3) **
        (.x11 ↦ᵣ carry3a) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ sum0) ** ((sp + 40) ↦ₘ result1) ** ((sp + 48) ↦ₘ result2) **
        ((sp + 56) ↦ₘ result3))
       ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  intro sum0 carry0 psum1 carry1a result1 carry1b carry1 psum2 carry2a result2 carry2b carry2 psum3 carry3a result3 carry3b carry3
  have h_body := EvmAsm.Evm64.evm_add_spec_within sp base a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 v5 v11
  -- evm_add_code base = CodeReq.ofProg base evm_add (by abbrev). Body length = 30.
  -- evm_add_spec_within has exit PC `base + 120` = `base + fourTimes 30`.
  have hBodyLen : EvmAsm.Evm64.evm_add.length = 30 := by decide
  have hExitEq : (base + (120 : Word)) = base + fourTimes 30 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree :
      (((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ carry3b) ** (.x5 ↦ᵣ carry3) **
        (.x11 ↦ᵣ carry3a) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ sum0) ** ((sp + 40) ↦ₘ result1) ** ((sp + 48) ↦ₘ result2) **
        ((sp + 56) ↦ₘ result3)) : Assertion).pcFree := by pcFree
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

-- ============================================================================
-- 4. Concrete instance — POP (0x50)
-- ============================================================================

/-- Handler-level spec for `h_POP` (opcode 0x50). The simplest possible
    handler: a 1-instruction body (`ADDI x12 x12 32`) that pops one
    256-bit EVM stack word, wrapped with the dispatcher's standard
    advance-by-1 tail. Total: 3 RISC-V instructions. -/
theorem evmPopHandlerSpec (sp base : Word) (x10_init x1_init : Word) :
    cpsTripleWithin 3 base (x1_init &&& ~~~1)
      (cleanRetHandlerCode base EvmAsm.Evm64.evm_pop 1)
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) := by
  have h_body := EvmAsm.Evm64.evm_pop_spec_within sp base
  have hBodyLen : EvmAsm.Evm64.evm_pop.length = 1 := by decide
  have hExitEq : (base + (4 : Word)) = base + fourTimes 1 := by
    simp only [fourTimes]; bv_omega
  rw [hExitEq] at h_body
  have hQpcFree : ((.x12 ↦ᵣ (sp + 32)) : Assertion).pcFree := pcFree_regIs
  have h := cleanRetHandlerSpec hQpcFree hBodyLen (by decide) h_body 1 x10_init x1_init
  have hAdvance : x10_init + signExtend12 (1 : BitVec 12) = x10_init + 1 := by
    have : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    rw [this]
  rw [hAdvance] at h
  exact h

end EvmAsm.Codegen.Proofs
