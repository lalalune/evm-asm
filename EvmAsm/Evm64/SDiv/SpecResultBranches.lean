/-
  EvmAsm.Evm64.SDiv.SpecResultBranches

  Sign-branch refinements for the top-level SDIV stack spec.
-/

import EvmAsm.Evm64.SDiv.Spec

namespace EvmAsm.Evm64

open EvmAsm.Evm64.SDiv.Compose

/-- Top-level exact-callable SDIV stack bridge with the produced sign-fixed
    result word folded together with the untouched tail stack. -/
theorem evm_sdiv_exact_callable_return_result_stack_spec_within
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (dividend divisor : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsSign (divisor.getLimbN 3)) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsMask (divisor.getLimbN 3))
          (sdivAbsCarry3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3)) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4)))) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCode base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: divisor :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
           (dividend.getLimbN 2) (dividend.getLimbN 3)
       let divisorAbsWord :=
         sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
           (divisor.getLimbN 2) (divisor.getLimbN 3)
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
           (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat)
       let resultWord :=
         sdivSignFixedWord resultSign
           (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
           (quotientWord.getLimbN 2) (quotientWord.getLimbN 3)
       let mask := (0 : Word) - resultSign
       let sum0 := (quotientWord.getLimbN 0 ^^^ mask) + resultSign
       let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
       let sum1 := (quotientWord.getLimbN 1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (quotientWord.getLimbN 2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (quotientWord.getLimbN 3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
         (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
         evmStackIs (sp + 32) (resultWord :: rest)) **
        saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord)) := by
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
      rw [saveRaDivCallCallableReturnSignFixedWordPostNoX9_unfold] at hp
      dsimp only at hp ⊢
      rw [evmStackIs_cons]
      rw [show (sp + 32 + 32 : Word) = sp + 64 by bv_addr]
      xperm_hyp hp)
    (evm_sdiv_exact_callable_return_sign_fixed_word_stack_spec_within
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 dividend divisor rest
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hStack)

/-- Top-level exact-callable SDIV stack bridge with the result stack head
    rewritten by the SDIV result-sign branch. -/
theorem evm_sdiv_exact_callable_return_result_sign_branch_stack_spec_within
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (dividend divisor : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsSign (divisor.getLimbN 3)) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsMask (divisor.getLimbN 3))
          (sdivAbsCarry3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3)) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4)))) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCode base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: divisor :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
           (dividend.getLimbN 2) (dividend.getLimbN 3)
       let divisorAbsWord :=
         sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
           (divisor.getLimbN 2) (divisor.getLimbN 3)
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
           (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat)
       let resultWord :=
         if resultSign = 0 then quotientWord else ~~~quotientWord + 1
       let mask := (0 : Word) - resultSign
       let sum0 := (quotientWord.getLimbN 0 ^^^ mask) + resultSign
       let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
       let sum1 := (quotientWord.getLimbN 1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (quotientWord.getLimbN 2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (quotientWord.getLimbN 3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
         (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
         evmStackIs (sp + 32) (resultWord :: rest)) **
        saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord)) := by
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
      rw [EvmAsm.Evm64.SDiv.Compose.sdivSignFixedWord_result_sign (dividend.getLimbN 3)
        (divisor.getLimbN 3)] at hp
      exact hp)
    (evm_sdiv_exact_callable_return_result_stack_spec_within
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 dividend divisor rest
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hStack)

/-- Top-level exact-callable SDIV stack bridge with the result stack head
    rewritten by equality of the operand sign bits. -/
theorem evm_sdiv_exact_callable_return_sign_bit_branch_stack_spec_within
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (dividend divisor : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsSign (divisor.getLimbN 3)) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsMask (divisor.getLimbN 3))
          (sdivAbsCarry3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3)) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4)))) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCode base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: divisor :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
           (dividend.getLimbN 2) (dividend.getLimbN 3)
       let divisorAbsWord :=
         sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
           (divisor.getLimbN 2) (divisor.getLimbN 3)
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
           (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat)
       let resultWord :=
         if dividend.getLimbN 3 >>> (63 : BitVec 6).toNat =
             divisor.getLimbN 3 >>> (63 : BitVec 6).toNat then
           quotientWord
         else
           ~~~quotientWord + 1
       let mask := (0 : Word) - resultSign
       let sum0 := (quotientWord.getLimbN 0 ^^^ mask) + resultSign
       let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
       let sum1 := (quotientWord.getLimbN 1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (quotientWord.getLimbN 2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (quotientWord.getLimbN 3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
         (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
         evmStackIs (sp + 32) (resultWord :: rest)) **
        saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord)) := by
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
      by_cases h_sign :
          dividend.getLimbN 3 >>> (63 : BitVec 6).toNat =
            divisor.getLimbN 3 >>> (63 : BitVec 6).toNat
      · simp at hp ⊢
        exact hp
      · simp at hp ⊢
        exact hp)
    (evm_sdiv_exact_callable_return_result_sign_branch_stack_spec_within
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 dividend divisor rest
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hStack)

/-- Same-sign exact-callable SDIV stack bridge: when the SDIV result sign is
    zero, the result stack head is the unsigned quotient word. -/
theorem evm_sdiv_exact_callable_return_result_sign_zero_stack_spec_within
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (dividend divisor : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hResultSign :
      (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
        (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat) = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsSign (divisor.getLimbN 3)) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsMask (divisor.getLimbN 3))
          (sdivAbsCarry3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3)) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4)))) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCode base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: divisor :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
           (dividend.getLimbN 2) (dividend.getLimbN 3)
       let divisorAbsWord :=
         sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
           (divisor.getLimbN 2) (divisor.getLimbN 3)
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
           (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat)
       let mask := (0 : Word) - resultSign
       let sum0 := (quotientWord.getLimbN 0 ^^^ mask) + resultSign
       let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
       let sum1 := (quotientWord.getLimbN 1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (quotientWord.getLimbN 2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (quotientWord.getLimbN 3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
         (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
         evmStackIs (sp + 32) (quotientWord :: rest)) **
        saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord)) := by
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
      rw [hResultSign] at hp ⊢
      simp at hp ⊢
      exact hp)
    (evm_sdiv_exact_callable_return_result_sign_branch_stack_spec_within
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 dividend divisor rest
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hStack)

/-- Same-sign exact-callable SDIV stack bridge, stated with equality of the
    extracted operand sign bits instead of a precomputed result-sign fact. -/
theorem evm_sdiv_exact_callable_return_same_sign_stack_spec_within
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (dividend divisor : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hSign :
      dividend.getLimbN 3 >>> (63 : BitVec 6).toNat =
        divisor.getLimbN 3 >>> (63 : BitVec 6).toNat)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsSign (divisor.getLimbN 3)) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsMask (divisor.getLimbN 3))
          (sdivAbsCarry3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3)) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4)))) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCode base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: divisor :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
           (dividend.getLimbN 2) (dividend.getLimbN 3)
       let divisorAbsWord :=
         sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
           (divisor.getLimbN 2) (divisor.getLimbN 3)
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
           (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat)
       let mask := (0 : Word) - resultSign
       let sum0 := (quotientWord.getLimbN 0 ^^^ mask) + resultSign
       let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
       let sum1 := (quotientWord.getLimbN 1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (quotientWord.getLimbN 2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (quotientWord.getLimbN 3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
         (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
         evmStackIs (sp + 32) (quotientWord :: rest)) **
        saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord)) :=
  evm_sdiv_exact_callable_return_result_sign_zero_stack_spec_within
    vRa vSavedOld sp sDividendOld sDivisorOld
    dividendMaskOld dividendValueOld dividendCarryOld
    v2 v5 v6 dividend divisor rest
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase
    (sdivResultSign_zero_of_eq hSign) hStack

/-- Opposite-sign exact-callable SDIV stack bridge: when the SDIV result sign
    is one, the result stack head is the two's-complement quotient word. -/
theorem evm_sdiv_exact_callable_return_result_sign_one_stack_spec_within
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (dividend divisor : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hResultSign :
      (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
        (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat) = 1)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsSign (divisor.getLimbN 3)) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsMask (divisor.getLimbN 3))
          (sdivAbsCarry3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3)) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4)))) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCode base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: divisor :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
           (dividend.getLimbN 2) (dividend.getLimbN 3)
       let divisorAbsWord :=
         sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
           (divisor.getLimbN 2) (divisor.getLimbN 3)
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
           (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat)
       let mask := (0 : Word) - resultSign
       let sum0 := (quotientWord.getLimbN 0 ^^^ mask) + resultSign
       let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
       let sum1 := (quotientWord.getLimbN 1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (quotientWord.getLimbN 2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (quotientWord.getLimbN 3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
         (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
         evmStackIs (sp + 32) ((~~~quotientWord + 1) :: rest)) **
        saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord)) := by
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
      rw [hResultSign] at hp ⊢
      simp at hp ⊢
      exact hp)
    (evm_sdiv_exact_callable_return_result_sign_branch_stack_spec_within
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 dividend divisor rest
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hStack)

/-- Opposite-sign exact-callable SDIV stack bridge, stated with disequality of
    the extracted operand sign bits instead of a precomputed result-sign fact. -/
theorem evm_sdiv_exact_callable_return_opposite_sign_stack_spec_within
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (dividend divisor : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hSign :
      dividend.getLimbN 3 >>> (63 : BitVec 6).toNat ≠
        divisor.getLimbN 3 >>> (63 : BitVec 6).toNat)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsSign (divisor.getLimbN 3)) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsMask (divisor.getLimbN 3))
          (sdivAbsCarry3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3)) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4)))) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCode base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: divisor :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
           (dividend.getLimbN 2) (dividend.getLimbN 3)
       let divisorAbsWord :=
         sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
           (divisor.getLimbN 2) (divisor.getLimbN 3)
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
           (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat)
       let mask := (0 : Word) - resultSign
       let sum0 := (quotientWord.getLimbN 0 ^^^ mask) + resultSign
       let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
       let sum1 := (quotientWord.getLimbN 1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (quotientWord.getLimbN 2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (quotientWord.getLimbN 3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
         (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
         evmStackIs (sp + 32) ((~~~quotientWord + 1) :: rest)) **
        saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord)) :=
  evm_sdiv_exact_callable_return_result_sign_one_stack_spec_within
    vRa vSavedOld sp sDividendOld sDivisorOld
    dividendMaskOld dividendValueOld dividendCarryOld
    v2 v5 v6 dividend divisor rest
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase
    (sdivResultSign_one_of_ne hSign) hStack


end EvmAsm.Evm64
