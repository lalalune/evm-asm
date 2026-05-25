/-
  EvmAsm.Evm64.DivMod.Counterexamples

  Kernel-checked regression pins for the two n4 call-addback counterexamples
  that motivated the div128 v4 migration.
-/

import EvmAsm.Evm64.DivMod.Callable
import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Evm64.DivMod.LoopDefs.IterV4
import EvmAsm.Evm64.DivMod.Spec.CallAddback

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace DivModCounterexamples

-- The executable DIV/MOD programs must keep the v4 div128 subroutine wired in.
theorem evm_div_uses_div128_v4 :
    evm_div =
      (divK_phaseA 1020 ;;
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
      single (.ADDI .x0 .x0 0) ;;
      divK_div128_v4) := rfl

theorem evm_mod_uses_div128_v4 :
    evm_mod =
      (divK_phaseA 1020 ;;
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
      single (.ADDI .x0 .x0 0) ;;
      divK_div128_v4) := rfl

theorem evm_div_callable_uses_div128_v4 :
    evm_div_callable =
      (divK_phaseA 1020 ;;
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
      divK_div128_v4) := rfl

theorem evm_mod_callable_uses_div128_v4 :
    evm_mod_callable =
      (divK_phaseA 1020 ;;
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
      divK_div128_v4) := rfl

theorem evm_div_callable_v4_uses_div128_v4 :
    evm_div_callable_v4 =
      (divK_phaseA 1020 ;;
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
      divK_div128_v4) := rfl

theorem evm_mod_callable_v4_uses_div128_v4 :
    evm_mod_callable_v4 =
      (divK_phaseA 1020 ;;
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
      divK_div128_v4) := rfl

-- Counterexample A:
--   a3 = 2^63 + 2^33, a2 = a1 = a0 = 0
--   b3 = 1, b2 = 2^33 - 1, b1 = b0 = 0
--   q_true = 2^63 + 2^32 - 2
abbrev ceA_a3 : Word := BitVec.ofNat 64 (2^63 + 2^33)
abbrev ceA_b2 : Word := BitVec.ofNat 64 (2^33 - 1)
abbrev ceA_b3 : Word := BitVec.ofNat 64 1
abbrev ceA_b3Norm : Word := (ceA_b3 <<< 63) ||| (ceA_b2 >>> 1)
abbrev ceA_u4 : Word := ceA_a3 >>> 1
abbrev ceA_u3 : Word := ceA_a3 <<< 63
abbrev ceA_qTrue : Nat := 2^63 + 2^32 - 2
abbrev ceA_qHatV4 : Word := BitVec.ofNat 64 (ceA_qTrue + 1)
abbrev ceA_a : EvmWord :=
  EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => 0 | 1 => 0 | 2 => 0 | 3 => ceA_a3
abbrev ceA_b : EvmWord :=
  EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => 0 | 1 => 0 | 2 => ceA_b2 | 3 => ceA_b3

theorem div128Quot_v4_counterexampleA_exact :
    div128Quot_v4 ceA_u4 ceA_u3 ceA_b3Norm = ceA_qHatV4 := by
  decide

theorem div128Quot_v4_counterexampleA_within_two_addbacks :
    (div128Quot_v4 ceA_u4 ceA_u3 ceA_b3Norm).toNat ≤ ceA_qTrue + 2 := by
  decide

theorem n4CallAddbackBeqSemanticHolds_counterexampleA_v4 :
    n4CallAddbackBeqSemanticHolds ceA_a ceA_b := by
  rw [n4CallAddbackBeqSemantic_unfold]
  decide

/-- Per-counterexample regression pin: the executable DIV body is on the v4
    path, and the normalized trial quotient for counterexample A has the v4
    bounded-overshoot shape. -/
theorem evm_div_counterexampleA_v4_regression_pin :
    evm_div =
      (divK_phaseA 1020 ;;
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
      single (.ADDI .x0 .x0 0) ;;
      divK_div128_v4) ∧
    div128Quot_v4 ceA_u4 ceA_u3 ceA_b3Norm = ceA_qHatV4 ∧
    (div128Quot_v4 ceA_u4 ceA_u3 ceA_b3Norm).toNat ≤ ceA_qTrue + 2 := by
  constructor
  · exact evm_div_uses_div128_v4
  constructor <;> decide

-- Counterexample B:
--   a3 = 2^64 - 2, a2 = a1 = a0 = 0
--   b3 = 1, b2 = 2^64 - 2, b1 = b0 = 0
--   q_true = floor(val256(a) / val256(b)) = 2^63 - 1
abbrev ceB_a3 : Word := BitVec.ofNat 64 (2^64 - 2)
abbrev ceB_b2 : Word := BitVec.ofNat 64 (2^64 - 2)
abbrev ceB_b3 : Word := BitVec.ofNat 64 1
abbrev ceB_b3Norm : Word := (ceB_b3 <<< 63) ||| (ceB_b2 >>> 1)
abbrev ceB_u4 : Word := ceB_a3 >>> 1
abbrev ceB_u3 : Word := ceB_a3 <<< 63
abbrev ceB_qTrue : Nat := 2^63 - 1
abbrev ceB_qHatV4 : Word := BitVec.ofNat 64 ceB_qTrue

theorem div128Quot_v4_counterexampleB_exact :
    div128Quot_v4 ceB_u4 ceB_u3 ceB_b3Norm = ceB_qHatV4 := by
  decide

theorem div128Quot_v4_counterexampleB_within_two_addbacks :
    (div128Quot_v4 ceB_u4 ceB_u3 ceB_b3Norm).toNat ≤ ceB_qTrue + 2 := by
  decide

/-- Per-counterexample regression pin: the executable DIV body is on the v4
    path, and the normalized trial quotient for counterexample B has the v4
    exact quotient shape. -/
theorem evm_div_counterexampleB_v4_regression_pin :
    evm_div =
      (divK_phaseA 1020 ;;
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
      single (.ADDI .x0 .x0 0) ;;
      divK_div128_v4) ∧
    div128Quot_v4 ceB_u4 ceB_u3 ceB_b3Norm = ceB_qHatV4 ∧
    (div128Quot_v4 ceB_u4 ceB_u3 ceB_b3Norm).toNat ≤ ceB_qTrue + 2 := by
  constructor
  · exact evm_div_uses_div128_v4
  constructor <;> decide

-- N1 universal-carry counterexample:
--   b0 = 2^63 - 1, b1 = b2 = b3 = 0, shift = 1
--   qHat = u0 = u1 = u2 = u3 = 2^64 - 1, uTop = 0
--
-- This does not exercise a reachable runtime state of the v4 program. It pins
-- the proof-shape failure: `Carry2NzAll` is too strong when quantified over
-- arbitrary qHat/u states, even for a normalized one-limb divisor.
abbrev ceN1CarryB0 : Word := BitVec.ofNat 64 (2^63 - 1)
abbrev ceN1CarryNormB0 : Word :=
  ceN1CarryB0 <<< (((clzResult ceN1CarryB0).1).toNat % 64)
abbrev ceN1CarryMaxWord : Word := BitVec.ofNat 64 (2^64 - 1)
abbrev ceN1CarryMs :=
  mulsubN4 ceN1CarryMaxWord ceN1CarryNormB0 0 0 0
    ceN1CarryMaxWord ceN1CarryMaxWord ceN1CarryMaxWord ceN1CarryMaxWord
abbrev ceN1CarryAb :=
  addbackN4 ceN1CarryMs.1 ceN1CarryMs.2.1 ceN1CarryMs.2.2.1
    ceN1CarryMs.2.2.2.1 (0 - ceN1CarryMs.2.2.2.2)
    ceN1CarryNormB0 0 0 0

theorem ceN1Carry_norm_eq :
    ceN1CarryNormB0 = BitVec.ofNat 64 (2^64 - 2) := by
  native_decide

theorem ceN1Carry_first_carry_zero :
    addbackN4_carry ceN1CarryMs.1 ceN1CarryMs.2.1 ceN1CarryMs.2.2.1
      ceN1CarryMs.2.2.2.1 ceN1CarryNormB0 0 0 0 = 0 := by
  native_decide

theorem ceN1Carry_second_carry_zero :
    addbackN4_carry ceN1CarryAb.1 ceN1CarryAb.2.1 ceN1CarryAb.2.2.1
      ceN1CarryAb.2.2.2.1 ceN1CarryNormB0 0 0 0 = 0 := by
  native_decide

theorem ceN1Carry_isAddbackCarry2Nz_false :
    ¬ isAddbackCarry2Nz ceN1CarryMaxWord ceN1CarryNormB0 0 0 0
      ceN1CarryMaxWord ceN1CarryMaxWord ceN1CarryMaxWord ceN1CarryMaxWord 0 := by
  intro h
  rw [isAddbackCarry2Nz] at h
  have h_second_ne := h ceN1Carry_first_carry_zero
  exact h_second_ne ceN1Carry_second_carry_zero

theorem ceN1Carry_Carry2NzAll_false :
    ¬ Carry2NzAll ceN1CarryNormB0 0 0 0 := by
  intro h
  exact ceN1Carry_isAddbackCarry2Nz_false
    (h ceN1CarryMaxWord ceN1CarryMaxWord ceN1CarryMaxWord ceN1CarryMaxWord
      ceN1CarryMaxWord 0)

-- Reachable N1-shaped semantic regression using the same divisor shape as the
-- universal-carry counterexample above.
abbrev ceN1ShapeA : EvmWord :=
  EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => ceN1CarryB0 | 1 => 0 | 2 => 0 | 3 => 0
abbrev ceN1ShapeB : EvmWord :=
  EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => ceN1CarryB0 | 1 => 0 | 2 => 0 | 3 => 0
abbrev ceN1ShapeQuot : EvmWord :=
  EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 0

theorem ceN1Shape_semantic_div_eq_one :
    EvmWord.div ceN1ShapeA ceN1ShapeB = ceN1ShapeQuot := by
  native_decide

theorem ceN1Shape_fullDivN1QuotientWord_eq_semantic_div :
    fullDivN1QuotientWord true true true true
      ceN1CarryB0 0 0 0 ceN1CarryB0 0 0 0 =
    EvmWord.div ceN1ShapeA ceN1ShapeB := by
  native_decide

theorem evm_div_ceN1Shape_v4_semantic_regression_pin :
    evm_div =
      (divK_phaseA 1020 ;;
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
      single (.ADDI .x0 .x0 0) ;;
      divK_div128_v4) ∧
    EvmWord.div ceN1ShapeA ceN1ShapeB = ceN1ShapeQuot ∧
    fullDivN1QuotientWord true true true true
      ceN1CarryB0 0 0 0 ceN1CarryB0 0 0 0 =
    EvmWord.div ceN1ShapeA ceN1ShapeB := by
  constructor
  · exact evm_div_uses_div128_v4
  constructor
  · exact ceN1Shape_semantic_div_eq_one
  · exact ceN1Shape_fullDivN1QuotientWord_eq_semantic_div

end DivModCounterexamples

end EvmAsm.Evm64
