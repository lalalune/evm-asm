/-
  EvmAsm.Evm64.Exp.Compose.TopCodeSpecs

  Small top-level EXP code-bundle specs split out of `Compose/Base.lean` to
  keep the base composition module under the Compose file-size guardrail.
-/

import EvmAsm.Evm64.Exp.Compose.Base

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Pointer advance lifted to the top-level EXP code bundle. -/
theorem exp_loop_pointer_advance_evm_exp_spec_within
    (vOld : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 1 (base + 24) (base + 28)
      (evmExpCode base mulOff skipOff backOff)
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 (64 : BitVec 12))) := by
  have h := EvmAsm.Evm64.exp_loop_pointer_advance_spec_within vOld (base + 24)
  have hnext : ((base + 24 : Word) + 4) = base + 28 := by bv_omega
  rw [hnext] at h
  exact cpsTripleWithin_extend_code (h := h) (hmono := evmExpCode_pointer_advance_sub)

/-- Pointer restore lifted to the top-level EXP code bundle. -/
theorem exp_loop_pointer_restore_evm_exp_spec_within
    (vOld : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 1 (base + 260) (base + 264)
      (evmExpCode base mulOff skipOff backOff)
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 ((-64) : BitVec 12))) := by
  have h := EvmAsm.Evm64.exp_loop_pointer_restore_spec_within vOld (base + 260)
  have hnext : ((base + 260 : Word) + 4) = base + 264 := by bv_omega
  rw [hnext] at h
  exact cpsTripleWithin_extend_code (h := h) (hmono := evmExpCode_pointer_restore_sub)

end EvmAsm.Evm64.Exp.Compose
