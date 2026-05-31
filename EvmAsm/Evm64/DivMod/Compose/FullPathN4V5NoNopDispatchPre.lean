/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopDispatchPre

  The n=4 v5 lane pre-bridge: from the stack-dispatch precondition
  `divModStackDispatchPreNoX1` (+ the `sp+3936` div128 scratch cell) to the
  explicit path-entry precondition consumed by the n=4 full call paths
  (`evm_div_n4_full_call_{skip,addback}_spec_v5_noNop`).  v2-agnostic mirror of
  `n1_dispatchPre_to_pathEntry_v5` (FullPathN1V5Full) — the dispatch pre carries
  the shift value `v2` in `x2`, which the n=4 lane instantiates to
  `(clzResult b3).2 >>> 63`.  Bead `evm-asm-wbc4i.8`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5Full

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- Bridge the v5 stack-dispatch pre to the n=4 explicit path-entry pre.  `v2`
    (the value in `x2`) is the precomputed normalization shift; the n=4 lane
    supplies `(clzResult b3).2 >>> 63`. -/
theorem n4_dispatchPre_to_pathEntry_v5 (sp : Word) (a b : EvmWord)
    (x1Val v2 v5 v6 v7 v10 v11Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3) :
    ∀ h,
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        v2 v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem)) h →
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) **
       ((sp + signExtend12 3976) ↦ₘ jMem) **
       (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) ** regOwn .x1) h := by
  intro h hp
  delta divModStackDispatchPreNoX1 at hp
  replace hp := sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x1)))) h hp
  rw [evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
      evmWordIs_sp32_limbs_eq sp b b0 b1 b2 b3 hb0 hb1 hb2 hb3,
      divScratchValuesCallNoX1_unfold, divScratchValues_unfold] at hp
  rw [word_add_zero]
  xperm_hyp hp

end EvmAsm.Evm64
