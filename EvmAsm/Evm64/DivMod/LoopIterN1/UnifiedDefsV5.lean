/-
  EvmAsm.Evm64.DivMod.LoopIterN1.UnifiedDefsV5

  v5 n=1 four-iteration (full loop, j=3,2,1,0) ALL-CALL loop PRE/POST.  Target of
  the v5 n=1 full-loop composition (chain the j=3 call body onto the all-call
  three-iteration composition #7277).  Mirror of the iter210 defs one level up.
  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.Iter210CallV5

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 n=1 full-loop precondition (entry at j=3) with the v5 `sp+3936` scratch
    cell. -/
@[irreducible] def loopN1UnifiedPreV5 (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1 u0_orig_0 q3Old q2Old q1Old q0Old
    retMem dMem dloMem scratch_un0 scratchMem : Word) : Assertion :=
  loopN1PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1 u0_orig_0 q3Old q2Old q1Old q0Old
    retMem dMem dloMem scratch_un0 **
  (sp + signExtend12 3936 ↦ₘ scratchMem)

/-- v5 n=1 full-loop (j=3,2,1,0) ALL-CALL postcondition.  (j=3 is always call,
    overwriting the div128 scratch, so the initial scratch values do not appear.) -/
@[irreducible] def loopN1UnifiedPostV5 (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0_orig_2 u0_orig_1 u0_orig_0 scratchMem : Word) : Assertion :=
  let r3 := iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_3 := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_3 := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  loopN1Iter210PostV5 sp base v0 v1 v2 v3
    u0_orig_2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1 u0_orig_1 u0_orig_0
    (divKTrialCallV5ScratchOut u1 u0 v0 scratchMem) **
  ((u_base_3 + signExtend12 4064) ↦ₘ r3.2.2.2.2.2) ** (q_addr_3 ↦ₘ r3.1)

end EvmAsm.Evm64
