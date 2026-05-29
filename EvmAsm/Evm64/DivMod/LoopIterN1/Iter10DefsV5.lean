/-
  EvmAsm.Evm64.DivMod.LoopIterN1.Iter10DefsV5

  v5 n=1 two-iteration (j=1, j=0) loop PRE/POST.  Unlike v4, the v5 div128 call
  exposes an extra Phase-2 scratch cell at `sp+3936`, so the v5 iteration PRE/POST
  must thread `scratchMem` (the `sp+3936` value) through each digit:

  - a CALL digit overwrites `sp+3936` with `divKTrialCallV5ScratchOut`;
  - a MAX  digit leaves it untouched.

  These defs (PRE = v4 iter10 PRE plus the `sp+3936` cell; POST over the v5 model
  `iterN1V5` and dispatcher `loopIterPostN1V5`) are the target of the v5 2-digit
  loop composition.  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.IterPostDispatchV5

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 n=1 two-iteration loop precondition: the v4 iter10 PRE plus the extra v5
    div128 Phase-2 scratch cell `sp+3936 ↦ scratchMem`. -/
@[irreducible] def loopN1Iter10PreV5 (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
    retMem dMem dloMem scratch_un0 scratchMem : Word) : Assertion :=
  loopN1Iter10PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
    retMem dMem dloMem scratch_un0 **
  (sp + signExtend12 3936 ↦ₘ scratchMem)

/-- v5 n=1 two-iteration (j=1, j=0) loop postcondition over the v5 model
    `iterN1V5` and per-digit dispatcher `loopIterPostN1V5`.  Mirror of
    `loopN1Iter10Post`, but the `sp+3936` scratch cell is threaded explicitly:
    when the final digit is MAX the surviving `sp+3936` value is whatever the
    earlier digit left. -/
@[irreducible] def loopN1Iter10PostV5 (bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
     retMem dMem dloMem scratch_un0 scratchMem : Word) : Assertion :=
  let r1 := iterN1V5 bltu_1 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  -- sp+3936 after j=1: call overwrites with ScratchOut, max passes scratchMem.
  let scratch1 := if bltu_1 then divKTrialCallV5ScratchOut u1 u0 v0 scratchMem else scratchMem
  loopIterPostN1V5 bltu_0 sp base (0 : Word) v0 v1 v2 v3
    u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 scratch1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1) **
  match bltu_1, bltu_0 with
  | false, false =>
    -- both max: nothing touched the div128 scratch region.
    (sp + signExtend12 3968 ↦ₘ retMem) **
    (sp + signExtend12 3960 ↦ₘ dMem) **
    (sp + signExtend12 3952 ↦ₘ dloMem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0) **
    (sp + signExtend12 3936 ↦ₘ scratchMem) ** regOwn .x1
  | true, false =>
    -- j=1 call left its scratch; j=0 max kept it.
    (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ divKTrialCallV5DLo v0) **
    (sp + signExtend12 3944 ↦ₘ divKTrialCallV5Un0 u0) **
    (sp + signExtend12 3936 ↦ₘ divKTrialCallV5ScratchOut u1 u0 v0 scratchMem) ** regOwn .x1
  | _, true => empAssertion

end EvmAsm.Evm64
