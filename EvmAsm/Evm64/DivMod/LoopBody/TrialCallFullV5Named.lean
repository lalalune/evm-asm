/-
  EvmAsm.Evm64.DivMod.LoopBody.TrialCallFullV5Named

  The v5 trial-call-full spec with a **compact NAMED post** — the brick-6
  unblock.  `divK_trial_call_full_v5` (TrialCallFullV5) produces
  `divKTrialCallFullPostV5 = div128V5SpecPost ** trial-frame`, whose registers
  are the huge raw Knuth-D quotient terms (the term-size wall).  Here we weaken
  that to `divKTrialCallFullPostV5Named`, mirror of the v4 `divKTrialCallFullPostV4`
  with the compact named v5 trial defs (`divKTrialCallV5QHat`/`Q1dd`/`Q0dd`/
  `DHi`/`X7Exit`/`X9Exit`/`ScratchOut`), using the register-name bridges
  (Div128V5FinalEqNamed / Div128V5X7X9Eq / #7252).  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.CallV5NoNop

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Compact NAMED v5 trial-call-full post (mirror of `divKTrialCallFullPostV4`
    with v5 trial defs). -/
def divKTrialCallFullPostV5Named (sp j n uHi uLo vTop base scratchMem : Word) : Assertion :=
  let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
  let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
  let dHi := divKTrialCallV5DHi vTop
  let dLo := divKTrialCallV5DLo vTop
  let un0Div := divKTrialCallV5Un0 uLo
  let q1'' := divKTrialCallV5Q1dd uHi uLo vTop
  let q0'' := divKTrialCallV5Q0dd uHi uLo vTop
  let x7Exit := divKTrialCallV5X7Exit uHi uLo vTop
  let x9Exit := divKTrialCallV5X9Exit uHi uLo vTop
  let q := divKTrialCallV5QHat uHi uLo vTop
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ x9Exit) ** regOwn .x1 **
  (.x5 ↦ᵣ q0'') ** (.x6 ↦ᵣ dHi) **
  (.x7 ↦ᵣ x7Exit) ** (.x10 ↦ᵣ q1'') ** (.x11 ↦ᵣ q) **
  (.x2 ↦ᵣ (base + div128CallRetOff)) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
  (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
  (vtopBase + signExtend12 32 ↦ₘ vTop) **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ vTop) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ un0Div) **
  (sp + signExtend12 3936 ↦ₘ divKTrialCallV5ScratchOut uHi uLo vTop scratchMem)

end EvmAsm.Evm64
