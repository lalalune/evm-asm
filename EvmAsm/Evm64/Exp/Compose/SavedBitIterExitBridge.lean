/-
  EvmAsm.Evm64.Exp.Compose.SavedBitIterExitBridge

  Exit bridge theorems: from the final-iteration exit post-condition
  (`expTwoMulIterExitPost 0 ...`) plus an "exponent frame" atom
  (`evmWordIs (evmSp + signExtend12 (-32)) exponentWord`), prove
  `(expTwoMulLoopExitFullStackPreFrame ... ** leftover_regs) ps`.

  Architecture:
  - `expTwoMulIterExitPost` owns: x9, x0, x18, x2, x12, x5, x1,
    regOwn{x6,x7,x10,x11}, sp[0..24], LP64[0..24](memOwn),
    LP64[32..56], LP64[-64..-40](=evmSp_orig[0..24])
  - The exponent frame owns: LP64[-32..-8] (= evmSp_orig[32..56])
  - `expTwoMulLoopExitFullStackPreFrame` with `rest = [w0, squarW/rwW]`
    claims: x9, x0, x12, x2, x5, sp[0..24], LP64[-64..-40],
    LP64[-32..-8], LP64[0..24](=w0), LP64[32..56]
  - Leftover (not in FullStackPreFrame): x18, x1, regOwn{x6,x7,x10,x11}

  The combined assertion (FullStackPreFrame ** leftover) covers ALL atoms
  in the hypothesis, making the proof a sep_perm repartitioning.

  Bead: evm-asm-w5mk.1.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoop

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Exit bridge for the COND path (bit ≠ 0, result = rwW).

    Given the combined state `(expTwoMulIterCondPost 0 ... ** exponent_frame) ps`,
    prove `(FullStackPreFrame ** leftover_regs) ps` covering ALL atoms.

    - FullStackPreFrame rest = [w0, rwW] where w0 is extracted from memOwn
    - d0..d3 = exponentWord.getLimb{0,1,2,3} (from exponent_frame)
    - baseWord = expResultWord a0 a1 a2 a3 (from LP64[-64..-40] = a0..a3)
    - leftover = x18 ** x1=(base+152+68) ** regOwn{x6,x7,x10,x11} -/
theorem expTwoMulIterCondExitPost_to_FullStackPreFrame
    {bit sp evmSp base a0 a1 a2 a3 : Word} {rwW exponentWord : EvmWord}
    {ps : PartialState}
    (h : (expTwoMulIterCondPost 0 bit sp evmSp base a0 a1 a2 a3 rwW (0 = 0) **
          evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) exponentWord) ps) :
    ∃ w0 : Word,
      (expTwoMulLoopExitFullStackPreFrame sp (evmSp - 64) 0
          (rwW.getLimbN 3)
          (rwW.getLimbN 0) (rwW.getLimbN 1) (rwW.getLimbN 2) (rwW.getLimbN 3)
          (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
          (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
          (expResultWord a0 a1 a2 a3)
          [expResultWord w0 w0 w0 w0, rwW]  -- rest covers LP64[0..24] and LP64[32..56]
          (0 = 0) **
       (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
       (.x1 ↦ᵣ ((base + 152) + 68)) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11) ps := by
  sorry

/-- Exit bridge for the SKIP path (bit = 0, result = squarW).

    Given the combined state `(expTwoMulIterSkipPost 0 ... ** exponent_frame) ps`,
    prove `(FullStackPreFrame ** leftover_regs) ps` covering ALL atoms.

    - FullStackPreFrame rest = [w0, squarW] where w0 is extracted from memOwn
    - d0..d3 = exponentWord.getLimb{0,1,2,3} (from exponent_frame)
    - baseWord = expResultWord a0 a1 a2 a3 (from LP64[-64..-40] = a0..a3)
    - leftover = x18 ** x1=(base+44+68) ** regOwn{x6,x7,x10,x11} -/
theorem expTwoMulIterSkipExitPost_to_FullStackPreFrame
    {bit sp evmSp base a0 a1 a2 a3 : Word} {squarW exponentWord : EvmWord}
    {ps : PartialState}
    (h : (expTwoMulIterSkipPost 0 bit sp evmSp base a0 a1 a2 a3 squarW (0 = 0) **
          evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) exponentWord) ps) :
    ∃ w0 : Word,
      (expTwoMulLoopExitFullStackPreFrame sp (evmSp - 64) 0
          (squarW.getLimbN 3)
          (squarW.getLimbN 0) (squarW.getLimbN 1) (squarW.getLimbN 2) (squarW.getLimbN 3)
          (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
          (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
          (expResultWord a0 a1 a2 a3)
          [expResultWord w0 w0 w0 w0, squarW]  -- rest covers LP64[0..24] and LP64[32..56]
          (0 = 0) **
       (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
       (.x1 ↦ᵣ ((base + 44) + 68)) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11) ps := by
  sorry

/-- Combined exit bridge: from `(expTwoMulIterExitPost 0 ... ** exponent_frame) ps`,
    prove `∃ tOld r0..r3 w0, (FullStackPreFrame ** leftover_regs) ps`.

    This is the `hExitUniv` ingredient for `exp_loop_from_looppost_induction_general`
    (bead evm-asm-w5mk.2). The leftover_regs are the iteration-internal registers
    (x18, x1, regOwn{x6,x7,x10,x11}) that FullStackPreFrame doesn't need.

    Key architectural note (2026-05-17 analysis):
    - `expTwoMulLoopExitFullStackPreFrame` does NOT claim x18, x1, regOwns.
    - `expTwoMulIterExitPost` DOES claim those registers.
    - Therefore the exit bridge CANNOT produce bare FullStackPreFrame on ps.
    - The `** leftover` in the output covers all unclaimed atoms, making the
      assertion exact and the sep_perm repartitioning possible. -/
theorem expTwoMulIterExitPost_to_FullStackPreFrame_framed
    {bit sp evmSp base a0 a1 a2 a3 : Word} {squarW rwW exponentWord : EvmWord}
    {ps : PartialState}
    (h : (expTwoMulIterExitPost 0 bit sp evmSp base a0 a1 a2 a3 squarW rwW **
          evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) exponentWord) ps) :
    ∃ tOld r0 r1 r2 r3 w0 vx18 vx1,
      (expTwoMulLoopExitFullStackPreFrame sp (evmSp - 64) 0 tOld r0 r1 r2 r3
          (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
          (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
          (expResultWord a0 a1 a2 a3)
          [expResultWord w0 w0 w0 w0, expResultWord r0 r1 r2 r3]
          (0 = 0) **
       (.x18 ↦ᵣ vx18) ** (.x1 ↦ᵣ vx1) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11) ps := by
  sorry

end EvmAsm.Evm64.Exp.Compose
