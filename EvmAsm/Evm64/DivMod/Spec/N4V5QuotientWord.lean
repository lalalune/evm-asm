/-
  EvmAsm.Evm64.DivMod.Spec.N4V5QuotientWord

  N4 v5 quotient word: the n=4 DIV quotient is single-limb (the divisor is full,
  `b3 ≠ 0 ⟹ b ≥ 2^192`, and `a < 2^256`, so `a / b < 2^64`), packed into an
  `EvmWord` with limb 0 = `qVal` and limbs 1,2,3 = 0.  The `_hdivs_of_word_eq`
  projector derives the four per-limb `EvmWord.div a b` facts (the `hdiv0..hdiv3`
  hypotheses of the n=4 lane skeletons) from the single word equality
  `fullDivN4QuotientWordV5 qVal = EvmWord.div a b`.  N=4 analog of
  `fullDivN3V5_hdivs_of_word_eq` (N3V5QuotientWord).  The word equality itself
  (Knuth-D quotient correctness, `qVal = a / b`) is the remaining deep obligation,
  supplied by the lane.  Bead `evm-asm-wbc4i.8`.
-/

import EvmAsm.Evm64.EvmWordArith.DivLimbBridge
import EvmAsm.Evm64.EvmWordArith.Div

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The v5 n=4 quotient (single-limb), packed into an `EvmWord`: limb 0 = `qVal`,
    limbs 1,2,3 = 0. -/
def fullDivN4QuotientWordV5 (qVal : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 => qVal
    | 1 => (0 : Word)
    | 2 => (0 : Word)
    | 3 => (0 : Word))

/-- If `fullDivN4QuotientWordV5 qVal = EvmWord.div a b`, then limb 0 of
    `EvmWord.div a b` is `qVal` and limbs 1,2,3 are zero — i.e. the four `hdiv`
    facts the n=4 lane skeletons consume. -/
theorem fullDivN4V5_hdivs_of_word_eq (a b : EvmWord) (qVal : Word)
    (hdiv : fullDivN4QuotientWordV5 qVal = EvmWord.div a b) :
    (EvmWord.div a b).getLimbN 0 = qVal ∧
    (EvmWord.div a b).getLimbN 1 = (0 : Word) ∧
    (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hdiv]; delta fullDivN4QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hdiv]; delta fullDivN4QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hdiv]; delta fullDivN4QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hdiv]; delta fullDivN4QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_3

end EvmAsm.Evm64
