/-
  EvmAsm.Evm64.DivMod.Spec.CallAddback

  Call+addback BEQ semantic predicate marker (n=4, shift ≠ 0).

  Contents:
  - the predicate below, retained only as the Phase 2a algorithm-fix target
    marker.
  - a small rfl unfolding theorem.

  The former stack specs, qHat sub-stubs, and Word-level Euclideans were
  deleted after they were found to depend transitively on the false n=4 addback
  semantic premise.
-/

import EvmAsm.Evm64.DivMod.Spec.CallSkip
import EvmAsm.Evm64.DivMod.Spec.CallSkipUnconditional

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)
open EvmWord (val256)
open EvmAsm.Rv64.Tactics

-- ============================================================================
-- Call+addback BEQ semantic predicate marker (n=4, shift ≠ 0)
-- ============================================================================

/-- Semantic-correctness precondition for the n=4 call+addback-BEQ sub-path:
    the final `q_out` (= `qHat - 1` single-addback or `qHat - 2` double-addback)
    equals `⌊val256(a)/val256(b)⌋`.

    Unlike `n4CallSkipSemanticHolds` which states a lower-bound on the raw
    `div128Quot`, this predicate directly states that the post-addback
    corrected quotient is the true quotient. Proving it from first
    principles requires the Knuth TAOCP Theorem B overestimate bound
    (`q̂ ≤ q_true + 2`) plus the algorithm's addback-correction semantics,
    which combine to ensure q_out is exactly correct. Deferred to a future
    task; the stack spec delegates the proof to callers.

    **🚨 STATUS (2026-04-27, updated): real correctness bug in algorithm**.

    Verified via `lean_run_code`: with
    `a3 = 2^63 + 2^33, a2 = a1 = a0 = 0, b3 = 1, b2 = 2^33 - 1,
    b1 = b0 = 0`, the input satisfies ALL runtime preconditions for
    the call-addback-BEQ branch (hbnz, hb3nz, hshift_nz, hbltu,
    hborrow, hcarry2_nz), but the algorithm computes
    `q_out = qHat - 1 = 2^63 + 2^33 - 4 = 9223372045444710396` while
    `q_true = val256(a) / val256(b) = 2^63 + 2^32 - 2 = 9223372041149743102`.
    The discrepancy is `2^32 - 2` ≈ 4.3 × 10⁹.

    **Root cause**: our `div128Quot` does only 1 Phase 1b correction
    (vs Knuth classical 2-correction loop), so qHat can overshoot at
    val256 level by up to ~2^33. The actual RISC-V program at
    `Program.lean:386` has an addback LOOP (`BEQ x7 x0` jumps back if
    x7 = 0), but the loop-exit heuristic "limb-3 carry of addback ≠ 0"
    fires after 1 addback in this case — leaving q_out = qHat - 1,
    still ~2^32 too large.

    **Implication**: the algorithm is genuinely buggy on this input
    class. This predicate is provably FALSE on runtime-reachable inputs.
    Closure theorems for it cannot be proven; the
    user-facing `evm_div_n4_full_call_addback_beq_stack_pre_spec` and
    its relatives are vacuous on this input class.

    See `memory/project_n4callbeq_addback_overshoot_2pow32.md` and
    `memory/project_knuth_d_one_correction_design.md` for the full
    analysis.

    **Remediation options**:
    1. Modify `div128Quot` to do 2 Phase 1b corrections (matching Knuth
       classical D3 loop). Restores Knuth Theorem B's per-digit ≤ 2
       overshoot bound. Requires changing both Lean abstraction and
       RISC-V code.
    2. Modify the addback loop's exit condition to detect 2^32-scale
       overshoots (e.g., bound iteration count by some explicit limit
       and re-check). Non-trivial.
    3. Document the input class as out-of-scope and gate it externally.
       Pragmatically blocks complete EVM-level verification.

    **BLOCKER for Phase 2a**: do not try to discharge this predicate under the
    current algorithm. It is false on runtime-reachable inputs until the
    addback loop / qHat correction logic is repaired.

    Mirror of `n4CallSkipSemanticHolds` for the call+addback branch. -/
def n4CallAddbackBeqSemanticHolds (a b : EvmWord) : Prop :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  let q_out : Word :=
    if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
    else qHat + signExtend12 4095
  q_out.toNat =
    val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

-- The v1 counterexample, v2 fix-verification, v2-buggy-confirmation and
-- the v2 mirror predicate (plus its
-- sanity check on the v1 counterexample input) live in
-- `EvmAsm/Evm64/DivMod/Spec/CallAddbackCounterexamples.lean` (extracted
-- 2026 toward the #1078 file-size cap; see beads evm-asm-b5i).




theorem n4CallAddbackBeqSemantic_unfold {a b : EvmWord} :
    n4CallAddbackBeqSemanticHolds a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift :=
       (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
     let q_out : Word :=
       if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
       else qHat + signExtend12 4095
     q_out.toNat =
       val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
         val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :=
  rfl

/-- Trial quotient used by the n=4 v4 call+addback-BEQ semantic marker. -/
def n4CallAddbackBeqQHatV4 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let u4 := (a.getLimbN 3) >>> antiShift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  div128Quot_v4 u4 u3 b3'

theorem n4CallAddbackBeqQHatV4_unfold {a b : EvmWord} :
    n4CallAddbackBeqQHatV4 a b =
      (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
       let antiShift :=
         (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
       let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
       let u4 := (a.getLimbN 3) >>> antiShift
       let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
       div128Quot_v4 u4 u3 b3') :=
  rfl

/-- First addback carry used by the n=4 v4 call+addback-BEQ semantic marker. -/
def n4CallAddbackBeqCarryV4 (a b : EvmWord) : Word :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let qHat := n4CallAddbackBeqQHatV4 a b
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'

theorem n4CallAddbackBeqCarryV4_unfold {a b : EvmWord} :
    n4CallAddbackBeqCarryV4 a b =
      (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
       let antiShift :=
         (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
       let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
       let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
       let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
       let b0' := (b.getLimbN 0) <<< shift
       let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
       let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
       let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
       let u0 := (a.getLimbN 0) <<< shift
       let qHat := n4CallAddbackBeqQHatV4 a b
       let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
       addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3') :=
  rfl

/-- Corrected quotient produced by the n=4 v4 call+addback-BEQ semantic marker. -/
def n4CallAddbackBeqQOutV4 (a b : EvmWord) : Word :=
  let qHat := n4CallAddbackBeqQHatV4 a b
  let carry := n4CallAddbackBeqCarryV4 a b
  if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
  else qHat + signExtend12 4095

theorem n4CallAddbackBeqQOutV4_unfold {a b : EvmWord} :
    n4CallAddbackBeqQOutV4 a b =
      (let qHat := n4CallAddbackBeqQHatV4 a b
       let carry := n4CallAddbackBeqCarryV4 a b
       if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
       else qHat + signExtend12 4095) :=
  rfl

theorem n4CallAddbackBeqQOutV4_raw_unfold {a b : EvmWord} :
    n4CallAddbackBeqQOutV4 a b =
      (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
       let antiShift :=
         (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
       let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
       let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
       let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
       let b0' := (b.getLimbN 0) <<< shift
       let u4 := (a.getLimbN 3) >>> antiShift
       let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
       let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
       let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
       let u0 := (a.getLimbN 0) <<< shift
       let qHat := div128Quot_v4 u4 u3 b3'
       let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
       let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
       if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
       else qHat + signExtend12 4095) :=
  rfl

/-- The zero-carry call+addback-BEQ case decrements the trial quotient twice. -/
theorem n4CallAddbackBeqQOutV4_of_carry_eq_zero {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b = 0) :
    n4CallAddbackBeqQOutV4 a b =
      n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095 := by
  simp [n4CallAddbackBeqQOutV4, h_carry]

/-- The nonzero-carry call+addback-BEQ case decrements the trial quotient once. -/
theorem n4CallAddbackBeqQOutV4_of_carry_ne_zero {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b ≠ 0) :
    n4CallAddbackBeqQOutV4 a b =
      n4CallAddbackBeqQHatV4 a b + signExtend12 4095 := by
  rw [n4CallAddbackBeqQOutV4]
  rw [if_neg h_carry]

/-- `toNat` form of the zero-carry double-decrement qOut case. -/
theorem n4CallAddbackBeqQOutV4_toNat_of_carry_eq_zero {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b = 0) :
    (n4CallAddbackBeqQOutV4 a b).toNat =
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat := by
  rw [n4CallAddbackBeqQOutV4_of_carry_eq_zero h_carry]

/-- `toNat` form of the nonzero-carry single-decrement qOut case. -/
theorem n4CallAddbackBeqQOutV4_toNat_of_carry_ne_zero {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b ≠ 0) :
    (n4CallAddbackBeqQOutV4 a b).toNat =
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat := by
  rw [n4CallAddbackBeqQOutV4_of_carry_ne_zero h_carry]

/-- True 256-bit quotient targeted by the n=4 v4 call+addback-BEQ marker. -/
def n4CallAddbackBeqQTrue (a b : EvmWord) : Nat :=
  val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
    val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem n4CallAddbackBeqQTrue_unfold {a b : EvmWord} :
    n4CallAddbackBeqQTrue a b =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  rfl

theorem eq_n4CallAddbackBeqQTrue_iff {a b : EvmWord} {q : Nat} :
    q = n4CallAddbackBeqQTrue a b ↔
      q =
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  Iff.rfl

theorem n4CallAddbackBeqQTrue_eq_iff {a b : EvmWord} {q : Nat} :
    n4CallAddbackBeqQTrue a b = q ↔
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        q :=
  Iff.rfl

/-- Carry-selected qHat equality targeted by the v4 n=4 call+addback-BEQ marker. -/
def n4CallAddbackBeqQHatBranchEqQTrue (a b : EvmWord) : Prop :=
  if n4CallAddbackBeqCarryV4 a b = 0 then
    (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
      n4CallAddbackBeqQTrue a b
  else
    (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
      n4CallAddbackBeqQTrue a b

theorem n4CallAddbackBeqQHatBranchEqQTrue_unfold {a b : EvmWord} :
    n4CallAddbackBeqQHatBranchEqQTrue a b =
      if n4CallAddbackBeqCarryV4 a b = 0 then
        (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b
      else
        (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b :=
  rfl

theorem n4CallAddbackBeqQHatBranchEqQTrue_carry_eq_zero_iff {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b = 0) :
    n4CallAddbackBeqQHatBranchEqQTrue a b ↔
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b := by
  rw [n4CallAddbackBeqQHatBranchEqQTrue, if_pos h_carry]

theorem n4CallAddbackBeqQHatBranchEqQTrue_carry_ne_zero_iff {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b ≠ 0) :
    n4CallAddbackBeqQHatBranchEqQTrue a b ↔
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b := by
  rw [n4CallAddbackBeqQHatBranchEqQTrue, if_neg h_carry]

theorem n4CallAddbackBeqQOutV4_toNat_eq_qTrue_carry_eq_zero_iff {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b = 0) :
    (n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b ↔
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b := by
  rw [n4CallAddbackBeqQOutV4_toNat_of_carry_eq_zero h_carry]

theorem n4CallAddbackBeqQOutV4_toNat_eq_qTrue_carry_ne_zero_iff {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b ≠ 0) :
    (n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b ↔
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b := by
  rw [n4CallAddbackBeqQOutV4_toNat_of_carry_ne_zero h_carry]

theorem n4CallAddbackBeqQOutV4_toNat_eq_qTrue_qHat_branch_iff {a b : EvmWord} :
    (n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b ↔
      if n4CallAddbackBeqCarryV4 a b = 0 then
        (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b
      else
        (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b := by
  by_cases h_carry : n4CallAddbackBeqCarryV4 a b = 0
  · rw [if_pos h_carry]
    exact n4CallAddbackBeqQOutV4_toNat_eq_qTrue_carry_eq_zero_iff h_carry
  · rw [if_neg h_carry]
    exact n4CallAddbackBeqQOutV4_toNat_eq_qTrue_carry_ne_zero_iff h_carry

/-- Introduce `qOut = qTrue` from the carry-selected qHat equality. -/
theorem n4CallAddbackBeqQOutV4_toNat_eq_qTrue_of_qHat_branch {a b : EvmWord}
    (h_qHat :
      if n4CallAddbackBeqCarryV4 a b = 0 then
        (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b
      else
        (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b) :
    (n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b :=
  (n4CallAddbackBeqQOutV4_toNat_eq_qTrue_qHat_branch_iff).2 h_qHat

/-- Eliminate `qOut = qTrue` to the carry-selected qHat equality. -/
theorem n4CallAddbackBeqQOutV4_toNat_eq_qTrue_qHat_branch {a b : EvmWord}
    (h_qOut : (n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b) :
    if n4CallAddbackBeqCarryV4 a b = 0 then
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b
    else
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b :=
  (n4CallAddbackBeqQOutV4_toNat_eq_qTrue_qHat_branch_iff).1 h_qOut

theorem n4CallAddbackBeqQOutV4_toNat_eq_qTrue_qHatBranchEqQTrue_iff {a b : EvmWord} :
    (n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b ↔
      n4CallAddbackBeqQHatBranchEqQTrue a b := by
  exact n4CallAddbackBeqQOutV4_toNat_eq_qTrue_qHat_branch_iff

/-- Introduce `qOut = qTrue` from the named carry-selected qHat predicate. -/
theorem n4CallAddbackBeqQOutV4_toNat_eq_qTrue_of_qHatBranchEqQTrue {a b : EvmWord}
    (h_qHat : n4CallAddbackBeqQHatBranchEqQTrue a b) :
    (n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b :=
  (n4CallAddbackBeqQOutV4_toNat_eq_qTrue_qHatBranchEqQTrue_iff).2 h_qHat

/-- Eliminate `qOut = qTrue` to the named carry-selected qHat predicate. -/
theorem n4CallAddbackBeqQOutV4_toNat_eq_qTrue_qHatBranchEqQTrue {a b : EvmWord}
    (h_qOut : (n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b) :
    n4CallAddbackBeqQHatBranchEqQTrue a b :=
  (n4CallAddbackBeqQOutV4_toNat_eq_qTrue_qHatBranchEqQTrue_iff).1 h_qOut

/-- V4 semantic-correctness precondition for the n=4 call+addback-BEQ sub-path.

    This is the v4 migration target for `n4CallAddbackBeqSemanticHolds`: it uses
    the fully corrected `div128Quot_v4` trial quotient. The closure theorem
    `n4CallAddbackBeqSemanticHolds_of_runtime_conditions` should target this
    quotient surface and then retire the legacy v1 marker. -/
def n4CallAddbackBeqSemanticHoldsV4 (a b : EvmWord) : Prop :=
  (n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b

theorem n4CallAddbackBeqSemanticV4_unfold {a b : EvmWord} :
    n4CallAddbackBeqSemanticHoldsV4 a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift :=
       (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let qHat := div128Quot_v4 u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
     let q_out : Word :=
       if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
       else qHat + signExtend12 4095
     q_out.toNat =
       val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
         val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :=
  rfl

theorem n4CallAddbackBeqSemanticHoldsV4_qOutV4_eq {a b : EvmWord} :
    n4CallAddbackBeqSemanticHoldsV4 a b =
      ((n4CallAddbackBeqQOutV4 a b).toNat =
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :=
  rfl

theorem n4CallAddbackBeqSemanticHoldsV4_qOutV4_qTrue_eq {a b : EvmWord} :
    n4CallAddbackBeqSemanticHoldsV4 a b =
      ((n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b) :=
  rfl

/-- Introduce the v4 n=4 call+addback-BEQ semantic predicate from the compact
    `qOut = qTrue` equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_qOutV4_toNat_eq_qTrue {a b : EvmWord}
    (h_qOut : (n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  h_qOut

/-- Eliminate the v4 n=4 call+addback-BEQ semantic predicate to the compact
    `qOut = qTrue` equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_qOutV4_toNat_eq_qTrue {a b : EvmWord}
    (hsem : n4CallAddbackBeqSemanticHoldsV4 a b) :
    (n4CallAddbackBeqQOutV4 a b).toNat = n4CallAddbackBeqQTrue a b :=
  hsem

/-- Introduce the v4 n=4 call+addback-BEQ semantic predicate from the named
    corrected quotient equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_qOutV4_toNat_eq {a b : EvmWord}
    (h_qOut :
      (n4CallAddbackBeqQOutV4 a b).toNat =
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  h_qOut

/-- Eliminate the v4 n=4 call+addback-BEQ semantic predicate to the named
    corrected quotient equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_qOutV4_toNat_eq {a b : EvmWord}
    (hsem : n4CallAddbackBeqSemanticHoldsV4 a b) :
    (n4CallAddbackBeqQOutV4 a b).toNat =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hsem

/-- Introduce the v4 semantic predicate from the zero-carry qHat equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_carry_eq_zero_qHat {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b = 0)
    (h_qHat :
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    n4CallAddbackBeqSemanticHoldsV4 a b := by
  apply n4CallAddbackBeqSemanticHoldsV4_of_qOutV4_toNat_eq
  rw [n4CallAddbackBeqQOutV4_toNat_of_carry_eq_zero h_carry]
  exact h_qHat

/-- Introduce the v4 semantic predicate from the nonzero-carry qHat equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_carry_ne_zero_qHat {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b ≠ 0)
    (h_qHat :
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    n4CallAddbackBeqSemanticHoldsV4 a b := by
  apply n4CallAddbackBeqSemanticHoldsV4_of_qOutV4_toNat_eq
  rw [n4CallAddbackBeqQOutV4_toNat_of_carry_ne_zero h_carry]
  exact h_qHat

/-- Eliminate the v4 semantic predicate to the zero-carry qHat equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_carry_eq_zero_qHat {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b = 0)
    (hsem : n4CallAddbackBeqSemanticHoldsV4 a b) :
    (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  rw [← n4CallAddbackBeqQOutV4_toNat_of_carry_eq_zero h_carry]
  exact n4CallAddbackBeqSemanticHoldsV4_qOutV4_toNat_eq hsem

/-- Eliminate the v4 semantic predicate to the nonzero-carry qHat equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_carry_ne_zero_qHat {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b ≠ 0)
    (hsem : n4CallAddbackBeqSemanticHoldsV4 a b) :
    (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  rw [← n4CallAddbackBeqQOutV4_toNat_of_carry_ne_zero h_carry]
  exact n4CallAddbackBeqSemanticHoldsV4_qOutV4_toNat_eq hsem

/-- Introduce the v4 semantic predicate from the zero-carry qHat equality to
    the compact qTrue target. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_carry_eq_zero_qHat_qTrue {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b = 0)
    (h_qHat :
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b := by
  apply n4CallAddbackBeqSemanticHoldsV4_of_qOutV4_toNat_eq_qTrue
  rw [n4CallAddbackBeqQOutV4_toNat_of_carry_eq_zero h_carry]
  exact h_qHat

/-- Introduce the v4 semantic predicate from the nonzero-carry qHat equality to
    the compact qTrue target. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_carry_ne_zero_qHat_qTrue {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b ≠ 0)
    (h_qHat :
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b := by
  apply n4CallAddbackBeqSemanticHoldsV4_of_qOutV4_toNat_eq_qTrue
  rw [n4CallAddbackBeqQOutV4_toNat_of_carry_ne_zero h_carry]
  exact h_qHat

/-- Eliminate the v4 semantic predicate to the zero-carry qHat equality against
    the compact qTrue target. -/
theorem n4CallAddbackBeqSemanticHoldsV4_carry_eq_zero_qHat_qTrue {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b = 0)
    (hsem : n4CallAddbackBeqSemanticHoldsV4 a b) :
    (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
      n4CallAddbackBeqQTrue a b := by
  rw [← n4CallAddbackBeqQOutV4_toNat_of_carry_eq_zero h_carry]
  exact n4CallAddbackBeqSemanticHoldsV4_qOutV4_toNat_eq_qTrue hsem

/-- Eliminate the v4 semantic predicate to the nonzero-carry qHat equality
    against the compact qTrue target. -/
theorem n4CallAddbackBeqSemanticHoldsV4_carry_ne_zero_qHat_qTrue {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b ≠ 0)
    (hsem : n4CallAddbackBeqSemanticHoldsV4 a b) :
    (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
      n4CallAddbackBeqQTrue a b := by
  rw [← n4CallAddbackBeqQOutV4_toNat_of_carry_ne_zero h_carry]
  exact n4CallAddbackBeqSemanticHoldsV4_qOutV4_toNat_eq_qTrue hsem

/-- Zero-carry branch-local qHat characterization of the v4 semantic predicate. -/
theorem n4CallAddbackBeqSemanticHoldsV4_carry_eq_zero_qHat_qTrue_iff {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b = 0) :
    n4CallAddbackBeqSemanticHoldsV4 a b ↔
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b := by
  constructor
  · exact n4CallAddbackBeqSemanticHoldsV4_carry_eq_zero_qHat_qTrue h_carry
  · exact n4CallAddbackBeqSemanticHoldsV4_of_carry_eq_zero_qHat_qTrue h_carry

/-- Nonzero-carry branch-local qHat characterization of the v4 semantic predicate. -/
theorem n4CallAddbackBeqSemanticHoldsV4_carry_ne_zero_qHat_qTrue_iff {a b : EvmWord}
    (h_carry : n4CallAddbackBeqCarryV4 a b ≠ 0) :
    n4CallAddbackBeqSemanticHoldsV4 a b ↔
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b := by
  constructor
  · exact n4CallAddbackBeqSemanticHoldsV4_carry_ne_zero_qHat_qTrue h_carry
  · exact n4CallAddbackBeqSemanticHoldsV4_of_carry_ne_zero_qHat_qTrue h_carry

theorem n4CallAddbackBeqSemanticHoldsV4_qHat_branch_iff {a b : EvmWord} :
    n4CallAddbackBeqSemanticHoldsV4 a b ↔
      if n4CallAddbackBeqCarryV4 a b = 0 then
        (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b
      else
        (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b := by
  by_cases h_carry : n4CallAddbackBeqCarryV4 a b = 0
  · rw [if_pos h_carry]
    exact n4CallAddbackBeqSemanticHoldsV4_carry_eq_zero_qHat_qTrue_iff h_carry
  · rw [if_neg h_carry]
    exact n4CallAddbackBeqSemanticHoldsV4_carry_ne_zero_qHat_qTrue_iff h_carry

/-- Introduce the v4 semantic predicate from the carry-selected qHat equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_qHat_branch {a b : EvmWord}
    (h_qHat :
      if n4CallAddbackBeqCarryV4 a b = 0 then
        (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b
      else
        (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
          n4CallAddbackBeqQTrue a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  (n4CallAddbackBeqSemanticHoldsV4_qHat_branch_iff).2 h_qHat

/-- Eliminate the v4 semantic predicate to the carry-selected qHat equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_qHat_branch {a b : EvmWord}
    (hsem : n4CallAddbackBeqSemanticHoldsV4 a b) :
    if n4CallAddbackBeqCarryV4 a b = 0 then
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095 + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b
    else
      (n4CallAddbackBeqQHatV4 a b + signExtend12 4095).toNat =
        n4CallAddbackBeqQTrue a b :=
  (n4CallAddbackBeqSemanticHoldsV4_qHat_branch_iff).1 hsem

theorem n4CallAddbackBeqSemanticHoldsV4_qHatBranchEqQTrue_iff {a b : EvmWord} :
    n4CallAddbackBeqSemanticHoldsV4 a b ↔
      n4CallAddbackBeqQHatBranchEqQTrue a b := by
  exact n4CallAddbackBeqSemanticHoldsV4_qHat_branch_iff

/-- Introduce the v4 semantic predicate from the named carry-selected qHat predicate. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_qHatBranchEqQTrue {a b : EvmWord}
    (h_qHat : n4CallAddbackBeqQHatBranchEqQTrue a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  (n4CallAddbackBeqSemanticHoldsV4_qHatBranchEqQTrue_iff).2 h_qHat

/-- Eliminate the v4 semantic predicate to the named carry-selected qHat predicate. -/
theorem n4CallAddbackBeqSemanticHoldsV4_qHatBranchEqQTrue {a b : EvmWord}
    (hsem : n4CallAddbackBeqSemanticHoldsV4 a b) :
    n4CallAddbackBeqQHatBranchEqQTrue a b :=
  (n4CallAddbackBeqSemanticHoldsV4_qHatBranchEqQTrue_iff).1 hsem

/-- Introduce the v4 n=4 call+addback-BEQ semantic predicate from the raw
    normalized `q_out` equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_qOut_toNat_eq {a b : EvmWord}
    (h_qOut :
      let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
      let antiShift :=
        (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
      let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
      let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
      let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
      let b0' := (b.getLimbN 0) <<< shift
      let u4 := (a.getLimbN 3) >>> antiShift
      let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
      let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
      let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
      let u0 := (a.getLimbN 0) <<< shift
      let qHat := div128Quot_v4 u4 u3 b3'
      let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
      let q_out : Word :=
        if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
        else qHat + signExtend12 4095
      q_out.toNat =
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    n4CallAddbackBeqSemanticHoldsV4 a b := by
  rw [n4CallAddbackBeqSemanticV4_unfold]
  exact h_qOut

/-- Eliminate the v4 n=4 call+addback-BEQ semantic predicate to the raw
    normalized `q_out` equality. -/
theorem n4CallAddbackBeqSemanticHoldsV4_qOut_toNat_eq {a b : EvmWord}
    (hsem : n4CallAddbackBeqSemanticHoldsV4 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot_v4 u4 u3 b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
    let q_out : Word :=
      if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
      else qHat + signExtend12 4095
    q_out.toNat =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  rw [n4CallAddbackBeqSemanticV4_unfold] at hsem
  exact hsem

end EvmAsm.Evm64
