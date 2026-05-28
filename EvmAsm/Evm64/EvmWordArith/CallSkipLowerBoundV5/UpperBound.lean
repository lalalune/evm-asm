/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.UpperBound

  **V5.4.5**: `div128Quot_v5 ≤ q_true_full + 1` unconditionally.

  Composition: V5.4.2 (Q1dd ≤ q_true_1) + V5.4.3 (un21 = r1) +
  V5.4.4 (Q0dd ≤ q_true_0 + 1) via `div128_two_step_upper_of_q0_upper_nat`.

  The bridge `divKTrialCallV5QHat_eq_div128Quot_v5` is fully proved. It is not
  a single `rfl`: the alias chain and `div128Quot_v5` are only *propositionally*
  equal because `rhat2c`'s else-branch uses `q0cCap` on one side and the
  let-bound `q0c = if hi2 = 0 then q0 else q0cCap` on the other. The proof
  splits the top-level `|||` (the `Q1dd` half is definitional) and discharges
  the `Q0dd` half with `div128Quot_v5_phase2_tail_eq`, an abstract Phase-2
  equality that keeps `un21` opaque (avoiding the Phase-1 duplication blowup)
  and case-splits on `hi2 = 0`.

  Bead evm-asm-wbc4i.4.5 (V5.4.5).
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q0ddBound
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.UpperBound
import EvmAsm.Evm64.DivMod.LoopBody.TrialCallBounds

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Abstract Phase-2 structural equality (the heart of the bridge).

    With `un21 dHi dLo un0` as *free variables*, the alias-side Phase-2
    expansion (the `Q0dd` chain: `Q0c`/`Rhat2c` → `Q0d` → `Rhat2d` → `Q0dd`)
    equals the `div128Quot_v5` Phase-2 tail (`q0''`).

    Keeping `un21` opaque is essential: it prevents the Phase-1 sub-expression
    from being duplicated across the four `Q0c`/`Rhat2c` occurrences, which is
    what makes a monolithic `rfl` exhaust the kernel.

    The two sides are *not* definitionally equal: in the `hi2 ≠ 0` branch the
    alias side uses `q0cCap` directly in `rhat2c`, while `div128Quot_v5` uses
    the let-bound `q0c = if hi2 = 0 then q0 else q0cCap`. These agree only once
    the `hi2 = 0` test is resolved — hence the `by_cases` + `if_pos`/`if_neg`. -/
private theorem div128Quot_v5_phase2_tail_eq (un21 dHi dLo un0 : Word) :
    -- alias-side Q0dd structural form (un21 abstract)
    div128Quot_phase2b_q0'
      (div128Quot_phase2b_q0'
        (let q0 := rv64_divu un21 dHi
         let hi2 := q0 >>> (32 : BitVec 6).toNat
         let q0cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
         if hi2 = 0 then q0 else q0cCap)
        (let q0 := rv64_divu un21 dHi
         let rhat2 := un21 - q0 * dHi
         let hi2 := q0 >>> (32 : BitVec 6).toNat
         let q0cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
         if hi2 = 0 then rhat2 else un21 - q0cCap * dHi)
        dLo un0)
      (let q0c :=
         (let q0 := rv64_divu un21 dHi
          let hi2 := q0 >>> (32 : BitVec 6).toNat
          let q0cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
          if hi2 = 0 then q0 else q0cCap)
       let rhat2c :=
         (let q0 := rv64_divu un21 dHi
          let rhat2 := un21 - q0 * dHi
          let hi2 := q0 >>> (32 : BitVec 6).toNat
          let q0cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
          if hi2 = 0 then rhat2 else un21 - q0cCap * dHi)
       let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
       let q0Dlo1 := q0c * dLo
       let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
       if rhat2cHi = 0 then
         if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
       else rhat2c)
      dLo un0
    =
    -- div128Quot_v5-side q0'' structural form (un21 abstract)
    (let q0 := rv64_divu un21 dHi
     let rhat2 := un21 - q0 * dHi
     let hi2 := q0 >>> (32 : BitVec 6).toNat
     let q0cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
     let q0c := if hi2 = 0 then q0 else q0cCap
     let rhat2c := if hi2 = 0 then rhat2 else un21 - q0c * dHi
     let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo un0
     let rhat2' :=
       if rhat2c >>> (32 : BitVec 6).toNat = 0 then
         let qDlo2 := q0c * dLo
         let rhatUn0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
         if BitVec.ult rhatUn0 qDlo2 then rhat2c + dHi else rhat2c
       else rhat2c
     div128Quot_phase2b_q0' q0' rhat2' dLo un0) := by
  by_cases h : (rv64_divu un21 dHi) >>> (32 : BitVec 6).toNat = 0
  · simp only [if_pos h]
  · simp only [if_neg h]

/-- Bridge: QHat = div128Quot_v5.

    Strategy (divide-and-conquer, avoiding a monolithic `rfl`):
    1. Unfold both sides to their `(q1'' <<< 32) ||| q0''` shape, rewriting the
       Phase-1 aliases (`Q1dd`, `Rhatdd`) to their `div128Quot_phase2b_q0'` form.
    2. `congr 1` splits the top-level `|||`; the `Q1dd` half is definitionally
       equal and closes by `rfl` automatically.
    3. The `Q0dd` half is *not* definitionally equal — `div128Quot_v5` writes
       `rhat2c`'s else-branch with the let-bound `q0c`, the alias chain writes
       it with `q0cCap` — so it is discharged by `div128Quot_v5_phase2_tail_eq`,
       which case-splits on `hi2 = 0` with `un21` kept opaque. -/
theorem divKTrialCallV5QHat_eq_div128Quot_v5 (uHi uLo vTop : Word) :
    divKTrialCallV5QHat uHi uLo vTop = div128Quot_v5 uHi uLo vTop := by
  unfold divKTrialCallV5QHat divKTrialCallV5Q0dd divKTrialCallV5Q0d divKTrialCallV5Rhat2d
    divKTrialCallV5Q0c divKTrialCallV5Rhat2c divKTrialCallV5Un21
  rw [divKTrialCallV5Rhatdd_eq_phase2b]
  rw [divKTrialCallV5Q1dd_eq_phase2b]
  unfold div128Quot_v5 divKTrialCallV5DHi divKTrialCallV5DLo divKTrialCallV5Un1
    divKTrialCallV5Un0
  -- Split the top-level `(_ <<< 32) ||| _`: congr closes the Q1dd half by rfl
  -- (definitionally equal), leaving the Q0dd half, which differs only in the
  -- `rhat2c` else-branch (`q0cCap` vs the let-bound `q0c`). The abstract
  -- Phase-2 lemma discharges that with `un21` opaque, avoiding the blowup.
  congr 1
  exact div128Quot_v5_phase2_tail_eq _ _ _ _

/-- QHat.toNat = Q1dd * 2^32 + Q0dd when both digits < 2^32. -/
private theorem divKTrialCallV5QHat_toNat_eq (uHi uLo vTop : Word)
    (hq1_lt : (divKTrialCallV5Q1dd uHi uLo vTop).toNat < 2^32)
    (hq0_lt : (divKTrialCallV5Q0dd uHi uLo vTop).toNat < 2^32) :
    (divKTrialCallV5QHat uHi uLo vTop).toNat =
      (divKTrialCallV5Q1dd uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV5Q0dd uHi uLo vTop).toNat := by
  unfold divKTrialCallV5QHat
  rw [show (32 : BitVec 6).toNat = 32 from by decide]
  exact EvmWord.halfword_combine _ _ hq1_lt hq0_lt

/-- **V5.4.5**: `div128Quot_v5 ≤ q_true + 1` unconditionally. -/
theorem div128Quot_v5_le_q_true_plus_one
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (div128Quot_v5 uHi uLo vTop).toNat ≤
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 1 := by
  rw [← divKTrialCallV5QHat_eq_div128Quot_v5]
  let q1 := divKTrialCallV5Q1dd uHi uLo vTop
  let q0 := divKTrialCallV5Q0dd uHi uLo vTop
  let un1 := divKTrialCallV5Un1 uLo
  let un0 := divKTrialCallV5Un0 uLo
  let un21 := divKTrialCallV5Un21 uHi uLo vTop
  have hvTop_pos : 0 < vTop.toNat := by omega
  -- Q1dd ≤ q_true_1 < 2^32.
  have h_q1_le : q1.toNat ≤ (uHi.toNat * 2^32 + un1.toNat) / vTop.toNat :=
    divKTrialCallV5Q1dd_le_q_true_1 uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_q1_lt : q1.toNat < 2^32 := by
    have h_N_lt : uHi.toNat * 2^32 + un1.toNat < vTop.toNat * 2^32 := by
      have h_un1 := divKTrialCallV5Un1_lt_pow32 uLo; nlinarith
    have : (uHi.toNat * 2^32 + un1.toNat) / vTop.toNat < 2^32 :=
      (Nat.div_lt_iff_lt_mul (by omega)).mpr (by linarith)
    omega
  -- Q0dd ≤ q_true_0 + 1 < 2^32.
  have h_q0_le : q0.toNat ≤ (un21.toNat * 2^32 + un0.toNat) / vTop.toNat + 1 :=
    divKTrialCallV5Q0dd_le_q_true_0_plus_one uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_q0_lt : q0.toNat < 2^32 := by
    -- Q0dd ≤ Q0d ≤ Q0c < 2^32 (from the cap)
    have h_q0c_lt : (divKTrialCallV5Q0c uHi uLo vTop).toNat < 2^32 := by
      rw [divKTrialCallV5Q0c_eq_algorithm]; exact algorithmQ0cV5_lt_pow32 uHi uLo vTop
    have h_q0d_le : (divKTrialCallV5Q0d uHi uLo vTop).toNat ≤
        (divKTrialCallV5Q0c uHi uLo vTop).toNat := by
      unfold divKTrialCallV5Q0d; exact div128Quot_phase2b_q0'_le_self _ _ _ _
    have h_q0dd_le : q0.toNat ≤ (divKTrialCallV5Q0d uHi uLo vTop).toNat := by
      show (divKTrialCallV5Q0dd uHi uLo vTop).toNat ≤ _
      delta divKTrialCallV5Q0dd; exact div128Quot_phase2b_q0'_le_self _ _ _ _
    exact lt_of_le_of_lt (le_trans h_q0dd_le h_q0d_le) h_q0c_lt
  -- QHat.toNat = q1 * 2^32 + q0.
  have h_qhat : (divKTrialCallV5QHat uHi uLo vTop).toNat = q1.toNat * 2^32 + q0.toNat :=
    divKTrialCallV5QHat_toNat_eq uHi uLo vTop h_q1_lt h_q0_lt
  rw [h_qhat]
  -- un21 = r1 = (uHi * 2^32 + un1) % vTop.
  have h_un21_eq_r1 : un21.toNat = (uHi.toNat * 2^32 + un1.toNat) % vTop.toNat :=
    divKTrialCallV5Un21_eq_r1 uHi uLo vTop hvTop_ge huHi_lt_vTop
  -- uLo.toNat = un1 * 2^32 + un0.
  have h_uLo : uLo.toNat = un1.toNat * 2^32 + un0.toNat := by
    unfold un1 un0 divKTrialCallV5Un1 divKTrialCallV5Un0
    exact div128Quot_vTop_decomp uLo
  -- Apply two-step Nat composition.
  have h_upper :=
    div128_two_step_upper_of_q0_upper_nat
      uHi.toNat un1.toNat un0.toNat vTop.toNat q1.toNat q0.toNat un21.toNat
      hvTop_pos h_q1_le h_un21_eq_r1 h_q0_le
  have h_eq : uHi.toNat * 2^64 + un1.toNat * 2^32 + un0.toNat =
      uHi.toNat * 2^64 + uLo.toNat := by rw [h_uLo]; ring
  rw [h_eq] at h_upper
  exact h_upper

end EvmAsm.Evm64
