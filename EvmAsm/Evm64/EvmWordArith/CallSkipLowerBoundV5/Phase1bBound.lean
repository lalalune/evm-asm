/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Phase1bBound

  The V5 Phase-1b post-2nd-correction dLo bound (algorithm-level form) —
  V5.4.1's headline theorem at the `div128Quot_phase2b_q0'` interface:

    Q1dd_alg.toNat * dLo.toNat ≤ Rhatdd_alg.toNat * 2^32 + un1.toNat

  where `Q1dd_alg := div128Quot_phase2b_q0' Q1d Rhatd dLo un1` and
  `Rhatdd_alg` is the corresponding `rhat` update — both at the V5
  algorithm level (over `algorithmQ1dV5` / `algorithmRhatdV5`).

  Composes the V5.4.0 chain (algorithm bundles, cap bounds, no-wrap,
  Euclidean, overshoot) with the generic
  `div128Quot_phase2b_q0'_dLo_bound_{fire,no_fire}` helpers from
  `CallSkipLowerBoundV4/Phase2bFireBound.lean` and `Phase2bNoFireBound.lean`.

  The irreducible-form wrapper `divKTrialCallV5_phase1b_dLo_bound`
  (matching the V5.4.1 bead's literal statement on `divKTrialCallV5Q1dd`
  / `divKTrialCallV5Rhatdd`) is left to a follow-up bead: the
  let-binding factoring between V5.2's `divKTrialCallV5Q1dd_eq_phase2b`
  (top-level lets) and the algorithm-level form (lets nested in
  arguments) doesn't normalize via `rfl`. Future bead can either
  refactor V5.2's eq_phase2b to factor lets identically, or do the
  bridge via per-component equational reasoning.

  Mirror of v4's `divKTrialCallV4_phase1b_dLo_bound`
  (`CallSkipLowerBoundV4/Phase1bBound.lean:988`).

  Bead `evm-asm-wbc4i.4.1` (V5.4.1, algorithm-level half).
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1dFireOvershoot
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase2bFireBound
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase2bNoFireBound

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **V5.4.1 algorithm-level**: Phase-1b 2nd-correction dLo bound for V5
    at the `div128Quot_phase2b_q0'` interface.

    Both `Q1dd_alg` and `Rhatdd_alg` are computed from `(Q1d, Rhatd)`
    via the generic phase2b_q0' helper and its corresponding `rhat`
    update; the bound holds unconditionally under normalisation. -/
theorem algorithmQ1dV5_phase1b_dLo_bound
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let q := algorithmQ1dV5 uHi uLo vTop
    let rhat := algorithmRhatdV5 uHi uLo vTop
    let dHi := divKTrialCallV5DHi vTop
    let dLo := divKTrialCallV5DLo vTop
    let un := divKTrialCallV5Un1 uLo
    (div128Quot_phase2b_q0' q rhat dLo un).toNat * dLo.toNat ≤
      (if rhat >>> (32 : BitVec 6).toNat = (0 : Word) ∧
          BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo) then
        rhat + dHi else rhat).toNat * 2^32 + un.toNat := by
  intro q rhat dHi dLo un
  have h_q_lt : q.toNat < 2^32 := algorithmQ1dV5_lt_pow32 uHi uLo vTop
  have h_q_le : q.toNat ≤ 2^32 + 1 := by omega
  have h_dLo_lt : dLo.toNat < 2^32 := divKTrialCallV5DLo_lt_pow32 vTop
  have h_un_lt : un.toNat < 2^32 := divKTrialCallV5Un1_lt_pow32 uLo
  have h_dHi_lt : dHi.toNat < 2^32 := divKTrialCallV5DHi_lt_pow32 vTop
  have h_no_wrap_q : (q * dLo).toNat = q.toNat * dLo.toNat :=
    algorithmQ1dV5_dLo_no_wrap uHi uLo vTop
  have h_overshoot : q.toNat * dLo.toNat ≤
      rhat.toNat * 2^32 + un.toNat + dHi.toNat * 2^32 + dLo.toNat :=
    algorithmQ1dV5_dLo_overshoot_le_vTop_closed uHi uLo vTop
      hvTop_ge huHi_lt_vTop
  by_cases h_guard : rhat >>> (32 : BitVec 6).toNat = (0 : Word) ∧
    BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
  · -- Fire case
    have h_guard_full := h_guard
    obtain ⟨h_rhat_hi_zero, h_ult⟩ := h_guard
    have h_no_wrap_rhat : (rhat + dHi).toNat = rhat.toNat + dHi.toNat :=
      phase2b_rhat_add_dHi_no_wrap_of_hi_zero rhat dHi h_rhat_hi_zero h_dHi_lt
    have h_q_pos : q.toNat ≥ 1 :=
      phase2b_q_pos_of_fire_ult q dLo ((rhat <<< (32 : BitVec 6).toNat) ||| un) h_ult
    obtain ⟨h_qeq, h_bound⟩ := div128Quot_phase2b_q0'_dLo_bound_fire_case
      q rhat dLo dHi un h_no_wrap_rhat h_q_pos h_rhat_hi_zero h_ult h_overshoot
    rw [h_qeq, if_pos h_guard_full]
    exact h_bound
  · -- No-fire case
    obtain ⟨h_qeq, h_bound⟩ := div128Quot_phase2b_q0'_dLo_bound_no_fire
      q rhat dLo un h_q_le h_dLo_lt h_un_lt h_no_wrap_q h_guard
    rw [h_qeq, if_neg h_guard]
    exact h_bound

end EvmAsm.Evm64
