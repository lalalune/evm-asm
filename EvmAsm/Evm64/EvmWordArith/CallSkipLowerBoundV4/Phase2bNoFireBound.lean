/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase2bNoFireBound

  The "no-fire" Knuth-D3 bound for `div128Quot_phase2b_q0'`: when the
  correction's BLTU test fails (i.e., `¬ BitVec.ult rhatUn1 (q * dLo)`)
  and `rhat < 2^32`, the resulting (un-corrected) quotient `q` already
  satisfies the Knuth D3 invariant `q.toNat * dLo.toNat ≤
  rhat.toNat * 2^32 + un.toNat`.

  This is the structurally trivial sub-case of the v4 Phase-1b
  2-correction post-condition (bead `evm-asm-9iqmw.7.1.3.1.1.2.1`).
  The two remaining sub-cases (`rhat ≥ 2^32` no-fire, and 2nd
  correction fires) are tracked separately.

  Generic in `q`/`rhat`/`dLo`/`un` so the same lemma serves both
  Phase-1b 2-correction (bead 7.1.3.1.1.2.1) and Phase-2 2-correction
  (bead 7.1.4.x) callers.
-/

import EvmAsm.Evm64.EvmWordArith.Div128Lemmas
import EvmAsm.Evm64.EvmWordArith.Common
import EvmAsm.Evm64.DivMod.LoopDefs.Iter

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- **Phase-2b no-fire case-b bound.** When `rhat < 2^32` and the BLTU
    test against the half-word combine `(rhat <<< 32) ||| un` fails,
    the un-corrected quotient `q` satisfies the Knuth D3 invariant
    `q.toNat * dLo.toNat ≤ rhat.toNat * 2^32 + un.toNat`.

    Requires `un < 2^32` (the standard `un1 := uLo >>> 32` shape) and
    `(q * dLo).toNat = q.toNat * dLo.toNat` (no Word-multiplication
    wrap — typically discharged by `div128Quot_q1_prime_dLo_no_wrap`
    when `q = q1'`).

    Two consequences in one statement:
    1. `div128Quot_phase2b_q0' q rhat dLo un = q` (the correction
       doesn't fire, since the BLTU test failed).
    2. `q.toNat * dLo.toNat ≤ rhat.toNat * 2^32 + un.toNat` (the
       BLTU-complement bound). -/
theorem div128Quot_phase2b_q0'_dLo_bound_no_fire_case_b
    (q rhat dLo un : Word)
    (h_rhat_lt : rhat.toNat < 2^32)
    (h_un_lt : un.toNat < 2^32)
    (h_no_wrap : (q * dLo).toNat = q.toNat * dLo.toNat)
    (h_no_ult : ¬ BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)) :
    div128Quot_phase2b_q0' q rhat dLo un = q ∧
    q.toNat * dLo.toNat ≤ rhat.toNat * 2^32 + un.toNat := by
  refine ⟨?_, ?_⟩
  · -- Step 1: the correction does not fire (the BLTU test failed).
    unfold div128Quot_phase2b_q0'
    by_cases h_hi : rhat >>> (32 : BitVec 6).toNat = (0 : Word)
    · rw [if_pos h_hi]; simp only []; rw [if_neg h_no_ult]
    · rw [if_neg h_hi]
  · -- Step 2: BLTU-complement gives the bound.
    have h_le : (q * dLo).toNat ≤
        ((rhat <<< (32 : BitVec 6).toNat) ||| un).toNat := by
      rcases (Decidable.em (BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un)
              (q * dLo))) with h | h
      · exact absurd h h_no_ult
      · rw [ult_iff] at h
        omega
    rw [h_no_wrap] at h_le
    rw [show ((32 : BitVec 6).toNat) = (32 : Nat) from rfl] at h_le
    rw [halfword_combine rhat un h_rhat_lt h_un_lt] at h_le
    exact h_le

end EvmAsm.Evm64
