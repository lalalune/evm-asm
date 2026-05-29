/-
  EvmAsm.Evm64.EvmWordArith.DivV5TrialOverestimate

  v5 analog of `DivV4TrialOverestimate` — but DISCHARGED, not just named.

  The v4 frontier `DivKTrialCallV4QHatLeFloorPlusOne` (bead `9iqmw.7.1.4.1`)
  was the open obstruction gating `evm_div_stack_spec_unconditional`:
    `divKTrialCallV4QHat uHi uLo vTop ≤ (uHi·2^64 + uLo)/vTop + 1`
  under the call regime + normalisation. Under v4 it is FALSE in general
  (PR #7080's `+2` counterexample), which is precisely why bead `7.1.4.1`
  was impossible.

  Under v5 the capped Knuth-D quotient `div128Quot_v5` satisfies this bound
  unconditionally (V5.4.5, `div128Quot_v5_le_q_true_plus_one`), and
  `divKTrialCallV5QHat = div128Quot_v5`
  (`divKTrialCallV5QHat_eq_div128Quot_v5`). So the v5 frontier discharges
  directly. This is the core payoff of the V5 repair: the obstruction that
  was impossible under v4 holds under v5. The companion lower bound
  (`≥ floor`, from V5.5.3) is included for the BLT-path bridges.

  Bead `evm-asm-wbc4i.4.7`.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.UpperBound
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.LowerBound

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The v5 call-trial Knuth-A `+1` upper bound at `(uHi, uLo, vTop)`, the v5
    analog of `DivKTrialCallV4QHatLeFloorPlusOne`. Mirror predicate so
    downstream beads/PRs have a single attackable (now discharged) target. -/
def DivKTrialCallV5QHatLeFloorPlusOne (uHi uLo vTop : Word) : Prop :=
  (divKTrialCallV5QHat uHi uLo vTop).toNat ≤
    (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 1

theorem DivKTrialCallV5QHatLeFloorPlusOne_unfold (uHi uLo vTop : Word) :
    DivKTrialCallV5QHatLeFloorPlusOne uHi uLo vTop ↔
      (divKTrialCallV5QHat uHi uLo vTop).toNat ≤
        (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 1 :=
  Iff.rfl

/-- **The V5 payoff** (v5 analog of the impossible v4 bead `7.1.4.1`):
    `divKTrialCallV5QHat ≤ (uHi·2^64 + uLo)/vTop + 1` discharged
    unconditionally from V5.4.5, under just the call regime
    (`uHi < vTop`) + normalisation (`vTop ≥ 2^63`). -/
theorem divKTrialCallV5QHat_le_floor_plus_one
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (divKTrialCallV5QHat uHi uLo vTop).toNat ≤
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 1 := by
  rw [divKTrialCallV5QHat_eq_div128Quot_v5]
  exact div128Quot_v5_le_q_true_plus_one uHi uLo vTop hvTop_ge huHi_lt_vTop

/-- Named-predicate form of `divKTrialCallV5QHat_le_floor_plus_one`. -/
theorem DivKTrialCallV5QHatLeFloorPlusOne_of_norm
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    DivKTrialCallV5QHatLeFloorPlusOne uHi uLo vTop :=
  divKTrialCallV5QHat_le_floor_plus_one uHi uLo vTop hvTop_ge huHi_lt_vTop

/-- Companion lower bound (from V5.5.3): `(uHi·2^64+uLo)/vTop ≤
    divKTrialCallV5QHat`. Together with the `+1` upper bound this pins the
    v5 trial quotient to within 1 of the floor — the input to the BLT-path
    `Carry2Nz` bridges. -/
theorem divKTrialCallV5QHat_ge_floor
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat ≤
      (divKTrialCallV5QHat uHi uLo vTop).toNat := by
  rw [divKTrialCallV5QHat_eq_div128Quot_v5]
  exact div128Quot_v5_ge_q_true uHi uLo vTop hvTop_ge huHi_lt_vTop

end EvmAsm.Evm64
