/-
  EvmAsm.Evm64.DivMod.Spec.N2V5HvSmall

  The n=2 small-divisor fact `2 * val256 v0 v1 0 0 < 2^256` (the `hv_small`
  hypothesis of `mulsubN4_c3_le_one_of_plus_two_of_v_lt` (#7430) /
  `callAddbackCarry2NzV5_of_borrow_n2` (#7431)), from the normalized n=2 divisor
  bound `val256 v0 v1 0 0 < 2^128` (`n2_val256_v_lt_pow128`).
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5RemainderLt

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- For the n=2 (two-limb) divisor, `2 * val256 v0 v1 0 0 < 2^256`. -/
theorem n2_two_val256_v_lt_pow256 (v0 v1 : Word) :
    2 * val256 v0 v1 0 0 < 2 ^ 256 := by
  have h := n2_val256_v_lt_pow128 v0 v1
  have he : (2 : Nat) ^ 256 = 2 * (2 ^ 128 * 2 ^ 127) := by norm_num
  rw [he]
  have hp : 0 < (2 : Nat) ^ 127 := by positivity
  calc 2 * val256 v0 v1 0 0 < 2 * 2 ^ 128 := by omega
    _ ≤ 2 * (2 ^ 128 * 2 ^ 127) := by
        have : (2 : Nat) ^ 128 ≤ 2 ^ 128 * 2 ^ 127 := Nat.le_mul_of_pos_right _ hp
        omega

end EvmAsm.Evm64
