/-
  EvmAsm.Evm64.EvmWordArith.TopWindowVal256Bound

  Word-level multi-limb Knuth Theorem A bound: the 128/64 top-window trial
  quotient over the normalized top divisor limb overestimates the full
  val256 quotient by at most 2.

  This composes the now-proven foundations into the Word-level statement
  that was the open "Knuth-A val256 frontier" for GENERAL (multi-limb)
  divisors (as the `+2` form consumed by the BLT-path
  `loopBodyN{2,3}CallAddbackCarry2Nz*_of_overestimate_c3` bridges):
  - `knuth_theorem_b_abstract` (KnuthTheoremB.lean) — the pure-Nat `+2`.
  - `val256_normalize_dividend` / `val256_normalize_divisor`
    (ShiftOrLimbToNat.lean) — the shift-OR limbs realize `val·2^s`.
  - `val256_split_top_limb` (KnuthTheoremB.lean) — top-limb splits.
  - `val256_div_scale_invariant` (KnuthTheoremB.lean) — cancels `2^s`.

  Bead `evm-asm-wbc4i.8.2.2` (toward `evm_div_stack_spec_unconditional`).
-/

import EvmAsm.Evm64.EvmWordArith.ShiftOrLimbToNat
import EvmAsm.Evm64.EvmWordArith.KnuthTheoremB

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Word-level multi-limb Knuth-A `+2`: for `0 < s < 64`, a normalized
    divisor whose top shift-OR limb `B3' ≥ 2^63` with no overflow
    (`b3/2^(64-s) = 0`), and the call regime `U4 < B3'`, the 128/64
    top-window trial quotient `(U4·2^64 + U3) / B3'` overestimates the full
    `val256 a / val256 b` by at most 2.

    `U4 = a3 >>> (64-s)`, `U3 = (a3 <<< s) ||| (a2 >>> (64-s))`,
    `B3' = (b3 <<< s) ||| (b2 >>> (64-s))` are the standard normalized
    top-window limbs (`s = clz(b3)` in the algorithm). -/
theorem topWindowFloor_le_val256_div_plus_two
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (s : Nat) (hs : 0 < s) (hs64 : s < 64)
    (hb3top : b3.toNat / 2^(64-s) = 0)
    (hbnorm : ((b3 <<< s) ||| (b2 >>> (64-s))).toNat ≥ 2^63)
    (hcall : (a3 >>> (64-s)).toNat < ((b3 <<< s) ||| (b2 >>> (64-s))).toNat) :
    ((a3 >>> (64-s)).toNat * 2^64 + ((a3 <<< s) ||| (a2 >>> (64-s))).toNat)
        / ((b3 <<< s) ||| (b2 >>> (64-s))).toNat
      ≤ EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 + 2 := by
  obtain ⟨urest, hurest_lt, hurest⟩ := val256_split_top_limb
    (a0 <<< s) ((a1 <<< s) ||| (a0 >>> (64-s)))
    ((a2 <<< s) ||| (a1 >>> (64-s))) ((a3 <<< s) ||| (a2 >>> (64-s)))
  obtain ⟨vrest, hvrest_lt, hvrest⟩ := val256_split_top_limb
    (b0 <<< s) ((b1 <<< s) ||| (b0 >>> (64-s)))
    ((b2 <<< s) ||| (b1 >>> (64-s))) ((b3 <<< s) ||| (b2 >>> (64-s)))
  have hdiv := val256_normalize_dividend a0 a1 a2 a3 s hs hs64
  have hdivisor := val256_normalize_divisor b0 b1 b2 b3 s hs hs64 hb3top
  have key := knuth_theorem_b_abstract
    (EvmWord.val256 a0 a1 a2 a3 * 2^s) (EvmWord.val256 b0 b1 b2 b3 * 2^s)
    (a3 >>> (64-s)).toNat ((a3 <<< s) ||| (a2 >>> (64-s))).toNat urest
    ((b3 <<< s) ||| (b2 >>> (64-s))).toNat vrest
    (by rw [← hdiv, hurest]; ring)
    (by rw [← hdivisor, hvrest])
    hvrest_lt hbnorm hcall (((a3 <<< s) ||| (a2 >>> (64-s))).isLt)
  rwa [val256_div_scale_invariant] at key

end EvmAsm.Evm64
