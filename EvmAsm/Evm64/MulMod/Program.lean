/-
  EvmAsm.Evm64.MulMod.Program

  MULMOD opcode (`MULMOD(a, b, N)` = (a * b) mod N under EVM
  rules, with `N = 0` returning `0`) as a 64-bit RISC-V program.

  This file currently carries the product-layout foundation for the
  eventual total `evm_mulmod`: a straight-line 4x4 schoolbook product
  block that leaves both halves of the 512-bit product addressable.
  Later slices add the reduction-by-N pipeline, top-level assembly,
  stack spec, and dispatcher wiring.
-/

import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.Program
import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Product layout
-- ============================================================================

/-- Low half of the full `a * b` product lives at `sp + 96 .. sp + 120`.
    The stack input itself stays untouched:

      * `sp + 0  .. sp + 24`: `a`
      * `sp + 32 .. sp + 56`: `b`
      * `sp + 64 .. sp + 88`: `N`
      * `sp + 96 .. sp + 120`: product low half `pL`
      * `sp + 128.. sp + 152`: product high half `pH`

    All slots are 8-byte aligned and remain within positive 12-bit LD/SD
    offsets from `x12`. -/
def mulmodProductLowBase : BitVec 12 := 96

/-- High half of the full `a * b` product. See `mulmodProductLowBase`. -/
def mulmodProductHighBase : BitVec 12 := 128

/-- All eight product-limb offsets, low half first then high half. -/
def mulmodProductOffsets : List (BitVec 12) :=
  [96, 104, 112, 120, 128, 136, 144, 152]

/-- Zero the product window before accumulating partial products. -/
def evm_mulmod_product_zero : Program :=
  SD .x12 .x0 96 ;;
  SD .x12 .x0 104 ;;
  SD .x12 .x0 112 ;;
  SD .x12 .x0 120 ;;
  SD .x12 .x0 128 ;;
  SD .x12 .x0 136 ;;
  SD .x12 .x0 144 ;;
  SD .x12 .x0 152

/-- Propagate the carry in `x10` through product result limbs.

    Each step adds the carry to one limb, stores the updated limb, and
    leaves the next carry in `x10`. Running this with `x10 = 0` is harmless,
    which keeps the per-partial-product shape straight-line. -/
def evm_mulmod_product_propagate_carry : List (BitVec 12) → Program
  | [] => []
  | off :: rest =>
      LD .x9 .x12 off ;;
      ADD .x9 .x9 .x10 ;;
      SLTU .x10 .x9 .x10 ;;
      SD .x12 .x9 off ;;
      evm_mulmod_product_propagate_carry rest

/-- Add one 64x64 partial product into the 512-bit result window.

    `aOff` and `bOff` select input limbs. `loOff` is product limb `i+j`;
    `hiOff` is product limb `i+j+1`; `carryOffsets` are the remaining
    higher limbs. The sequence computes `lo = MUL(a_i,b_j)` and
    `hi = MULHU(a_i,b_j)`, adds `lo` into `loOff`, adds `hi` plus the
    low-limb carry into `hiOff`, and then propagates any carry through
    `carryOffsets`. -/
def evm_mulmod_product_add_partial
    (aOff bOff loOff hiOff : BitVec 12) (carryOffsets : List (BitVec 12)) : Program :=
  LD .x5 .x12 aOff ;;
  LD .x6 .x12 bOff ;;
  single (.MUL .x7 .x5 .x6) ;;
  single (.MULHU .x8 .x5 .x6) ;;
  LD .x9 .x12 loOff ;;
  ADD .x9 .x9 .x7 ;;
  SLTU .x10 .x9 .x7 ;;
  SD .x12 .x9 loOff ;;
  LD .x9 .x12 hiOff ;;
  ADD .x11 .x9 .x8 ;;
  SLTU .x13 .x11 .x8 ;;
  ADD .x11 .x11 .x10 ;;
  SLTU .x14 .x11 .x10 ;;
  OR' .x10 .x13 .x14 ;;
  SD .x12 .x11 hiOff ;;
  evm_mulmod_product_propagate_carry carryOffsets

/-- Full 4x4 schoolbook product layout for MULMOD.

    Entry stack: `[a, b, N, ...]` at `x12 + 0`, `x12 + 32`, `x12 + 64`.
    Exit: `x12` and the input cells are unchanged; the 512-bit product is
    available as eight little-endian limbs at `mulmodProductOffsets`.
    The first four limbs are `pL`; the last four limbs are `pH`. -/
def evm_mulmod_product_layout : Program :=
  evm_mulmod_product_zero ;;
  evm_mulmod_product_add_partial 0 32 96 104 [112, 120, 128, 136, 144, 152] ;;
  evm_mulmod_product_add_partial 8 32 104 112 [120, 128, 136, 144, 152] ;;
  evm_mulmod_product_add_partial 0 40 104 112 [120, 128, 136, 144, 152] ;;
  evm_mulmod_product_add_partial 16 32 112 120 [128, 136, 144, 152] ;;
  evm_mulmod_product_add_partial 8 40 112 120 [128, 136, 144, 152] ;;
  evm_mulmod_product_add_partial 0 48 112 120 [128, 136, 144, 152] ;;
  evm_mulmod_product_add_partial 24 32 120 128 [136, 144, 152] ;;
  evm_mulmod_product_add_partial 16 40 120 128 [136, 144, 152] ;;
  evm_mulmod_product_add_partial 8 48 120 128 [136, 144, 152] ;;
  evm_mulmod_product_add_partial 0 56 120 128 [136, 144, 152] ;;
  evm_mulmod_product_add_partial 24 40 128 136 [144, 152] ;;
  evm_mulmod_product_add_partial 16 48 128 136 [144, 152] ;;
  evm_mulmod_product_add_partial 8 56 128 136 [144, 152] ;;
  evm_mulmod_product_add_partial 24 48 136 144 [152] ;;
  evm_mulmod_product_add_partial 16 56 136 144 [152] ;;
  evm_mulmod_product_add_partial 24 56 144 152 []

theorem evm_mulmod_product_zero_length :
    evm_mulmod_product_zero.length = 8 := by decide

theorem evm_mulmod_product_zero_byte_length :
    4 * evm_mulmod_product_zero.length = 32 := by
  rw [evm_mulmod_product_zero_length]

theorem evm_mulmod_product_layout_length :
    evm_mulmod_product_layout.length = 440 := by native_decide

theorem evm_mulmod_product_layout_byte_length :
    4 * evm_mulmod_product_layout.length = 1760 := by
  rw [evm_mulmod_product_layout_length]

-- ============================================================================
-- Reduction helper blocks
-- ============================================================================

/-- Scratch dividend base for 256-bit `evm_mod_callable` calls used by the
    MULMOD reduction pipeline. The original stack and product layout stay at:

      * `sp + 0  .. sp + 24`: input `a`
      * `sp + 32 .. sp + 56`: input `b`
      * `sp + 64 .. sp + 88`: modulus `N`
      * `sp + 96 .. sp + 120`: product low half `pL`
      * `sp + 128.. sp + 152`: product high half `pH`

    The reduction work window starts after `pH`:

      * `sp + 160.. sp + 184`: callable MOD dividend
      * `sp + 192.. sp + 216`: callable MOD divisor, then MOD remainder

    `evm_mod_callable` is entered with `x12 = sp + 160`; it returns with
    `x12 = sp + 192` and the remainder in `sp + 192..216`. The caller then
    restores `x12` back to the original `sp`. -/
def mulmodReductionWorkDividendBase : BitVec 12 := 160

/-- Scratch divisor / result base for MULMOD reduction helper calls. -/
def mulmodReductionWorkModulusBase : BitVec 12 := 192

/-- Phase 2 -- short-circuit test for `N = 0`.

    On entry, `x12 = sp` and `N` is still the third input stack cell at
    `sp + 64..88`. OR-fold the four limbs into `x6`; if all are zero, branch
    to the zero-result path. The branch byte distance is a parameter so the
    later top-level `evm_mulmod` assembly can pin the concrete layout.

    8 instructions. -/
def evm_mulmod_reduce_n_zero_test (zeroPathOff : BitVec 13) : Program :=
  LD .x6 .x12 64 ;;
  LD .x5 .x12 72 ;;
  OR' .x6 .x6 .x5 ;;
  LD .x5 .x12 80 ;;
  OR' .x6 .x6 .x5 ;;
  LD .x5 .x12 88 ;;
  OR' .x6 .x6 .x5 ;;
  single (.BEQ .x6 .x0 zeroPathOff)

theorem evm_mulmod_reduce_n_zero_test_length (zeroPathOff : BitVec 13) :
    (evm_mulmod_reduce_n_zero_test zeroPathOff).length = 8 := by
  revert zeroPathOff
  decide

theorem evm_mulmod_reduce_n_zero_test_byte_length (zeroPathOff : BitVec 13) :
    4 * (evm_mulmod_reduce_n_zero_test zeroPathOff).length = 32 := by
  rw [evm_mulmod_reduce_n_zero_test_length]

/-- Prepare the shared 256-bit MOD work window.

    Copies a four-limb dividend from `src + 0..24` and the original modulus
    `N` from `sp + 64..88` into the callable work slots:

      * `sp + 160..184`: dividend
      * `sp + 192..216`: divisor `N`

    The block does not change `x12`; it only prepares memory. The later
    call block temporarily moves `x12` to `sp + 160` for `evm_mod_callable`.

    16 instructions. -/
def evm_mulmod_reduce_prepare_mod_args (src : BitVec 12) : Program :=
  LD .x5 .x12 src ;;
  SD .x12 .x5 160 ;;
  LD .x5 .x12 (src + 8) ;;
  SD .x12 .x5 168 ;;
  LD .x5 .x12 (src + 16) ;;
  SD .x12 .x5 176 ;;
  LD .x5 .x12 (src + 24) ;;
  SD .x12 .x5 184 ;;
  LD .x5 .x12 64 ;;
  SD .x12 .x5 192 ;;
  LD .x5 .x12 72 ;;
  SD .x12 .x5 200 ;;
  LD .x5 .x12 80 ;;
  SD .x12 .x5 208 ;;
  LD .x5 .x12 88 ;;
  SD .x12 .x5 216

theorem evm_mulmod_reduce_prepare_mod_args_length (src : BitVec 12) :
    (evm_mulmod_reduce_prepare_mod_args src).length = 16 := by
  revert src
  decide

theorem evm_mulmod_reduce_prepare_mod_args_byte_length (src : BitVec 12) :
    4 * (evm_mulmod_reduce_prepare_mod_args src).length = 64 := by
  rw [evm_mulmod_reduce_prepare_mod_args_length]

/-- Call `evm_mod_callable` on the prepared work window.

    Precondition: `evm_mulmod_reduce_prepare_mod_args` has copied a dividend
    into `sp + 160..184` and `N` into `sp + 192..216`. This block shifts
    `x12` to `sp + 160`, performs a near call to the callable MOD routine, and
    restores `x12` to the original `sp`. Since callable MOD returns with
    `x12 = sp + 192`, the restore is `ADDI x12, x12, -192`, encoded as the
    12-bit immediate `3904`.

    The MOD remainder is left in `sp + 192..216`.

    3 instructions. -/
def evm_mulmod_reduce_call_mod (modOff : BitVec 21) : Program :=
  ADDI .x12 .x12 160 ;;
  JAL .x1 modOff ;;
  ADDI .x12 .x12 3904

theorem evm_mulmod_reduce_call_mod_length (modOff : BitVec 21) :
    (evm_mulmod_reduce_call_mod modOff).length = 3 := by
  show (((ADDI .x12 .x12 160 ;; JAL .x1 modOff) ;;
          ADDI .x12 .x12 3904) : Program).length = 3
  simp only [seq, Program.length_append]
  rfl

theorem evm_mulmod_reduce_call_mod_byte_length (modOff : BitVec 21) :
    4 * (evm_mulmod_reduce_call_mod modOff).length = 12 := by
  rw [evm_mulmod_reduce_call_mod_length]

/-- Reduce the high half of the product, `pH mod N`.

    Entry contract from `evm_mulmod_product_layout`: `pH` is at
    `sp + 128..152`, `N` is at `sp + 64..88`, and `x12 = sp`. Exit:
    `x12 = sp`; `sp + 192..216` contains `pH mod N` as returned by
    `evm_mod_callable`.

    19 instructions. -/
def evm_mulmod_reduce_high_half (modOff : BitVec 21) : Program :=
  evm_mulmod_reduce_prepare_mod_args mulmodProductHighBase ;;
  evm_mulmod_reduce_call_mod modOff

theorem evm_mulmod_reduce_high_half_length (modOff : BitVec 21) :
    (evm_mulmod_reduce_high_half modOff).length = 19 := by
  unfold evm_mulmod_reduce_high_half
  simp only [seq, Program.length_append,
    evm_mulmod_reduce_prepare_mod_args_length, evm_mulmod_reduce_call_mod_length]

theorem evm_mulmod_reduce_high_half_byte_length (modOff : BitVec 21) :
    4 * (evm_mulmod_reduce_high_half modOff).length = 76 := by
  rw [evm_mulmod_reduce_high_half_length]

/-- Reduce the low half of the product, `pL mod N`.

    Entry contract from `evm_mulmod_product_layout`: `pL` is at
    `sp + 96..120`, `N` is at `sp + 64..88`, and `x12 = sp`. Exit:
    `x12 = sp`; `sp + 192..216` contains `pL mod N` as returned by
    `evm_mod_callable`.

    19 instructions. -/
def evm_mulmod_reduce_low_half (modOff : BitVec 21) : Program :=
  evm_mulmod_reduce_prepare_mod_args mulmodProductLowBase ;;
  evm_mulmod_reduce_call_mod modOff

theorem evm_mulmod_reduce_low_half_length (modOff : BitVec 21) :
    (evm_mulmod_reduce_low_half modOff).length = 19 := by
  unfold evm_mulmod_reduce_low_half
  simp only [seq, Program.length_append,
    evm_mulmod_reduce_prepare_mod_args_length, evm_mulmod_reduce_call_mod_length]

theorem evm_mulmod_reduce_low_half_byte_length (modOff : BitVec 21) :
    4 * (evm_mulmod_reduce_low_half modOff).length = 76 := by
  rw [evm_mulmod_reduce_low_half_length]

/-- Zero-result path for `N = 0`.

    MULMOD pops `[a, b, N]` and pushes one result, so the final result slot is
    the original `sp + 64..88` after the epilogue advances `x12` by 64. This
    block writes the four zero limbs there and leaves pointer movement to
    `evm_mulmod_epilogue`.

    4 instructions. -/
def evm_mulmod_reduce_zero_path : Program :=
  SD .x12 .x0 64 ;;
  SD .x12 .x0 72 ;;
  SD .x12 .x0 80 ;;
  SD .x12 .x0 88

theorem evm_mulmod_reduce_zero_path_length :
    evm_mulmod_reduce_zero_path.length = 4 := by native_decide

theorem evm_mulmod_reduce_zero_path_byte_length :
    4 * evm_mulmod_reduce_zero_path.length = 16 := by
  rw [evm_mulmod_reduce_zero_path_length]

/-- MULMOD epilogue: advance the EVM stack pointer after the result has been
    placed at the original `sp + 64..88`. -/
def evm_mulmod_epilogue : Program :=
  ADDI .x12 .x12 64

theorem evm_mulmod_epilogue_length :
    evm_mulmod_epilogue.length = 1 := by native_decide

theorem evm_mulmod_epilogue_byte_length :
    4 * evm_mulmod_epilogue.length = 4 := by
  rw [evm_mulmod_epilogue_length]

-- ============================================================================
-- Concrete execution checks for the layout slice
-- ============================================================================

/-- Create a test state for the product-layout block with `a`, `b`, and `N`
    in the eventual MULMOD stack order. -/
def mkMulModProductLayoutTestState (sp : Word)
    (a0 a1 a2 a3 : Word)
    (b0 b1 b2 b3 : Word)
    (n0 n1 n2 n3 : Word) : MachineState where
  regs := fun r =>
    match r with
    | .x12 => sp
    | _    => 0
  mem := fun a =>
    if a == sp then a0
    else if a == sp + 8 then a1
    else if a == sp + 16 then a2
    else if a == sp + 24 then a3
    else if a == sp + 32 then b0
    else if a == sp + 40 then b1
    else if a == sp + 48 then b2
    else if a == sp + 56 then b3
    else if a == sp + 64 then n0
    else if a == sp + 72 then n1
    else if a == sp + 80 then n2
    else if a == sp + 88 then n3
    else 0
  code := loadProgram 0 evm_mulmod_product_layout
  pc := 0

/-- Run the product-layout block and extract `(x12, N limbs, pL limbs, pH limbs)`. -/
def runMulModProductLayout (sp : Word)
    (a0 a1 a2 a3 : Word)
    (b0 b1 b2 b3 : Word)
    (n0 n1 n2 n3 : Word)
    (steps : Nat) : Option (Word × List Word × List Word × List Word) :=
  let s := mkMulModProductLayoutTestState sp a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3
  match stepN steps s with
  | some s' =>
      some (s'.getReg .x12,
        [s'.getMem (sp + 64), s'.getMem (sp + 72), s'.getMem (sp + 80), s'.getMem (sp + 88)],
        [s'.getMem (sp + 96), s'.getMem (sp + 104), s'.getMem (sp + 112), s'.getMem (sp + 120)],
        [s'.getMem (sp + 128), s'.getMem (sp + 136), s'.getMem (sp + 144), s'.getMem (sp + 152)])
  | none => none

/-- Zero product leaves both halves zero and preserves `N`. -/
example : runMulModProductLayout 1024
    0 0 0 0
    0 0 0 0
    7 0 0 0
    440 = some (1024, [7, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]) := by native_decide

/-- Small product: 2 * 3 = 6, high half zero. -/
example : runMulModProductLayout 1024
    2 0 0 0
    3 0 0 0
    5 0 0 0
    440 = some (1024, [5, 0, 0, 0], [6, 0, 0, 0], [0, 0, 0, 0]) := by native_decide

/-- High-half-producing product: 2^192 * 2^64 = 2^256. -/
example : runMulModProductLayout 1024
    0 0 0 1
    0 1 0 0
    11 0 0 0
    440 = some (1024, [11, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]) := by native_decide

/-- Carry-heavy product: `(2^256 - 1)^2 = 1 + (2^256 - 2) * 2^256`. -/
example : runMulModProductLayout 1024
    0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF
    0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF
    13 0 0 0
    440 = some (1024, [13, 0, 0, 0],
      [1, 0, 0, 0],
      [0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF]) := by native_decide

end EvmAsm.Evm64
