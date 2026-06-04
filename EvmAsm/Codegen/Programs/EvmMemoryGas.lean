/-
  EvmAsm.Codegen.Programs.EvmMemoryGas

  Runtime active-memory high-water tracking and EVM memory-expansion gas
  (M31). Extracted from Programs/Evm.lean so the main opcode registry stays
  under the file-size guardrail.

  The high-water mark (in bytes, a multiple of 32) lives at
  `env + activeMemorySizeOff`; `MSIZE` reads it. Memory-expansion gas (per
  `execution-specs/.../vm/gas.py` `calculate_memory_gas_cost`) is
  `cost(w) = GAS_MEMORY·w + ⌊w²/512⌋` with `GAS_MEMORY = 3` and `w` = 32-byte
  words; an access that grows the mark from `old` to `new` words is charged
  `cost(new) − cost(old)` (each `cost` floored independently).
-/

namespace EvmAsm.Codegen

/-- Dispatcher env offset (bytes) of the runtime active-memory high-water
    mark. `MSIZE` reads it; memory handlers update it. (Mirrors
    `mcopyActiveMemorySizeOff` in `EvmMcopyGas.lean`.) -/
def activeMemorySizeOff : Nat := 488

/-- Inline asm that updates the runtime `MSIZE` high-water mark from one
    memory access `(offset, length)` (low u64 limbs) and — when
    `chargeGas` is true — charges the EVM memory-expansion gas for any
    growth against `env.gasRemaining` (`env+568`, the M30 cell).

    `chargeGas = false` is for callers that have already charged their own
    memory gas (MCOPY, via `mcopyDynamicGasAsm`) and only need the size
    bookkeeping; passing `true` would double-charge them.

    If `length = 0` the EVM never expands memory, so the whole block is
    skipped. If the access does not grow the mark (`current ≥ rounded`),
    no gas is charged. A `mulhu` guard sends `w ≥ 2^32` (≈128 GiB,
    astronomically expensive) straight to `.exit_outofgas` rather than
    letting `w²` wrap mod 2^64; gas underflow likewise routes there
    (`halt_kind = 6`).

    Register use: `offsetReg` and `roundedReg` are preserved across the
    block; `lengthReg` is preserved (so MCOPY can keep the copy length in
    it across two calls); `maskReg`, `currentReg`, and `gasTmpReg` are
    clobbered as scratch. -/
def updateActiveMemorySizeAsm
    (tag offsetReg lengthReg roundedReg currentReg maskReg gasTmpReg : String)
    (chargeGas : Bool) : String :=
  "  beqz " ++ lengthReg ++ ", .Lmemsize_" ++ tag ++ "_done\n" ++
  "  add " ++ roundedReg ++ ", " ++ offsetReg ++ ", " ++ lengthReg ++ "\n" ++
  "  addi " ++ roundedReg ++ ", " ++ roundedReg ++ ", 31\n" ++
  "  li " ++ maskReg ++ ", -32\n" ++
  "  and " ++ roundedReg ++ ", " ++ roundedReg ++ ", " ++ maskReg ++ "\n" ++
  "  ld " ++ currentReg ++ ", " ++ toString activeMemorySizeOff ++ "(x20)\n" ++
  "  bgeu " ++ currentReg ++ ", " ++ roundedReg ++ ", .Lmemsize_" ++ tag ++ "_done\n" ++
  (if chargeGas then
    -- M31 expansion gas: charge cost(new_words) − cost(old_words). Temps:
    -- maskReg = words; gasTmpReg = new_cost then delta; currentReg → old_cost.
    "  srli " ++ maskReg ++ ", " ++ roundedReg ++ ", 5\n" ++            -- M = new words
    "  mulhu " ++ gasTmpReg ++ ", " ++ maskReg ++ ", " ++ maskReg ++ "\n" ++
    "  bnez " ++ gasTmpReg ++ ", .exit_outofgas\n" ++                   -- w² ≥ 2^64 ⇒ OOG
    "  mul " ++ gasTmpReg ++ ", " ++ maskReg ++ ", " ++ maskReg ++ "\n" ++
    "  srli " ++ gasTmpReg ++ ", " ++ gasTmpReg ++ ", 9\n" ++           -- T = ⌊nw²/512⌋
    "  add " ++ gasTmpReg ++ ", " ++ gasTmpReg ++ ", " ++ maskReg ++ "\n" ++
    "  add " ++ gasTmpReg ++ ", " ++ gasTmpReg ++ ", " ++ maskReg ++ "\n" ++
    "  add " ++ gasTmpReg ++ ", " ++ gasTmpReg ++ ", " ++ maskReg ++ "\n" ++ -- T = new_cost
    "  srli " ++ maskReg ++ ", " ++ currentReg ++ ", 5\n" ++            -- M = old words
    "  mul " ++ currentReg ++ ", " ++ maskReg ++ ", " ++ maskReg ++ "\n" ++
    "  srli " ++ currentReg ++ ", " ++ currentReg ++ ", 9\n" ++         -- C = ⌊ow²/512⌋
    "  add " ++ currentReg ++ ", " ++ currentReg ++ ", " ++ maskReg ++ "\n" ++
    "  add " ++ currentReg ++ ", " ++ currentReg ++ ", " ++ maskReg ++ "\n" ++
    "  add " ++ currentReg ++ ", " ++ currentReg ++ ", " ++ maskReg ++ "\n" ++ -- C = old_cost
    "  sub " ++ gasTmpReg ++ ", " ++ gasTmpReg ++ ", " ++ currentReg ++ "\n" ++ -- T = delta
    "  ld " ++ maskReg ++ ", 568(x20)\n" ++                             -- M = gas remaining
    "  bltu " ++ maskReg ++ ", " ++ gasTmpReg ++ ", .exit_outofgas\n" ++
    "  sub " ++ maskReg ++ ", " ++ maskReg ++ ", " ++ gasTmpReg ++ "\n" ++
    "  sd " ++ maskReg ++ ", 568(x20)\n"
   else "") ++
  "  sd " ++ roundedReg ++ ", " ++ toString activeMemorySizeOff ++ "(x20)\n" ++
  ".Lmemsize_" ++ tag ++ "_done:\n"

/-- `updateActiveMemorySizeAsm` for a constant access length (MLOAD/MSTORE =
    32, MSTORE8 = 1). Materializes the length into `tmpLengthReg` first. -/
def updateActiveMemorySizeConstAsm
    (tag offsetReg tmpLengthReg roundedReg currentReg maskReg gasTmpReg : String)
    (chargeGas : Bool) (length : Nat) : String :=
  "  li " ++ tmpLengthReg ++ ", " ++ toString length ++ "\n" ++
  updateActiveMemorySizeAsm tag offsetReg tmpLengthReg roundedReg currentReg maskReg gasTmpReg chargeGas

/-- EXP dynamic gas add-on before exponentiation. The dispatch loop already
    charges the fixed EXP base cost (10), so this charges only
    `50 * exponentByteLength(exponent)`.

    Stack layout before EXP body: `base` at 0(x12), `exponent` at 32(x12).
    EVM words are stored little-endian as four u64 limbs; the byte length is
    therefore the highest non-zero limb index times 8 plus that limb's own
    non-zero byte length. Scratch registers x5/x6/x7 are clobbered. -/
def expDynamicGasAsm : String :=
  "  li x6, 0\n" ++
  "  ld x5, 56(x12)\n" ++
  "  bnez x5, .Lexp_gas_limb3\n" ++
  "  ld x5, 48(x12)\n" ++
  "  bnez x5, .Lexp_gas_limb2\n" ++
  "  ld x5, 40(x12)\n" ++
  "  bnez x5, .Lexp_gas_limb1\n" ++
  "  ld x5, 32(x12)\n" ++
  "  beqz x5, .Lexp_gas_charge\n" ++
  "  j .Lexp_gas_count_limb\n" ++
  ".Lexp_gas_limb1:\n" ++
  "  li x6, 8\n" ++
  "  j .Lexp_gas_count_limb\n" ++
  ".Lexp_gas_limb2:\n" ++
  "  li x6, 16\n" ++
  "  j .Lexp_gas_count_limb\n" ++
  ".Lexp_gas_limb3:\n" ++
  "  li x6, 24\n" ++
  ".Lexp_gas_count_limb:\n" ++
  "  addi x6, x6, 1\n" ++
  "  srli x5, x5, 8\n" ++
  "  bnez x5, .Lexp_gas_count_limb\n" ++
  ".Lexp_gas_charge:\n" ++
  "  li x7, 50\n" ++
  "  mul x6, x6, x7\n" ++
  "  ld x5, 568(x20)\n" ++
  "  bltu x5, x6, .exit_outofgas\n" ++
  "  sub x5, x5, x6\n" ++
  "  sd x5, 568(x20)\n"

end EvmAsm.Codegen
