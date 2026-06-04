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

/-- COPY-family dynamic word gas. The dispatch loop already charges each
    opcode's static base cost; this charges only
    `3 * ceil32(length) / 32` against `env.gasRemaining`.

    This helper preserves `lengthReg`, so callers can load the size once and
    then call `updateActiveMemorySizeAsm` for the destination range. It treats
    low-limb `length + 31` wraparound as OOG, matching memory-expansion style
    failures for ranges too large for this u64-addressed runtime. -/
def copyWordGasAsm (tag lengthReg roundedReg wordsReg gasReg : String) : String :=
  "  beqz " ++ lengthReg ++ ", .Lcopygas_" ++ tag ++ "_done\n" ++
  "  addi " ++ roundedReg ++ ", " ++ lengthReg ++ ", 31\n" ++
  "  bltu " ++ roundedReg ++ ", " ++ lengthReg ++ ", .exit_outofgas\n" ++
  "  srli " ++ wordsReg ++ ", " ++ roundedReg ++ ", 5\n" ++
  "  slli " ++ gasReg ++ ", " ++ wordsReg ++ ", 1\n" ++
  "  add " ++ gasReg ++ ", " ++ gasReg ++ ", " ++ wordsReg ++ "\n" ++
  "  ld " ++ roundedReg ++ ", 568(x20)\n" ++
  "  bltu " ++ roundedReg ++ ", " ++ gasReg ++ ", .exit_outofgas\n" ++
  "  sub " ++ roundedReg ++ ", " ++ roundedReg ++ ", " ++ gasReg ++ "\n" ++
  "  sd " ++ roundedReg ++ ", 568(x20)\n" ++
  ".Lcopygas_" ++ tag ++ "_done:\n"

end EvmAsm.Codegen
