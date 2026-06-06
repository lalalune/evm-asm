/-
  EvmAsm.Codegen.Programs.BlockGasRemaining

  EIP-7778 remaining block-gas availability checker. The full block executor
  will eventually feed exact per-transaction `block_gas_used_in_tx` increments
  from gas-metered execution; this helper isolates the execution-spec
  `tx.gas <= block_gas_limit - block_output.block_gas_used` gate.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## eip7778_remaining_block_gas_check

    ABI:
      a0 = block_gas_limit
      a1 = pointer to `count` u64 transaction gas limits
      a2 = pointer to `count` u64 exact block-gas-used increments
      a3 = count

    Returns:
      a0 = status:
        0 ok
        1 transaction gas exceeds currently available block gas
        2 cumulative block-gas-used overflow while applying increments
      a1 = first failing transaction index, 1-based; 0 on success
      a2 = block_gas_used before the failing transaction/increment, or final
           block_gas_used on success.

    The check mirrors execution-specs Amsterdam `check_transaction`:
      gas_available = block_env.block_gas_limit - block_output.block_gas_used
      if tx.gas > gas_available: raise GasUsedExceedsLimitError

    The helper intentionally takes block-gas-used increments as input rather
    than deriving them from tx gas limits. EIP-7778 increments
    `block_output.block_gas_used` by max(gas used before refund, calldata
    floor), which only a gas-metered execution slice can compute exactly. -/
def eip7778RemainingBlockGasCheckFunction : String :=
  "eip7778_remaining_block_gas_check:\n" ++
  "  mv t0, a0                   # block_gas_limit\n" ++
  "  mv t1, a1                   # tx_gas ptr\n" ++
  "  mv t2, a2                   # block_gas_used_in_tx ptr\n" ++
  "  mv t3, a3                   # count\n" ++
  "  li t4, 0                    # i\n" ++
  "  li t5, 0                    # block_gas_used\n" ++
  ".Le7778_loop:\n" ++
  "  beq t4, t3, .Le7778_ok\n" ++
  "  bltu t0, t5, .Le7778_tx_fail\n" ++
  "  slli t6, t4, 3\n" ++
  "  add a4, t1, t6\n" ++
  "  ld a5, 0(a4)                # tx.gas\n" ++
  "  sub a6, t0, t5              # gas_available\n" ++
  "  bgtu a5, a6, .Le7778_tx_fail\n" ++
  "  add a4, t2, t6\n" ++
  "  ld a5, 0(a4)                # exact block_gas_used_in_tx\n" ++
  "  add a6, t5, a5\n" ++
  "  bltu a6, t5, .Le7778_overflow\n" ++
  "  mv t5, a6\n" ++
  "  addi t4, t4, 1\n" ++
  "  j .Le7778_loop\n" ++
  ".Le7778_tx_fail:\n" ++
  "  li a0, 1\n" ++
  "  addi a1, t4, 1\n" ++
  "  mv a2, t5\n" ++
  "  ret\n" ++
  ".Le7778_overflow:\n" ++
  "  li a0, 2\n" ++
  "  addi a1, t4, 1\n" ++
  "  mv a2, t5\n" ++
  "  ret\n" ++
  ".Le7778_ok:\n" ++
  "  li a0, 0\n" ++
  "  li a1, 0\n" ++
  "  mv a2, t5\n" ++
  "  ret"

/-- `zisk_eip7778_remaining_block_gas_check`: focused zisk probe.
    Host input payload after the zisk length prefix:
      +0  block_gas_limit u64
      +8  count u64
      +16 count u64 tx.gas entries
      then count u64 exact block_gas_used_in_tx entries

    Output:
      +0  status
      +8  failing tx index, 1-based
      +16 block_gas_used before failure, or final block_gas_used. -/
def ziskEip7778RemainingBlockGasCheckPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  li s1, 0xa0010000\n" ++
  "  ld a0, 8(s0)                # block_gas_limit\n" ++
  "  ld a3, 16(s0)               # count\n" ++
  "  addi a1, s0, 24             # tx_gas array\n" ++
  "  slli t0, a3, 3\n" ++
  "  add a2, a1, t0              # block_gas_used_in_tx array\n" ++
  "  jal ra, eip7778_remaining_block_gas_check\n" ++
  "  sd a0, 0(s1)\n" ++
  "  sd a1, 8(s1)\n" ++
  "  sd a2, 16(s1)\n" ++
  "  j .Le7778_probe_done\n" ++
  eip7778RemainingBlockGasCheckFunction ++ "\n" ++
  ".Le7778_probe_done:"

def ziskEip7778RemainingBlockGasCheckProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskEip7778RemainingBlockGasCheckPrologue
  dataAsm     := ".section .data\n.balign 8\n"
}

end EvmAsm.Codegen
