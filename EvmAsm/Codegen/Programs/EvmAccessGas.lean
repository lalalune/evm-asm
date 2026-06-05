/-
  EvmAsm.Codegen.Programs.EvmAccessGas

  Shared runtime account-access gas helper for EIP-2929 warm/cold account
  costs. Consumers pass a bounded 32-byte-stride table of 20-byte canonical
  big-endian addresses. The dispatcher static gas table already charges the
  100-gas warm floor for account opcodes, so this helper charges only the
  2500-gas cold delta and records newly cold addresses.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

def runtimeAccessAccountCapacity : Nat := 64
def runtimeAccessAccountRecordSize : Nat := 32
def runtimeAccessColdDeltaGas : Nat := 2500

/-! ## runtime_access_account_charge

    Calling convention:
      a0 (input)  : address ptr (20 bytes, canonical BE)
      a1 (input)  : table ptr (capacity * 32 bytes)
      a2 (input)  : count ptr (u64)
      a3 (input)  : capacity (records)
      x20 (input) : runtime env base; gasRemaining is env+568
      a0 (output) : 0 if warm/precompile, 1 if cold and inserted

    Exceptional paths jump to `.exit_outofgas`:
      - cold access when `gasRemaining < 2500`
      - table is full and the target is not already warm

    Active precompiles are always warm and are not inserted. The active set
    mirrors the runtime precompile dispatcher surface: 0x01..0x11 and 0x100. -/
def runtimeAccessAccountChargeFunction : String :=
  "runtime_access_account_charge:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # address ptr\n" ++
  "  mv s1, a1                   # table ptr\n" ++
  "  mv s2, a2                   # count ptr\n" ++
  "  mv s3, a3                   # capacity\n" ++
  "  # Active precompiles are warm: canonical BE address with first 18 bytes zero\n" ++
  "  li t0, 0\n" ++
  ".Lraag_pc_prefix_loop:\n" ++
  "  li t1, 18\n" ++
  "  beq t0, t1, .Lraag_pc_low16\n" ++
  "  add t2, s0, t0\n" ++
  "  lbu t3, 0(t2)\n" ++
  "  bnez t3, .Lraag_scan_table\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lraag_pc_prefix_loop\n" ++
  ".Lraag_pc_low16:\n" ++
  "  lbu t2, 18(s0)\n" ++
  "  lbu t3, 19(s0)\n" ++
  "  slli t2, t2, 8\n" ++
  "  or t2, t2, t3\n" ++
  "  li t3, 1\n" ++
  "  bltu t2, t3, .Lraag_scan_table\n" ++
  "  li t3, 17\n" ++
  "  bgeu t3, t2, .Lraag_warm\n" ++
  "  li t3, 256\n" ++
  "  beq t2, t3, .Lraag_warm\n" ++
  ".Lraag_scan_table:\n" ++
  "  ld t6, 0(s2)                # count\n" ++
  "  li t0, 0                    # i\n" ++
  ".Lraag_scan_loop:\n" ++
  "  beq t0, t6, .Lraag_cold\n" ++
  "  slli t1, t0, 5              # i * 32\n" ++
  "  add t1, s1, t1              # record ptr\n" ++
  "  li t2, 0                    # byte index\n" ++
  ".Lraag_cmp_loop:\n" ++
  "  li t3, 20\n" ++
  "  beq t2, t3, .Lraag_warm\n" ++
  "  add t4, s0, t2\n" ++
  "  add t5, t1, t2\n" ++
  "  lbu t4, 0(t4)\n" ++
  "  lbu t5, 0(t5)\n" ++
  "  bne t4, t5, .Lraag_next_record\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lraag_cmp_loop\n" ++
  ".Lraag_next_record:\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lraag_scan_loop\n" ++
  ".Lraag_cold:\n" ++
  "  bgeu t6, s3, .exit_outofgas\n" ++
  "  ld t0, 568(x20)\n" ++
  "  li t1, " ++ toString runtimeAccessColdDeltaGas ++ "\n" ++
  "  bltu t0, t1, .exit_outofgas\n" ++
  "  sub t0, t0, t1\n" ++
  "  sd t0, 568(x20)\n" ++
  "  slli t0, t6, 5\n" ++
  "  add t1, s1, t0\n" ++
  "  li t2, 0\n" ++
  ".Lraag_copy_loop:\n" ++
  "  li t3, 20\n" ++
  "  beq t2, t3, .Lraag_insert_done\n" ++
  "  add t4, s0, t2\n" ++
  "  add t5, t1, t2\n" ++
  "  lbu t4, 0(t4)\n" ++
  "  sb t4, 0(t5)\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lraag_copy_loop\n" ++
  ".Lraag_insert_done:\n" ++
  "  sw zero, 20(t1); sw zero, 24(t1); sw zero, 28(t1)\n" ++
  "  addi t6, t6, 1\n" ++
  "  sd t6, 0(s2)\n" ++
  "  li a0, 1\n" ++
  "  j .Lraag_ret\n" ++
  ".Lraag_warm:\n" ++
  "  li a0, 0\n" ++
  ".Lraag_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_runtime_access_account_gas`: probe BuildUnit.

    Input selector at byte 0:
      0 = success sequence: cold A, warm A, active precompile 0x04.
      1 = under-gas cold access; expects `.exit_outofgas`.

    Success output:
      +0 first status, +8 gas, +16 count, +24 second status, +32 gas,
      +40 count, +48 precompile status, +56 gas, +64 count. -/
def ziskRuntimeAccessAccountGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la x20, rta_env\n" ++
  "  li t0, 0x40000008\n" ++
  "  ld t0, 0(t0)\n" ++
  "  beqz t0, .Lraag_probe_success\n" ++
  "  li t1, 2499\n" ++
  "  sd t1, 568(x20)\n" ++
  "  la a0, rta_addr_b\n" ++
  "  la a1, rta_table\n" ++
  "  la a2, rta_count\n" ++
  "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_charge\n" ++
  "  j .Lraag_probe_done\n" ++
  ".Lraag_probe_success:\n" ++
  "  li t1, 3000\n" ++
  "  sd t1, 568(x20)\n" ++
  "  la t0, rta_count\n" ++
  "  sd zero, 0(t0)\n" ++
  "  la a0, rta_addr_a\n" ++
  "  la a1, rta_table\n" ++
  "  la a2, rta_count\n" ++
  "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_charge\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  ld t1, 568(x20); sd t1, 8(t0)\n" ++
  "  la t2, rta_count; ld t1, 0(t2); sd t1, 16(t0)\n" ++
  "  la a0, rta_addr_a\n" ++
  "  la a1, rta_table\n" ++
  "  la a2, rta_count\n" ++
  "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_charge\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 24(t0)\n" ++
  "  ld t1, 568(x20); sd t1, 32(t0)\n" ++
  "  la t2, rta_count; ld t1, 0(t2); sd t1, 40(t0)\n" ++
  "  la a0, rta_addr_precompile\n" ++
  "  la a1, rta_table\n" ++
  "  la a2, rta_count\n" ++
  "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_charge\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 48(t0)\n" ++
  "  ld t1, 568(x20); sd t1, 56(t0)\n" ++
  "  la t2, rta_count; ld t1, 0(t2); sd t1, 64(t0)\n" ++
  "  j .Lraag_probe_done\n" ++
  runtimeAccessAccountChargeFunction ++ "\n" ++
  ".exit_outofgas:\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  li t1, 6\n" ++
  "  sd t1, 32(t0)\n" ++
  ".Lraag_probe_done:"

def ziskRuntimeAccessAccountGasDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rta_env:\n" ++
  "  .zero 656\n" ++
  ".balign 8\n" ++
  "rta_count:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "rta_table:\n" ++
  "  .zero " ++ toString (runtimeAccessAccountCapacity * runtimeAccessAccountRecordSize) ++ "\n" ++
  "rta_addr_a:\n" ++
  "  .byte 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0xaa,0xbb,0xcc,0xdd\n" ++
  "rta_addr_b:\n" ++
  "  .byte 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x11,0x22,0x33,0x44\n" ++
  "rta_addr_precompile:\n" ++
  "  .byte 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4"

def ziskRuntimeAccessAccountGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRuntimeAccessAccountGasPrologue
  dataAsm     := ziskRuntimeAccessAccountGasDataSection
}

end EvmAsm.Codegen
