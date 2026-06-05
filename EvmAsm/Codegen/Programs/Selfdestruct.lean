/-
  EvmAsm.Codegen.Programs.Selfdestruct

  SELFDESTRUCT runtime assembly helpers split out of `Programs.Noop` to keep
  the halt-handler module under the file-size guardrail.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmAccessGas

namespace EvmAsm.Codegen

def selfdestructNewAccountSurchargeAsm : String :=
  "  ld t0, 584(x20)\n" ++
  "  beqz t0, .L_selfdestruct_surcharge_done\n" ++
  "  la t1, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
  runtimeAccessWordToBe20Asm "selfdestruct_origin" "x20" "t1" "t2" "t3" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  ld a0, 576(x20)\n" ++
  "  ld a1, 584(x20)\n" ++
  "  la a2, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
  "  ld a3, 592(x20)\n" ++
  "  ld a4, 600(x20)\n" ++
  "  la a5, bal_output_scratch\n" ++
  "  jal ra, balance_at_header_state_root\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  bnez a0, .L_selfdestruct_surcharge_done\n" ++
  "  la t0, bal_output_scratch\n" ++
  "  ld t1, 0(t0)\n" ++
  "  bnez t1, .L_selfdestruct_origin_nonzero\n" ++
  "  ld t1, 8(t0)\n" ++
  "  bnez t1, .L_selfdestruct_origin_nonzero\n" ++
  "  ld t1, 16(t0)\n" ++
  "  bnez t1, .L_selfdestruct_origin_nonzero\n" ++
  "  ld t1, 24(t0)\n" ++
  "  beqz t1, .L_selfdestruct_surcharge_done\n" ++
  ".L_selfdestruct_origin_nonzero:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  ld a0, 576(x20)\n" ++
  "  ld a1, 584(x20)\n" ++
  "  la a2, evm_selfdestruct_beneficiary\n" ++
  "  ld a3, 592(x20)\n" ++
  "  ld a4, 600(x20)\n" ++
  "  jal ra, account_exists_at_header_state_root\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  bnez a0, .L_selfdestruct_surcharge_done\n" ++
  "  la t0, aex_predicate\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beqz t1, .L_selfdestruct_charge_new_account\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  ld a0, 576(x20)\n" ++
  "  ld a1, 584(x20)\n" ++
  "  la a2, evm_selfdestruct_beneficiary\n" ++
  "  ld a3, 592(x20)\n" ++
  "  ld a4, 600(x20)\n" ++
  "  jal ra, account_is_empty_at_header_state_root\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  bnez a0, .L_selfdestruct_surcharge_done\n" ++
  "  la t0, aie_predicate\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beqz t1, .L_selfdestruct_surcharge_done\n" ++
  ".L_selfdestruct_charge_new_account:\n" ++
  "  ld t0, 568(x20)\n" ++
  "  li t1, 25000\n" ++
  "  bltu t0, t1, .exit_outofgas\n" ++
  "  sub t0, t0, t1\n" ++
  "  sd t0, 568(x20)\n" ++
  ".L_selfdestruct_surcharge_done:\n"

end EvmAsm.Codegen
