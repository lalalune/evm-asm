/-
  EvmAsm.Codegen.Programs.SelfdestructDescriptors

  SELFDESTRUCT descriptor builders for post-state-root replay.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Mpt

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## selfdestruct_delete_descriptor

    Build one `mpt_state_root_ins` account-delete descriptor from a canonical
    20-byte account address. This is the descriptor shape needed for EIP-6780
    deletion of contracts created and selfdestructed in the same transaction.

    Calling convention:
      a0 = 20-byte account address ptr
      a1 = descriptor out ptr (40 bytes)
      a2 = path out ptr (64 bytes)

    Descriptor layout:
      +0 path ptr
      +8 path length = 64
      +16 value ptr = 0
      +24 value length = 0
      +32 mode = 2 (delete)

    a0 returns 0. -/
def selfdestructDeleteDescriptorFunction : String :=
  "selfdestruct_delete_descriptor:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  mv s0, a1                   # descriptor out\n" ++
  "  mv s1, a2                   # path out\n" ++
  "  li a1, 20\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, mpt_account_path_nibbles\n" ++
  "  sd s1, 0(s0)\n" ++
  "  li t0, 64\n" ++
  "  sd t0, 8(s0)\n" ++
  "  sd zero, 16(s0)\n" ++
  "  sd zero, 24(s0)\n" ++
  "  li t0, 2\n" ++
  "  sd t0, 32(s0)\n" ++
  "  li a0, 0\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_selfdestruct_delete_descriptor`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  20-byte account address
    Output layout:
      OUTPUT+0    descriptor (40 bytes)
      OUTPUT+40   path (64 nibble bytes)
      OUTPUT+248  status -/
def ziskSelfdestructDeleteDescriptorPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  addi a0, t0, 8              # 20-byte account address\n" ++
  "  li a1, 0xa0010000           # descriptor\n" ++
  "  li a2, 0xa0010028           # path\n" ++
  "  jal ra, selfdestruct_delete_descriptor\n" ++
  "  li t0, 0xa00100f8\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsddd_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  mptAccountPathNibblesFunction ++ "\n" ++
  selfdestructDeleteDescriptorFunction ++ "\n" ++
  ".Lsddd_pdone:"

def ziskSelfdestructDeleteDescriptorProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSelfdestructDeleteDescriptorPrologue
  dataAsm     := ziskMptAccountPathNibblesDataSection
}

end EvmAsm.Codegen
