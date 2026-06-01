/-
  EvmAsm.Codegen.Programs.BlockAccessListHash

  block_access_list_hash (bead evm-asm-fhsxz.2.4.2.5): compute the Amsterdam RLP
  header field `block_access_list_hash` (field 21 of 23) = keccak256 of the raw
  `block_access_list` section bytes in the SSZ ExecutionPayload. Verified against
  real zkevm@v0.4.0 fixtures (the fixture blockHeader's blockAccessListHash).

  This is a prerequisite for `block_hash` verification (reconstruct the full
  23-field Amsterdam header and check keccak == payload.block_hash), the
  cornerstone of a SOUND Step-2 verdict that can be wired into the guest without
  false-positive regressions.

  Navigation (all byte-wise; no-misaligned invariant):
    NPR          = SSZ_BASE + 16          (outer.offsets[0] is 16 for this schema)
    exec_payload = NPR + 44               (NPR fixed header)
    bal_off      = u32 @ exec_payload+528 (block_access_list offset, rel exec_payload)
    vh_off       = u32 @ NPR+4            (versioned_hashes offset, rel NPR = payload end)
    bal_start    = exec_payload + bal_off
    bal_end      = NPR + vh_off           (= exec_payload end)
  block_access_list_hash = keccak256(bal_start .. bal_end).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bah_u32le -- read a little-endian u32 byte-wise (a0=ptr -> a0). Leaf. -/
def bahU32leFunction : String :=
  "bah_u32le:\n" ++
  "  lbu t0, 0(a0)\n" ++
  "  lbu t1, 1(a0); slli t1, t1, 8;  or t0, t0, t1\n" ++
  "  lbu t1, 2(a0); slli t1, t1, 16; or t0, t0, t1\n" ++
  "  lbu t1, 3(a0); slli t1, t1, 24; or t0, t0, t1\n" ++
  "  mv a0, t0\n" ++
  "  ret"

/-! ## block_access_list_hash
    a0 = SSZ_BASE ptr   a1 = 32-byte out hash ptr.   a0 (output) = 0. -/
def blockAccessListHashFunction : String :=
  "block_access_list_hash:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # SSZ_BASE\n" ++
  "  mv s1, a1                   # out hash\n" ++
  "  addi s2, s0, 16             # NPR = SSZ_BASE + 16\n" ++
  "  # exec_payload = NPR + 44\n" ++
  "  addi t3, s2, 44             # exec_payload (kept in t3 across the u32 reads;\n" ++
  "                              # bah_u32le clobbers only t0/t1)\n" ++
  "  # bal_off = u32 @ exec_payload+528\n" ++
  "  addi a0, t3, 528; jal ra, bah_u32le\n" ++
  "  addi t3, s2, 44             # re-derive exec_payload (a0-call safe but cheap)\n" ++
  "  add t4, t3, a0              # bal_start = exec_payload + bal_off\n" ++
  "  la t0, bah_bal_start; sd t4, 0(t0)\n" ++
  "  # vh_off = u32 @ NPR+4 ; bal_end = NPR + vh_off\n" ++
  "  addi a0, s2, 4; jal ra, bah_u32le\n" ++
  "  add t5, s2, a0              # bal_end = NPR + vh_off\n" ++
  "  la t0, bah_bal_start; ld t4, 0(t0)\n" ++
  "  sub a1, t5, t4              # bal_len = bal_end - bal_start\n" ++
  "  mv a0, t4                   # bal_start\n" ++
  "  mv a2, s1                   # out hash\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_access_list_hash`: probe. Fed the SAME `-i` input as the guest
    (SSZ_BASE = 0x40000012). Output: OUTPUT+0 = block_access_list_hash (32 B). -/
def ziskBlockAccessListHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a0, 0x40000000; addi a0, a0, 18    # SSZ_BASE\n" ++
  "  li a1, 0xa0010000\n" ++
  "  jal ra, block_access_list_hash\n" ++
  "  j .Lbah_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  bahU32leFunction ++ "\n" ++
  blockAccessListHashFunction ++ "\n" ++
  ".Lbah_pdone:"

def ziskBlockAccessListHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n  .zero 200\n" ++
  ".balign 8\n" ++
  "bah_bal_start:\n  .zero 8"

def ziskBlockAccessListHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockAccessListHashPrologue
  dataAsm     := ziskBlockAccessListHashDataSection
}

end EvmAsm.Codegen
