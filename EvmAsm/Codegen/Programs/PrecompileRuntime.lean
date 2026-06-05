/-
  EvmAsm.Codegen.Programs.PrecompileRuntime

  Shared precompile helper builders reused by Noop.lean's child-frame
  handler (`childFrameHandlers`) across multiple precompile entries:
  ECRECOVER fixed-gas and input staging, and general precompile-frame
  window copy helpers added for BN254 / BLS12 / KZG backends.

  Extracted from Noop.lean to keep that file under the 1500-line guard.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

def precompileFrameAddi (dst : String) (off : Nat) : String :=
  "  addi " ++ dst ++ ", x15, " ++ toString off ++ "\n"

private def precompileGasRemainingOff : Nat := 568

def chargePrecompileGasAsm (costReg remainingReg : String) : String :=
  "  ld " ++ remainingReg ++ ", " ++ toString precompileGasRemainingOff ++ "(x20)\n" ++
  "  bltu " ++ remainingReg ++ ", " ++ costReg ++ ", .exit_outofgas\n" ++
  "  sub " ++ remainingReg ++ ", " ++ remainingReg ++ ", " ++ costReg ++ "\n" ++
  "  sd " ++ remainingReg ++ ", " ++ toString precompileGasRemainingOff ++ "(x20)\n"

def chargePrecompileGasConstAsm (cost : Nat)
    (costReg remainingReg : String) : String :=
  "  li " ++ costReg ++ ", " ++ toString cost ++ "\n" ++
  chargePrecompileGasAsm costReg remainingReg

def stageEcrecoverInputAsm
    (inOffsetOff inSizeOff : Nat) : String :=
  "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
  "  ld x18, " ++ toString inOffsetOff ++ "(x12)\n" ++
  "  add x18, x13, x18\n" ++
  precompileFrameAddi "x19" precompileFrameEcrecoverInputOff ++
  "  mv x22, x17\n" ++
  "  li x23, 128\n" ++
  "  bgeu x23, x22, 30f\n" ++
  "  mv x22, x23\n" ++
  "30:\n" ++
  "  mv x24, x22\n" ++
  "  beqz x24, 32f\n" ++
  "31:\n" ++
  "  lbu x16, 0(x18)\n" ++
  "  sb x16, 0(x19)\n" ++
  "  addi x18, x18, 1\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x24, x24, -1\n" ++
  "  bnez x24, 31b\n" ++
  "32:\n" ++
  "  sub x24, x23, x22\n" ++
  "  beqz x24, 34f\n" ++
  "33:\n" ++
  "  sb x0, 0(x19)\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x24, x24, -1\n" ++
  "  bnez x24, 33b\n" ++
  "34:\n"

def ecrecoverVGateAsm : String :=
  precompileFrameAddi "x18" (precompileFrameEcrecoverInputOff + 32) ++
  "  li x19, 31\n" ++
  "40:\n" ++
  "  beqz x19, 41f\n" ++
  "  lbu x16, 0(x18)\n" ++
  "  bnez x16, 43f\n" ++
  "  addi x18, x18, 1\n" ++
  "  addi x19, x19, -1\n" ++
  "  j 40b\n" ++
  "41:\n" ++
  "  lbu x16, 0(x18)\n" ++
  "  li x19, 27\n" ++
  "  beq x16, x19, 42f\n" ++
  "  li x19, 28\n" ++
  "  beq x16, x19, 42f\n" ++
  "43:\n" ++
  "  j 7b\n" ++
  "42:\n"

def ecrecoverNonzeroRSGateAsm : String :=
  precompileFrameAddi "x18" (precompileFrameEcrecoverInputOff + 64) ++
  "  ld x16, 0(x18)\n" ++
  "  ld x17, 8(x18)\n" ++
  "  or x16, x16, x17\n" ++
  "  ld x17, 16(x18)\n" ++
  "  or x16, x16, x17\n" ++
  "  ld x17, 24(x18)\n" ++
  "  or x16, x16, x17\n" ++
  "  beqz x16, 7b\n" ++
  precompileFrameAddi "x18" (precompileFrameEcrecoverInputOff + 96) ++
  "  ld x16, 0(x18)\n" ++
  "  ld x17, 8(x18)\n" ++
  "  or x16, x16, x17\n" ++
  "  ld x17, 16(x18)\n" ++
  "  or x16, x16, x17\n" ++
  "  ld x17, 24(x18)\n" ++
  "  or x16, x16, x17\n" ++
  "  beqz x16, 7b\n"

private def secp256k1OrderBytes : List Nat :=
  [ 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
  , 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe
  , 0xba, 0xae, 0xdc, 0xe6, 0xaf, 0x48, 0xa0, 0x3b
  , 0xbf, 0xd2, 0x5e, 0x8c, 0xd0, 0x36, 0x41, 0x41
  ]

private def ecrecoverScalarBelowOrderCompareAsm
    (bytes : List Nat) (idx belowLabel : Nat) : String :=
  match bytes with
  | [] => ""
  | byte :: rest =>
      "  lbu x16, " ++ toString idx ++ "(x18)\n" ++
      "  li x17, " ++ toString byte ++ "\n" ++
      "  bltu x17, x16, 7b\n" ++
      "  bltu x16, x17, " ++ toString belowLabel ++ "f\n" ++
      ecrecoverScalarBelowOrderCompareAsm rest (idx + 1) belowLabel

private def ecrecoverScalarBelowOrderGateAsm
    (wordOff : Nat) (belowLabel : Nat) : String :=
  precompileFrameAddi "x18" (precompileFrameEcrecoverInputOff + wordOff) ++
  ecrecoverScalarBelowOrderCompareAsm secp256k1OrderBytes 0 belowLabel ++
  "  j 7b\n" ++
  toString belowLabel ++ ":\n"

def ecrecoverScalarOrderGateAsm : String :=
  ecrecoverScalarBelowOrderGateAsm 64 44 ++
  ecrecoverScalarBelowOrderGateAsm 96 45

def chargePrecompileWordGasAsm
    (baseGas perWordGas : Nat) (sizeReg costReg scratchReg : String) : String :=
  "  li " ++ scratchReg ++ ", 31\n" ++
  "  add " ++ costReg ++ ", " ++ sizeReg ++ ", " ++ scratchReg ++ "\n" ++
  "  bltu " ++ costReg ++ ", " ++ sizeReg ++ ", .exit_outofgas\n" ++
  "  srli " ++ costReg ++ ", " ++ costReg ++ ", 5\n" ++
  "  li " ++ scratchReg ++ ", " ++ toString perWordGas ++ "\n" ++
  "  mul " ++ costReg ++ ", " ++ costReg ++ ", " ++ scratchReg ++ "\n" ++
  "  li " ++ scratchReg ++ ", " ++ toString baseGas ++ "\n" ++
  "  add " ++ costReg ++ ", " ++ costReg ++ ", " ++ scratchReg ++ "\n" ++
  chargePrecompileGasAsm costReg scratchReg

def stagePrecompileInputWindowAsm
    (tag : String) (inOffsetOff inSizeOff frameOff sourceOff byteLen : Nat) : String :=
  -- Zero-fill the fixed accelerator window, then copy the available suffix of
  -- EVM call data. This mirrors execution-specs `buffer_read` padding.
  precompileFrameAddi "x18" frameOff ++
  "  li x19, " ++ toString byteLen ++ "\n" ++
  ".L" ++ tag ++ "_zero:\n" ++
  "  beqz x19, .L" ++ tag ++ "_zero_done\n" ++
  "  sb x0, 0(x18)\n" ++
  "  addi x18, x18, 1\n" ++
  "  addi x19, x19, -1\n" ++
  "  j .L" ++ tag ++ "_zero\n" ++
  ".L" ++ tag ++ "_zero_done:\n" ++
  "  ld x18, " ++ toString inSizeOff ++ "(x12)\n" ++
  "  li x19, " ++ toString sourceOff ++ "\n" ++
  "  bgeu x19, x18, .L" ++ tag ++ "_done\n" ++
  "  sub x18, x18, x19\n" ++
  "  li x22, " ++ toString byteLen ++ "\n" ++
  "  bgeu x22, x18, .L" ++ tag ++ "_copy_len_ok\n" ++
  "  mv x18, x22\n" ++
  ".L" ++ tag ++ "_copy_len_ok:\n" ++
  "  ld x19, " ++ toString inOffsetOff ++ "(x12)\n" ++
  "  add x19, x19, x13\n" ++
  "  li x22, " ++ toString sourceOff ++ "\n" ++
  "  add x19, x19, x22\n" ++
  precompileFrameAddi "x21" frameOff ++
  ".L" ++ tag ++ "_copy:\n" ++
  "  beqz x18, .L" ++ tag ++ "_done\n" ++
  "  lbu x23, 0(x19)\n" ++
  "  sb x23, 0(x21)\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x21, x21, 1\n" ++
  "  addi x18, x18, -1\n" ++
  "  j .L" ++ tag ++ "_copy\n" ++
  ".L" ++ tag ++ "_done:\n"

def precompileSuccess64FromFrameAsm
    (tag : String) (outOffsetOff outSizeOff resultFrameOff : Nat) : String :=
  "  la x15, evm_precompile_frame\n" ++
  "  addi x18, x15, 16\n" ++
  precompileFrameAddi "x19" resultFrameOff ++
  "  li x22, 64\n" ++
  ".L" ++ tag ++ "_retcopy:\n" ++
  "  beqz x22, .L" ++ tag ++ "_retcopy_done\n" ++
  "  lbu x16, 0(x19)\n" ++
  "  sb x16, 0(x18)\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x18, x18, 1\n" ++
  "  addi x22, x22, -1\n" ++
  "  j .L" ++ tag ++ "_retcopy\n" ++
  ".L" ++ tag ++ "_retcopy_done:\n" ++
  "  li x16, 1\n" ++
  "  sd x16, 0(x15)\n" ++
  "  li x16, 64\n" ++
  "  sd x16, 8(x15)\n" ++
  "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
  "  li x23, 64\n" ++
  "  bgeu x22, x23, .L" ++ tag ++ "_out_len_ok\n" ++
  "  mv x23, x22\n" ++
  ".L" ++ tag ++ "_out_len_ok:\n" ++
  "  beqz x23, 7b\n" ++
  "  addi x18, x15, 16\n" ++
  "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
  "  add x19, x13, x19\n" ++
  ".L" ++ tag ++ "_outcopy:\n" ++
  "  lbu x16, 0(x18)\n" ++
  "  sb x16, 0(x19)\n" ++
  "  addi x18, x18, 1\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x23, x23, -1\n" ++
  "  bnez x23, .L" ++ tag ++ "_outcopy\n" ++
  "  j 7b\n"

def kzgVersionedHashCompareBytesAsm : String :=
  String.intercalate "" <| (List.range 31).map fun i =>
    let idx := i + 1
    "  lbu x16, " ++ toString (precompileFrameBls12G2InputOff + idx) ++ "(x15)\n" ++
    "  lbu x17, " ++ toString (precompileFrameBls12G2OutputOff + idx) ++ "(x15)\n" ++
    "  bne x16, x17, 1f\n"

def kzgVersionedHashGateAsm : String :=
  "  mv s10, x10\n" ++
  "  mv s11, x12\n" ++
  precompileFrameAddi "a0" (precompileFrameBls12G2InputOff + 96) ++
  "  li a1, 48\n" ++
  precompileFrameAddi "a2" precompileFrameBls12G2OutputOff ++
  "  jal x1, zkvm_keccak256\n" ++
  "  mv x10, s10\n" ++
  "  mv x12, s11\n" ++
  "  bnez a0, 1f\n" ++
  "  la x15, evm_precompile_frame\n" ++
  "  lbu x16, " ++ toString precompileFrameBls12G2InputOff ++ "(x15)\n" ++
  "  li x17, 1\n" ++
  "  bne x16, x17, 1f\n" ++
  kzgVersionedHashCompareBytesAsm

def precompileSuccessBoolFromFrameAsm
    (tag : String) (outOffsetOff outSizeOff resultFrameOff : Nat) : String :=
  "  la x15, evm_precompile_frame\n" ++
  "  sd x0, 16(x15)\n" ++
  "  sd x0, 24(x15)\n" ++
  "  sd x0, 32(x15)\n" ++
  "  sd x0, 40(x15)\n" ++
  "  lbu x16, " ++ toString resultFrameOff ++ "(x15)\n" ++
  "  sb x16, 47(x15)\n" ++
  "  li x16, 1\n" ++
  "  sd x16, 0(x15)\n" ++
  "  li x16, 32\n" ++
  "  sd x16, 8(x15)\n" ++
  "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
  "  li x23, 32\n" ++
  "  bgeu x22, x23, .L" ++ tag ++ "_out_len_ok\n" ++
  "  mv x23, x22\n" ++
  ".L" ++ tag ++ "_out_len_ok:\n" ++
  "  beqz x23, 7b\n" ++
  "  addi x18, x15, 16\n" ++
  "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
  "  add x19, x13, x19\n" ++
  ".L" ++ tag ++ "_outcopy:\n" ++
  "  lbu x16, 0(x18)\n" ++
  "  sb x16, 0(x19)\n" ++
  "  addi x18, x18, 1\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x23, x23, -1\n" ++
  "  bnez x23, .L" ++ tag ++ "_outcopy\n" ++
  "  j 7b\n"


def precompileSuccessKzgPointEvalAsm
    (tag : String) (outOffsetOff outSizeOff : Nat) : String :=
  "  la x15, evm_precompile_frame\n" ++
  "  addi x18, x15, 16\n" ++
  "  li x22, 30\n" ++
  ".L" ++ tag ++ "_field_zero:\n" ++
  "  beqz x22, .L" ++ tag ++ "_field_tail\n" ++
  "  sb x0, 0(x18)\n" ++
  "  addi x18, x18, 1\n" ++
  "  addi x22, x22, -1\n" ++
  "  j .L" ++ tag ++ "_field_zero\n" ++
  ".L" ++ tag ++ "_field_tail:\n" ++
  "  li x16, 0x10\n" ++
  "  sb x16, 0(x18)\n" ++
  "  sb x0, 1(x18)\n" ++
  "  addi x18, x18, 2\n" ++
  "  li x16, 0x73\n" ++
  "  sb x16, 0(x18)\n" ++
  "  li x16, 0xed\n" ++
  "  sb x16, 1(x18)\n" ++
  "  li x16, 0xa7\n" ++
  "  sb x16, 2(x18)\n" ++
  "  li x16, 0x53\n" ++
  "  sb x16, 3(x18)\n" ++
  "  li x16, 0x29\n" ++
  "  sb x16, 4(x18)\n" ++
  "  li x16, 0x9d\n" ++
  "  sb x16, 5(x18)\n" ++
  "  li x16, 0x7d\n" ++
  "  sb x16, 6(x18)\n" ++
  "  li x16, 0x48\n" ++
  "  sb x16, 7(x18)\n" ++
  "  li x16, 0x33\n" ++
  "  sb x16, 8(x18)\n" ++
  "  sb x16, 9(x18)\n" ++
  "  li x16, 0xd8\n" ++
  "  sb x16, 10(x18)\n" ++
  "  li x16, 0x08\n" ++
  "  sb x16, 11(x18)\n" ++
  "  li x16, 0x09\n" ++
  "  sb x16, 12(x18)\n" ++
  "  li x16, 0xa1\n" ++
  "  sb x16, 13(x18)\n" ++
  "  li x16, 0xd8\n" ++
  "  sb x16, 14(x18)\n" ++
  "  li x16, 0x05\n" ++
  "  sb x16, 15(x18)\n" ++
  "  li x16, 0x53\n" ++
  "  sb x16, 16(x18)\n" ++
  "  li x16, 0xbd\n" ++
  "  sb x16, 17(x18)\n" ++
  "  li x16, 0xa4\n" ++
  "  sb x16, 18(x18)\n" ++
  "  li x16, 0x02\n" ++
  "  sb x16, 19(x18)\n" ++
  "  li x16, 0xff\n" ++
  "  sb x16, 20(x18)\n" ++
  "  li x16, 0xfe\n" ++
  "  sb x16, 21(x18)\n" ++
  "  li x16, 0x5b\n" ++
  "  sb x16, 22(x18)\n" ++
  "  li x16, 0xfe\n" ++
  "  sb x16, 23(x18)\n" ++
  "  li x16, 0xff\n" ++
  "  sb x16, 24(x18)\n" ++
  "  sb x16, 25(x18)\n" ++
  "  sb x16, 26(x18)\n" ++
  "  sb x16, 27(x18)\n" ++
  "  sb x0, 28(x18)\n" ++
  "  sb x0, 29(x18)\n" ++
  "  sb x0, 30(x18)\n" ++
  "  li x16, 0x01\n" ++
  "  sb x16, 31(x18)\n" ++
  "  li x16, 1\n" ++
  "  sd x16, 0(x15)\n" ++
  "  li x16, 64\n" ++
  "  sd x16, 8(x15)\n" ++
  "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
  "  li x23, 64\n" ++
  "  bgeu x22, x23, .L" ++ tag ++ "_out_len_ok\n" ++
  "  mv x23, x22\n" ++
  ".L" ++ tag ++ "_out_len_ok:\n" ++
  "  beqz x23, 7b\n" ++
  "  addi x18, x15, 16\n" ++
  "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
  "  add x19, x13, x19\n" ++
  ".L" ++ tag ++ "_outcopy:\n" ++
  "  lbu x16, 0(x18)\n" ++
  "  sb x16, 0(x19)\n" ++
  "  addi x18, x18, 1\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x23, x23, -1\n" ++
  "  bnez x23, .L" ++ tag ++ "_outcopy\n" ++
  "  j 7b\n"

end EvmAsm.Codegen
