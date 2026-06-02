/-
  EvmAsm.Stateless.VM.Precompiles

  Dispatch and pure framing helpers for precompile addresses
  (0x01..0x14 + 0x100 for P256VERIFY).

  ## Implementation status

  Per the project plan (see `~/.claude/plans/please-cut-a-branch-warm-wand.md`
  and `PLAN.md` "Stateless Guest"), precompile dispatch started as
  an unimplemented frontier:

  - ECRECOVER, SHA-256, RIPEMD-160, IDENTITY, MODEXP
  - ALT_BN128 ADD / MUL / PAIRING (BN254)
  - BLAKE2F
  - POINT_EVALUATION (EIP-4844 KZG)
  - BLS12-381 G1/G2 ADD/MSM, PAIRING, MAP
  - SECP256R1_VERIFY (P256)

  Unsupported concrete call sites still trigger `REASON_PRECOMPILE + addr`
  per the reason-code table in `Stateless/Unimplemented.lean`. Implemented
  slices in this file expose pure EVM return-data/gas framing first, then
  later CALL/STATICCALL wiring can call those helpers.

  ## What's NOT in this file

  Hashes needed for **block processing** (KECCAK256 for header
  hashing, MPT, code hashing, tx hashing, address derivation;
  SHA-256 for SSZ Merkleization of the output) are bridged
  separately and do NOT route through this file. They live in
  `EvmAsm/EL/Keccak*EcallBridge.lean` (existing) and
  `EvmAsm/Stateless/Bridges/Sha256EcallBridge.lean` (scaffolded
  in PR-K12). See `docs/execution-specs-feedback.md` #1 for the
  cost-picture discussion.

-/

import EvmAsm.EL.Secp256r1VerifyEcallBridge

namespace EvmAsm.Stateless.VM.Precompiles

abbrev Byte := EvmAsm.EL.Byte
abbrev ByteList := List Byte
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

namespace P256Verify

abbrev MemoryReader := EvmAsm.EL.Secp256r1VerifyInputBridge.MemoryReader
abbrev AcceleratorInput := EvmAsm.EL.Secp256r1VerifyInputBridge.AcceleratorInput
abbrev AcceleratorResult := EvmAsm.EL.Secp256r1VerifyResultBridge.AcceleratorResult

/-- EVM precompile address for P256VERIFY / secp256r1 verification. -/
def address : Nat := 0x100

/-- Osaka/BPO executable-spec gas cost for P256VERIFY. -/
def gasCost : Nat := 6900

/-- P256VERIFY consumes exactly five 32-byte fields. -/
def inputLength : Nat := 160

/-- Successful P256VERIFY returns `left_pad_zero_bytes(b"\x01", 32)`. -/
def successOutput : ByteList :=
  List.replicate 31 (0 : Byte) ++ [1]

/-- Invalid input, invalid signature, or accelerator failure returns no bytes. -/
def emptyOutput : ByteList := []

/-- Result surface exposed to the caller by the pure precompile framing layer. -/
structure Result where
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr

/--
Build the fixed accelerator input fields from the EVM call data. The executable
spec first checks `len(data) == 160`; callers must guard this helper with that
length check. Field starts mirror `p256verify.py`: msg, r, s, qx, qy.
-/
def acceleratorInputFromCallData (memory : MemoryReader) (dataStart : Nat) :
    AcceleratorInput :=
  EvmAsm.EL.Secp256r1VerifyInputBridge.secp256r1VerifyInputFromMemory
    memory dataStart (dataStart + 32) (dataStart + 96)

/-- Convert a successful accelerator boolean to the EVM return-data bytes. -/
def outputFromVerified (verified : Bool) : ByteList :=
  if verified then successOutput else emptyOutput

/--
Pure P256VERIFY precompile framing. This models the EVM-side guards and
return-data shape; scalar bounds, curve membership, and signature validation are
part of the supplied accelerator model, matching the existing secp256r1 bridge.
-/
def execute
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if dataLength = inputLength then
    let input := acceleratorInputFromCallData memory dataStart
    let result := accelerator input
    match result.status with
    | .eok =>
        { status := result.status
          output := outputFromVerified result.output.verified
          gasCharged := gasCost }
    | .efail =>
        { status := result.status, output := emptyOutput, gasCharged := gasCost }
  else
    { status := .eok, output := emptyOutput, gasCharged := gasCost }

theorem successOutput_length :
    successOutput.length = 32 := by
  simp [successOutput]

theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl

@[simp] theorem outputFromVerified_true :
    outputFromVerified true = successOutput := rfl

@[simp] theorem outputFromVerified_false :
    outputFromVerified false = emptyOutput := rfl

@[simp] theorem execute_badLength
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_length : dataLength ≠ inputLength) :
    execute accelerator memory dataStart dataLength =
      { status := .eok, output := emptyOutput, gasCharged := gasCost } := by
  simp [execute, h_length]

@[simp] theorem execute_status
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute accelerator memory dataStart inputLength).status =
      (accelerator (acceleratorInputFromCallData memory dataStart)).status := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
    simp [execute, inputLength, h_status]

@[simp] theorem execute_output_eok
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok) :
    (execute accelerator memory dataStart inputLength).output =
      outputFromVerified
        (accelerator (acceleratorInputFromCallData memory dataStart)).output.verified := by
  simp [execute, inputLength, h_status]

@[simp] theorem execute_output_efail
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .efail) :
    (execute accelerator memory dataStart inputLength).output = emptyOutput := by
  simp [execute, inputLength, h_status]

@[simp] theorem execute_gasCharged
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute accelerator memory dataStart dataLength).gasCharged = gasCost := by
  by_cases h_length : dataLength = inputLength
  · subst dataLength
    cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
      simp [execute, inputLength, h_status]
  · simp [execute, h_length]

end P256Verify

end EvmAsm.Stateless.VM.Precompiles
