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

import EvmAsm.EL.Bn254G1AddEcallBridge
import EvmAsm.EL.Bn254G1MulEcallBridge
import EvmAsm.EL.Bn254PairingEcallBridge
import EvmAsm.EL.KzgPointEvalEcallBridge
import EvmAsm.EL.Secp256r1VerifyEcallBridge

namespace EvmAsm.Stateless.VM.Precompiles

abbrev Byte := EvmAsm.EL.Byte
abbrev ByteList := List Byte
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

namespace BN254

/-- Gas constants for the BN254 precompiles at a fork. -/
structure GasSchedule where
  ecadd : Nat
  ecmul : Nat
  pairingBase : Nat
  pairingPerPoint : Nat
  deriving Repr

/-- Byzantium gas schedule from execution-specs. -/
def byzantiumGasSchedule : GasSchedule :=
  { ecadd := 500
    ecmul := 40000
    pairingBase := 100000
    pairingPerPoint := 80000 }

/-- Istanbul-and-later gas schedule, still current in Osaka/BPO forks. -/
def currentGasSchedule : GasSchedule :=
  { ecadd := 150
    ecmul := 6000
    pairingBase := 45000
    pairingPerPoint := 34000 }

/-- BN254 G1 addition precompile address. -/
def addAddress : Nat := 0x06

/-- BN254 G1 scalar multiplication precompile address. -/
def mulAddress : Nat := 0x07

/-- BN254 pairing precompile address. -/
def pairingAddress : Nat := 0x08

/-- BN254 add reads two 64-byte G1 points, with EVM `buffer_read` zero padding. -/
def addInputLength : Nat := 128

/-- BN254 mul reads one 64-byte G1 point and one 32-byte scalar. -/
def mulInputLength : Nat := 96

/-- BN254 pairing consumes 192-byte G1/G2 pairs. -/
def pairingPairLength : Nat := 192

/-- `U256(1).to_be_bytes32()`. -/
def successWordOutput : ByteList :=
  List.replicate 31 (0 : Byte) ++ [1]

/-- `U256(0).to_be_bytes32()`. -/
def zeroWordOutput : ByteList :=
  List.replicate 32 (0 : Byte)

/-- Invalid point, malformed pairing length, or accelerator failure returns no bytes. -/
def emptyOutput : ByteList := []

structure Result where
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr

namespace Add

abbrev MemoryReader := EvmAsm.EL.Bn254G1AddInputBridge.MemoryReader
abbrev AcceleratorInput := EvmAsm.EL.Bn254G1AddInputBridge.AcceleratorInput
abbrev AcceleratorOutput := EvmAsm.EL.Bn254G1AddResultBridge.AcceleratorOutput

def acceleratorInputFromCallData (memory : MemoryReader) (dataStart : Nat) :
    AcceleratorInput :=
  EvmAsm.EL.Bn254G1AddInputBridge.bn254G1AddInputFromMemory
    memory dataStart (dataStart + 64)

def execute
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → ZkvmStatus × AcceleratorOutput)
    (memory : MemoryReader) (dataStart : Nat) : Result :=
  let result := accelerator (acceleratorInputFromCallData memory dataStart)
  match result.1 with
  | .eok =>
      { status := result.1
        output := EvmAsm.EL.Bn254G1AddResultBridge.outputBytesList result.2
        gasCharged := schedule.ecadd }
  | .efail =>
      { status := result.1, output := emptyOutput, gasCharged := schedule.ecadd }

@[simp] theorem execute_status
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → ZkvmStatus × AcceleratorOutput)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute schedule accelerator memory dataStart).status =
      (accelerator (acceleratorInputFromCallData memory dataStart)).1 := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).1 <;>
    simp [execute, h_status]

@[simp] theorem execute_output_eok
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → ZkvmStatus × AcceleratorOutput)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).1 = .eok) :
    (execute schedule accelerator memory dataStart).output =
      EvmAsm.EL.Bn254G1AddResultBridge.outputBytesList
        (accelerator (acceleratorInputFromCallData memory dataStart)).2 := by
  simp [execute, h_status]

@[simp] theorem execute_output_efail
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → ZkvmStatus × AcceleratorOutput)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).1 = .efail) :
    (execute schedule accelerator memory dataStart).output = emptyOutput := by
  simp [execute, h_status]

@[simp] theorem execute_gasCharged
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → ZkvmStatus × AcceleratorOutput)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute schedule accelerator memory dataStart).gasCharged = schedule.ecadd := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).1 <;>
    simp [execute, h_status]

end Add

namespace Mul

abbrev MemoryReader := EvmAsm.EL.Bn254G1MulInputBridge.MemoryReader
abbrev AcceleratorInput := EvmAsm.EL.Bn254G1MulInputBridge.AcceleratorInput
abbrev AcceleratorResult := EvmAsm.EL.Bn254G1MulResultBridge.AcceleratorResult

def acceleratorInputFromCallData (memory : MemoryReader) (dataStart : Nat) :
    AcceleratorInput :=
  EvmAsm.EL.Bn254G1MulInputBridge.bn254G1MulInputFromMemory
    memory dataStart (dataStart + 64)

def execute
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat) : Result :=
  let result := accelerator (acceleratorInputFromCallData memory dataStart)
  match result.status with
  | .eok =>
      { status := result.status
        output := EvmAsm.EL.Bn254G1MulResultBridge.g1PointBytesList result.output.point
        gasCharged := schedule.ecmul }
  | .efail =>
      { status := result.status, output := emptyOutput, gasCharged := schedule.ecmul }

@[simp] theorem execute_status
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute schedule accelerator memory dataStart).status =
      (accelerator (acceleratorInputFromCallData memory dataStart)).status := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
    simp [execute, h_status]

@[simp] theorem execute_output_eok
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok) :
    (execute schedule accelerator memory dataStart).output =
      EvmAsm.EL.Bn254G1MulResultBridge.g1PointBytesList
        (accelerator (acceleratorInputFromCallData memory dataStart)).output.point := by
  simp [execute, h_status]

@[simp] theorem execute_output_efail
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status = .efail) :
    (execute schedule accelerator memory dataStart).output = emptyOutput := by
  simp [execute, h_status]

@[simp] theorem execute_gasCharged
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat) :
    (execute schedule accelerator memory dataStart).gasCharged = schedule.ecmul := by
  cases h_status : (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
    simp [execute, h_status]

end Mul

namespace Pairing

abbrev MemoryReader := EvmAsm.EL.Bn254PairingInputBridge.MemoryReader
abbrev AcceleratorInput := EvmAsm.EL.Bn254PairingInputBridge.AcceleratorInput
abbrev AcceleratorResult := EvmAsm.EL.Bn254PairingResultBridge.AcceleratorResult

def numPairs (dataLength : Nat) : Nat :=
  dataLength / pairingPairLength

def gasCharged (schedule : GasSchedule) (dataLength : Nat) : Nat :=
  schedule.pairingBase + schedule.pairingPerPoint * numPairs dataLength

def acceleratorInputFromCallData
    (memory : MemoryReader) (dataStart dataLength : Nat) : AcceleratorInput :=
  EvmAsm.EL.Bn254PairingInputBridge.bn254PairingInputFromMemory
    memory dataStart (numPairs dataLength)

def outputFromVerified (verified : Bool) : ByteList :=
  if verified then successWordOutput else zeroWordOutput

def execute
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if dataLength % pairingPairLength = 0 then
    let input := acceleratorInputFromCallData memory dataStart dataLength
    let result := accelerator input
    match result.status with
    | .eok =>
        { status := result.status
          output := outputFromVerified result.output.verified
          gasCharged := gasCharged schedule dataLength }
    | .efail =>
        { status := result.status
          output := emptyOutput
          gasCharged := gasCharged schedule dataLength }
  else
    { status := .efail
      output := emptyOutput
      gasCharged := gasCharged schedule dataLength }

@[simp] theorem outputFromVerified_true :
    outputFromVerified true = successWordOutput := rfl

@[simp] theorem outputFromVerified_false :
    outputFromVerified false = zeroWordOutput := rfl

@[simp] theorem execute_badLength
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_length : dataLength % pairingPairLength ≠ 0) :
    execute schedule accelerator memory dataStart dataLength =
      { status := .efail
        output := emptyOutput
        gasCharged := gasCharged schedule dataLength } := by
  simp [execute, h_length]

@[simp] theorem execute_status_validLength
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_length : dataLength % pairingPairLength = 0) :
    (execute schedule accelerator memory dataStart dataLength).status =
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status := by
  cases h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status <;>
    simp [execute, h_length, h_status]

@[simp] theorem execute_gasCharged
    (schedule : GasSchedule)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute schedule accelerator memory dataStart dataLength).gasCharged =
      gasCharged schedule dataLength := by
  by_cases h_length : dataLength % pairingPairLength = 0
  · cases h_status :
        (accelerator (acceleratorInputFromCallData memory dataStart dataLength)).status <;>
      simp [execute, h_length, h_status]
  · simp [execute, h_length]

end Pairing

theorem successWordOutput_length :
    successWordOutput.length = 32 := by
  simp [successWordOutput]

theorem zeroWordOutput_length :
    zeroWordOutput.length = 32 := by
  simp [zeroWordOutput]

theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl

end BN254

namespace KzgPointEvaluation

abbrev MemoryReader := EvmAsm.EL.KzgPointEvalInputBridge.MemoryReader
abbrev Bytes32 := EvmAsm.EL.KzgPointEvalInputBridge.Bytes32
abbrev AcceleratorInput := EvmAsm.EL.KzgPointEvalInputBridge.AcceleratorInput
abbrev AcceleratorResult := EvmAsm.EL.KzgPointEvalResultBridge.AcceleratorResult

/-- EVM precompile address for EIP-4844 KZG point evaluation. -/
def address : Nat := 0x0a

/-- Osaka/BPO executable-spec fixed gas cost for KZG point evaluation. -/
def gasCost : Nat := 50000

/-- KZG point evaluation consumes exactly 192 bytes. -/
def inputLength : Nat := 192

def versionedHashOffset : Nat := 0
def zOffset : Nat := 32
def yOffset : Nat := 64
def commitmentOffset : Nat := 96
def proofOffset : Nat := 144

/-- `U256(4096).to_be_bytes32()`, i.e. `FIELD_ELEMENTS_PER_BLOB`. -/
def fieldElementsPerBlobOutput : ByteList :=
  List.replicate 30 (0 : Byte) ++ [0x10, 0x00]

/-- `U256(BLS_MODULUS).to_be_bytes32()` from execution-specs. -/
def blsModulusOutput : ByteList :=
  [ 0x73, 0xed, 0xa7, 0x53, 0x29, 0x9d, 0x7d, 0x48
  , 0x33, 0x39, 0xd8, 0x08, 0x09, 0xa1, 0xd8, 0x05
  , 0x53, 0xbd, 0xa4, 0x02, 0xff, 0xfe, 0x5b, 0xfe
  , 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01 ]

/-- Successful KZG point evaluation returns `FIELD_ELEMENTS_PER_BLOB || BLS_MODULUS`. -/
def successOutput : ByteList :=
  fieldElementsPerBlobOutput ++ blsModulusOutput

/-- Invalid length, invalid hash/proof, or accelerator failure returns no bytes. -/
def emptyOutput : ByteList := []

/--
Result surface exposed by the pure precompile framing layer. `exceptional`
records execution-spec `KZGProofError` cases; later CALL/STATICCALL wiring can
translate that into the enclosing EVM failure semantics.
-/
structure Result where
  exceptional : Bool
  status : ZkvmStatus
  output : ByteList
  gasCharged : Nat
  deriving Repr

/-- The versioned hash is the first 32 bytes of the precompile payload. -/
def versionedHashFromCallData (memory : MemoryReader) (dataStart : Nat) : Bytes32 :=
  EvmAsm.EL.KzgPointEvalInputBridge.bytes32FromMemory
    memory (dataStart + versionedHashOffset)

/--
Build the accelerator input from the EVM call data. The executable spec first
checks `len(data) == 192`; callers must guard this helper with that exact
length check. Field starts mirror `point_evaluation.py`.
-/
def acceleratorInputFromCallData (memory : MemoryReader) (dataStart : Nat) :
    AcceleratorInput :=
  EvmAsm.EL.KzgPointEvalInputBridge.kzgPointEvalInputFromMemory
    memory
    (dataStart + commitmentOffset)
    (dataStart + zOffset)
    (dataStart + yOffset)
    (dataStart + proofOffset)

/-- Convert the accelerator proof-verification result to EVM return data. -/
def outputFromVerified (verified : Bool) : ByteList :=
  if verified then successOutput else emptyOutput

/--
Pure KZG point-evaluation precompile framing. This models the executable-spec
guards and return-data shape:

* input length must be exactly 192 bytes;
* the supplied `versionedHashIsValid` hook checks
  `kzg_commitment_to_versioned_hash(commitment) == versioned_hash`;
* the supplied accelerator verifies `(commitment, z, y, proof)`;
* success returns `FIELD_ELEMENTS_PER_BLOB || BLS_MODULUS`.
-/
def execute
    (versionedHashIsValid : Bytes32 → AcceleratorInput → Bool)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) : Result :=
  if dataLength = inputLength then
    let input := acceleratorInputFromCallData memory dataStart
    let versionedHash := versionedHashFromCallData memory dataStart
    if versionedHashIsValid versionedHash input then
      let request := EvmAsm.EL.KzgPointEvalEcallBridge.requestFromInput input
      let result := EvmAsm.EL.KzgPointEvalEcallBridge.executeKzgPointEvalEcall
        accelerator request
      match result.status with
      | .eok =>
          { exceptional := !result.output.verified
            status := if result.output.verified then .eok else .efail
            output := outputFromVerified result.output.verified
            gasCharged := gasCost }
      | .efail =>
          { exceptional := true
            status := result.status
            output := emptyOutput
            gasCharged := gasCost }
    else
      { exceptional := true
        status := .efail
        output := emptyOutput
        gasCharged := gasCost }
  else
    { exceptional := true
      status := .efail
      output := emptyOutput
      gasCharged := 0 }

theorem fieldElementsPerBlobOutput_length :
    fieldElementsPerBlobOutput.length = 32 := by
  native_decide

theorem blsModulusOutput_length :
    blsModulusOutput.length = 32 := by
  native_decide

theorem successOutput_length :
    successOutput.length = 64 := by
  native_decide

theorem emptyOutput_length :
    emptyOutput.length = 0 := rfl

@[simp] theorem outputFromVerified_true :
    outputFromVerified true = successOutput := rfl

@[simp] theorem outputFromVerified_false :
    outputFromVerified false = emptyOutput := rfl

@[simp] theorem execute_badLength
    (versionedHashIsValid : Bytes32 → AcceleratorInput → Bool)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat)
    (h_length : dataLength ≠ inputLength) :
    execute versionedHashIsValid accelerator memory dataStart dataLength =
      { exceptional := true
        status := .efail
        output := emptyOutput
        gasCharged := 0 } := by
  simp [execute, h_length]

@[simp] theorem execute_invalidVersionedHash
    (versionedHashIsValid : Bytes32 → AcceleratorInput → Bool)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_hash :
      versionedHashIsValid
        (versionedHashFromCallData memory dataStart)
        (acceleratorInputFromCallData memory dataStart) = false) :
    execute versionedHashIsValid accelerator memory dataStart inputLength =
      { exceptional := true
        status := .efail
        output := emptyOutput
        gasCharged := gasCost } := by
  simp [execute, inputLength, h_hash]

@[simp] theorem execute_output_verified
    (versionedHashIsValid : Bytes32 → AcceleratorInput → Bool)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_hash :
      versionedHashIsValid
        (versionedHashFromCallData memory dataStart)
        (acceleratorInputFromCallData memory dataStart) = true)
    (h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok)
    (h_verified :
      (accelerator (acceleratorInputFromCallData memory dataStart)).output.verified = true) :
    (execute versionedHashIsValid accelerator memory dataStart inputLength).output =
      successOutput := by
  simp [execute, inputLength, h_hash, h_status, h_verified,
    EvmAsm.EL.KzgPointEvalEcallBridge.executeKzgPointEvalEcall,
    EvmAsm.EL.KzgPointEvalEcallBridge.requestFromInput]

@[simp] theorem execute_output_unverified
    (versionedHashIsValid : Bytes32 → AcceleratorInput → Bool)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart : Nat)
    (h_hash :
      versionedHashIsValid
        (versionedHashFromCallData memory dataStart)
        (acceleratorInputFromCallData memory dataStart) = true)
    (h_status :
      (accelerator (acceleratorInputFromCallData memory dataStart)).status = .eok)
    (h_verified :
      (accelerator (acceleratorInputFromCallData memory dataStart)).output.verified = false) :
    (execute versionedHashIsValid accelerator memory dataStart inputLength).output =
      emptyOutput := by
  simp [execute, inputLength, h_hash, h_status, h_verified,
    EvmAsm.EL.KzgPointEvalEcallBridge.executeKzgPointEvalEcall,
    EvmAsm.EL.KzgPointEvalEcallBridge.requestFromInput]

@[simp] theorem execute_gasCharged
    (versionedHashIsValid : Bytes32 → AcceleratorInput → Bool)
    (accelerator : AcceleratorInput → AcceleratorResult)
    (memory : MemoryReader) (dataStart dataLength : Nat) :
    (execute versionedHashIsValid accelerator memory dataStart dataLength).gasCharged =
      if dataLength = inputLength then gasCost else 0 := by
  by_cases h_length : dataLength = inputLength
  · subst dataLength
    cases h_hash :
        versionedHashIsValid
          (versionedHashFromCallData memory dataStart)
          (acceleratorInputFromCallData memory dataStart)
    · simp [execute, inputLength, h_hash]
    · cases h_status :
          (accelerator (acceleratorInputFromCallData memory dataStart)).status <;>
        cases h_verified :
          (accelerator (acceleratorInputFromCallData memory dataStart)).output.verified <;>
        simp [execute, inputLength, h_hash, h_status, h_verified,
          EvmAsm.EL.KzgPointEvalEcallBridge.executeKzgPointEvalEcall,
          EvmAsm.EL.KzgPointEvalEcallBridge.requestFromInput]
  · simp [execute, h_length]

end KzgPointEvaluation

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
