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

end EvmAsm.Stateless.VM.Precompiles
