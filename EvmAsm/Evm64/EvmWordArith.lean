/-
  EvmAsm.Evm64.EvmWordArith

  Mathematical correctness lemmas connecting limb-level computations
  to 256-bit EvmWord operations. Used by stack-level specs.

  Re-exports all sub-modules for backwards compatibility. Many of the
  listed leaves transitively cover their Arithmetic / MultiLimb /
  Common prefix chain; see per-module comments below for the routing.
-/

-- Opcode-specific leaves that nothing else here imports:
import EvmAsm.Evm64.EvmWordArith.IsZero
import EvmAsm.Evm64.EvmWordArith.Eq
import EvmAsm.Evm64.EvmWordArith.Comparison
import EvmAsm.Evm64.EvmWordArith.ByteOps
import EvmAsm.Evm64.EvmWordArith.SignExtend
import EvmAsm.Evm64.EvmWordArith.SDiv
import EvmAsm.Evm64.EvmWordArith.SMod

-- MulCorrect covers Arithmetic → MultiLimb → Common.
import EvmAsm.Evm64.EvmWordArith.MulCorrect

-- Pure EXP semantic target.
import EvmAsm.Evm64.EvmWordArith.Exp

-- ADDMOD/MULMOD helper: 2^256 mod N as an EvmWord (#91).

-- Div128Shift0 → Div128CallSkipClose → {Div128FinalAssembly +
-- Div128KnuthLower + Div128QuotientBounds → KnuthTheoremB →
-- {DivN4Overestimate, MaxTrialVacuity → CLZLemmas → DivN4Lemmas,
-- DenormLemmas}, DivMod.LoopSemantic → {DivMulSubCarry, DivAddbackCarry}}.
-- `DivN4DoubleAddback` imports `DivN4Overestimate`, which in turn imports
-- `DivAccumulate`, covering
-- DivRemainderBound → DivAddbackLimb → DivMulSubLimb → DivLimbBridge →
-- DivBridge → Normalization → MulSubChain → Div128Lemmas → MultiLimb →
-- Div → Common.
import EvmAsm.Evm64.EvmWordArith.Div128Shift0
import EvmAsm.Evm64.EvmWordArith.DivCorrect
import EvmAsm.Evm64.EvmWordArith.AddMod
import EvmAsm.Evm64.EvmWordArith.MulHigh
import EvmAsm.Evm64.EvmWordArith.MulMod

-- ModBridgeAssemble covers ModBridgeUtop → Val256ModBridge.
import EvmAsm.Evm64.EvmWordArith.ModBridgeAssemble

-- Standalone leaves:
import EvmAsm.Evm64.EvmWordArith.DivN4Lemmas
import EvmAsm.Evm64.EvmWordArith.SkipBorrowExtract
import EvmAsm.Evm64.EvmWordArith.DivN4DoubleAddback
import EvmAsm.Evm64.EvmWordArith.DivMulsubC3LeTwo
import EvmAsm.Evm64.EvmWordArith.DivN3MaxOverestimate
import EvmAsm.Evm64.EvmWordArith.DivN2MaxOverestimate
import EvmAsm.Evm64.EvmWordArith.DivBltC3Invariant
import EvmAsm.Evm64.EvmWordArith.DivMaxC3Invariant
import EvmAsm.Evm64.EvmWordArith.DivC3InvariantUnifiedCase
import EvmAsm.Evm64.EvmWordArith.DivN3NormVStructure
import EvmAsm.Evm64.EvmWordArith.DivN2NormVStructure
import EvmAsm.Evm64.EvmWordArith.DivBltBridge
import EvmAsm.Evm64.EvmWordArith.DivBltBridgeSpecializations
import EvmAsm.Evm64.EvmWordArith.DivV4TrialOverestimate
import EvmAsm.Evm64.EvmWordArith.DivV4TrialVal256Composition
import EvmAsm.Evm64.EvmWordArith.DivC3InvariantTrivials
import EvmAsm.Evm64.EvmWordArith.DivC3InvariantFromCarryNz
import EvmAsm.Evm64.EvmWordArith.AddbackBorrowExtract
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Algorithm
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase2bNoFireBound
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase2bFireBound
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase1bBound
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Un21Bound
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.QuotientBounds
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.UpperBound
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.ExactQuotient
import EvmAsm.Evm64.EvmWordArith.Div128CallSkipCloseV4
