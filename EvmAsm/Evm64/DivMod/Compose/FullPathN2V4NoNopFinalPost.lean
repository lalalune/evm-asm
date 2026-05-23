import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopSource

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Compact postcondition for the n=2 v4/no-NOP source path whose three loop
    iterations all take the callable trial-division path.  The definition keeps
    the final source-to-j0 theorem statement small enough for Lean to elaborate:
    the expanded form is the j=0 call post plus retained j=1/j=2 stored u4/q
    atoms and exact caller `x1`. -/
@[irreducible]
def loopN2CallCallCallSourceFinalPostNoX1 (sp base : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal scratchMem : Word) :
    Assertion :=
  let r2 := iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r1 := iterN2Call v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1
    r2.2.2.2.2.1
  let qHat0 := divKTrialCallV4QHat r1.2.2.1 r1.2.1 v1
  let dLo0 := divKTrialCallV4DLo v1
  let divUn00 := divKTrialCallV4Un0 r1.2.1
  let scratch2 := divKTrialCallV4ScratchOut u2 u1 v1 scratchMem
  let scratch1 := divKTrialCallV4ScratchOut r2.2.2.1 r2.2.1 v1 scratch2
  let scratch0 := divKTrialCallV4ScratchOut r1.2.2.1 r1.2.1 v1 scratch1
  let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  ((loopIterPostN2CallScratchNoX1 sp base (0 : Word)
    qHat0 dLo0 divUn00 scratch0
    v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
    (.x1 ↦ᵣ raVal)) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
      (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) **
      (qAddr2 ↦ₘ r2.1))))

theorem loopN2CallCallCallSourceFinalPostNoX1_unfold (sp base : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal scratchMem : Word) :
    loopN2CallCallCallSourceFinalPostNoX1 sp base
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal scratchMem =
    let r2 := iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := iterN2Call v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1
      r2.2.2.2.2.1
    let qHat0 := divKTrialCallV4QHat r1.2.2.1 r1.2.1 v1
    let dLo0 := divKTrialCallV4DLo v1
    let divUn00 := divKTrialCallV4Un0 r1.2.1
    let scratch2 := divKTrialCallV4ScratchOut u2 u1 v1 scratchMem
    let scratch1 := divKTrialCallV4ScratchOut r2.2.2.1 r2.2.1 v1 scratch2
    let scratch0 := divKTrialCallV4ScratchOut r1.2.2.1 r1.2.1 v1 scratch1
    let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    ((loopIterPostN2CallScratchNoX1 sp base (0 : Word)
      qHat0 dLo0 divUn00 scratch0
      v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
      (.x1 ↦ᵣ raVal)) **
      (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
        (qAddr1 ↦ₘ r1.1)) **
       ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) **
        (qAddr2 ↦ₘ r2.1)))) := by
  delta loopN2CallCallCallSourceFinalPostNoX1
  rfl

end EvmAsm.Evm64
