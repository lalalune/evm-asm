/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5Families

  N2 v5 iteration family: `iterN2V5` + `fullDivN2R{0,1,2}V5` + `fullDivN2C3V5`.
  Mirror of the v4 family (`FullPathN2V4Families`), with the per-digit trial
  quotient swapped from `divKTrialCallV4QHat` to `divKTrialCallV5QHat` (the only
  version-dependent component — the normalization, `iterWithDoubleAddback`,
  `iterN2Max`, and `mulsubN4` are version-agnostic).  Foundational schoolbook
  defs for the v5 n=2 DIV lane.  Bead `evm-asm-wbc4i.9.2`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4Families
import EvmAsm.Evm64.DivMod.LoopBody.TrialCallV5

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 n=2 per-digit iteration: the call path uses the v5 trial quotient
    `divKTrialCallV5QHat u2 u1 v1` (top two dividend limbs over the divisor's
    top limb `v1`); the max path is version-agnostic. -/
@[irreducible]
def iterN2V5 (bltu : Bool) (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  if bltu then
    iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
  else
    iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop

@[irreducible]
def fullDivN2R2V5 (bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN2NormV b0 b1 b2 b3
  let u := fullDivN2NormU a0 a1 a2 a3 b1
  iterN2V5 bltu_2 v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word)

@[irreducible]
def fullDivN2R1V5 (bltu_2 bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN2NormV b0 b1 b2 b3
  let u := fullDivN2NormU a0 a1 a2 a3 b1
  let r2 := fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  iterN2V5 bltu_1 v.1 v.2.1 v.2.2.1 v.2.2.2 u.2.1
    r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1

@[irreducible]
def fullDivN2R0V5 (bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN2NormV b0 b1 b2 b3
  let u := fullDivN2NormU a0 a1 a2 a3 b1
  let r1 := fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  iterN2V5 bltu_0 v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1

@[irreducible]
def fullDivN2C3V5 (bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word :=
  let v := fullDivN2NormV b0 b1 b2 b3
  let u := fullDivN2NormU a0 a1 a2 a3 b1
  let r1 := fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  if bltu_0 then
    (mulsubN4 (divKTrialCallV5QHat r1.2.2.1 r1.2.1 v.2.1)
      v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
  else
    (mulsubN4 (signExtend12 4095 : Word)
      v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2

end EvmAsm.Evm64
