/-
  EvmAsm.Evm64.SDiv.LimbSpec

  Per-block / per-limb cpsTriple specs for SDIV sub-blocks (sign
  extraction, abs negation, callable-divide JAL, sign-correction).

  Per `OPCODE_TEMPLATE.md`, each sub-block gets exactly one cpsTriple
  lemma; later Compose slices chain them.
-/

import EvmAsm.Evm64.SDiv.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- CodeReq for `evm_sdiv_sign_bit_block` at byte offset `base`. -/
abbrev evm_sdiv_sign_bit_block_code
    (addrReg signReg : Reg) (topLimbOff : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_sdiv_sign_bit_block addrReg signReg topLimbOff)

/-- 2-instruction leaf spec: load `topLimbOff(addrReg)` into `signReg`,
    then shift right logically by 63 to expose the top bit. The
    post-state's `signReg` holds `topLimbVal >>> 63` (i.e. `0` for
    non-negative inputs and `1` for negative inputs).

    Requires `signReg ≠ x0`; separation of `(addrReg ↦ᵣ _)` and
    `(signReg ↦ᵣ _)` in the precondition implicitly forces
    `addrReg ≠ signReg`. -/
theorem evm_sdiv_sign_bit_block_spec_within
    (addrReg signReg : Reg) (topLimbOff : BitVec 12)
    (vAddr sOld topLimbVal : Word) (base : Word)
    (hsign_ne_x0 : signReg ≠ .x0) :
    let code := evm_sdiv_sign_bit_block_code addrReg signReg topLimbOff base
    cpsTripleWithin 2 base (base + 8) code
      ((addrReg ↦ᵣ vAddr) ** (signReg ↦ᵣ sOld) **
       ((vAddr + signExtend12 topLimbOff) ↦ₘ topLimbVal))
      ((addrReg ↦ᵣ vAddr) ** (signReg ↦ᵣ (topLimbVal >>> (63 : BitVec 6).toNat)) **
       ((vAddr + signExtend12 topLimbOff) ↦ₘ topLimbVal)) := by
  have L := ld_spec_gen_within signReg addrReg vAddr sOld topLimbVal
              topLimbOff base hsign_ne_x0
  have S := srli_spec_gen_same_within signReg topLimbVal (63 : BitVec 6)
              (base + 4) hsign_ne_x0
  runBlock L S

/-- CodeReq for `evm_sdiv_div_call_block` at byte offset `base`. -/
abbrev evm_sdiv_div_call_block_code (divOff : BitVec 21) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_sdiv_div_call_block divOff)

/-- 1-instruction leaf spec: near-`JAL` from SDIV into the unsigned
    `evm_div_callable` shim. Control transfers to
    `base + signExtend21 divOff` and `.x1` is updated with the return
    address `base + 4`. Argument-marshalling (placing both operands in
    the LP64 a-slots) is handled by the surrounding scaffold and is not
    part of this leaf cpsTriple. Mirrors `exp_square_block_spec_within`
    (`Evm64/Exp/LimbSpec.lean`). -/
theorem evm_sdiv_div_call_block_spec_within
    (divOff : BitVec 21) (vOld : Word) (base : Word) :
    let code := evm_sdiv_div_call_block_code divOff base
    cpsTripleWithin 1 base (base + signExtend21 divOff) code
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ (base + 4)) := by
  show cpsTripleWithin 1 base (base + signExtend21 divOff)
    (CodeReq.ofProg base (evm_sdiv_div_call_block divOff)) _ _
  rw [show CodeReq.ofProg base (evm_sdiv_div_call_block divOff) =
      CodeReq.singleton base (.JAL .x1 divOff) from CodeReq.ofProg_singleton]
  exact jal_spec_within .x1 vOld divOff base (by nofun)

end EvmAsm.Evm64
