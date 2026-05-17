/-
  EvmAsm.Rv64.RLP.Phase4HintLen

  Phase 4 wrappers for the RLP decoder: read private-input metadata.

  Contains `read_input` (t0=0xF2) wrappers per the zkvm-standards C ABI.
  The legacy SP1 HINT_LEN (t0=0xF0) wrappers have been retired.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Rv64.HintSpecs
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64.Tactics

-- ============================================================================
-- read_input wrappers (zkvm-standards C ABI, t0 = 0xF2)
-- ============================================================================

/-- `read_input` Phase-4 program: ADDI+ADDI+LI+ECALL sequence that calls the
    zkvm-standards `read_input` (t0=0xF2), writing `inputBufBase` to
    `sp + ptr_ptr_off` and `privateInput.length` to `sp + size_ptr_off`.

    Parameters `ptr_ptr_off` / `size_ptr_off` are 12-bit signed SP-relative
    offsets for the two out-pointer cells allocated by the caller. -/
def rlp_phase4_read_input_len_prog
    (ptr_ptr_off size_ptr_off : BitVec 12) : Program :=
  [.ADDI .x10 .x12 ptr_ptr_off,
   .ADDI .x11 .x12 size_ptr_off,
   .LI   .x5  (BitVec.ofNat 64 0xF2),
   .ECALL]

theorem rlp_phase4_read_input_len_code_eq_ofProg
    (ptr_ptr_off size_ptr_off : BitVec 12) (base : Word) :
    CodeReq.ofProg base (rlp_phase4_read_input_len_prog ptr_ptr_off size_ptr_off) =
      (CodeReq.singleton base (.ADDI .x10 .x12 ptr_ptr_off)).union
        ((CodeReq.singleton (base + 4) (.ADDI .x11 .x12 size_ptr_off)).union
          ((CodeReq.singleton (base + 4 + 4) (.LI .x5 (BitVec.ofNat 64 0xF2))).union
            (CodeReq.singleton (base + 4 + 4 + 4) .ECALL))) := by
  simp only [rlp_phase4_read_input_len_prog, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil, CodeReq.union_empty_right]

theorem rlp_phase4_read_input_len_prog_length
    (ptr_ptr_off size_ptr_off : BitVec 12) :
    (rlp_phase4_read_input_len_prog ptr_ptr_off size_ptr_off).length = 4 := rfl

theorem rlp_phase4_read_input_len_prog_byte_length
    (ptr_ptr_off size_ptr_off : BitVec 12) :
    4 * (rlp_phase4_read_input_len_prog ptr_ptr_off size_ptr_off).length = 16 := rfl

/-- `read_input` Phase-4 spec: four-instruction wrapper that calls
    `read_input` (t0=0xF2) and writes (inputBufBase, privateInput.length)
    to the two SP-relative out-pointer cells.

    Pre:  x12 = sp (stack ptr); x10/x11/x5 caller-owned (any value);
          (sp + ptr_ptr_off) ↦ₘ old_ptr; (sp + size_ptr_off) ↦ₘ old_size;
          inputBufBaseIs buf_base; privateInputIs input.
    Post: (sp + ptr_ptr_off) ↦ₘ buf_base;
          (sp + size_ptr_off) ↦ₘ input.length;
          x10 = sp + ptr_ptr_off; x11 = sp + size_ptr_off; x5 = 0xF2;
          inputBufBaseIs and privateInputIs unchanged.
    Variant: takes specific initial register values for x10/x11/x5. -/
theorem rlp_phase4_read_input_len_spec_within_exact
    (ptr_ptr_off size_ptr_off : BitVec 12)
    (sp buf_base old_ptr old_size v10 v11 v5 : Word)
    (input : List (BitVec 8)) (base : Word)
    (hvalid_a0 : isValidDwordAccess (sp + signExtend12 ptr_ptr_off) = true)
    (hvalid_a1 : isValidDwordAccess (sp + signExtend12 size_ptr_off) = true) :
    cpsTripleWithin 4 base (base + 16)
      (CodeReq.ofProg base (rlp_phase4_read_input_len_prog ptr_ptr_off size_ptr_off))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x5 ↦ᵣ v5) **
        (base + 12 ↦ᵢ .ECALL) **
        ((sp + signExtend12 ptr_ptr_off) ↦ₘ old_ptr) **
        ((sp + signExtend12 size_ptr_off) ↦ₘ old_size) **
        inputBufBaseIs buf_base ** privateInputIs input)
      ((.x12 ↦ᵣ sp) **
        (.x10 ↦ᵣ sp + signExtend12 ptr_ptr_off) **
        (.x11 ↦ᵣ sp + signExtend12 size_ptr_off) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0xF2)) **
        (base + 12 ↦ᵢ .ECALL) **
        ((sp + signExtend12 ptr_ptr_off) ↦ₘ buf_base) **
        ((sp + signExtend12 size_ptr_off) ↦ₘ (BitVec.ofNat 64 input.length)) **
        inputBufBaseIs buf_base ** privateInputIs input) := by
  rw [rlp_phase4_read_input_len_code_eq_ofProg]
  have haddi1 := addi_spec_gen_within .x10 .x12 v10 sp ptr_ptr_off base (by nofun)
  have haddi2 := addi_spec_gen_within .x11 .x12 v11 sp size_ptr_off (base + 4) (by nofun)
  have hli3 := li_spec_gen_within .x5 v5 (BitVec.ofNat 64 0xF2) (base + 8) (by nofun)
  have hecall_base := ecall_read_input_spec_gen_within buf_base old_ptr old_size
    (sp + signExtend12 ptr_ptr_off) (sp + signExtend12 size_ptr_off)
    input (base + 4 + 4 + 4) hvalid_a0 hvalid_a1
  have hecall := cpsTripleWithin_frameR ((.x12 ↦ᵣ sp)) (by pcFree) hecall_base
  runBlock haddi1 haddi2 hli3 hecall


end EvmAsm.Rv64.RLP
