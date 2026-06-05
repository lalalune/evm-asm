/-
  EvmAsm.Codegen.Programs.EvmExtcodecopy

  Runtime dispatcher EXTCODECOPY handler backed by account-witness code bytes.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.EvmMemoryGas

namespace EvmAsm.Codegen

/-! ## Runtime EXTCODECOPY witness opcode

    EXTCODECOPY (0x3c) reads account code bytes through the optional runtime
    account-witness context and writes directly into `evm_memory`. -/

/-- Copy an EVM stack address word into natural 20-byte address order.

    Stack bytes 0..19 hold the low 160-bit address little-endian; trie lookup
    helpers expect the big-endian byte string whose keccak selects the account
    path. `x12` is the EVM stack pointer and `t1` points at
    `ecc_address_scratch`. -/
private def extcodecopyWitnessAddressCopy : String :=
  String.intercalate "" <|
    (List.range 20).map fun i =>
      s!"  lbu t2, {19 - i}(x12)
  sb t2, {i}(t1)
"

/-- Raw dispatcher handler for EXTCODECOPY backed by
    `extcodecopy_at_header_state_root`.

    Stack contract from execution-specs Amsterdam `extcodecopy`:
      top word     : address
      second word  : memory_start_index
      third word   : code_start_index
      fourth word  : size

    The prelude charges the copy word gas plus destination memory expansion
    before mutation, matching execution-specs `extcodecopy`. The helper writes
    `size` bytes into `evm_memory + memory_start_index`, zero-padding
    missing/empty/past-end cases. This handler ignores helper status after the
    call because the helper pre-zeroes the requested output window before
    trie/code lookup. -/
private def extcodecopyWitnessTail : HandlerTail :=
  .custom <|
    "  ld x14, 32(x12)
" ++         -- memory_start_index
    "  ld x15, 96(x12)
" ++         -- size
    copyWordGasAsm "extcodecopy" "x15" "x16" "x17" "x18" ++
    updateActiveMemorySizeAsm "extcodecopy" "x14" "x15" "x16" "x17" "x18" "x6" true ++
    "  add x19, x13, x14
" ++       -- output ptr = evm_memory + memory_start
    "  la t1, ecc_address_scratch
" ++
    extcodecopyWitnessAddressCopy ++
    "  addi sp, sp, -32
" ++
    "  sd x10, 0(sp)
" ++
    "  sd x12, 8(sp)
" ++
    "  sd x13, 16(sp)
" ++
    "  la a0, ecc_address_scratch
" ++
    "  la a1, " ++ runtimeAccessAccountTableLabel ++ "
" ++
    "  la a2, " ++ runtimeAccessAccountCountLabel ++ "
" ++
    "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "
" ++
    "  jal ra, runtime_access_account_charge
" ++
    "  ld x10, 0(sp)
" ++
    "  ld x12, 8(sp)
" ++
    "  ld x13, 16(sp)
" ++
    "  addi sp, sp, 32
" ++
    "  ld t0, 608(x20)
" ++         -- witness.codes ptr
    "  la t1, eccp_codes_ptr
" ++
    "  sd t0, 0(t1)
" ++
    "  ld t0, 616(x20)
" ++         -- witness.codes len
    "  la t1, eccp_codes_len
" ++
    "  sd t0, 0(t1)
" ++
    "  addi sp, sp, -32
" ++
    "  sd x10, 0(sp)
" ++
    "  sd x12, 8(sp)
" ++
    "  sd x13, 16(sp)
" ++
    "  ld a0, 576(x20)
" ++         -- header ptr
    "  ld a1, 584(x20)
" ++         -- header len; zero means no witness context
    "  beqz a1, .Lrt_ecc_no_context
" ++
    "  ld a3, 64(x12)
" ++          -- code_start_index
    "  la a2, ecc_address_scratch
" ++
    "  mv a4, x15
" ++              -- size
    "  mv a5, x19
" ++              -- output buffer
    "  ld a6, 592(x20)
" ++         -- witness.state ptr
    "  ld a7, 600(x20)
" ++         -- witness.state len
    "  jal ra, extcodecopy_at_header_state_root
" ++
    "  ld x10, 0(sp)
" ++
    "  ld x12, 8(sp)
" ++
    "  ld x13, 16(sp)
" ++
    "  addi sp, sp, 32
" ++
    "  addi x12, x12, 128
" ++
    "  addi x10, x10, 1
" ++
    "  j .dispatch_loop
" ++
    ".Lrt_ecc_no_context:
" ++
    "  mv t0, x19
" ++
    "  mv t1, x15
" ++
    ".Lrt_ecc_zero_loop:
" ++
    "  beqz t1, .Lrt_ecc_zero_done
" ++
    "  sb zero, 0(t0)
" ++
    "  addi t0, t0, 1
" ++
    "  addi t1, t1, -1
" ++
    "  j .Lrt_ecc_zero_loop
" ++
    ".Lrt_ecc_zero_done:
" ++
    "  ld x10, 0(sp)
" ++
    "  ld x12, 8(sp)
" ++
    "  ld x13, 16(sp)
" ++
    "  addi sp, sp, 32
" ++
    "  addi x12, x12, 128
" ++
    "  addi x10, x10, 1
" ++
    "  j .dispatch_loop"

def extcodecopyWitnessHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_EXTCODECOPY"
    , opcodes := [0x3c]
    , preBody := stackUnderflowGuardAsm 4
    , body := []
    , tail := extcodecopyWitnessTail } ]

end EvmAsm.Codegen
