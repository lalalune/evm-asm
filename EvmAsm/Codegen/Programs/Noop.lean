/-
  EvmAsm.Codegen.Programs.Noop

  M18 stack-pop / push-zero / halt no-op handler builders. These
  16 opcodes share the same "trusted bytecode, no host state model"
  shape: pop the right number of EVM stack words, optionally push
  32 zero bytes, advance PC by 1 (or halt). Lifted out of
  `Programs/Evm.lean` per the file-size guard at the bottom of
  `EvmAsm/Codegen/Programs.lean`.

  Four builders are exported:
  - `haltHandlers` — RETURN, REVERT, INVALID, SELFDESTRUCT
  - `pushZeroHandlers` — empty (CODESIZE graduated to `codeHandlers` in M33;
    MSIZE/GAS/RETURNDATASIZE have real implementations)
  - `popPushZeroHandlers` — empty (BALANCE and EXTCODESIZE both have
    witness-backed implementations; EXTCODEHASH, BLOBHASH, and BLOCKHASH
    have real implementations in Programs/Evm.lean)
  - `copyNoopHandlers` — empty (CALLDATACOPY/CODECOPY/RETURNDATACOPY all
    have real implementations; CODECOPY graduated to `codeHandlers` in M33)
  - `returnDataHandlers` — RETURNDATASIZE and RETURNDATACOPY

  These opcodes ship with at least one spec-incompliance (returns
  zero / drops side effects) because the dispatcher has no model
  for the relevant state (accounts, calldata, block history, blob
  context, return-data buffers). Trusted bytecode that avoids
  introspecting those subsystems passes through correctly. See
  the CODEGEN.md M18 narrative for the full limitation list.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.EvmMemoryGas
import EvmAsm.Codegen.Programs.NoopChildFrame
import EvmAsm.Codegen.Programs.Selfdestruct
import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- M18 / M23 / M31 EVM-terminating opcodes (RETURN, REVERT,
    INVALID, SELFDESTRUCT). All halt the dispatcher loop.

    RETURN (0xf3) and REVERT (0xfd) read `offset_low` / `size_low`
    from the stack, keep the legacy `OUTPUT_ADDR[0..32]` return-data
    prefix and `halt_kind` at `OUTPUT_ADDR+32`, and also expose a
    wider diagnostic return-data surface inside ziskemu's 256-byte
    output dump:

    - `OUTPUT_ADDR+64`: requested low-u64 length.
    - `OUTPUT_ADDR+72`: copied return-data bytes, capped to 176 bytes.
    - `OUTPUT_ADDR+248`: copied length.

    The copied bytes share the later storage/event diagnostic window,
    so tests should assert either extended returndata or those diagnostics
    for a given case. `OUTPUT+40` and `OUTPUT+48` remain available for
    persistent/transient log lengths, and `OUTPUT+32` remains the
    halt/revert status byte range.

    INVALID and SELFDESTRUCT jump to shared dispatcher exceptional-exit
    blocks, preserving their distinct halt kinds. -/
private def returnRevertTail (kind : Nat) (rollbackAsm : String := "") : String :=
  "  ld x14, 0(x12)\n" ++          -- x14 = offset_low (low u64 of offset)
  "  ld x15, 32(x12)\n" ++         -- x15 = size_low
  "  li x16, 0xa0010000\n" ++      -- x16 = OUTPUT_ADDR
  "  sd x0, 0(x16)\n" ++           -- legacy OUTPUT[0..32] prefix
  "  sd x0, 8(x16)\n" ++
  "  sd x0, 16(x16)\n" ++
  "  sd x0, 24(x16)\n" ++
  "  addi x19, x16, 72\n" ++       -- zero extended returndata window
  "  li x21, 22\n" ++              -- 22 dwords = 176 bytes
  "1:\n" ++
  "  beqz x21, 2f\n" ++
  "  sd x0, 0(x19)\n" ++
  "  addi x19, x19, 8\n" ++
  "  addi x21, x21, -1\n" ++
  "  j 1b\n" ++
  "2:\n" ++
  "  mv x21, x15\n" ++             -- x21 = copied length, capped at 176
  "  li x22, 176\n" ++
  "  bgeu x22, x21, 3f\n" ++
  "  mv x21, x22\n" ++
  "3:\n" ++
  "  sd x15, 64(x16)\n" ++         -- requested length, u64 LE
  "  sd x21, 248(x16)\n" ++        -- copied length, u64 LE
  "  la x17, evm_memory\n" ++
  "  add x17, x17, x14\n" ++       -- source = &evm_memory[offset]
  "  addi x19, x16, 72\n" ++       -- destination = extended window
  "  mv x22, x21\n" ++
  "4:\n" ++
  "  beqz x22, 5f\n" ++
  "  lbu x23, 0(x17)\n" ++
  "  sb x23, 0(x19)\n" ++
  "  addi x17, x17, 1\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x22, x22, -1\n" ++
  "  j 4b\n" ++
  "5:\n" ++
  "  la x17, evm_memory\n" ++      -- repeat first min(size,32) bytes into legacy prefix
  "  add x17, x17, x14\n" ++
  "  mv x22, x15\n" ++
  "  li x21, 32\n" ++
  "  bgeu x21, x22, 6f\n" ++
  "  mv x22, x21\n" ++
  "6:\n" ++
  "  mv x19, x16\n" ++
  "7:\n" ++
  "  beqz x22, 8f\n" ++
  "  lbu x23, 0(x17)\n" ++
  "  sb x23, 0(x19)\n" ++
  "  addi x17, x17, 1\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x22, x22, -1\n" ++
  "  j 7b\n" ++
  "8:\n" ++
  s!"  li x17, {kind}\n" ++
  "  sd x17, 32(x16)\n" ++        -- halt_kind
  rollbackAsm ++
  "  j .exit_no_epilogue"

/-- Stage the popped SELFDESTRUCT beneficiary for later EIP-6780 state work.

    The dispatcher stack word is little-endian-limb encoded. SELFDESTRUCT
    addresses mask to the low 160 bits, so this copies bytes `stack[19..0]`
    into `evm_selfdestruct_beneficiary[0..19]` as canonical big-endian address
    bytes and ignores `stack[20..31]`. The current runtime env has no static
    context flag yet; the follow-up frame/runtime-env slice must reject
    SELFDESTRUCT before this state staging when static mode is exposed. -/
private def selfdestructTailAsm : String :=
  "  la x14, evm_selfdestruct_beneficiary\n" ++
  "  mv x15, x14\n" ++
  "  li x16, 4\n" ++
  ".L_selfdestruct_zero_scratch:\n" ++
  "  sd x0, 0(x15)\n" ++
  "  addi x15, x15, 8\n" ++
  "  addi x16, x16, -1\n" ++
  "  bnez x16, .L_selfdestruct_zero_scratch\n" ++
  "  addi x15, x12, 19\n" ++
  "  li x16, 20\n" ++
  ".L_selfdestruct_copy_beneficiary:\n" ++
  "  lbu x17, 0(x15)\n" ++
  "  sb x17, 0(x14)\n" ++
  "  addi x15, x15, -1\n" ++
  "  addi x14, x14, 1\n" ++
  "  addi x16, x16, -1\n" ++
  "  bnez x16, .L_selfdestruct_copy_beneficiary\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  la a0, evm_selfdestruct_beneficiary\n" ++
  "  la a1, " ++ runtimeAccessAccountTableLabel ++ "\n" ++
  "  la a2, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
  "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_charge\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  selfdestructNewAccountSurchargeAsm ++
  "  la x14, evm_selfdestruct_staged\n" ++
  "  li x15, 1\n" ++
  "  sd x15, 0(x14)\n" ++
  "  addi x12, x12, 32\n" ++
  "  j .exit_selfdestruct"

def haltHandlers : List OpcodeHandlerSpec :=
  [ -- RETURN. Pops (offset, size); keeps the legacy 32-byte prefix and
    -- also records up to 176 bytes plus length metadata at OUTPUT+64/+248.
    { label   := "h_RETURN"
    , opcodes := [0xf3]
    , preBody := stackUnderflowGuardAsm 2 ++ "\n" ++
                 returnRevertMemoryGasAsm "return"
    , body    := []
    , tail    := .custom (returnRevertTail 1) }
  , -- REVERT. Identical data path to RETURN; halt_kind = 2 and state logs roll back.
    { label   := "h_REVERT"
    , opcodes := [0xfd]
    , preBody := stackUnderflowGuardAsm 2 ++ "\n" ++
                 returnRevertMemoryGasAsm "revert"
    , body    := []
    , tail    := .custom <|
        returnRevertTail 2 <|
          -- M24: roll back storage logs. Persistent log truncates to
          -- the checkpoint captured at the end of the dispatcher
          -- prologue (post-preload); transient log resets to 0
          -- (transient storage starts empty at tx start). RETURN /
          -- STOP / INVALID / SELFDESTRUCT do NOT roll back — they
          -- commit successfully. M26 also restores receipt event logs
          -- to the transaction checkpoint.
          "  ld x17, 456(x20)\n" ++      -- persistentLogCheckpointOff
          "  sd x17, 448(x20)\n" ++      -- persistentLogLengthOff = checkpoint
          "  sd x0, 464(x20)\n" ++       -- transientLogLengthOff = 0
          "  ld x17, 480(x20)\n" ++      -- eventLogCheckpointOff
          "  sd x17, 472(x20)\n" }      -- eventLogLengthOff = checkpoint
  , -- INVALID (0xfe). M23.5: exceptional halt — zero result +
    -- halt_kind = 3 via the dispatcher's .exit_invalid_op block.
    { label := "h_INVALID", opcodes := [0xfe]
    , body := []
    , tail := .custom "  j .exit_invalid_op" }
  , -- SELFDESTRUCT (0xff). Pops 1 (recipient address). M23.5: normal
    -- halt with no return data — zero result + halt_kind = 5 via the
    -- dispatcher's .exit_selfdestruct block.
    { label := "h_SELFDESTRUCT", opcodes := [0xff]
    , preBody := stackUnderflowGuardAsm 1
    , body := []
    , tail := .custom selfdestructTailAsm } ]

/-- M18 push-zero handlers — now empty.

    All former members have graduated to real env-cell-reading handlers
    in `Programs/Evm.lean`:
    - MSIZE / GAS (M30) → `memoryMetadataHandlers` / `gasHandlers`.
    - RETURNDATASIZE (M32) → `returnDataHandlers`.
    - CODESIZE (M33) → `codeHandlers` (pushes the running bytecode length
      from `env.codeSize`). -/
def pushZeroHandlers : List OpcodeHandlerSpec :=
  []

/-- M18 pop-and-push-zero handlers (BALANCE and EXTCODESIZE).
    This opcode pops one 32-byte input (an address) and pushes a 32-byte zero
    value. Net EVM stack delta = 0.

    Body (4 instructions): overwrite the popped slot with 32 zero
    bytes — same shape as M17's `SLOAD`/`TLOAD`. No `x12` movement
    needed.

    **Known limitations**:
    - BALANCE and EXTCODESIZE both have witness-backed implementations.

    **M21 update**: CALLDATALOAD (0x35) was removed from this group
    and now has a real implementation in `calldataHandlers` (see
    `Programs/Evm.lean`). It reads real calldata bytes from the
    `ziskemu -i` input region.

    **M28 update**: BLOBHASH (0x49) was moved to `blobContextHandlers`
    in `Programs/Evm.lean` with a real blob-hash-list implementation.

    **M29 update**: BLOCKHASH (0x40) was moved to `blockHashHandlers`
    in `Programs/Evm.lean` with a real block-history implementation.

    **M32 update**: EXTCODESIZE (0x3b) and BALANCE (0x31) moved to
    witness-backed implementations (`EvmAccountWitness.lean` / `EvmBalance.lean`). -/
def popPushZeroHandlers : List OpcodeHandlerSpec :=
  []

/-- M18 copy-no-op handlers — now empty.

    All former members have graduated to real handlers in
    `Programs/Evm.lean`:
    - CALLDATACOPY (M21) → `calldataHandlers`.
    - RETURNDATACOPY (M32) → `returnDataHandlers` (EIP-211 bounds against
      the dispatcher-maintained precompile return-data frame).
    - CODECOPY (M33) → `codeHandlers` (verified `Code.evm_codecopy` byte
      loop over the running bytecode, zero-filling past `len(code)`). -/
def copyNoopHandlers : List OpcodeHandlerSpec :=
  []

/-- Runtime RETURNDATASIZE / RETURNDATACOPY handlers backed by
    `evm_precompile_frame`. CALL/STATICCALL precompile paths store
    their return-data length at `+8` and up to 256 bytes at `+16`.
    Non-precompile, absent-account, CREATE, and CREATE2 paths clear
    the length to model an empty return-data buffer.

    RETURNDATACOPY follows execution-specs EIP-211 behavior for bounds:
    copying past the current buffer is an exceptional halt, not zero-fill.
    This runtime slice retains a 256-byte prefix of child returndata, so
    copies beyond that retained prefix are also exceptional until a wider
    return-data arena lands. -/
def returnDataHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_RETURNDATASIZE", opcodes := [0x3d]
    , body := []
    , tail := .custom <|
        "  la x14, evm_precompile_frame\n" ++
        "  ld x15, 8(x14)\n" ++
        "  addi x12, x12, -32\n" ++
        "  sd x15, 0(x12)\n" ++
        "  sd x0, 8(x12)\n" ++
        "  sd x0, 16(x12)\n" ++
        "  sd x0, 24(x12)\n" ++
        "  addi x10, x10, 1\n" ++
        "  ret" }
  , { label := "h_RETURNDATACOPY", opcodes := [0x3e]
    , body := []
    , tail := .custom <|
        "  ld x14, 0(x12)\n" ++      -- memory_start_index
        "  ld x15, 32(x12)\n" ++     -- return_data_start_position
        "  ld x16, 64(x12)\n" ++     -- size
        "  la x17, evm_precompile_frame\n" ++
        "  ld x18, 8(x17)\n" ++      -- return-data length
        "  add x19, x15, x16\n" ++
        "  bltu x19, x15, .exit_invalid\n" ++
        "  bltu x18, x19, .exit_invalid\n" ++
        "  li x18, 256\n" ++
        "  bltu x18, x19, .exit_invalid\n" ++
        copyWordGasAsm "returndatacopy" "x16" "x17" "x18" "x19" ++
        updateActiveMemorySizeAsm "returndatacopy" "x14" "x16" "x17" "x18" "x19" "x6" true ++
        "  addi x12, x12, 96\n" ++
        "  beqz x16, 2f\n" ++
        "  la x17, evm_precompile_frame\n" ++
        "  addi x17, x17, 16\n" ++
        "  add x17, x17, x15\n" ++
        "  add x18, x13, x14\n" ++
        "1:\n" ++
        "  lbu x19, 0(x17)\n" ++
        "  sb x19, 0(x18)\n" ++
        "  addi x17, x17, 1\n" ++
        "  addi x18, x18, 1\n" ++
        "  addi x16, x16, -1\n" ++
        "  bnez x16, 1b\n" ++
        "2:\n" ++
        "  addi x10, x10, 1\n" ++
        "  ret" } ]


end EvmAsm.Codegen
