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
  - `pushZeroHandlers` — CODESIZE (MSIZE/GAS and RETURNDATASIZE have real implementations)
  - `popPushZeroHandlers` — EXTCODESIZE
    (EXTCODEHASH, BLOBHASH, and BLOCKHASH have real implementations in Programs/Evm.lean)
  - `copyNoopHandlers` — CODECOPY
  - `returnDataHandlers` — RETURNDATASIZE and RETURNDATACOPY

  These opcodes ship with at least one spec-incompliance (returns
  zero / drops side effects) because the dispatcher has no model
  for the relevant state (accounts, calldata, block history, blob
  context, return-data buffers). Trusted bytecode that avoids
  introspecting those subsystems passes through correctly. See
  the CODEGEN.md M18 narrative for the full limitation list.
-/

import EvmAsm.Codegen.Dispatch
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

def haltHandlers : List OpcodeHandlerSpec :=
  [ -- RETURN. Pops (offset, size); keeps the legacy 32-byte prefix and
    -- also records up to 176 bytes plus length metadata at OUTPUT+64/+248.
    { label   := "h_RETURN"
    , opcodes := [0xf3]
    , preBody := stackUnderflowGuardAsm 2
    , body    := []
    , tail    := .custom (returnRevertTail 1) }
  , -- REVERT. Identical data path to RETURN; halt_kind = 2 and state logs roll back.
    { label   := "h_REVERT"
    , opcodes := [0xfd]
    , preBody := stackUnderflowGuardAsm 2
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
    , tail := .custom "  addi x12, x12, 32\n  j .exit_selfdestruct" } ]

/-- M18 push-zero handler for CODESIZE.
    The opcode pushes a single 32-byte zero value onto
    the EVM stack — no input, no output content.
    (MSIZE and GAS graduated to real env-cell-reading handlers in
    Programs/Evm.lean.)

    Body (5 instructions): decrement `x12` by 32 (push), then write
    four 8-byte zero limbs via `SD .x12 .x0 …`.

    **Known limitations** (documented in CODEGEN.md M18 narrative):
    - CODESIZE pushes 0 instead of the running code's length. -/
def pushZeroHandlers : List OpcodeHandlerSpec :=
  let pushZeroBody : Program :=
    ADDI .x12 .x12 (-32) ;;
    SD .x12 .x0 0 ;;
    SD .x12 .x0 8 ;;
    SD .x12 .x0 16 ;;
    SD .x12 .x0 24
  -- GAS (0x5a) graduated to a real handler in Programs/Evm.lean (M30) —
  -- it pushes env.gasRemaining maintained by the dispatch-loop gas charge.
  [ { label := "h_CODESIZE", opcodes := [0x38]
    , body := pushZeroBody, tail := .advanceAndRet 1 } ]

/-- M18 pop-and-push-zero handlers (EXTCODESIZE).
    This opcode pops one 32-byte input (an address) and pushes a 32-byte zero
    value. Net EVM stack delta = 0.

    Body (4 instructions): overwrite the popped slot with 32 zero
    bytes — same shape as M17's `SLOAD`/`TLOAD`. No `x12` movement
    needed.

    **Known limitations**:
    - EXTCODESIZE always returns 0 (no external code-byte model yet).

    **M21 update**: CALLDATALOAD (0x35) was removed from this group
    and now has a real implementation in `calldataHandlers` (see
    `Programs/Evm.lean`). It reads real calldata bytes from the
    `ziskemu -i` input region.

    **M28 update**: BLOBHASH (0x49) was moved to `blobContextHandlers`
    in `Programs/Evm.lean` with a real blob-hash-list implementation.

    **M29 update**: BLOCKHASH (0x40) was moved to `blockHashHandlers`
    in `Programs/Evm.lean` with a real block-history implementation.

    **M32 update**: BALANCE (0x31) was moved to `balanceWitnessHandlers`
    in `Programs/EvmBalance.lean` with a witness-backed implementation. -/
def popPushZeroHandlers : List OpcodeHandlerSpec :=
  let body : Program :=
    SD .x12 .x0 0 ;;
    SD .x12 .x0 8 ;;
    SD .x12 .x0 16 ;;
    SD .x12 .x0 24
  [ { label := "h_EXTCODESIZE", opcodes := [0x3b]
    , preBody := stackUnderflowGuardAsm 1
    , body := body, tail := .advanceAndRet 1 } ]

/-- M18 copy-no-op handler for CODECOPY.
    CODECOPY pops 3 stack words and would copy bytes into EVM memory.
    As a no-op we just drop the stack args.

    Body: a single `ADDI .x12 .x12 96`.

    **Known limitations**: the copies are dropped on the floor.
    Programs that copy into EVM memory and then MLOAD see whatever
    was there before (typically zero, since `evm_memory` is
    zero-initialised by the dispatcher's data section). For trusted
    programs that don't depend on these reads, this is correct.

    **M21 update**: CALLDATACOPY (0x37) was removed from this group
    and now has a real implementation in `calldataHandlers` (see
    `Programs/Evm.lean`).

    **M32 update**: RETURNDATACOPY (0x3e) moved to `returnDataHandlers`
    below and reads the dispatcher-maintained precompile return-data frame. -/
def copyNoopHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_CODECOPY", opcodes := [0x39]
    , preBody := stackUnderflowGuardAsm 3
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 96)
    , tail := .advanceAndRet 1 } ]

/-- Runtime RETURNDATASIZE / RETURNDATACOPY handlers backed by
    `evm_precompile_frame`. CALL/STATICCALL precompile paths store
    their return-data length at `+8` and up to 64 bytes at `+16`.
    Non-precompile, absent-account, CREATE, and CREATE2 paths clear
    the length to model an empty return-data buffer.

    RETURNDATACOPY follows execution-specs EIP-211 behavior for bounds:
    copying past the current buffer is an exceptional halt, not zero-fill.
    This first runtime slice retains a 64-byte prefix of child returndata, so
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
        "  li x18, 64\n" ++
        "  bltu x18, x19, .exit_invalid\n" ++
        "  addi x12, x12, 96\n" ++
        "  beqz x16, 2f\n" ++
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

/-- M19 child-frame opcodes (CREATE, CALL, CALLCODE, DELEGATECALL,
    CREATE2, STATICCALL). All ship as **pop-N + push-zero** no-ops:
    the dispatcher pops the EVM-spec input count, then writes 32
    zero bytes into the new top-of-stack slot (= "call failed" /
    "create returned address 0").

    Net stack delta per opcode (= pop − push, multiplied by 32):

    - **CREATE (0xf0)**: pops 3 (value, offset, size), pushes 1 (addr).
      Net = +64 bytes (= 2 × 32).
    - **CALL (0xf1)** / **CALLCODE (0xf2)**: pops 7 (gas, to, value,
      in_off, in_size, out_off, out_size), pushes 1 (success).
      Net = +192 (= 6 × 32).
    - **DELEGATECALL (0xf4)** / **STATICCALL (0xfa)**: pops 6 (gas,
      to, in_off, in_size, out_off, out_size), pushes 1 (success).
      Net = +160 (= 5 × 32).
    - **CREATE2 (0xf5)**: pops 4 (value, offset, size, salt),
      pushes 1 (addr). Net = +96 (= 3 × 32).

    EVM stack-arg ordering: `μ_s[0]` (top) is `gas`/`value` per the
    Yellow Paper; for our no-op the ordering doesn't matter because
    we drop everything.

    **M27 update**: CALL / STATICCALL now recognize target
    addresses 0x01..0x04 as the basic precompile frame surface.
    SHA256 (0x02) hashes input bytes through `zkvm_sha256`,
    IDENTITY (0x04) copies input bytes to caller output memory, and
    both push success = 1. ECRECOVER / RIPEMD160 remain success
    stubs in this slice; follow-up PRs wire their output semantics.

    **M27.1 update**: inactive near-zero addresses 0x12 and 0x101
    are not precompiles in the Amsterdam active set. Route them as
    absent-account calls with success = 1 and empty returndata so the
    precompile_absence fixtures do not stop at the dispatcher surface.

    **Known limitations** (documented in CODEGEN.md M19 narrative):
    - Non-precompile CALL / CALLCODE / DELEGATECALL / STATICCALL
      still return 0 (= "call failed"). No actual sub-frame
      execution.
    - ECRECOVER / RIPEMD160 CALL / STATICCALL targets currently
      return success without producing returndata.
    - CREATE / CREATE2 always return address 0 (= "deployment
      failed"). The would-be deployed code is not executed.
    - No frame stack / recursion. The dispatcher doesn't push a
      sub-frame, run called code, and resume. Real frame-stack
      design is deferred (likely tied to STF integration). -/
def childFrameHandlers : List OpcodeHandlerSpec :=
  let mkHandler (lbl : String) (op : Nat) (netPopBytes : Nat) : OpcodeHandlerSpec :=
    { label := lbl
    , opcodes := [op]
    , preBody := stackUnderflowGuardAsm (netPopBytes / evmStackWordBytes + 1) ++
               "\n  la x15, evm_precompile_frame\n  sd x0, 8(x15)"
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 netPopBytes) ;;
              SD .x12 .x0 0 ;;
              SD .x12 .x0 8 ;;
              SD .x12 .x0 16 ;;
              SD .x12 .x0 24
    , tail := .advanceAndRet 1 }
  let basicPrecompileCallTail
      (netPopBytes inOffsetOff inSizeOff outOffsetOff outSizeOff : Nat) : String :=
    -- Stack top at entry is the call gas word. The destination
    -- address is the next word for both CALL and STATICCALL. EVM
    -- address operands are masked to the low 160 bits: limb 1 and
    -- the low 32 bits of limb 2 participate in precompile dispatch,
    -- while bits 160..255 are ignored.
    "  ld x14, 32(x12)\n" ++
    "  ld x15, 40(x12)\n" ++
    "  bnez x15, 1f\n" ++
    "  ld x15, 48(x12)\n" ++
    "  slli x15, x15, 32\n" ++
    "  srli x15, x15, 32\n" ++
    "  bnez x15, 1f\n" ++
    "  li x15, 1\n" ++
    "  bltu x14, x15, 1f\n" ++
    "  li x15, 4\n" ++
    "  bgeu x15, x14, 11f\n" ++
    "  li x15, 0x12\n" ++
    "  beq x14, x15, 12f\n" ++
    "  li x15, 0x101\n" ++
    "  beq x14, x15, 12f\n" ++
    "  j 1f\n" ++
    "11:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  li x16, 2\n" ++
    "  beq x14, x16, 8f\n" ++
    "  li x16, 4\n" ++
    "  bne x14, x16, 7f\n" ++
    "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  sd x17, 8(x15)\n" ++       -- returndata length = full input size
    "  ld x18, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add x18, x13, x18\n" ++    -- x18 = identity input bytes
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++    -- x19 = caller output bytes
    -- Copy up to 64 bytes of returndata into the shared frame.
    "  mv x22, x18\n" ++
    "  addi x23, x15, 16\n" ++
    "  mv x24, x17\n" ++
    "  li x16, 64\n" ++
    "  bgeu x16, x24, 2f\n" ++
    "  mv x24, x16\n" ++
    "2:\n" ++
    "  beqz x24, 4f\n" ++
    "3:\n" ++
    "  lbu x16, 0(x22)\n" ++
    "  sb x16, 0(x23)\n" ++
    "  addi x22, x22, 1\n" ++
    "  addi x23, x23, 1\n" ++
    "  addi x24, x24, -1\n" ++
    "  bnez x24, 3b\n" ++
    -- Copy min(input_size, output_size) bytes to caller memory.
    "4:\n" ++
    "  mv x22, x17\n" ++
    "  ld x23, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  bgeu x23, x22, 5f\n" ++
    "  mv x22, x23\n" ++
    "5:\n" ++
    "  beqz x22, 7f\n" ++
    "6:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 6b\n" ++
    "7:\n" ++
    "  addi x12, x12, " ++ toString netPopBytes ++ "\n" ++
    "  li x14, 1\n" ++
    "  sd x14, 0(x12)\n" ++
    "  sd x0, 8(x12)\n" ++
    "  sd x0, 16(x12)\n" ++
    "  sd x0, 24(x12)\n" ++
    "  addi x10, x10, 1\n" ++
    "  j .dispatch_loop\n" ++
    -- SHA256: digest = sha256(memory[in_offset .. in_offset+in_size)).
    -- The wrapper uses the LP64 a0/a1/a2 registers, so save the
    -- dispatcher code and stack pointers before setting up arguments.
    "8:\n" ++
    "  li x16, 32\n" ++
    "  sd x16, 8(x15)\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld a1, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  ld x18, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x18\n" ++
    "  addi a2, x15, 16\n" ++
    "  jal x1, zkvm_sha256\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  ld x23, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  li x22, 32\n" ++
    "  bgeu x23, x22, 9f\n" ++
    "  mv x22, x23\n" ++
    "9:\n" ++
    "  beqz x22, 7b\n" ++
    "  addi x18, x15, 16\n" ++
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++
    "10:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 10b\n" ++
    "  j 7b\n" ++
    "12:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  j 7b\n" ++
    "1:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  sd x0, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  addi x12, x12, " ++ toString netPopBytes ++ "\n" ++
    "  sd x0, 0(x12)\n" ++
    "  sd x0, 8(x12)\n" ++
    "  sd x0, 16(x12)\n" ++
    "  sd x0, 24(x12)\n" ++
    "  addi x10, x10, 1\n" ++
    "  j .dispatch_loop"
  [ mkHandler "h_CREATE"        0xf0 64
  , { label := "h_CALL"
    , opcodes := [0xf1]
    , preBody := stackUnderflowGuardAsm 7
    , body := []
    , tail := .custom (basicPrecompileCallTail 192 96 128 160 192) }
  , mkHandler "h_CALLCODE"      0xf2 192
  , mkHandler "h_DELEGATECALL"  0xf4 160
  , mkHandler "h_CREATE2"       0xf5 96
  , { label := "h_STATICCALL"
    , opcodes := [0xfa]
    , preBody := stackUnderflowGuardAsm 6
    , body := []
    , tail := .custom (basicPrecompileCallTail 160 64 96 128 160) } ]

/-- M20 arithmetic no-op handlers.

    The original M20 placeholders covered MULMOD and EXP. Both have now moved
    to real dispatcher handlers in `EvmAsm/Codegen/Programs/Evm.lean`, so this
    list is intentionally empty and remains only to keep the registry assembly
    expression stable. -/
def arithNoopHandlers : List OpcodeHandlerSpec := []

end EvmAsm.Codegen
