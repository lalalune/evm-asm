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
import EvmAsm.Codegen.Programs.PrecompileRuntime
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
    , tail := .custom "  addi x12, x12, 32\n  j .exit_selfdestruct" } ]

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

/-- M19 child-frame opcodes (CREATE, CALL, CALLCODE, DELEGATECALL,
    CREATE2, STATICCALL). CALL-family non-precompile paths still ship as
    **pop-N + push-zero** no-ops. CREATE-family paths decode operands and
    derive the target address, while later slices still own collision checks,
    child execution, and code-deposit descriptors.

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
    addresses 0x01..0x05 as the basic precompile frame surface.
    SHA256 (0x02) hashes input bytes through `zkvm_sha256`,
    IDENTITY (0x04) copies input bytes to caller output memory, and
    both push success = 1. SHA256 and IDENTITY charge their exact
    word-linear inner precompile gas through the shared helper.
    MODEXP (0x05) handles the zero-length-header shortcut and charges
    its 500 minimum gas before returning empty output. ECRECOVER /
    RIPEMD160 remain success stubs in this slice;
    follow-up PRs wire their output semantics.

    **M27.2 update**: CALL / STATICCALL also recognize BLS12-381 G1
    active precompile addresses 0x0b (G1 ADD) and 0x0c (G1 MSM).
    This first runtime slice implements the execution-specs input-length
    gates before the future accelerator body: G1 ADD requires exactly
    256 bytes; G1 MSM requires a nonzero multiple of 160 bytes.

    **M27.3 update**: CALL / STATICCALL also recognize BLS12-381 G2
    active precompile addresses 0x0d (G2 ADD) and 0x0e (G2 MSM).
    This first runtime slice applies the same execution-specs length
    gates before the future accelerator body: G2 ADD requires exactly
    512 bytes; G2 MSM requires a nonzero multiple of 288 bytes.

    **M27.4 update**: CALL / STATICCALL also recognize BLS12-381 pairing
    and map precompile addresses 0x0f (pairing), 0x10 (map-Fp-to-G1), and
    0x11 (map-Fp2-to-G2). Valid-length inputs invoke the linkable backend
    wrappers; current ziskemu safe-fails those wrappers, so EVM observes
    precompile failure until success-output slices land.

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
    - CREATE / CREATE2 derive the would-be target address and reject
      code-or-nonce collisions when account-witness context is attached,
      but the would-be deployed code is not executed or deposited yet.
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
  let createUnsupportedTail (netPopBytes : Nat) (hasSalt : Bool) : String :=
    -- Decode CREATE-family operands, derive the would-be target address using
    -- the shared CREATE/CREATE2 address helpers, and enforce the currently
    -- runtime-visible prechecks before later child/deposit execution slices.
    "  la x15, evm_precompile_frame\n" ++
    "  sd x0, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  ld x14, 0(x12)\n" ++    -- value low limb
    "  ld x15, 32(x12)\n" ++   -- offset low limb
    "  ld x16, 64(x12)\n" ++   -- size low limb
    "  la x18, create_init_offset\n" ++
    "  sd x15, 0(x18)\n" ++
    "  la x18, create_init_size\n" ++
    "  sd x16, 0(x18)\n" ++
    (if hasSalt then
      "  ld x17, 96(x12)\n"   -- salt low limb; full salt is converted below
     else
      "") ++
    -- A nonzero high limb in size is outside the current static memory
    -- envelope. Offset high limbs matter only for nonempty initcode.
    "  ld x18, 72(x12)\n" ++
    "  bnez x18, .exit_outofgas\n" ++
    "  ld x18, 80(x12)\n" ++
    "  bnez x18, .exit_outofgas\n" ++
    "  ld x18, 88(x12)\n" ++
    "  bnez x18, .exit_outofgas\n" ++
    "  beqz x16, 1f\n" ++
    "  ld x18, 40(x12)\n" ++
    "  bnez x18, .exit_outofgas\n" ++
    "  ld x18, 48(x12)\n" ++
    "  bnez x18, .exit_outofgas\n" ++
    "  ld x18, 56(x12)\n" ++
    "  bnez x18, .exit_outofgas\n" ++
    "  add x18, x15, x16\n" ++
    "  bltu x18, x15, .exit_outofgas\n" ++
    "  li x19, 0x8000\n" ++
    "  bltu x19, x18, .exit_outofgas\n" ++
    "1:\n" ++
    createInitcodeGasAsm
      (if hasSalt then "create2" else "create")
      "x16" "x18" "x19" "x23" hasSalt ++
    updateActiveMemorySizeAsm
      (if hasSalt then "create2_init" else "create_init")
      "x15" "x16" "x18" "x19" "x23" "x6" true ++
    -- Convert env.ADDRESS from stack-word representation to the canonical
    -- 20-byte big-endian input expected by address_compute_create*.
    "  la x18, create_sender_be\n" ++
    "  addi x19, x20, 19\n" ++
    "  li x23, 20\n" ++
    "2:\n" ++
    "  lbu x24, 0(x19)\n" ++
    "  sb x24, 0(x18)\n" ++
    "  addi x19, x19, -1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 2b\n" ++
    -- With account-witness context, enforce the executable-spec
    -- insufficient-balance zero-result branch before deriving success.
    "  ld a1, 584(x20)\n" ++
    "  beqz a1, 9f\n" ++
    "  la x18, create_value_be\n" ++
    "  addi x19, x12, 31\n" ++
    "  li x23, 32\n" ++
    "10:\n" ++
    "  lbu x24, 0(x19)\n" ++
    "  sb x24, 0(x18)\n" ++
    "  addi x19, x19, -1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 10b\n" ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld a0, 576(x20)\n" ++
    "  ld a1, 584(x20)\n" ++
    "  la a2, create_sender_be\n" ++
    "  ld a3, 592(x20)\n" ++
    "  ld a4, 600(x20)\n" ++
    "  la a5, create_balance_be\n" ++
    "  jal x1, balance_at_header_state_root\n" ++
    "  mv t0, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  bnez t0, 7f\n" ++
    "  la x18, create_balance_be\n" ++
    "  la x19, create_value_be\n" ++
    "  li x23, 32\n" ++
    "11:\n" ++
    "  lbu x24, 0(x18)\n" ++
    "  lbu x25, 0(x19)\n" ++
    "  bltu x24, x25, 7f\n" ++
    "  bltu x25, x24, 9f\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 11b\n" ++
    "9:\n" ++
    -- Default to nonce 0 when no account-witness context is attached.
    "  la x18, create_nonce\n" ++
    "  sd x0, 0(x18)\n" ++
    "  ld a1, 584(x20)\n" ++
    "  beqz a1, 3f\n" ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld a0, 576(x20)\n" ++
    "  la a2, create_sender_be\n" ++
    "  ld a3, 592(x20)\n" ++
    "  ld a4, 600(x20)\n" ++
    "  la a5, create_nonce\n" ++
    "  jal x1, nonce_at_header_state_root\n" ++
    "  mv t0, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  beqz t0, 3f\n" ++
    "  la x18, create_nonce\n" ++
    "  sd x0, 0(x18)\n" ++
    "3:\n" ++
    (if hasSalt then
      -- Convert the CREATE2 salt stack word to canonical 32-byte big-endian.
      "  la x18, create_salt_be\n" ++
      "  addi x19, x12, 127\n" ++
      "  li x23, 32\n" ++
      "4:\n" ++
      "  lbu x24, 0(x19)\n" ++
      "  sb x24, 0(x18)\n" ++
      "  addi x19, x19, -1\n" ++
      "  addi x18, x18, 1\n" ++
      "  addi x23, x23, -1\n" ++
      "  bnez x23, 4b\n" ++
      "  mv s9, x13\n" ++
      "  mv s10, x10\n" ++
      "  mv s11, x12\n" ++
      "  la a0, create_sender_be\n" ++
      "  la a1, create_salt_be\n" ++
      "  ld a2, create_init_offset\n" ++
      "  add a2, x13, a2\n" ++
      "  ld a3, create_init_size\n" ++
      "  la a4, create_address_be\n" ++
      "  jal x1, address_compute_create2\n" ++
      "  mv x13, s9\n" ++
      "  mv x10, s10\n" ++
      "  mv x12, s11\n"
     else
      "  mv s9, x13\n" ++
      "  mv s10, x10\n" ++
      "  mv s11, x12\n" ++
      "  la a0, create_sender_be\n" ++
      "  ld a1, create_nonce\n" ++
      "  la a2, create_address_be\n" ++
      "  jal x1, address_compute_create\n" ++
      "  mv x13, s9\n" ++
      "  mv x10, s10\n" ++
      "  mv x12, s11\n") ++
    -- If an account-witness context is attached, apply the EIP-684
    -- code-or-nonce collision check to the derived target address.
    "  ld a1, 584(x20)\n" ++
    "  beqz a1, 6f\n" ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld a0, 576(x20)\n" ++
    "  la a2, create_address_be\n" ++
    "  ld a3, 592(x20)\n" ++
    "  ld a4, 600(x20)\n" ++
    "  jal x1, has_code_or_nonce_at_header_state_root\n" ++
    "  mv t0, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  bnez t0, 7f\n" ++
    "  la x18, hcon_predicate\n" ++
    "  ld x18, 0(x18)\n" ++
    "  bnez x18, 7f\n" ++
    "6:\n" ++
    "  addi x12, x12, " ++ toString netPopBytes ++ "\n" ++
    -- Push the derived 160-bit address as an EVM stack word: low 160 bits in
    -- stack byte order, high 96 bits zero.
    "  sd x0, 0(x12)\n" ++
    "  sd x0, 8(x12)\n" ++
    "  sd x0, 16(x12)\n" ++
    "  sd x0, 24(x12)\n" ++
    "  la x18, create_address_be\n" ++
    "  addi x19, x18, 19\n" ++
    "  mv x22, x12\n" ++
    "  li x23, 20\n" ++
    "5:\n" ++
    "  lbu x24, 0(x19)\n" ++
    "  sb x24, 0(x22)\n" ++
    "  addi x19, x19, -1\n" ++
    "  addi x22, x22, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 5b\n" ++
    "  j 8f\n" ++
    "7:\n" ++
    "  addi x12, x12, " ++ toString netPopBytes ++ "\n" ++
    "  sd x0, 0(x12)\n" ++
    "  sd x0, 8(x12)\n" ++
    "  sd x0, 16(x12)\n" ++
    "  sd x0, 24(x12)\n" ++
    "8:\n" ++
    "  addi x10, x10, 1\n" ++
    "  j .dispatch_loop"
  let basicPrecompileCallTail
      (tag : String) (netPopBytes inOffsetOff inSizeOff outOffsetOff outSizeOff : Nat) : String :=
    -- Stack top at entry is the call gas word. The destination
    -- address is the next word for both CALL and STATICCALL. EVM
    -- address operands are masked to the low 160 bits: limb 1 and
    -- the low 32 bits of limb 2 participate in precompile dispatch,
    -- while bits 160..255 are ignored.
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  addi t0, x12, 32\n" ++
    "  la t1, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
    runtimeAccessWordToBe20Asm tag "t0" "t1" "t2" "t3" ++
    "  la a0, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
    "  la a1, " ++ runtimeAccessAccountTableLabel ++ "\n" ++
    "  la a2, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
    "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
    "  jal ra, runtime_access_account_charge\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    callMemoryExpansionGasAsm
      ("precompile_" ++ toString netPopBytes)
      inOffsetOff inSizeOff outOffsetOff outSizeOff ++
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
    "  li x15, 5\n" ++
    "  beq x14, x15, .Lmodexp_zero_header_" ++ toString netPopBytes ++ "\n" ++
    "  li x15, 0x06\n" ++
    "  beq x14, x15, .L" ++ tag ++ "_bn254_add\n" ++
    "  li x15, 0x07\n" ++
    "  beq x14, x15, .L" ++ tag ++ "_bn254_mul\n" ++
    "  li x15, 0x08\n" ++
    "  beq x14, x15, .L" ++ tag ++ "_bn254_pairing\n" ++
    "  li x15, 0x09\n" ++
    "  beq x14, x15, .L" ++ tag ++ "_blake2f\n" ++
    "  li x15, 0x0a\n" ++
    "  beq x14, x15, .L" ++ tag ++ "_kzg_point_eval\n" ++
    "  li x15, 0x0b\n" ++
    "  beq x14, x15, 13f\n" ++
    "  li x15, 0x0c\n" ++
    "  beq x14, x15, 14f\n" ++
    "  li x15, 0x0d\n" ++
    "  beq x14, x15, 15f\n" ++
    "  li x15, 0x0e\n" ++
    "  beq x14, x15, 16f\n" ++
    "  li x15, 0x0f\n" ++
    "  beq x14, x15, 17f\n" ++
    "  li x15, 0x10\n" ++
    "  beq x14, x15, 18f\n" ++
    "  li x15, 0x11\n" ++
    "  beq x14, x15, 19f\n" ++
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
    "  li x16, 1\n" ++
    "  beq x14, x16, 29f\n" ++
    "  li x16, 2\n" ++
    "  beq x14, x16, 8f\n" ++
    "  li x16, 4\n" ++
    "  bne x14, x16, 7f\n" ++
    "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
    chargePrecompileWordGasAsm 15 3 "x17" "x16" "x22" ++
    "  sd x17, 8(x15)\n" ++       -- returndata length = full input size
    "  ld x18, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add x18, x13, x18\n" ++    -- x18 = identity input bytes
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++    -- x19 = caller output bytes
    -- Copy up to 256 bytes of returndata into the shared frame.
    "  mv x22, x18\n" ++
    "  addi x23, x15, 16\n" ++
    "  mv x24, x17\n" ++
    "  li x16, 256\n" ++
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
    chargePrecompileWordGasAsm 60 12 "a1" "x16" "x22" ++
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
    -- ECRECOVER fixed gas, input staging, and v gate. Later slices consume
    -- valid staged r/s words for validation, backend recovery, and output.
    "29:\n" ++
    chargePrecompileGasConstAsm 3000 "x16" "x17" ++
    stageEcrecoverInputAsm inOffsetOff inSizeOff ++
    ecrecoverVGateAsm ++
    ecrecoverNonzeroRSGateAsm ++
    ecrecoverScalarOrderGateAsm ++
    "  j 7b\n" ++
    -- MODEXP zero-header shortcut. execution-specs decodes missing bytes as
    -- zero, so an empty input or all-zero 96-byte length header means
    -- baseLen = expLen = modulusLen = 0. That path charges the minimum 500
    -- gas and succeeds with empty returndata. Nonzero headers remain deferred
    -- to the full zkvm_modexp marshalling/backend slice.
    ".Lmodexp_zero_header_" ++ toString netPopBytes ++ ":\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  ld x18, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add x18, x13, x18\n" ++
    "  li x19, 96\n" ++
    "  bgeu x19, x17, .Lmodexp_scan_capped_" ++ toString netPopBytes ++ "\n" ++
    "  mv x17, x19\n" ++
    ".Lmodexp_scan_capped_" ++ toString netPopBytes ++ ":\n" ++
    "  beqz x17, .Lmodexp_zero_lengths_" ++ toString netPopBytes ++ "\n" ++
    ".Lmodexp_scan_loop_" ++ toString netPopBytes ++ ":\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  bnez x16, 1f\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x17, x17, -1\n" ++
    "  bnez x17, .Lmodexp_scan_loop_" ++ toString netPopBytes ++ "\n" ++
    ".Lmodexp_zero_lengths_" ++ toString netPopBytes ++ ":\n" ++
    chargePrecompileGasConstAsm 500 "x16" "x17" ++
    "  j 7b\n" ++
    -- BN254 G1 ADD: fixed 150 gas, two 64-byte zero-padded G1 inputs.
    -- The current runtime wrapper deterministic-fails until the host backend
    -- path is available, so valid calls surface precompile failure after gas.
    ".L" ++ tag ++ "_bn254_add:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    chargePrecompileGasConstAsm 150 "x16" "x17" ++
    stagePrecompileInputWindowAsm
      (tag ++ "_bn254_add_p1") inOffsetOff inSizeOff precompileFrameBls12G1Input0Off 0 64 ++
    stagePrecompileInputWindowAsm
      (tag ++ "_bn254_add_p2") inOffsetOff inSizeOff precompileFrameBls12G1Input1Off 64 64 ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    precompileFrameAddi "a0" precompileFrameBls12G1Input0Off ++
    precompileFrameAddi "a1" precompileFrameBls12G1Input1Off ++
    precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
    "  jal x1, zkvm_bn254_g1_add\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  bnez a0, 1f\n" ++
    precompileSuccess64FromFrameAsm
      (tag ++ "_bn254_add_success") outOffsetOff outSizeOff precompileFrameBls12G1OutputOff ++
    -- BN254 G1 MUL: fixed 6000 gas, one 64-byte point plus one 32-byte scalar.
    ".L" ++ tag ++ "_bn254_mul:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    chargePrecompileGasConstAsm 6000 "x16" "x17" ++
    stagePrecompileInputWindowAsm
      (tag ++ "_bn254_mul_point") inOffsetOff inSizeOff precompileFrameBls12G1Input0Off 0 64 ++
    stagePrecompileInputWindowAsm
      (tag ++ "_bn254_mul_scalar") inOffsetOff inSizeOff precompileFrameBls12G1Input1Off 64 32 ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    precompileFrameAddi "a0" precompileFrameBls12G1Input0Off ++
    precompileFrameAddi "a1" precompileFrameBls12G1Input1Off ++
    precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
    "  jal x1, zkvm_bn254_g1_mul\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  bnez a0, 1f\n" ++
    precompileSuccess64FromFrameAsm
      (tag ++ "_bn254_mul_success") outOffsetOff outSizeOff precompileFrameBls12G1OutputOff ++
    -- BN254 pairing: charge 45000 + 34000 * floor(input_size / 192), then
    -- reject non-multiple lengths as precompile failure with gas consumed.
    ".L" ++ tag ++ "_bn254_pairing:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  ld x18, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x16, 192\n" ++
    "  divu x22, x18, x16\n" ++
    "  li x16, 34000\n" ++
    "  mulhu x23, x22, x16\n" ++
    "  bnez x23, .exit_outofgas\n" ++
    "  mul x16, x22, x16\n" ++
    "  li x23, 45000\n" ++
    "  add x16, x16, x23\n" ++
    "  bltu x16, x23, .exit_outofgas\n" ++
    chargePrecompileGasAsm "x16" "x17" ++
    "  li x16, 192\n" ++
    "  remu x17, x18, x16\n" ++
    "  bnez x17, 1f\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld x17, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x17\n" ++
    "  mv a1, x22\n" ++
    precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
    "  jal x1, zkvm_bn254_pairing\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  bnez a0, 1f\n" ++
    precompileSuccessBoolFromFrameAsm
      (tag ++ "_bn254_pairing_success") outOffsetOff outSizeOff precompileFrameBls12G1OutputOff ++
    -- BLAKE2F: exact 213-byte payload, then charge gas equal to the BE
    -- rounds field, then validate the final flag. The current runtime wrapper
    -- deterministic-fails, but the path is ready to expose the updated 64-byte
    -- state from h once a success-producing backend is available.
    ".L" ++ tag ++ "_blake2f:\n" ++
    "  ld x16, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x17, 213\n" ++
    "  bne x16, x17, 1f\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    stagePrecompileInputWindowAsm
      (tag ++ "_blake2f_payload") inOffsetOff inSizeOff precompileFrameBls12G2InputOff 0 213 ++
    precompileFrameAddi "x18" precompileFrameBls12G2InputOff ++
    "  lbu x16, 0(x18)\n" ++
    "  slli x16, x16, 24\n" ++
    "  lbu x17, 1(x18)\n" ++
    "  slli x17, x17, 16\n" ++
    "  or x16, x16, x17\n" ++
    "  lbu x17, 2(x18)\n" ++
    "  slli x17, x17, 8\n" ++
    "  or x16, x16, x17\n" ++
    "  lbu x17, 3(x18)\n" ++
    "  or x16, x16, x17\n" ++
    chargePrecompileGasAsm "x16" "x17" ++
    "  lbu x17, 212(x18)\n" ++
    "  li x22, 1\n" ++
    "  bltu x22, x17, 1f\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  mv a0, x16\n" ++
    precompileFrameAddi "a1" (precompileFrameBls12G2InputOff + 4) ++
    precompileFrameAddi "a2" (precompileFrameBls12G2InputOff + 68) ++
    precompileFrameAddi "a3" (precompileFrameBls12G2InputOff + 196) ++
    "  mv a4, x17\n" ++
    "  jal x1, zkvm_blake2f\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  bnez a0, 1f\n" ++
    precompileSuccess64FromFrameAsm
      (tag ++ "_blake2f_success") outOffsetOff outSizeOff (precompileFrameBls12G2InputOff + 4) ++
    -- KZG point evaluation: execution-specs rejects non-192-byte input before
    -- gas, then charges fixed 50000 gas before hash/proof validation.
    ".L" ++ tag ++ "_kzg_point_eval:\n" ++
    "  ld x16, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x17, 192\n" ++
    "  bne x16, x17, 1f\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    chargePrecompileGasConstAsm 50000 "x16" "x17" ++
    stagePrecompileInputWindowAsm
      (tag ++ "_kzg_payload") inOffsetOff inSizeOff precompileFrameBls12G2InputOff 0 192 ++
    kzgVersionedHashGateAsm ++
    "  sb x0, " ++ toString precompileFrameBls12G2OutputOff ++ "(x15)\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    precompileFrameAddi "a0" (precompileFrameBls12G2InputOff + 96) ++
    precompileFrameAddi "a1" (precompileFrameBls12G2InputOff + 32) ++
    precompileFrameAddi "a2" (precompileFrameBls12G2InputOff + 64) ++
    precompileFrameAddi "a3" (precompileFrameBls12G2InputOff + 144) ++
    precompileFrameAddi "a4" precompileFrameBls12G2OutputOff ++
    "  jal x1, zkvm_kzg_point_eval\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  bnez a0, 1f\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  lbu x16, " ++ toString precompileFrameBls12G2OutputOff ++ "(x15)\n" ++
    "  beqz x16, 1f\n" ++
    precompileSuccessKzgPointEvalAsm
      (tag ++ "_kzg_point_eval_success") outOffsetOff outSizeOff ++
    "12:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  j 7b\n" ++
    -- BLS12-381 G1 ADD: execution-specs rejects unless calldata length is 256.
    -- Valid-length input invokes the linkable backend wrapper. Current ziskemu
    -- routes this through a deterministic safe-fail shim, which surfaces EVM
    -- precompile failure instead of placeholder success.
    "13:\n" ++
    "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x16, 256\n" ++
    "  bne x17, x16, 1f\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    precompileFrameAddi "a0" precompileFrameBls12G1Input0Off ++
    precompileFrameAddi "a1" precompileFrameBls12G1Input1Off ++
    precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
    "  jal x1, zkvm_bls12_g1_add\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  bnez a0, 1f\n" ++
    -- EIP-2537 `g1_to_bytes`: each compact 48-byte coordinate is left-padded
    -- to a 64-byte big-endian field element.
    "  addi x18, x15, 16\n" ++
    "  li x22, 16\n" ++
    "20:\n" ++
    "  sb x0, 0(x18)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 20b\n" ++
    precompileFrameAddi "x18" precompileFrameBls12G1OutputOff ++
    "  addi x19, x15, 32\n" ++
    "  li x22, 48\n" ++
    "21:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 21b\n" ++
    "  addi x18, x15, 80\n" ++
    "  li x22, 16\n" ++
    "22:\n" ++
    "  sb x0, 0(x18)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 22b\n" ++
    precompileFrameAddi "x18" (precompileFrameBls12G1OutputOff + 48) ++
    "  addi x19, x15, 96\n" ++
    "  li x22, 48\n" ++
    "23:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 23b\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  li x16, 128\n" ++
    "  sd x16, 8(x15)\n" ++
    "  j 7b\n" ++
    -- BLS12-381 G1 MSM: execution-specs rejects empty input and non-160
    -- multiples before charging gas or invoking curve arithmetic. Valid-length
    -- input invokes the linkable backend wrapper; the current safe-fail shim
    -- surfaces EVM precompile failure instead of placeholder success.
    "14:\n" ++
    "  ld x18, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  beqz x18, 1f\n" ++
    "  li x16, 160\n" ++
    "  remu x17, x18, x16\n" ++
    "  bnez x17, 1f\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    precompileFrameAddi "a0" precompileFrameBls12G1Input0Off ++
    "  divu a1, x18, x16\n" ++
    precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
    "  jal x1, zkvm_bls12_g1_msm\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  bnez a0, 1f\n" ++
    -- Pack the compact accelerator G1 result into EIP-2537 returndata:
    -- 16 zero bytes + 48-byte x coordinate + 16 zero bytes + 48-byte y coordinate.
    "  sd x0, 16(x15)\n" ++
    "  sd x0, 24(x15)\n" ++
    precompileFrameAddi "x17" precompileFrameBls12G1OutputOff ++
    "  addi x18, x15, 32\n" ++
    "  li x19, 48\n" ++
    "20:\n" ++
    "  lbu x20, 0(x17)\n" ++
    "  sb x20, 0(x18)\n" ++
    "  addi x17, x17, 1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, -1\n" ++
    "  bnez x19, 20b\n" ++
    "  sd x0, 80(x15)\n" ++
    "  sd x0, 88(x15)\n" ++
    precompileFrameAddi "x17" (precompileFrameBls12G1OutputOff + 48) ++
    "  addi x18, x15, 96\n" ++
    "  li x19, 48\n" ++
    "21:\n" ++
    "  lbu x20, 0(x17)\n" ++
    "  sb x20, 0(x18)\n" ++
    "  addi x17, x17, 1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, -1\n" ++
    "  bnez x19, 21b\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  li x16, 128\n" ++
    "  sd x16, 8(x15)\n" ++
    "  j 7b\n" ++
    -- BLS12-381 G2 ADD: execution-specs rejects unless calldata length is 512.
    -- Valid-length input invokes the linkable backend wrapper. Current ziskemu
    -- routes this through a deterministic safe-fail shim, which surfaces EVM
    -- precompile failure instead of placeholder success.
    "15:\n" ++
    "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x16, 512\n" ++
    "  bne x17, x16, 1f\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    precompileFrameAddi "a0" precompileFrameBls12G2AddInput0Off ++
    precompileFrameAddi "a1" precompileFrameBls12G2AddInput1Off ++
    precompileFrameAddi "a2" precompileFrameBls12G2AddOutputOff ++
    "  jal x1, zkvm_bls12_g2_add\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  bnez a0, 1f\n" ++
    -- EIP-2537 `g2_to_bytes`: each compact 48-byte FQ component is left-padded
    -- to a 64-byte big-endian field element.
    "  addi x18, x15, 16\n" ++
    precompileFrameAddi "x19" precompileFrameBls12G2AddOutputOff ++
    "  li x23, 4\n" ++
    "20:\n" ++
    "  li x22, 16\n" ++
    "21:\n" ++
    "  sb x0, 0(x18)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 21b\n" ++
    "  li x22, 48\n" ++
    "22:\n" ++
    "  lbu x16, 0(x19)\n" ++
    "  sb x16, 0(x18)\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 22b\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 20b\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  li x16, 256\n" ++
    "  sd x16, 8(x15)\n" ++
    "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  li x23, 256\n" ++
    "  bgeu x22, x23, 23f\n" ++
    "  mv x23, x22\n" ++
    "23:\n" ++
    "  beqz x23, 7b\n" ++
    "  addi x18, x15, 16\n" ++
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++
    "24:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 24b\n" ++
    "  j 7b\n" ++
    -- BLS12-381 G2 MSM: execution-specs rejects empty input and non-288
    -- multiples before charging gas or invoking curve arithmetic. Valid-length
    -- input invokes the linkable backend wrapper; the current safe-fail shim
    -- surfaces EVM precompile failure instead of placeholder success.
    "16:\n" ++
    "  ld x18, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  beqz x18, 1f\n" ++
    "  li x16, 288\n" ++
    "  remu x17, x18, x16\n" ++
    "  bnez x17, 1f\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    precompileFrameAddi "a0" precompileFrameBls12G2InputOff ++
    "  divu a1, x18, x16\n" ++
    precompileFrameAddi "a2" precompileFrameBls12G2OutputOff ++
    "  jal x1, zkvm_bls12_g2_msm\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  bnez a0, 1f\n" ++
    -- EIP-2537 `g2_to_bytes`: each compact 48-byte FQ component is left-padded
    -- to a 64-byte big-endian field element.
    "  addi x18, x15, 16\n" ++
    precompileFrameAddi "x19" precompileFrameBls12G2OutputOff ++
    "  li x23, 4\n" ++
    "20:\n" ++
    "  li x22, 16\n" ++
    "21:\n" ++
    "  sb x0, 0(x18)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 21b\n" ++
    "  li x22, 48\n" ++
    "22:\n" ++
    "  lbu x16, 0(x19)\n" ++
    "  sb x16, 0(x18)\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 22b\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 20b\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  li x16, 256\n" ++
    "  sd x16, 8(x15)\n" ++
    "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  li x23, 256\n" ++
    "  bgeu x22, x23, 23f\n" ++
    "  mv x23, x22\n" ++
    "23:\n" ++
    "  beqz x23, 7b\n" ++
    "  addi x18, x15, 16\n" ++
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++
    "24:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 24b\n" ++
    "  j 7b\n" ++
    -- BLS12-381 pairing: execution-specs rejects empty input and non-384
    -- multiples before invoking pairing arithmetic.
    "17:\n" ++
    "  ld x18, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  beqz x18, 1f\n" ++
    "  li x16, 384\n" ++
    "  remu x17, x18, x16\n" ++
    "  bnez x17, 1f\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld x17, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x17\n" ++
    "  divu a1, x18, x16\n" ++
    precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
    "  jal x1, zkvm_bls12_pairing\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  bnez a0, 1f\n" ++
    -- EIP-2537 pairing returns a 32-byte boolean word: 31 zero bytes followed
    -- by the backend `verified` byte.
    "  sd x0, 16(x15)\n" ++
    "  sd x0, 24(x15)\n" ++
    "  sd x0, 32(x15)\n" ++
    "  sd x0, 40(x15)\n" ++
    "  lbu x16, " ++ toString precompileFrameBls12G1OutputOff ++ "(x15)\n" ++
    "  sb x16, 47(x15)\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  li x16, 32\n" ++
    "  sd x16, 8(x15)\n" ++
    "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  li x23, 32\n" ++
    "  bgeu x22, x23, 22f\n" ++
    "  mv x23, x22\n" ++
    "22:\n" ++
    "  beqz x23, 7b\n" ++
    "  addi x18, x15, 16\n" ++
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++
    "23:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 23b\n" ++
    "  j 7b\n" ++
    -- BLS12-381 map-Fp-to-G1: execution-specs requires exactly one
    -- 64-byte Fp field element; the compact 48-byte field payload starts
    -- after the 16-byte EIP-2537 zero pad.
    "18:\n" ++
    "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x16, 64\n" ++
    "  bne x17, x16, 1f\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld x18, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add x18, x13, x18\n" ++
    "  addi a0, x18, 16\n" ++
    precompileFrameAddi "a1" precompileFrameBls12G1OutputOff ++
    "  jal x1, zkvm_bls12_map_fp_to_g1\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  bnez a0, 1f\n" ++
    -- EIP-2537 `g1_to_bytes`: each compact 48-byte coordinate is left-padded
    -- to a 64-byte big-endian field element.
    "  sd x0, 16(x15)\n" ++
    "  sd x0, 24(x15)\n" ++
    precompileFrameAddi "x17" precompileFrameBls12G1OutputOff ++
    "  addi x18, x15, 32\n" ++
    "  li x19, 48\n" ++
    "34:\n" ++
    "  lbu x16, 0(x17)\n" ++
    "  sb x16, 0(x18)\n" ++
    "  addi x17, x17, 1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, -1\n" ++
    "  bnez x19, 34b\n" ++
    "  sd x0, 80(x15)\n" ++
    "  sd x0, 88(x15)\n" ++
    precompileFrameAddi "x17" (precompileFrameBls12G1OutputOff + 48) ++
    "  addi x18, x15, 96\n" ++
    "  li x19, 48\n" ++
    "35:\n" ++
    "  lbu x16, 0(x17)\n" ++
    "  sb x16, 0(x18)\n" ++
    "  addi x17, x17, 1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, -1\n" ++
    "  bnez x19, 35b\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  li x16, 128\n" ++
    "  sd x16, 8(x15)\n" ++
    "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  li x23, 128\n" ++
    "  bgeu x22, x23, 36f\n" ++
    "  mv x23, x22\n" ++
    "36:\n" ++
    "  beqz x23, 7b\n" ++
    "  addi x18, x15, 16\n" ++
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++
    "37:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 37b\n" ++
    "  j 7b\n" ++
    -- BLS12-381 map-Fp2-to-G2: execution-specs requires exactly one
    -- 128-byte Fp2 element. Project the two compact 48-byte Fp chunks into
    -- the G2-class compact input lane before calling the backend.
    "19:\n" ++
    "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x16, 128\n" ++
    "  bne x17, x16, 1f\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  ld x18, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add x18, x13, x18\n" ++
    "  addi x19, x18, 16\n" ++
    precompileFrameAddi "x23" precompileFrameBls12G2InputOff ++
    "  li x22, 48\n" ++
    "20:\n" ++
    "  lbu x16, 0(x19)\n" ++
    "  sb x16, 0(x23)\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 20b\n" ++
    "  addi x19, x18, 80\n" ++
    "  li x22, 48\n" ++
    "21:\n" ++
    "  lbu x16, 0(x19)\n" ++
    "  sb x16, 0(x23)\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 21b\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    precompileFrameAddi "a0" precompileFrameBls12G2InputOff ++
    precompileFrameAddi "a1" precompileFrameBls12G2OutputOff ++
    "  jal x1, zkvm_bls12_map_fp2_to_g2\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  bnez a0, 1f\n" ++
    -- EIP-2537 `g2_to_bytes`: each compact 48-byte FQ component is left-padded
    -- to a 64-byte big-endian field element.
    "  addi x18, x15, 16\n" ++
    precompileFrameAddi "x19" precompileFrameBls12G2OutputOff ++
    "  li x23, 4\n" ++
    "34:\n" ++
    "  li x22, 16\n" ++
    "35:\n" ++
    "  sb x0, 0(x18)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 35b\n" ++
    "  li x22, 48\n" ++
    "36:\n" ++
    "  lbu x16, 0(x19)\n" ++
    "  sb x16, 0(x18)\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 36b\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 34b\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  li x16, 256\n" ++
    "  sd x16, 8(x15)\n" ++
    "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  li x23, 256\n" ++
    "  bgeu x22, x23, 37f\n" ++
    "  mv x23, x22\n" ++
    "37:\n" ++
    "  beqz x23, 7b\n" ++
    "  addi x18, x15, 16\n" ++
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++
    "38:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 38b\n" ++
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
  [ { label := "h_CREATE"
    , opcodes := [0xf0]
    , preBody := stackUnderflowGuardAsm 3 ++ "\n"
    , body := []
    , tail := .custom (createUnsupportedTail 64 false) }
  , { label := "h_CALL"
    , opcodes := [0xf1]
    , preBody := stackUnderflowGuardAsm 7 ++ "\n"
    , body := []
    , tail := .custom (basicPrecompileCallTail "call_target" 192 96 128 160 192) }
  , { mkHandler "h_CALLCODE" 0xf2 192 with
      preBody := stackUnderflowGuardAsm 7 ++ "\n" }
  , { mkHandler "h_DELEGATECALL" 0xf4 160 with
      preBody := stackUnderflowGuardAsm 6 ++ "\n" }
  , { label := "h_CREATE2"
    , opcodes := [0xf5]
    , preBody := stackUnderflowGuardAsm 4 ++ "\n"
    , body := []
    , tail := .custom (createUnsupportedTail 96 true) }
  , { label := "h_STATICCALL"
    , opcodes := [0xfa]
    , preBody := stackUnderflowGuardAsm 6 ++ "\n"
    , body := []
    , tail := .custom (basicPrecompileCallTail "staticcall_target" 160 64 96 128 160) } ]

/-- M20 arithmetic no-op handlers.

    The original M20 placeholders covered MULMOD and EXP. Both have now moved
    to real dispatcher handlers in `EvmAsm/Codegen/Programs/Evm.lean`, so this
    list is intentionally empty and remains only to keep the registry assembly
    expression stable. -/
def arithNoopHandlers : List OpcodeHandlerSpec := []

end EvmAsm.Codegen
