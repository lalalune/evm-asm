/-
  EvmAsm.Codegen.Programs.Noop

  M18 stack-pop / push-zero / halt no-op handler builders. These
  20 opcodes share the same "trusted bytecode, no host state model"
  shape: pop the right number of EVM stack words, optionally push
  32 zero bytes, advance PC by 1 (or halt). Lifted out of
  `Programs/Evm.lean` per the file-size guard at the bottom of
  `EvmAsm/Codegen/Programs.lean`.

  Four builders are exported:
  - `haltHandlers` — RETURN, REVERT, INVALID, SELFDESTRUCT
  - `pushZeroHandlers` — CODESIZE, RETURNDATASIZE, BLOBBASEFEE,
    MSIZE, GAS
  - `popPushZeroHandlers` — BALANCE, CALLDATALOAD, EXTCODESIZE,
    EXTCODEHASH, BLOCKHASH, BLOBHASH
  - `copyNoopHandlers` — CALLDATACOPY, CODECOPY, EXTCODECOPY,
    RETURNDATACOPY, MCOPY

  All 20 opcodes ship with at least one spec-incompliance (returns
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

/-- M18 EVM-terminating opcodes (RETURN, REVERT, INVALID, SELFDESTRUCT).
    All halt the dispatcher loop by jumping to `.exit_label`. They
    differ only in stack-pop count and modelling.

    - **RETURN (0xf3)** / **REVERT (0xfd)**: pop `(offset, size)` (2
      words = 64 B). For our top-level dispatcher there's no caller
      to return data TO — the dispatcher's exit body
      (`evmAddEpilogue`) simply surfaces what's at the EVM stack top
      after the pop to OUTPUT_ADDR. Trusted test programs prefix a
      PUSH so this is deterministic.
    - **INVALID (0xfe)**: pop 0; just halt. Functionally identical
      to the dispatcher's `h_invalid` catch-all, but listed
      explicitly so the registry count and the opcode coverage table
      mark it as deliberately wired.
    - **SELFDESTRUCT (0xff)**: pop 1 (recipient address, 32 B). For
      our purposes the account isn't actually destroyed; just halt.

    All four use `body := []` and a `.custom` tail that inlines the
    pop (when any) + `j .exit_label`. Same shape as `stopHandler`. -/
def haltHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_RETURN", opcodes := [0xf3]
    , body := []
    , tail := .custom "  addi x12, x12, 64\n  j .exit_label" }
  , { label := "h_REVERT", opcodes := [0xfd]
    , body := []
    , tail := .custom "  addi x12, x12, 64\n  j .exit_label" }
  , { label := "h_INVALID", opcodes := [0xfe]
    , body := []
    , tail := .custom "  j .exit_label" }
  , { label := "h_SELFDESTRUCT", opcodes := [0xff]
    , body := []
    , tail := .custom "  addi x12, x12, 32\n  j .exit_label" } ]

/-- M18 push-zero handlers (CODESIZE, RETURNDATASIZE, BLOBBASEFEE,
    MSIZE, GAS). Each opcode pushes a single 32-byte zero value onto
    the EVM stack — no input, no output content.

    Body (5 instructions): decrement `x12` by 32 (push), then write
    four 8-byte zero limbs via `SD .x12 .x0 …`.

    **Known limitations** (documented in CODEGEN.md M18 narrative):
    - CODESIZE pushes 0 instead of the running code's length.
    - RETURNDATASIZE pushes 0 (no caller return-data buffer).
    - BLOBBASEFEE pushes 0 (no Dencun blob context in our `EvmEnv`
      yet).
    - MSIZE pushes 0 (memory-expansion bookkeeping deferred to
      issue #99).
    - GAS pushes 0 (no gas metering in the dispatcher). -/
def pushZeroHandlers : List OpcodeHandlerSpec :=
  let pushZeroBody : Program :=
    ADDI .x12 .x12 (-32) ;;
    SD .x12 .x0 0 ;;
    SD .x12 .x0 8 ;;
    SD .x12 .x0 16 ;;
    SD .x12 .x0 24
  [ { label := "h_CODESIZE", opcodes := [0x38]
    , body := pushZeroBody, tail := .advanceAndRet 1 }
  , { label := "h_RETURNDATASIZE", opcodes := [0x3d]
    , body := pushZeroBody, tail := .advanceAndRet 1 }
  , { label := "h_BLOBBASEFEE", opcodes := [0x4a]
    , body := pushZeroBody, tail := .advanceAndRet 1 }
  , { label := "h_MSIZE", opcodes := [0x59]
    , body := pushZeroBody, tail := .advanceAndRet 1 }
  , { label := "h_GAS", opcodes := [0x5a]
    , body := pushZeroBody, tail := .advanceAndRet 1 } ]

/-- M18 pop-and-push-zero handlers (BALANCE, CALLDATALOAD,
    EXTCODESIZE, EXTCODEHASH, BLOCKHASH, BLOBHASH). Each opcode pops
    one 32-byte input (e.g., an address or index) and pushes a
    32-byte zero value. Net EVM stack delta = 0.

    Body (4 instructions): overwrite the popped slot with 32 zero
    bytes — same shape as M17's `SLOAD`/`TLOAD`. No `x12` movement
    needed.

    **Known limitations**:
    - BALANCE always returns 0 (no account state model).
    - CALLDATALOAD always returns 0 (the dispatcher has no top-level
      calldata; EVM bytecode is loaded via `ziskemu -i`, not
      calldata).
    - EXTCODESIZE / EXTCODEHASH always return 0 (no external account
      model).
    - BLOCKHASH always returns 0 (no block history).
    - BLOBHASH always returns 0 (no Dencun blob context). -/
def popPushZeroHandlers : List OpcodeHandlerSpec :=
  let body : Program :=
    SD .x12 .x0 0 ;;
    SD .x12 .x0 8 ;;
    SD .x12 .x0 16 ;;
    SD .x12 .x0 24
  [ { label := "h_BALANCE", opcodes := [0x31]
    , body := body, tail := .advanceAndRet 1 }
  , { label := "h_CALLDATALOAD", opcodes := [0x35]
    , body := body, tail := .advanceAndRet 1 }
  , { label := "h_EXTCODESIZE", opcodes := [0x3b]
    , body := body, tail := .advanceAndRet 1 }
  , { label := "h_EXTCODEHASH", opcodes := [0x3f]
    , body := body, tail := .advanceAndRet 1 }
  , { label := "h_BLOCKHASH", opcodes := [0x40]
    , body := body, tail := .advanceAndRet 1 }
  , { label := "h_BLOBHASH", opcodes := [0x49]
    , body := body, tail := .advanceAndRet 1 } ]

/-- M18 copy-no-op handlers (CALLDATACOPY, CODECOPY, EXTCODECOPY,
    RETURNDATACOPY, MCOPY). Each opcode pops 3 or 4 stack values
    and would copy bytes into EVM memory. As no-ops we just drop the
    stack args.

    Body: a single `ADDI .x12 .x12 (popBytes)`. CALLDATACOPY /
    CODECOPY / RETURNDATACOPY / MCOPY pop 3 words = 96 bytes;
    EXTCODECOPY pops 4 = 128.

    **Known limitations**: the copies are dropped on the floor.
    Programs that copy into EVM memory and then MLOAD see whatever
    was there before (typically zero, since `evm_memory` is
    zero-initialised by the dispatcher's data section). For trusted
    programs that don't depend on these reads, this is correct. -/
def copyNoopHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_CALLDATACOPY", opcodes := [0x37]
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 96)
    , tail := .advanceAndRet 1 }
  , { label := "h_CODECOPY", opcodes := [0x39]
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 96)
    , tail := .advanceAndRet 1 }
  , { label := "h_EXTCODECOPY", opcodes := [0x3c]
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 128)
    , tail := .advanceAndRet 1 }
  , { label := "h_RETURNDATACOPY", opcodes := [0x3e]
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 96)
    , tail := .advanceAndRet 1 }
  , { label := "h_MCOPY", opcodes := [0x5e]
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 96)
    , tail := .advanceAndRet 1 } ]

end EvmAsm.Codegen
