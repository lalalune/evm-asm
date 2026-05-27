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

    **Known limitations** (documented in CODEGEN.md M19 narrative):
    - CALL / CALLCODE / DELEGATECALL / STATICCALL always return 0
      (= "call failed"). No actual sub-frame execution.
    - CREATE / CREATE2 always return address 0 (= "deployment
      failed"). The would-be deployed code is not executed.
    - No frame stack / recursion. The dispatcher doesn't push a
      sub-frame, run called code, and resume. Real frame-stack
      design is deferred (likely tied to STF integration). -/
def childFrameHandlers : List OpcodeHandlerSpec :=
  let mkHandler (lbl : String) (op : Nat) (netPopBytes : Nat) : OpcodeHandlerSpec :=
    { label := lbl
    , opcodes := [op]
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 netPopBytes) ;;
              SD .x12 .x0 0 ;;
              SD .x12 .x0 8 ;;
              SD .x12 .x0 16 ;;
              SD .x12 .x0 24
    , tail := .advanceAndRet 1 }
  [ mkHandler "h_CREATE"        0xf0 64
  , mkHandler "h_CALL"          0xf1 192
  , mkHandler "h_CALLCODE"      0xf2 192
  , mkHandler "h_DELEGATECALL"  0xf4 160
  , mkHandler "h_CREATE2"       0xf5 96
  , mkHandler "h_STATICCALL"    0xfa 160 ]

/-- M20 arithmetic no-op handlers (MULMOD, EXP). The last two
    unwired opcodes shipped as placeholders to **hit 100% opcode
    coverage**. Same pop-N + push-zero pattern as
    `childFrameHandlers` above, just with smaller pop counts.

    | Opcode | Byte | Pops | Pushes | Net pops × 32 |
    |---|---|---|---|---|
    | **MULMOD** | 0x09 | 3 (a, b, N) | 1 (result) | 64 |
    | **EXP**    | 0x0a | 2 (base, exponent) | 1 (result) | 32 |

    Both within the 12-bit signed ADDI immediate range.

    **Known limitations** (documented in CODEGEN.md M20 narrative):

    - **MULMOD** always returns 0. The verified body is a
      placeholder in `EvmAsm/Evm64/MulMod/Program.lean` (slice
      evm-asm-m4wu unscheduled). A future PR will swap in the
      real Knuth-style 512-bit + reduce-by-N body once it lands.
    - **EXP** always returns 0. **The verified body actually
      exists** (`evm_exp_msb_saved_bit_two_mul_fixed` in
      `EvmAsm/Evm64/Exp/Program.lean`, x19-callee-saved cursor
      design; ~84 instructions). The M21 PR after this one will
      wire it via the M10-style inline-callable composition
      pattern (~300–500 LOC: embed `mul_callable` in the
      dispatcher epilogue, pin JAL offsets for the squaring +
      conditional-multiply calls, use M9-style trampoline tail).

    Trusted bytecode that doesn't depend on MULMOD / EXP results
    continues to work correctly. -/
def arithNoopHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_MULMOD", opcodes := [0x09]
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 64) ;;
              SD .x12 .x0 0 ;;
              SD .x12 .x0 8 ;;
              SD .x12 .x0 16 ;;
              SD .x12 .x0 24
    , tail := .advanceAndRet 1 }
  , { label := "h_EXP", opcodes := [0x0a]
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 32) ;;
              SD .x12 .x0 0 ;;
              SD .x12 .x0 8 ;;
              SD .x12 .x0 16 ;;
              SD .x12 .x0 24
    , tail := .advanceAndRet 1 } ]

end EvmAsm.Codegen
