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

/-- M18 / M23 EVM-terminating opcodes (RETURN, REVERT, INVALID,
    SELFDESTRUCT). All halt the dispatcher loop.

    **M23 update**: RETURN (0xf3) and REVERT (0xfd) graduate from
    M18 no-ops (which just popped args and ran `evmAddEpilogue`,
    surfacing whatever stack top happened to be left behind) to
    real bodies that:
      1. Read `offset_low` / `size_low` (low u64 limbs) from the
         stack.
      2. Zero-fill `OUTPUT_ADDR[0..32]`.
      3. Byte-copy `min(size_low, 32)` bytes from
         `evm_memory + offset_low` into `OUTPUT_ADDR`.
      4. Write `halt_kind` (1 = RETURN, 2 = REVERT) at
         `OUTPUT_ADDR + 32`.
      5. Jump to `.exit_no_epilogue` (the M23-added label that
         skips `evmAddEpilogue`'s clobbering stack-top copy).

    INVALID (0xfe) and SELFDESTRUCT (0xff) continue to flow through
    `.exit_label` → `evmAddEpilogue`, inheriting `halt_kind = 0`.
    A follow-up PR can tag them with distinct kinds (3 / 4).

    ### EVM stack contracts (RETURN / REVERT)

    Top word = `offset` (256-bit), second word = `size` (256-bit).
    M23 reads only the low u64 of each; tests must keep
    offset / size < 2^64 (always true if they fit in the 32 KiB
    `evm_memory` block).

    ### Inline-asm conventions

    Numeric local labels (`1:`, `1b`, `1f`, …) — unique-per-use
    across the emitted file (same convention M22 storage scan
    loops use), so RETURN and REVERT can reuse label numbers
    without collision.

    ### Known limitations

    - **Returndata clamped to 32 bytes.** Larger payloads are
      silently truncated. A future PR can extend the OUTPUT
      layout with a length prefix or wider region.
    - **No INVALID/SELFDESTRUCT halt-kind tagging.** Both inherit
      `halt_kind = 0` from `evmAddEpilogue`. Follow-up PR. -/
def haltHandlers : List OpcodeHandlerSpec :=
  [ -- M23 real RETURN. Pops (offset, size); writes
    -- memory[offset..offset+min(size, 32)] to OUTPUT_ADDR[0..32]
    -- (zero-padded if size < 32); writes halt_kind = 1 at
    -- OUTPUT_ADDR + 32; halts via .exit_no_epilogue.
    { label   := "h_RETURN"
    , opcodes := [0xf3]
    , body    := []
    , tail    := .custom <|
        "  ld x14, 0(x12)\n" ++          -- x14 = offset_low (low u64 of offset)
        "  ld x15, 32(x12)\n" ++         -- x15 = size_low
        "  li x16, 0xa0010000\n" ++      -- x16 = OUTPUT_ADDR
        "  sd x0, 0(x16)\n" ++           -- zero-fill OUTPUT[0..32]
        "  sd x0, 8(x16)\n" ++
        "  sd x0, 16(x16)\n" ++
        "  sd x0, 24(x16)\n" ++
        "  li x17, 32\n" ++              -- clamp size to 32
        "  bgeu x17, x15, 1f\n" ++       -- if 32 >= size, keep size
        "  mv x15, x17\n" ++             -- else size = 32
        "1:\n" ++
        "  la x17, evm_memory\n" ++
        "  add x17, x17, x14\n" ++       -- source = &evm_memory[offset]
        "2:\n" ++                        -- byte-copy loop
        "  beqz x15, 3f\n" ++
        "  lbu x18, 0(x17)\n" ++
        "  sb x18, 0(x16)\n" ++
        "  addi x17, x17, 1\n" ++
        "  addi x16, x16, 1\n" ++
        "  addi x15, x15, -1\n" ++
        "  j 2b\n" ++
        "3:\n" ++
        "  li x16, 0xa0010000\n" ++      -- write halt_kind at OUTPUT_ADDR + 32
        "  li x17, 1\n" ++               -- RETURN
        "  sd x17, 32(x16)\n" ++
        "  j .exit_no_epilogue" }
  , -- M23 real REVERT. Identical data path to RETURN; halt_kind = 2.
    { label   := "h_REVERT"
    , opcodes := [0xfd]
    , body    := []
    , tail    := .custom <|
        "  ld x14, 0(x12)\n" ++
        "  ld x15, 32(x12)\n" ++
        "  li x16, 0xa0010000\n" ++
        "  sd x0, 0(x16)\n" ++
        "  sd x0, 8(x16)\n" ++
        "  sd x0, 16(x16)\n" ++
        "  sd x0, 24(x16)\n" ++
        "  li x17, 32\n" ++
        "  bgeu x17, x15, 1f\n" ++
        "  mv x15, x17\n" ++
        "1:\n" ++
        "  la x17, evm_memory\n" ++
        "  add x17, x17, x14\n" ++
        "2:\n" ++
        "  beqz x15, 3f\n" ++
        "  lbu x18, 0(x17)\n" ++
        "  sb x18, 0(x16)\n" ++
        "  addi x17, x17, 1\n" ++
        "  addi x16, x16, 1\n" ++
        "  addi x15, x15, -1\n" ++
        "  j 2b\n" ++
        "3:\n" ++
        "  li x16, 0xa0010000\n" ++
        "  li x17, 2\n" ++               -- REVERT
        "  sd x17, 32(x16)\n" ++
        -- M24: roll back storage logs. Persistent log truncates to
        -- the checkpoint captured at the end of the dispatcher
        -- prologue (post-preload); transient log resets to 0
        -- (transient storage starts empty at tx start). RETURN /
        -- STOP / INVALID / SELFDESTRUCT do NOT roll back — they
        -- commit successfully. M26 also restores receipt event logs
        -- to the transaction checkpoint.
        "  ld x17, 456(x20)\n" ++         -- persistentLogCheckpointOff
        "  sd x17, 448(x20)\n" ++         -- persistentLogLengthOff = checkpoint
        "  sd x0, 464(x20)\n" ++          -- transientLogLengthOff = 0
        "  ld x17, 480(x20)\n" ++         -- eventLogCheckpointOff
        "  sd x17, 472(x20)\n" ++         -- eventLogLengthOff = checkpoint
        "  j .exit_no_epilogue" }
  , -- INVALID (M18 no-op, deferred halt-kind tagging). Flows through
    -- .exit_label → evmAddEpilogue → halt_kind = 0.
    { label := "h_INVALID", opcodes := [0xfe]
    , body := []
    , tail := .custom "  j .exit_label" }
  , -- SELFDESTRUCT (M18 no-op, deferred halt-kind tagging). Pops 1
    -- (recipient address). Flows through .exit_label.
    { label := "h_SELFDESTRUCT", opcodes := [0xff]
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

/-- M18 pop-and-push-zero handlers (BALANCE, EXTCODESIZE,
    EXTCODEHASH, BLOCKHASH, BLOBHASH). Each opcode pops one 32-byte
    input (e.g., an address or index) and pushes a 32-byte zero
    value. Net EVM stack delta = 0.

    Body (4 instructions): overwrite the popped slot with 32 zero
    bytes — same shape as M17's `SLOAD`/`TLOAD`. No `x12` movement
    needed.

    **Known limitations**:
    - BALANCE always returns 0 (no account state model).
    - EXTCODESIZE / EXTCODEHASH always return 0 (no external account
      model).
    - BLOCKHASH always returns 0 (no block history).
    - BLOBHASH always returns 0 (no Dencun blob context).

    **M21 update**: CALLDATALOAD (0x35) was removed from this group
    and now has a real implementation in `calldataHandlers` (see
    `Programs/Evm.lean`). It reads real calldata bytes from the
    `ziskemu -i` input region. -/
def popPushZeroHandlers : List OpcodeHandlerSpec :=
  let body : Program :=
    SD .x12 .x0 0 ;;
    SD .x12 .x0 8 ;;
    SD .x12 .x0 16 ;;
    SD .x12 .x0 24
  [ { label := "h_BALANCE", opcodes := [0x31]
    , body := body, tail := .advanceAndRet 1 }
  , { label := "h_EXTCODESIZE", opcodes := [0x3b]
    , body := body, tail := .advanceAndRet 1 }
  , { label := "h_EXTCODEHASH", opcodes := [0x3f]
    , body := body, tail := .advanceAndRet 1 }
  , { label := "h_BLOCKHASH", opcodes := [0x40]
    , body := body, tail := .advanceAndRet 1 }
  , { label := "h_BLOBHASH", opcodes := [0x49]
    , body := body, tail := .advanceAndRet 1 } ]

/-- M18 copy-no-op handlers (CODECOPY, EXTCODECOPY, RETURNDATACOPY,
    MCOPY). Each opcode pops 3 or 4 stack values and would copy
    bytes into EVM memory. As no-ops we just drop the stack args.

    Body: a single `ADDI .x12 .x12 (popBytes)`. CODECOPY /
    RETURNDATACOPY / MCOPY pop 3 words = 96 bytes; EXTCODECOPY pops
    4 = 128.

    **Known limitations**: the copies are dropped on the floor.
    Programs that copy into EVM memory and then MLOAD see whatever
    was there before (typically zero, since `evm_memory` is
    zero-initialised by the dispatcher's data section). For trusted
    programs that don't depend on these reads, this is correct.

    **M21 update**: CALLDATACOPY (0x37) was removed from this group
    and now has a real implementation in `calldataHandlers` (see
    `Programs/Evm.lean`). It actually copies calldata bytes into EVM
    memory from the `ziskemu -i` input region, with zero-fill for
    source bytes outside the calldata window. -/
def copyNoopHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_CODECOPY", opcodes := [0x39]
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
