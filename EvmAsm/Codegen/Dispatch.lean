/-
  EvmAsm.Codegen.Dispatch

  Declarative registry shape for the M5b runtime fetch/decode/dispatch
  loop. Each opcode is one `OpcodeHandlerSpec` entry; the helpers
  below render the dispatcher prologue, the 256-entry jump table, and
  the handler subroutines from a `List OpcodeHandlerSpec`.

  Adding a new opcode to the dispatcher = adding one entry to the
  registry. The dispatcher scaffolding (loop body, exit path, invalid
  fallback) stays here so `Programs.lean` only declares opcode-
  specific data.

  Per CODEGEN.md §Tricky bits #9 the loop scaffold is raw asm; only
  verified opcode bodies (rendered via `emitProgram`) sit inside the
  handler subroutines.
-/

import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Tail emitted after each handler's verified body.

    `advanceAndRet width` is the standard subroutine return: advance
    the EVM PC (`x10`) by the opcode's byte width, then `ret` back to
    the dispatcher loop. `custom asm` is for handlers that don't
    return to the dispatcher (e.g. STOP → `j .exit_label`). -/
inductive HandlerTail where
  | advanceAndRet (width : Nat)
  | custom (asm : String)

/-- Spec for one opcode handler in the M5b dispatch registry. -/
structure OpcodeHandlerSpec where
  /-- Subroutine label (e.g. `"h_ADD"`). Must be unique across the
      registry; rendered as a label in the emitted asm and as a
      target in the 256-entry jump table. -/
  label   : String
  /-- Opcode bytes this handler covers. Bytes not claimed by any
      spec route to `h_invalid` via the jump table fill. -/
  opcodes : List Nat
  /-- Raw asm emitted *between* the label and the verified body.
      Used to save dispatcher-state registers that the verified body
      may clobber. For example, `evm_mul` / `evm_signextend` /
      `evm_byte` / `evm_shr` use `x10` as a scratch accumulator —
      our dispatcher expects `x10` to be the preserved EVM code
      pointer, so those handlers carry `preBody := "  mv x9, x10"`
      and a tail that restores via `mv x10, x9` before advancing.
      Empty string means "no save needed". -/
  preBody : String := ""
  /-- Verified RV64 body, rendered verbatim via `emitProgram`.
      May be empty (e.g. STOP has no work to do before exiting). -/
  body    : Program
  /-- Optional label emitted *between* the verified body and the tail.
      Used by M9's trampoline pattern for handlers whose verified
      bodies end with a saved-ra-ret (`JALR x0, x18, 0`): the body's
      ret-jump targets this label (set in `preBody` via
      `la x18, <postBodyLabel>`), and the tail then restores `x10`
      and falls through. Handlers that return cleanly via the
      standard `addi; ret` tail leave this `none` — emission is then
      byte-identical to pre-M9. -/
  postBodyLabel : Option String := none
  /-- Tail emitted after the body (or after `postBodyLabel:` if set). -/
  tail    : HandlerTail

namespace OpcodeHandlerSpec

/-- Render a handler tail as raw asm. -/
def emitTail : HandlerTail → String
  | .advanceAndRet width => s!"  addi x10, x10, {width}\n  ret"
  | .custom asm          => asm

/-- Render the handler as a labeled subroutine. Empty bodies (STOP,
    INVALID-style entries) skip the body line entirely to avoid a
    blank line after the label. `preBody` is inserted between the
    label and the body (used for clobber-saving). `postBodyLabel`,
    when set, emits an additional label between the body and the
    tail (M9 trampoline pattern). -/
def emitSubroutine (h : OpcodeHandlerSpec) : String :=
  let preLine  := if h.preBody.isEmpty then "" else h.preBody ++ "\n"
  let bodyText := emitProgram h.body
  let bodyLine := if bodyText.isEmpty then "" else bodyText ++ "\n"
  let postLine := match h.postBodyLabel with
                  | some lbl => s!"{lbl}:\n"
                  | none     => ""
  s!"{h.label}:\n" ++ preLine ++ bodyLine ++ postLine ++ emitTail h.tail

end OpcodeHandlerSpec

/-- The label that opcode byte `b` should dispatch to. Bytes not
    claimed by any spec route to `h_invalid`. -/
def jumpTargetLabel (registry : List OpcodeHandlerSpec) (b : Nat) : String :=
  match registry.find? (fun h => h.opcodes.contains b) with
  | some h => h.label
  | none   => "h_invalid"

/-- Render the 256-entry jump table inside the `.data` section.
    Does *not* emit its own `.section .data` directive — the caller
    (`emitDispatcherDataSection`) opens the section once at the top. -/
def emitJumpTable (registry : List OpcodeHandlerSpec) : String :=
  let entries :=
    (List.range 256).map (fun b => s!"  .dword {jumpTargetLabel registry b}")
  ".balign 8\n" ++
  "opcode_handlers:\n" ++
  String.intercalate "\n" entries

/-- Shared scratch for the CALL/STATICCALL precompile frame surface.
    Follow-up precompile bodies can write returndata bytes here before
    copying them into caller memory. Layout:
      +0  status / success word
      +8  returndata length
      +16 first 64 bytes of returndata scratch. -/
def emitPrecompileFrameData : String :=
  ".balign 8\n" ++
  "evm_precompile_frame:\n" ++
  "  .zero 80\n"

/-- Scratch buffers used by `zkvm_sha256`. The wrapper expects these
    labels to exist in the dispatcher's data section. -/
def emitSha256Data : String :=
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n"

/-- Dispatcher prologue: init EVM pointers (`x10` = code, `x12` =
    stack top, `x13` = EVM memory base) and enter the main
    fetch/decode/dispatch loop. Each iteration loads the opcode byte
    at `[x10]`, indexes the jump table, `jalr`s to the handler, then
    jumps back to `.dispatch_loop`.

    `x13` is added in M7 for the memory opcodes (MLOAD, MSTORE,
    MSTORE8). Handlers that don't touch memory ignore it; the verified
    bodies that do use it take `memBaseReg` as a Lean argument and our
    M7 handler entries pass `.x13`.

    `x20` is added in M12 for the simple environment opcodes
    (ADDRESS, CALLER, …). The verified `evm_env_load` body takes
    `envBaseReg` as a Lean argument and our M12 env handler entries
    pass `.x20`. `x20` was chosen because no verified body in
    `EvmAsm/Evm64/*/Program.lean` references it AND no existing
    handler `preBody` writes to it — the M8/M9/M10 DIV/MOD/SDIV/
    SMOD/ADDMOD handlers all save `x10` to `x14`, so `x14` is
    NOT safe as a permanent dispatcher register.

    `x21` is added in M15 for the control-flow opcodes
    (PC, JUMP, JUMPI). It holds the **initial value of `x10`** at
    `_start` — the EVM code base. PC computes `pc = x10 - x21`;
    JUMP/JUMPI compute `target = x21 + dest`. `x21` is audited the
    same way `x20` was: zero references across `EvmAsm/Evm64/*/Program.lean`
    and zero uses by any existing handler `preBody`/`tail`. -/
def emitDispatcherPrologue : String :=
  "  la sp, lp64_sp_top\n" ++     -- M16: LP64 stack ptr for ECALL-bridge helpers
                                  -- (e.g. zkvm_keccak256's `addi sp, sp, -32`)
  "  la x10, evm_code\n" ++
  "  la x21, evm_code\n" ++       -- M15: preserved code base (for PC, JUMP, JUMPI)
  "  la x12, evm_stack_top\n" ++
  "  la x13, evm_memory\n" ++
  "  la x20, evm_env\n" ++
  -- M21: .data-baked variant has no calldata input. Initialize env's
  -- callDataPtrOff (416) to point at a safe zero region (`evm_memory`)
  -- and callDataLenOff (424) to 0. Any CALLDATALOAD reads zeros from
  -- evm_memory (M17 no-op-equivalent); CALLDATASIZE returns 0.
  -- Calldata-requiring tests must use the runtime-bytecode dispatcher
  -- (codegen-opcodes-runtime-check.sh).
  "  la x5, evm_memory\n" ++
  "  sd x5, 416(x20)\n" ++         -- env.callDataPtrOff = &evm_memory (zeros)
  "  sd x0, 424(x20)\n" ++         -- env.callDataLenOff = 0
  -- M24: .data-baked variant has no storage input. Initialize all
  -- three log-state env cells to 0. Persistent + transient logs live
  -- at STATE_TRACKER_AREA (0xa0630000 / 0xa0830000) outside `.data`;
  -- the regions are byte-accessed directly by the storage handlers.
  "  sd x0, 448(x20)\n" ++         -- env.persistentLogLengthOff = 0
  "  sd x0, 456(x20)\n" ++         -- env.persistentLogCheckpointOff = 0
  "  sd x0, 464(x20)\n" ++         -- env.transientLogLengthOff = 0
  "  sd x0, 472(x20)\n" ++         -- env.eventLogLengthOff = 0
  "  sd x0, 480(x20)\n" ++         -- env.eventLogCheckpointOff = 0
  "  sd x0, 512(x20)\n" ++         -- M28: blobBaseFee trailer slot = 0
  "  sd x0, 520(x20)\n" ++
  "  sd x0, 528(x20)\n" ++
  "  sd x0, 536(x20)\n" ++
  ".dispatch_loop:\n" ++
  "  lbu x5, 0(x10)\n" ++
  "  la x6, opcode_handlers\n" ++
  "  slli x5, x5, 3\n" ++
  "  add x6, x6, x5\n" ++
  "  ld x7, 0(x6)\n" ++
  "  jalr x1, x7, 0\n" ++
  "  j .dispatch_loop"

/-- Dispatcher epilogue: handler subroutines (each ends with `ret` or
    `j .exit_label`), the `h_invalid` fallback, and `.exit_label`
    which runs `exitBody` (e.g. `evmAddEpilogue`) and falls through
    to the halt stub appended by `emitBuildUnit`.

    **M23 addition**: the `.exit_no_epilogue` label is emitted
    *after* `exitBody` and *before* the halt stub. Handlers that
    surface their own output bytes to `OUTPUT_ADDR` (e.g. real
    RETURN / REVERT) jump there to skip the default exit body
    (which would otherwise clobber their writes with the EVM
    stack-top copy). STOP and the other halts continue to flow
    through `.exit_label` → `exitBody` → halt stub. -/
def emitDispatcherEpilogue
    (registry : List OpcodeHandlerSpec) (exitBody : Program) : String :=
  String.intercalate "\n" (registry.map OpcodeHandlerSpec.emitSubroutine) ++ "\n" ++
  -- M16/M27: hash subroutines sit BETWEEN the handler subroutines
  -- and the `h_invalid:` / `.exit_label:` blocks so it's reachable only
  -- via explicit `jal`s (not by fall-through from exitBody).
  -- Each handler subroutine ends with `ret` / `j .dispatch_loop`, so
  -- they don't fall through into these labels. The subroutines end
  -- with `ret`, returning to whoever JAL'd them.
  zkvmSha256Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  "h_invalid:\n" ++
  "  j .exit_label\n" ++
  ".exit_label:\n" ++
  emitProgram exitBody ++ "\n" ++
  ".exit_no_epilogue:\n" ++
  -- M24: surface final log lengths at OUTPUT_ADDR + 40 / + 48.
  -- This runs for EVERY halt path: STOP / RETURN / REVERT /
  -- INVALID / SELFDESTRUCT. REVERT's body has already restored
  -- the persistent log length to the checkpoint (and zeroed the
  -- transient length) by the time we get here, so the surfaced
  -- values reflect the post-rollback state for reverted txs and
  -- the live committed state for successful ones.
  "  li x16, 0xa0010000\n" ++       -- x16 = OUTPUT_ADDR
  "  ld x17, 448(x20)\n" ++         -- persistent log length
  "  sd x17, 40(x16)\n" ++          -- OUTPUT[40..48]
  "  ld x17, 464(x20)\n" ++         -- transient log length
  "  sd x17, 48(x16)\n" ++          -- OUTPUT[48..56]
  -- M25: dedup-and-emit modified persistent slots at OUTPUT+56..
  -- Walks the persistent log from end (last-write-wins); for each
  -- entry, checks if its slotKey has already been emitted at
  -- OUTPUT[64..64+count*64]; if not, emits (slotKey, current) and
  -- bumps the count cell at OUTPUT+56. Capped at 3 entries (192 B
  -- of slot data fits in the 200-byte slack after byte 56).
  -- All halt paths (STOP / RETURN / REVERT / INVALID / SELFDESTRUCT)
  -- run this; REVERT has already truncated the log to the checkpoint,
  -- so the surfaced slots reflect the post-rollback state.
  "  ld x15, 448(x20)\n" ++         -- x15 = persistent log_length
  "  li x17, 0\n" ++                -- x17 = emitted count
  "  sd x17, 56(x16)\n" ++          -- init OUTPUT+56 = 0
  "  beqz x15, 4f\n" ++             -- empty log → done
  "  li x14, 0xa0630000\n" ++       -- x14 = log base
  "  slli x18, x15, 7\n" ++         -- x18 = log_length * 128
  "  add x14, x14, x18\n" ++        -- x14 = past last entry
  "1:\n" ++                         -- scan iter (work backward)
  "  addi x14, x14, -128\n" ++      -- x14 = current entry
  -- Dedup: scan output[OUTPUT+64 .. OUTPUT+64+x17*64] for slotKey
  "  li x18, 0xa0010040\n" ++       -- x18 = OUTPUT + 64
  "  mv x19, x17\n" ++              -- x19 = emitted count to check
  "2:\n" ++                         -- dedup loop
  "  beqz x19, 3f\n" ++             -- exhausted → not duplicate, emit
  "  ld x21, 0(x18)\n" ++
  "  ld x22, 32(x14)\n" ++
  "  bne x21, x22, 5f\n" ++
  "  ld x21, 8(x18)\n" ++
  "  ld x22, 40(x14)\n" ++
  "  bne x21, x22, 5f\n" ++
  "  ld x21, 16(x18)\n" ++
  "  ld x22, 48(x14)\n" ++
  "  bne x21, x22, 5f\n" ++
  "  ld x21, 24(x18)\n" ++
  "  ld x22, 56(x14)\n" ++
  "  bne x21, x22, 5f\n" ++
  "  j 6f\n" ++                     -- match → already emitted, skip
  "5:\n" ++                         -- not match this output entry
  "  addi x18, x18, 64\n" ++
  "  addi x19, x19, -1\n" ++
  "  j 2b\n" ++
  "3:\n" ++                         -- emit (slotKey, current)
  "  li x19, 3\n" ++
  "  bgeu x17, x19, 4f\n" ++        -- cap reached
  "  slli x18, x17, 6\n" ++         -- x18 = emitted count * 64
  "  li x19, 0xa0010040\n" ++       -- x19 = OUTPUT + 64
  "  add x18, x19, x18\n" ++        -- x18 = write target
  -- Copy slotKey: log[+32..+64] → out[+0..+32]
  "  ld x21, 32(x14)\n" ++
  "  sd x21, 0(x18)\n" ++
  "  ld x21, 40(x14)\n" ++
  "  sd x21, 8(x18)\n" ++
  "  ld x21, 48(x14)\n" ++
  "  sd x21, 16(x18)\n" ++
  "  ld x21, 56(x14)\n" ++
  "  sd x21, 24(x18)\n" ++
  -- Copy current: log[+96..+128] → out[+32..+64]
  "  ld x21, 96(x14)\n" ++
  "  sd x21, 32(x18)\n" ++
  "  ld x21, 104(x14)\n" ++
  "  sd x21, 40(x18)\n" ++
  "  ld x21, 112(x14)\n" ++
  "  sd x21, 48(x18)\n" ++
  "  ld x21, 120(x14)\n" ++
  "  sd x21, 56(x18)\n" ++
  "  addi x17, x17, 1\n" ++
  "  sd x17, 56(x16)\n" ++          -- update count cell
  "6:\n" ++                         -- loop step
  "  addi x15, x15, -1\n" ++
  "  bnez x15, 1b\n" ++
  "4:\n" ++                         -- done — surface first LOG event, then halt
  -- M26: event LOG capture test surface. If receipt event logs
  -- exist, this intentionally reuses the storage diagnostic window:
  --   OUTPUT+56       : event log count (u64 LE)
  --   OUTPUT+64..256  : first event descriptor prefix
  -- Current opcode probes assert either storage post-state or LOG
  -- capture, not both. A future wider receipt-output ABI should
  -- carry both without sharing this test-only window.
  "  li x16, 0xa0010000\n" ++
  "  ld x17, 472(x20)\n" ++
  "  beqz x17, 8f\n" ++
  "  sd x17, 56(x16)\n" ++
  "  la x18, evm_event_logs\n" ++
  "  addi x19, x16, 64\n" ++
  "  li x21, 192\n" ++
  "7:\n" ++
  "  lbu x22, 0(x18)\n" ++
  "  sb x22, 0(x19)\n" ++
  "  addi x18, x18, 1\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x21, x21, -1\n" ++
  "  bnez x21, 7b\n" ++
  "8:\n"                            -- done — fall through to halt stub

/-- `.data` section layout (starts at `0xa0000000` per
    `Driver.lean`'s `-Tdata=...`):

    ```
    evm_code:         <bytecode> (~50 B)
    .balign 32
    evm_stack_low:    .zero 256             (256-byte EVM stack scratch)
    evm_stack_top:
    .balign 32
    evm_memory:       .zero 0x8000          (32 KiB EVM memory, M7 onward)
    .balign 8
    opcode_handlers:  256 × .dword (jump table, 2 KiB)
    ```

    Total: ~50 + 256 + 32768 + 2048 ≈ 35 KiB, well under the 64 KiB
    cap before `OUTPUT_ADDR = 0xa0010000`. Going beyond 32 KiB of
    EVM memory would risk overrunning OUTPUT_ADDR.

    The EVM stack region grows downward from `evm_stack_top`; safe at
    the worst-case M5b depth of 2 (= 64 bytes). The EVM memory region
    grows upward from `evm_memory` indexed by `memBaseReg + offset`. -/
def emitDispatcherDataSection
    (bytecodeBytes : String) (registry : List OpcodeHandlerSpec) : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "evm_code:\n" ++
  s!"  .byte {bytecodeBytes}\n" ++
  ".balign 32\n" ++
  "evm_stack_low:\n" ++
  "  .zero 256\n" ++
  "evm_stack_top:\n" ++
  ".balign 32\n" ++
  "evm_memory:\n" ++
  "  .zero 0x8000\n" ++   -- 32 KiB EVM memory (M7 onward)
  ".balign 8\n" ++
  "evm_env:\n" ++
  "  .zero 544\n" ++      -- 13 SimpleEnvField slots × 32 B + calldata/return-data
                          -- + M22/M24/M26 log-state cells up to env+480
                          -- + M28 BLOBBASEFEE word at env+512
  ".balign 8\n" ++
  "evm_event_logs:\n" ++
  "  .zero 4096\n" ++     -- M26: 16 × 256-byte bounded LOG event descriptors
  emitPrecompileFrameData ++
  emitSha256Data ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++      -- M16: 25 × u64 keccak permutation state buffer
  ".balign 16\n" ++
  "lp64_stack:\n" ++
  "  .zero 512\n" ++      -- M16: LP64 stack region for ECALL-bridge helpers
  "lp64_sp_top:\n" ++     -- (the keccak subroutine's `sp` frame lives here)
  emitJumpTable registry

/-! ## Runtime-bytecode dispatcher (M8.5)

    Variant of the dispatcher that reads its bytecode at runtime
    from ziskemu's `-i <file>` input region instead of baking it
    into `.data`. Lets a single ELF run any bytecode — the test
    harness packs each per-case bytecode into an input file and
    re-uses the same ELF.

    Reads bytecode at `INPUT_ADDR + INPUT_DATA_OFFSET = 0x40000010`
    (see `EvmAsm/Codegen/Programs.lean` for the symbolic constants).
    All other dispatcher state (stack scratch, evm_memory, jump
    table) is identical to the `.data`-baked variant — only the
    prologue's `la x10, evm_code` swaps to `li x10, 0x40000010`
    and the `.data` section drops the `evm_code:` block. -/

/-- Runtime-bytecode dispatcher prologue. Same fetch/decode/dispatch
    loop as `emitDispatcherPrologue`; differs only in how `x10` is
    initialised — pointed at the input region instead of an
    in-`.data` label. The hex literal `0x40000010` matches
    `INPUT_ADDR + INPUT_DATA_OFFSET` in `Programs.lean`. -/
def emitRuntimeDispatcherPrologue : String :=
  "  la sp, lp64_sp_top\n" ++   -- M16: LP64 stack ptr for ECALL-bridge helpers
                                -- (e.g. zkvm_keccak256's `addi sp, sp, -32`)
  "  li x10, 0x40000010\n" ++   -- INPUT_ADDR + INPUT_DATA_OFFSET
  "  li x21, 0x40000010\n" ++   -- M15: preserved code base (mirrors x10 init)
  "  la x12, evm_stack_top\n" ++
  "  la x13, evm_memory\n" ++
  "  la x20, evm_env\n" ++       -- M12: env-region base (ADDRESS, CALLER, …)
  -- M21: populate env's callDataPtr / callDataLen from the input region.
  -- The input file format (pack-bytecode.py) is:
  --   [8B bytecode-length][bytecode bytes][pad to 8][8B calldata-length][calldata bytes]
  -- bytecode-length sits at INPUT_ADDR + 8 = 0x40000008. We round it up
  -- to 8-byte boundary, add to bytecode start (x10), and that's the
  -- calldata-length address. Eight bytes past it is the calldata.
  "  li x5, 0x40000008\n" ++       -- &(bytecode length)
  "  ld x5, 0(x5)\n" ++            -- x5 = bytecode length
  "  addi x5, x5, 7\n" ++          -- round up to 8-byte boundary
  "  srli x5, x5, 3\n" ++
  "  slli x5, x5, 3\n" ++          -- x5 = padded bytecode length
  "  add x6, x10, x5\n" ++         -- x6 = &(calldata length)
  "  ld x7, 0(x6)\n" ++            -- x7 = calldata length
  "  addi x6, x6, 8\n" ++          -- x6 = calldata ptr
  "  sd x6, 416(x20)\n" ++         -- env.callDataPtrOff (416) = ptr
  "  sd x7, 424(x20)\n" ++         -- env.callDataLenOff (424) = len
  -- M24: locate the storage preload segment past the calldata pad and
  -- expand each 64-byte (key, value) input entry into a 128-byte
  -- Option A entry (addrHash=0, slotKey=key, original=value,
  -- current=value) at STATE_TRACKER_AREA = 0xa0630000. Save the
  -- preload count to both the live persistent log length AND the
  -- checkpoint (so REVERT rolls back to post-preload). Init
  -- transient log length to 0 (transient storage starts empty).
  --
  -- Input layout (unchanged from M22 `pack-bytecode.py --storage`):
  --   <u64 slot_count> followed by slot_count × (key:32, value:32)
  --   then a 32-byte BLOBBASEFEE word (M28; zero by default)
  -- Output layout (Option A):
  --   STATE_TRACKER_AREA + i*128 = (addrHash=0:32, slotKey:32,
  --                                 original=value:32, current=value:32)
  "  add x5, x6, x7\n" ++          -- x5 = end of calldata bytes
  "  addi x5, x5, 7\n" ++          -- round up to 8-byte boundary
  "  srli x5, x5, 3\n" ++
  "  slli x5, x5, 3\n" ++          -- x5 = &(slot count)
  "  ld x6, 0(x5)\n" ++            -- x6 = slot_count (= preload count)
  "  sd x6, 448(x20)\n" ++         -- env.persistentLogLengthOff = preload count
  "  sd x6, 456(x20)\n" ++         -- env.persistentLogCheckpointOff = preload count
  "  sd x0, 464(x20)\n" ++         -- env.transientLogLengthOff = 0
  "  sd x0, 472(x20)\n" ++         -- env.eventLogLengthOff = 0
  "  sd x0, 480(x20)\n" ++         -- env.eventLogCheckpointOff = 0
  "  addi x5, x5, 8\n" ++          -- x5 = src ptr (first preload entry)
  "  li x7, 0xa0630000\n" ++       -- x7 = dst ptr (STATE_TRACKER_AREA persistent log)
  ".preload_expand_loop:\n" ++
  "  beqz x6, .preload_expand_done\n" ++
  -- addrHash = 0 (32 bytes)
  "  sd x0, 0(x7)\n" ++
  "  sd x0, 8(x7)\n" ++
  "  sd x0, 16(x7)\n" ++
  "  sd x0, 24(x7)\n" ++
  -- slotKey = src[0..32] → dst[32..64]
  "  ld x8, 0(x5)\n" ++
  "  sd x8, 32(x7)\n" ++
  "  ld x8, 8(x5)\n" ++
  "  sd x8, 40(x7)\n" ++
  "  ld x8, 16(x5)\n" ++
  "  sd x8, 48(x7)\n" ++
  "  ld x8, 24(x5)\n" ++
  "  sd x8, 56(x7)\n" ++
  -- value (src[32..64]) → original (dst[64..96]) AND current (dst[96..128])
  "  ld x8, 32(x5)\n" ++
  "  sd x8, 64(x7)\n" ++
  "  sd x8, 96(x7)\n" ++
  "  ld x8, 40(x5)\n" ++
  "  sd x8, 72(x7)\n" ++
  "  sd x8, 104(x7)\n" ++
  "  ld x8, 48(x5)\n" ++
  "  sd x8, 80(x7)\n" ++
  "  sd x8, 112(x7)\n" ++
  "  ld x8, 56(x5)\n" ++
  "  sd x8, 88(x7)\n" ++
  "  sd x8, 120(x7)\n" ++
  "  addi x5, x5, 64\n" ++         -- next input entry (64 B)
  "  addi x7, x7, 128\n" ++        -- next output entry (128 B)
  "  addi x6, x6, -1\n" ++
  "  j .preload_expand_loop\n" ++
  ".preload_expand_done:\n" ++
  -- M28: x5 now points at the blob-base-fee trailer. Copy the 32-byte
  -- EVM-stack word into a separate env slot; opcode 0x4a loads it.
  "  ld x8, 0(x5)\n" ++
  "  sd x8, 512(x20)\n" ++
  "  ld x8, 8(x5)\n" ++
  "  sd x8, 520(x20)\n" ++
  "  ld x8, 16(x5)\n" ++
  "  sd x8, 528(x20)\n" ++
  "  ld x8, 24(x5)\n" ++
  "  sd x8, 536(x20)\n" ++
  ".dispatch_loop:\n" ++
  "  lbu x5, 0(x10)\n" ++
  "  la x6, opcode_handlers\n" ++
  "  slli x5, x5, 3\n" ++
  "  add x6, x6, x5\n" ++
  "  ld x7, 0(x6)\n" ++
  "  jalr x1, x7, 0\n" ++
  "  j .dispatch_loop"

/-- Runtime-bytecode `.data` section. Drops the `evm_code:` block
    (no baked bytecode); everything else matches the `.data`-baked
    variant. Same 32 KiB budget concerns. -/
def emitRuntimeDispatcherDataSection
    (registry : List OpcodeHandlerSpec) : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "evm_stack_low:\n" ++
  "  .zero 256\n" ++
  "evm_stack_top:\n" ++
  ".balign 32\n" ++
  "evm_memory:\n" ++
  "  .zero 0x8000\n" ++   -- 32 KiB EVM memory (M7 onward)
  ".balign 8\n" ++
  "evm_env:\n" ++
  "  .zero 544\n" ++      -- 13 SimpleEnvField slots × 32 B + calldata/return-data
                          -- + M22/M24/M26 log-state cells up to env+480
                          -- + M28 BLOBBASEFEE word at env+512
  ".balign 8\n" ++
  "evm_event_logs:\n" ++
  "  .zero 4096\n" ++     -- M26: 16 × 256-byte bounded LOG event descriptors
  emitPrecompileFrameData ++
  emitSha256Data ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++      -- M16: 25 × u64 keccak permutation state buffer
  ".balign 16\n" ++
  "lp64_stack:\n" ++
  "  .zero 512\n" ++      -- M16: LP64 stack region for ECALL-bridge helpers
  "lp64_sp_top:\n" ++     -- (the keccak subroutine's `sp` frame lives here)
  emitJumpTable registry

/-- Build a runtime-bytecode `BuildUnit` for `registry` + `exitBody`.
    The emitted ELF doesn't carry any bytecode — the test harness
    supplies it at runtime via `ziskemu -i <file>` (8-byte LE length
    prefix + raw bytes; see M4's input-region convention). -/
def buildRuntimeDispatchUnit
    (registry : List OpcodeHandlerSpec)
    (exitBody : Program) : BuildUnit := {
  body        := []
  prologueAsm := emitRuntimeDispatcherPrologue
  epilogueAsm := emitDispatcherEpilogue registry exitBody
  dataAsm     := emitRuntimeDispatcherDataSection registry
}

/-- Build a `BuildUnit` that runs the dispatcher over `bytecodeBytes`
    using `registry`. `exitBody` is the verified `Program` invoked
    at `.exit_label` to surface the result (usually `evmAddEpilogue`). -/
def buildDispatchUnit
    (registry : List OpcodeHandlerSpec)
    (exitBody : Program)
    (bytecodeBytes : String) : BuildUnit := {
  body        := []
  prologueAsm := emitDispatcherPrologue
  epilogueAsm := emitDispatcherEpilogue registry exitBody
  dataAsm     := emitDispatcherDataSection bytecodeBytes registry
}

end EvmAsm.Codegen
