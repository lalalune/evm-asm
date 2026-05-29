/-
  EvmAsm.Codegen.Tests.Cases

  Per-opcode regression test registry. Each `OpcodeTestCase` is a
  bytecode + expected output bytes; the bash runner
  (`scripts/codegen-opcodes-check.sh`) iterates the list, emitting
  one ELF per case via `lake exe codegen --test-case <name>` and
  diffing the first 32 bytes of `ziskemu`'s public output against
  `expectedOutHex`.

  Adding a regression test = appending one record to
  `opcodeTestCases` below.
-/

import EvmAsm.Codegen.Programs

namespace EvmAsm.Codegen.Tests

open EvmAsm.Codegen

/-- One per-opcode regression test wrapped around the M5b dispatcher
    (`tinyInterpRegistry`). The bytecode bakes into `.data`; the
    expected output is the first 32 bytes of `OUTPUT_ADDR` (i.e. the
    EVM stack top after STOP, written by `evmAddEpilogue`). -/
structure OpcodeTestCase where
  /-- Identifier (becomes `gen-out/<name>.{s,o,elf,output}`). -/
  name           : String
  /-- EVM bytecode as a comma-separated `.byte` directive payload
      (e.g. `"0x60, 0xff, 0x60, 0x01, 0x01, 0x00"`). -/
  bytecode       : String
  /-- Expected first 32 bytes of `OUTPUT_ADDR` as 64 hex chars. -/
  expectedOutHex : String
  /-- Optional EVM calldata passed alongside the bytecode (M21).
      Accepted shapes: CSV (e.g. `"0x01, 0x02, 0x03"`) or hex blob
      (e.g. `"0xdeadbeef"`). Empty string = no calldata (M17
      no-op CALLDATA behavior for back-compat with pre-M21 cases). -/
  calldata       : String := ""
  /-- Optional pre-loaded EVM storage slots (M22). Format:
      parenthesized hex pairs `"(0x00, 0xdead) (0x01, 0xbeef)"`.
      Each key / value is interpreted as a u256 integer; the
      packer serializes them in EVM-stack byte order. Empty
      string = no preload (table starts empty; SSTORE may grow
      it; SLOAD against an unset key returns zero). -/
  storage        : String := ""
  /-- Optional expected halt-kind at `OUTPUT_ADDR + 32` (M23).
      16 hex chars = 8-byte LE u64 (e.g. `"0100000000000000"` for
      RETURN = 1, `"0200000000000000"` for REVERT = 2). Empty
      string = don't assert (back-compat for pre-M23 cases). The
      bash runner reads `OUTPUT_ADDR + 32..40` and compares only
      when this field is non-empty. -/
  expectedHaltKind : String := ""
  /-- Optional expected persistent log length at
      `OUTPUT_ADDR + 40` (M24). 16 hex chars = 8-byte LE u64.
      The dispatcher epilogue surfaces the FINAL persistent log
      length (post-revert if REVERT ran) here for every exit
      path. Test SSTORE commit / REVERT rollback via this. Empty
      string = don't assert. -/
  expectedPersistentLogLength : String := ""
  /-- Optional expected transient log length at
      `OUTPUT_ADDR + 48` (M24). 16 hex chars = 8-byte LE u64.
      Reset to 0 by REVERT. Test TSTORE commits / REVERT
      clears via this. Empty string = don't assert. -/
  expectedTransientLogLength : String := ""

/-- Registry of test cases. M5a/M5b's two original bytecodes are
    migrated as `add_basic` / `add_chain`; M6b adds ~20 more — one
    per singleton opcode, one per parametric family, plus a kitchen-
    sink case that chains multiple opcodes.

    EVM convention reminder: stack values are 256-bit big-endian;
    `OUTPUT_ADDR` receives the post-STOP stack top as 32 bytes,
    interpreted as four little-endian u64 limbs. So `0x42` on the
    EVM stack surfaces as `42 00 00 00 00 00 00 00 ...` (low byte
    first in the LE limb encoding).

    Binary opcodes pop top (`a`) then second (`b`); the order
    matters for non-commutative ones (`SUB`, `DIV`, `MOD`, `SHR`,
    comparisons). For SUB specifically: pushes `a - b` where `a`
    was the top — so `PUSH1 0x03; PUSH1 0x05; SUB` yields `5 - 3 = 2`. -/
def opcodeTestCases : List OpcodeTestCase :=
  [ -- ## Baseline (migrated from M5a/M5b)
    -- PUSH1 0xff; PUSH1 0x01; ADD; STOP → 0x100
    { name           := "add_basic"
      bytecode       := "0x60, 0xff, 0x60, 0x01, 0x01, 0x00"
      expectedOutHex := "0001000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x10; PUSH1 0x20; ADD; PUSH1 0x30; ADD; STOP → 0x60
    { name           := "add_chain"
      bytecode       := "0x60, 0x10, 0x60, 0x20, 0x01, 0x60, 0x30, 0x01, 0x00"
      expectedOutHex := "6000000000000000000000000000000000000000000000000000000000000000" }
    -- ## Singletons (16, one per fixed-shape opcode)
  , -- PUSH1 0x03; PUSH1 0x05; SUB; STOP → 5 - 3 = 2
    { name           := "sub_basic"
      bytecode       := "0x60, 0x03, 0x60, 0x05, 0x03, 0x00"
      expectedOutHex := "0200000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x03; PUSH1 0x04; MUL; STOP → 4 * 3 = 12 = 0x0c
    { name           := "mul_basic"
      bytecode       := "0x60, 0x03, 0x60, 0x04, 0x02, 0x00"
      expectedOutHex := "0c00000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x7f; PUSH1 0x00; SIGNEXTEND; STOP — byte 0 of 0x7f has
    -- high bit 0, so sign-extension is a no-op → 0x7f.
    { name           := "signextend_basic"
      bytecode       := "0x60, 0x7f, 0x60, 0x00, 0x0b, 0x00"
      expectedOutHex := "7f00000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x05; PUSH1 0x03; LT; STOP → 3 < 5 = 1
    { name           := "lt_basic"
      bytecode       := "0x60, 0x05, 0x60, 0x03, 0x10, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x03; PUSH1 0x05; GT; STOP → 5 > 3 = 1
    { name           := "gt_basic"
      bytecode       := "0x60, 0x03, 0x60, 0x05, 0x11, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x02; PUSH1 0x01; SLT; STOP — signed `a < b` with a=1, b=2 → 1
    { name           := "slt_basic"
      bytecode       := "0x60, 0x02, 0x60, 0x01, 0x12, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x03; PUSH1 0x05; SGT; STOP — signed `a > b` with a=5, b=3 → 1
    { name           := "sgt_basic"
      bytecode       := "0x60, 0x03, 0x60, 0x05, 0x13, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x42; PUSH1 0x42; EQ; STOP → 1
    { name           := "eq_basic"
      bytecode       := "0x60, 0x42, 0x60, 0x42, 0x14, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x00; ISZERO; STOP → 1
    { name           := "iszero_basic"
      bytecode       := "0x60, 0x00, 0x15, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x0f; PUSH1 0xff; AND; STOP → 0xff & 0x0f = 0x0f
    { name           := "and_basic"
      bytecode       := "0x60, 0x0f, 0x60, 0xff, 0x16, 0x00"
      expectedOutHex := "0f00000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x0f; PUSH1 0xa0; OR; STOP → 0xa0 | 0x0f = 0xaf
    { name           := "or_basic"
      bytecode       := "0x60, 0x0f, 0x60, 0xa0, 0x17, 0x00"
      expectedOutHex := "af00000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x0f; PUSH1 0xff; XOR; STOP → 0xff ^ 0x0f = 0xf0
    { name           := "xor_basic"
      bytecode       := "0x60, 0x0f, 0x60, 0xff, 0x18, 0x00"
      expectedOutHex := "f000000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x00; NOT; STOP → ~0 (32 bytes of 0xff)
    { name           := "not_basic"
      bytecode       := "0x60, 0x00, 0x19, 0x00"
      expectedOutHex := "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" }
  , -- PUSH32 0x0102…20; PUSH1 0x1f; BYTE; STOP — byte 31 (LSByte
    -- big-endian) of 0x0102…1f20 is 0x20.
    { name           := "byte_basic"
      bytecode       := "0x7f, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x60, 0x1f, 0x1a, 0x00"
      expectedOutHex := "2000000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x01; PUSH1 0x04; SHL; STOP — shift=4 on top, value=0x01
    -- → 0x01 << 4 = 0x10.
    { name           := "shl_basic"
      bytecode       := "0x60, 0x01, 0x60, 0x04, 0x1b, 0x00"
      expectedOutHex := "1000000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x80; PUSH1 0x04; SHR; STOP — shift=4 on top, value=0x80
    -- → 0x80 >> 4 = 0x08.
    { name           := "shr_basic"
      bytecode       := "0x60, 0x80, 0x60, 0x04, 0x1c, 0x00"
      expectedOutHex := "0800000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0xff; PUSH1 0x01; SAR; STOP — shift=1 on top, value=0xff
    -- (MSB clear → positive in 256-bit two's complement). 0xff >>>arith 1
    -- = 0x7f; SAR matches SHR on the positive path.
    { name           := "sar_basic_positive"
      bytecode       := "0x60, 0xff, 0x60, 0x01, 0x1d, 0x00"
      expectedOutHex := "7f00000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH32 (2^256 - 1); PUSH1 0x01; SAR; STOP — value is -1 in two's
    -- complement (all 256 bits set). SAR sign-fills, so -1 >>>arith 1 = -1
    -- (all bits stay set). Exercises the sign-extension path.
    { name           := "sar_basic_negative"
      bytecode       := "0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x60, 0x01, 0x1d, 0x00"
      expectedOutHex := "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" }
  , -- PUSH1 0x42; PUSH1 0xff; POP; STOP — POP removes 0xff, leaves 0x42
    { name           := "pop_basic"
      bytecode       := "0x60, 0x42, 0x60, 0xff, 0x50, 0x00"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000" }
    -- ## Family representatives (3, one per parametric family)
  , -- PUSH32 0x0102…20; STOP — the 32 immediate bytes are read
    -- big-endian into the EVM word; surfaced LE in OUTPUT_ADDR.
    { name           := "push32_basic"
      bytecode       := "0x7f, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x00"
      expectedOutHex := "201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201" }
  , -- PUSH1 0x42; DUP1; ADD; STOP — DUP1 makes stack [0x42, 0x42];
    -- ADD → 0x84.
    { name           := "dup1_basic"
      bytecode       := "0x60, 0x42, 0x80, 0x01, 0x00"
      expectedOutHex := "8400000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x05; PUSH1 0x02; SWAP1; SUB; STOP — SWAP1 yields top=5,
    -- second=2; SUB → 5 - 2 = 3.
    { name           := "swap1_basic"
      bytecode       := "0x60, 0x05, 0x60, 0x02, 0x90, 0x03, 0x00"
      expectedOutHex := "0300000000000000000000000000000000000000000000000000000000000000" }
    -- ## Kitchen sink (cross-family chain)
  , -- PUSH1 0x03; PUSH1 0x05; MUL; PUSH1 0x10; SUB; STOP
    -- MUL: 5*3=15=0x0f. SUB: 0x10 - 0x0f = 0x01.
    { name           := "arith_mix"
      bytecode       := "0x60, 0x03, 0x60, 0x05, 0x02, 0x60, 0x10, 0x03, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
    -- ## M7 memory opcodes (MLOAD / MSTORE / MSTORE8)
  , -- PUSH1 0x42; PUSH1 0x00; MSTORE; PUSH1 0x00; MLOAD; STOP
    -- MSTORE writes 0x42 big-endian to memory[0..32]; MLOAD reads it
    -- back to the stack. EVM word = 0x42, on the stack as four LE u64
    -- limbs with limb 0 = 0x42 (decimal 66).
    { name           := "mstore_mload"
      bytecode       := "0x60, 0x42, 0x60, 0x00, 0x52, 0x60, 0x00, 0x51, 0x00"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0xff; PUSH1 0x00; MSTORE8; PUSH1 0x00; MLOAD; STOP
    -- MSTORE8 writes one byte (0xff) at memory[0]. MLOAD reads 32 bytes
    -- big-endian → EVM word = 0xff · 2^248. As LE limbs that's
    -- [0, 0, 0, 0xff00000000000000]; limb 3 written to bytes 24..31
    -- in LE order ends with 0xff at byte 31.
    { name           := "mstore8_basic"
      bytecode       := "0x60, 0xff, 0x60, 0x00, 0x53, 0x60, 0x00, 0x51, 0x00"
      expectedOutHex := "00000000000000000000000000000000000000000000000000000000000000ff" }
    -- ## M12 simple environment opcodes (ADDRESS, CALLER, …)
    -- The evm_env data region is zero-initialised by the dispatcher's
    -- .data section. Each test confirms the handler routes through
    -- evm_env_load + x12 advances + 32 bytes land on the stack.
  , -- ADDRESS; STOP — routes byte 0x30 to evm_env_load .x20 .x15 .address.
    -- Reads 32 zero bytes from evm_env + 0 and pushes them.
    { name           := "address_zero"
      bytecode       := "0x30, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- CALLER; DUP1; ADD; STOP — exercises a non-trivial post-ENV stack
    -- flow. CALLER pushes 0 (zero-init env). DUP1 yields [0, 0].
    -- ADD → 0. Confirms env handler advances x12 correctly so DUP1/ADD
    -- find their operand.
    { name           := "caller_via_dup_add"
      bytecode       := "0x33, 0x80, 0x01, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- TIMESTAMP; NUMBER; SUB; STOP — exercises two distinct env field
    -- offsets back-to-back. Both fields zero-init → SUB yields 0.
    -- Confirms different opcode bytes resolve to different env cells
    -- (handler-table dispatch, not aliasing).
    { name           := "env_field_offset_distinct"
      bytecode       := "0x42, 0x43, 0x03, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
    -- ## M13 calldata-context opcode (CALLDATASIZE)
    -- The calldata-length cell at evm_env + 424 is zero-initialised by the
    -- dispatcher's .data section, so CALLDATASIZE pushes 32 zero bytes.
    -- This confirms (a) byte 0x36 routes to evm_calldatasize, (b) the
    -- env-region size bump to 512 bytes makes offset 424 reachable.
  , -- CALLDATASIZE; STOP
    { name           := "calldatasize_zero"
      bytecode       := "0x36, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
    -- ## M14 control-flow opcode (JUMPDEST)
    -- JUMPDEST is an EVM no-op marker. The dispatcher emits empty body
    -- + .advanceAndRet 1, so x10 is bumped by 1 and the loop continues.
    -- This case confirms JUMPDEST doesn't corrupt the stack and the
    -- next opcode (PUSH1) executes correctly.
  , -- JUMPDEST; PUSH1 0x42; STOP — JUMPDEST is a no-op; PUSH1 0x42 lands
    -- the value on the stack; STOP halts. Expected: 0x42 in low limb.
    { name           := "jumpdest_basic"
      bytecode       := "0x5b, 0x60, 0x42, 0x00"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000" }
    -- ## M15 control-flow opcodes (PC, JUMP, JUMPI)
    -- These use the dispatcher's preserved code-base register x21
    -- (initialised in the prologue) to compute PC values and jump
    -- targets. JUMP/JUMPI's "valid-target" check (code[dest] == 0x5b)
    -- is DEFERRED; the test cases below all jump to real JUMPDEST
    -- bytes.
  , -- PC; STOP — PC at offset 0 = 0. Expected: 0 in low limb.
    { name           := "pc_at_zero"
      bytecode       := "0x58, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x42; POP; PC; STOP — PC opcode at offset 3 after the
    -- 2-byte PUSH1 and 1-byte POP. Expected: 3 in low limb.
    { name           := "pc_after_push"
      bytecode       := "0x60, 0x42, 0x50, 0x58, 0x00"
      expectedOutHex := "0300000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x04; JUMP; INVALID; JUMPDEST; PUSH1 0xff; STOP
    -- Layout: 0=PUSH1, 1=0x04, 2=JUMP, 3=INVALID (0xfe), 4=JUMPDEST,
    -- 5=PUSH1, 6=0xff, 7=STOP. JUMP target = 4 (the JUMPDEST byte).
    -- Skips the INVALID at byte 3, lands on JUMPDEST, executes PUSH1
    -- 0xff. Expected: 0xff in low limb.
    { name           := "jump_forward"
      bytecode       := "0x60, 0x04, 0x56, 0xfe, 0x5b, 0x60, 0xff, 0x00"
      expectedOutHex := "ff00000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x01; PUSH1 0x06; JUMPI; INVALID; JUMPDEST; PUSH1 0xff; STOP
    -- Bytecode layout: 0=PUSH1 1=0x01(cond) 2=PUSH1 3=0x06(dest) 4=JUMPI
    -- 5=INVALID(0xfe) 6=JUMPDEST 7=PUSH1 8=0xff 9=STOP.
    -- Stack after both PUSHes: [0x01, 0x06] with 0x06 on top. JUMPI pops
    -- dest=0x06 (top) then cond=0x01 (below). cond != 0 → jump to byte 6,
    -- the JUMPDEST. Then PUSH1 0xff. Expected: 0xff in low limb.
    { name           := "jumpi_taken"
      bytecode       := "0x60, 0x01, 0x60, 0x06, 0x57, 0xfe, 0x5b, 0x60, 0xff, 0x00"
      expectedOutHex := "ff00000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x00; PUSH1 0xff; JUMPI; PUSH1 0x42; STOP
    -- dest=0xff (top), cond=0x00 (below). cond == 0 → fall through.
    -- Next opcode is PUSH1 0x42. Expected: 0x42 in low limb.
    -- Confirms JUMPI advances x10 by 1 on the cond=0 branch instead
    -- of jumping to the (out-of-bounds) dest.
    { name           := "jumpi_not_taken"
      bytecode       := "0x60, 0x00, 0x60, 0xff, 0x57, 0x60, 0x42, 0x00"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000" }
    -- ## M16 hash opcode (KECCAK256 via ECALL bridge to Zisk accelerator)
    -- KECCAK256 pops offset (top of stack) and size (next word), hashes the
    -- memory[offset..offset+size] region, pushes the 32-byte digest.
    -- The handler is all-raw-asm in `.custom` tail (no verified Program).
    -- The dispatcher epilogue ships the `zkvm_keccak256` subroutine + a
    -- 200-byte `zk3_state:` data block.
  , -- PUSH1 0x00; PUSH1 0x00; KECCAK256; STOP — hashes empty bytes.
    -- Expected: standard keccak256("") =
    -- c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
    { name           := "keccak256_empty"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x20, 0x00"
      expectedOutHex := "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470" }
    -- ## M17 LOG opcodes (LOG0-LOG4) — wired as stack-pop no-ops.
    -- LOGn pops (2+n) 256-bit words and advances PC; the EVM event
    -- is dropped (no host log syscall yet).
  , -- PUSH1 0x11; PUSH1 0x22; LOG0; PUSH1 0x33; STOP — LOG0 pops the
    -- two pushed words; PUSH1 0x33 lands on the now-empty stack.
    -- Confirms byte 0xa0 routes correctly and stack delta is +64.
    { name           := "log0_pop"
      bytecode       := "0x60, 0x11, 0x60, 0x22, 0xa0, 0x60, 0x33, 0x00"
      expectedOutHex := "3300000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x01..0x06; LOG4; PUSH1 0xff; STOP — LOG4 pops the six
    -- pushed words (offset + size + 4 topics); PUSH1 0xff lands on
    -- the now-empty stack. Confirms byte 0xa4 routes correctly and
    -- stack delta is +192.
    { name           := "log4_pop"
      bytecode       := "0x60, 0x01, 0x60, 0x02, 0x60, 0x03, 0x60, 0x04, 0x60, 0x05, 0x60, 0x06, 0xa4, 0x60, 0xff, 0x00"
      expectedOutHex := "ff00000000000000000000000000000000000000000000000000000000000000" }
    -- ## M17 / M22 / M24 transient storage (TLOAD/TSTORE)
    -- M24 graduated TLOAD/TSTORE from M17 no-ops to real Option A
    -- transient storage: a separate append-log at 0xa0830000.
    -- Coverage is in the M24 test block at the end of
    -- `opcodeTestCases` (test `tstore_tload_round_trip`, which
    -- additionally asserts the transient log_length surface).
    -- ## M18 trivial no-op handlers (94.6% coverage milestone)
    -- 20 opcodes across 4 builders: haltHandlers (4), pushZeroHandlers
    -- (5), popPushZeroHandlers (6), copyNoopHandlers (5). One
    -- representative test per builder + an INVALID smoke.
  , -- PUSH1 0xff; PUSH1 0x11; PUSH1 0x22; RETURN
    -- RETURN(offset=0x22, size=0x11) reads 0x11 bytes from
    -- memory[0x22..0x33]. Memory hasn't been written, so all bytes
    -- are zero; OUTPUT[0..0x11] = 0, OUTPUT[0x11..32] zero-filled.
    -- Confirms RETURN's data path with no prior MSTORE + the size <
    -- 32 zero-fill. halt_kind = 1.
    --
    -- (Pre-M23 this test asserted the M18 no-op behavior: the
    -- remaining stack top 0xff surfaced via evmAddEpilogue. Updated
    -- in M23 to reflect the new real-RETURN semantics.)
    { name             := "return_pop2_halt"
      bytecode         := "0x60, 0xff, 0x60, 0x11, 0x60, 0x22, 0xf3"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0100000000000000" }
  , -- PUSH1 0xff; PUSH1 0x42; INVALID — INVALID just halts; top of
    -- stack = 0x42. Expected: 0x42 in low limb. Confirms
    -- haltHandlers.INVALID routes 0xfe (instead of falling through to
    -- the h_invalid catch-all unchanged).
    { name           := "invalid_halt"
      bytecode       := "0x60, 0xff, 0x60, 0x42, 0xfe"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000" }
  , -- GAS; STOP — GAS pushes 0 (no gas metering); STOP halts.
    -- Expected: 0 in low limb. Smoke test for pushZeroHandlers.
    { name           := "gas_push_zero"
      bytecode       := "0x5a, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0xab; BALANCE; STOP — BALANCE pops the pushed 0xab as
    -- the address and overwrites with 0. Expected: 0 in low limb.
    -- Smoke test for popPushZeroHandlers.
    { name           := "balance_pop_push_zero"
      bytecode       := "0x60, 0xab, 0x31, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x01; PUSH1 0x02; PUSH1 0x03; MCOPY; PUSH1 0x42; STOP
    -- MCOPY pops 3 args (no-op copy); PUSH1 0x42 lands on the empty
    -- stack. Expected: 0x42 in low limb. Smoke test for
    -- copyNoopHandlers.
    { name           := "mcopy_pop3"
      bytecode       := "0x60, 0x01, 0x60, 0x02, 0x60, 0x03, 0x5e, 0x60, 0x42, 0x00"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000" }
    -- ## M19 child-frame opcodes (CREATE/CALL/CALLCODE/DELEGATECALL/
    -- CREATE2/STATICCALL) — wired as pop-N + push-zero no-ops.
    -- Each opcode pops the EVM-spec input count and writes 32 zero
    -- bytes to the new top-of-stack slot ("call failed" / "address 0").
    -- Three representative test cases spanning the net-pop spectrum
    -- (CREATE = 2, STATICCALL = 5, CALL = 6).
  , -- PUSH1 0x01; PUSH1 0x02; PUSH1 0x03; CREATE; PUSH1 0x42; STOP
    -- CREATE pops 3 (value, offset, size), pushes 1 (addr = 0). Net
    -- pop = 2 words = +64 bytes. Then PUSH1 0x42 lands on the
    -- now-1-deep stack; the address slot at the previous top is
    -- replaced by 0x42 via the new PUSH. Expected: 0x42.
    { name           := "create_pop3_push_zero"
      bytecode       := "0x60, 0x01, 0x60, 0x02, 0x60, 0x03, 0xf0, 0x60, 0x42, 0x00"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x01..0x07; CALL; PUSH1 0xff; STOP
    -- CALL pops 7 (gas, to, value, in_off, in_size, out_off,
    -- out_size), pushes 1 (success = 0). Net pop = 6 = +192 bytes.
    -- Then PUSH1 0xff lands on the 1-deep stack and replaces the
    -- success slot. Expected: 0xff.
    { name           := "call_pop7_push_zero"
      bytecode       := "0x60, 0x01, 0x60, 0x02, 0x60, 0x03, 0x60, 0x04, 0x60, 0x05, 0x60, 0x06, 0x60, 0x07, 0xf1, 0x60, 0xff, 0x00"
      expectedOutHex := "ff00000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x01..0x06; STATICCALL; PUSH1 0xab; STOP
    -- STATICCALL pops 6 (gas, to, in_off, in_size, out_off,
    -- out_size), pushes 1 (success = 0). Net pop = 5 = +160 bytes.
    -- Confirms the third distinct ADDI immediate (160). Expected:
    -- 0xab.
    { name           := "staticcall_pop6_push_zero"
      bytecode       := "0x60, 0x01, 0x60, 0x02, 0x60, 0x03, 0x60, 0x04, 0x60, 0x05, 0x60, 0x06, 0xfa, 0x60, 0xab, 0x00"
      expectedOutHex := "ab00000000000000000000000000000000000000000000000000000000000000" }
    -- ## M20 arithmetic no-ops (MULMOD, EXP) — the LAST TWO unwired
    -- opcodes; M20 brings tinyInterpRegistry to 100% coverage 🎯.
    -- Both ship as placeholders; real upgrades follow in M21+.
  , -- PUSH1 0x03; PUSH1 0x05; PUSH1 0x07; MULMOD; PUSH1 0x42; STOP
    -- MULMOD pops 3 (a, b, N), pushes 1 (result = 0). Net pop = 2 =
    -- +64 bytes. PUSH1 0x42 lands on the 1-deep stack and replaces
    -- the zero result. Expected: 0x42.
    { name           := "mulmod_pop3"
      bytecode       := "0x60, 0x03, 0x60, 0x05, 0x60, 0x07, 0x09, 0x60, 0x42, 0x00"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x02; PUSH1 0x03; EXP; PUSH1 0xff; STOP
    -- EXP pops 2 (base, exponent), pushes 1 (result = 0). Net pop =
    -- 1 = +32 bytes. PUSH1 0xff lands on the 1-deep stack and
    -- replaces the zero result. Expected: 0xff.
    { name           := "exp_pop2"
      bytecode       := "0x60, 0x02, 0x60, 0x03, 0x0a, 0x60, 0xff, 0x00"
      expectedOutHex := "ff00000000000000000000000000000000000000000000000000000000000000" }
    -- ## M8 unsigned division opcodes
    -- (SDIV / SMOD deferred: their verified bodies use a saved-ra-ret
    -- pattern that bypasses the dispatcher's standard wrapper tail;
    -- integrating them needs a trampoline approach planned as the
    -- next codegen PR.)
  , -- PUSH1 0x02; PUSH1 0x0a; DIV; STOP — 10 / 2 = 5
    { name           := "div_basic"
      bytecode       := "0x60, 0x02, 0x60, 0x0a, 0x04, 0x00"
      expectedOutHex := "0500000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x03; PUSH1 0x0a; MOD; STOP — 10 % 3 = 1
    { name           := "mod_basic"
      bytecode       := "0x60, 0x03, 0x60, 0x0a, 0x06, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
    -- ## M9 signed division opcodes (trampoline wrapper for saved-ra-ret)
  , -- PUSH1 0x02; PUSH1 0x05; SDIV; STOP — signed 5 / 2 = 2 (positive path)
    { name           := "sdiv_basic"
      bytecode       := "0x60, 0x02, 0x60, 0x05, 0x05, 0x00"
      expectedOutHex := "0200000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x02; PUSH1 0x01; NOT; SDIV; STOP
    -- Stack at SDIV: top = NOT(1) = -2 (= 0xff..fe), second = 2.
    -- EVM SDIV pops `a` (top) then `b`; computes `a / b` in two's
    -- complement. -2 / 2 = -1 (= 0xff..ff).
    { name           := "sdiv_negative"
      bytecode       := "0x60, 0x02, 0x60, 0x01, 0x19, 0x05, 0x00"
      expectedOutHex := "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" }
  , -- PUSH1 0x05; PUSH1 0x01; NOT; SMOD; STOP
    -- Stack at SMOD: top = -2, second = 5. EVM SMOD: a % b with
    -- sign(result) = sign(a). -2 % 5 = -2 (= 0xff..fe).
    { name           := "smod_negative"
      bytecode       := "0x60, 0x05, 0x60, 0x01, 0x19, 0x07, 0x00"
      expectedOutHex := "feffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" }
    -- ## M10 self-calling opcodes (inline mod_callable / mul_callable)
  , -- PUSH1 0x04; PUSH1 0x03; PUSH1 0x02; ADDMOD; STOP — (2+3) % 4 = 1
    -- ADDMOD pops `a` (top), then `b`, then `N`. So stack
    -- [N=4, b=3, a=2] yields (a+b) mod N = 5 mod 4 = 1.
    { name           := "addmod_basic"
      bytecode       := "0x60, 0x04, 0x60, 0x03, 0x60, 0x02, 0x08, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x00; PUSH1 0x03; PUSH1 0x02; ADDMOD; STOP — divisor=0 ⇒ 0
    { name           := "addmod_div_zero"
      bytecode       := "0x60, 0x00, 0x60, 0x03, 0x60, 0x02, 0x08, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
    -- ## M21 real calldata (CALLDATASIZE / CALLDATALOAD / CALLDATACOPY)
    -- The dispatcher prologue now populates env.callDataPtrOff (416)
    -- and env.callDataLenOff (424) from the ziskemu `-i` input file.
    -- These three cases confirm the wiring end-to-end:
    --   1. CALLDATASIZE reads len from env.
    --   2. CALLDATALOAD reads 32 BE bytes from calldata.
    --   3. CALLDATACOPY copies calldata bytes into EVM memory; the
    --      follow-up MLOAD round-trips them back to the stack.
  , -- CALLDATASIZE; STOP with calldata = 0xdeadbeef (4 bytes).
    -- Expected: size = 4 in the low limb's low byte → "04 00...00".
    { name           := "calldatasize_with_input"
      bytecode       := "0x36, 0x00"
      calldata       := "0xdeadbeef"
      expectedOutHex := "0400000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x00; CALLDATALOAD; STOP with calldata = 32 bytes
    -- 0x0102…20 (same content as push32_basic). CALLDATALOAD reads
    -- 32 BE bytes from calldata[0..32] into the EVM word, then the
    -- OUTPUT_ADDR copy surfaces the 4 LE u64 limbs verbatim — the
    -- byte sequence matches push32_basic exactly.
    { name           := "calldataload_basic"
      bytecode       := "0x60, 0x00, 0x35, 0x00"
      calldata       := "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20"
      expectedOutHex := "201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201" }
  , -- PUSH1 0x04 (size); PUSH1 0x00 (offset); PUSH1 0x00 (destOffset);
    -- CALLDATACOPY; PUSH1 0x00; MLOAD; STOP with calldata = 0xdeadbeef.
    -- Copies 4 bytes into memory[0..4]; MLOAD reads memory[0..32] BE
    -- → u256 = 0xdeadbeef << 224 (high 4 BE bytes are deadbeef, rest
    -- zero). In limbs: limb 3 = 0xdeadbeef00000000, others 0. Output
    -- LE bytes of limb 3 = 00 00 00 00 ef be ad de.
    { name           := "calldatacopy_basic"
      bytecode       := "0x60, 0x04, 0x60, 0x00, 0x60, 0x00, 0x37, 0x60, 0x00, 0x51, 0x00"
      calldata       := "0xdeadbeef"
      expectedOutHex := "00000000000000000000000000000000000000000000000000000000efbeadde" }
    -- ## M22 real storage (SLOAD / SSTORE via pre-loaded slot table)
    -- The dispatcher prologue copies the input file's storage segment
    -- into a writable `evm_slot_table` (16 KiB, 256 slots × 64 B) and
    -- records the count in `env.slotTableCountOff = 448`. SLOAD /
    -- SSTORE inline-asm bodies scan the table linearly:
    --   1. round_trip      — SSTORE then SLOAD with empty preload.
    --   2. preloaded_match — SLOAD against a preloaded key.
    --   3. preloaded_no_match — SLOAD against an absent key → 0.
    --   4. overwrites_preload — SSTORE replaces a preloaded value.
  , -- PUSH1 0x42; PUSH1 0x00; SSTORE; PUSH1 0x00; SLOAD; STOP
    -- SSTORE pops key=0x00 (top) then value=0x42; appends slot.
    -- SLOAD pops key=0x00; reads value=0x42 back.
    { name           := "sstore_then_sload_round_trip"
      bytecode       := "0x60, 0x42, 0x60, 0x00, 0x55, 0x60, 0x00, 0x54, 0x00"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x00; SLOAD; STOP with preload [(0x00, 0xdead)].
    -- 0xdead in limb 0 LE = ad de 00 00 00 00 00 00.
    { name           := "sload_preloaded_match"
      bytecode       := "0x60, 0x00, 0x54, 0x00"
      storage        := "(0x00, 0xdead)"
      expectedOutHex := "adde000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0xff; SLOAD; STOP with preload [(0x00, 0xdead)].
    -- key 0xff doesn't match preloaded 0x00 → SLOAD pushes zero.
    { name           := "sload_preloaded_no_match"
      bytecode       := "0x60, 0xff, 0x54, 0x00"
      storage        := "(0x00, 0xdead)"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH2 0xbeef; PUSH1 0x00; SSTORE; PUSH1 0x00; SLOAD; STOP with
    -- preload [(0x00, 0xdead)]. SSTORE finds a matching key and
    -- overwrites the value in place (does NOT append). SLOAD reads
    -- back 0xbeef. 0xbeef in limb 0 LE = ef be 00 00 00 00 00 00.
    { name           := "sstore_overwrites_preload"
      bytecode       := "0x61, 0xbe, 0xef, 0x60, 0x00, 0x55, 0x60, 0x00, 0x54, 0x00"
      storage        := "(0x00, 0xdead)"
      expectedOutHex := "efbe000000000000000000000000000000000000000000000000000000000000" }
    -- ## M23 real RETURN / REVERT with returndata buffer + halt-kind
    -- Both opcodes graduate from M18 halt no-ops to real bodies that:
    --   - pop (offset, size)
    --   - copy memory[offset..offset+min(size,32)] to OUTPUT_ADDR[0..32]
    --     (zero-padded if size < 32; clamped at 32 in M23)
    --   - write halt_kind (1 = RETURN, 2 = REVERT) to OUTPUT_ADDR + 32
    --   - halt via .exit_no_epilogue (skipping evmAddEpilogue's stack-top copy)
    -- The 32-byte returndata cap and the deferred INVALID/SELFDESTRUCT
    -- halt-kind tagging are documented in CODEGEN.md M23.
  , -- PUSH1 0x42; PUSH1 0x00; MSTORE; PUSH1 0x20; PUSH1 0x00; RETURN.
    -- MSTORE writes BE(0x42) to memory[0..32] (= 31 zero bytes then 0x42).
    -- RETURN(offset=0, size=32) copies that to OUTPUT[0..32].
    { name             := "return_word_basic"
      bytecode         := "0x60, 0x42, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000042"
      expectedHaltKind := "0100000000000000" }
  , -- PUSH1 0xff; PUSH1 0x00; MSTORE8; PUSH1 0x01; PUSH1 0x00; RETURN.
    -- MSTORE8 writes 1 byte (0xff) at memory[0]; rest of memory zero.
    -- RETURN(offset=0, size=1) copies 1 byte; OUTPUT[1..32] is zero-filled
    -- by the body's pre-copy SD pass. Exercises the size < 32 path.
    { name             := "return_small_pads_zeros"
      bytecode         := "0x60, 0xff, 0x60, 0x00, 0x53, 0x60, 0x01, 0x60, 0x00, 0xf3"
      expectedOutHex   := "ff00000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0100000000000000" }
  , -- PUSH1 0x42; PUSH1 0x00; MSTORE; PUSH1 0x20; PUSH1 0x00; REVERT.
    -- Same data path as return_word_basic but byte 0xfd (REVERT) instead
    -- of 0xf3 (RETURN). Returndata bytes identical; halt_kind differs.
    -- This is the test that proves RETURN and REVERT are distinguishable.
    { name             := "revert_word_basic"
      bytecode         := "0x60, 0x42, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xfd"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000042"
      expectedHaltKind := "0200000000000000" }
    -- ## M24 storage on Option A — append-log + journal + real TLOAD/TSTORE
    -- Three tests exercise the new machinery via the OUTPUT[40..48]
    -- (persistent log length) and OUTPUT[48..56] (transient log
    -- length) surfaces written by `.exit_no_epilogue`:
    --   1. SSTORE then REVERT → persistent log rolls back to checkpoint=0
    --   2. SSTORE then STOP   → persistent log commits at length=1
    --   3. TSTORE + TLOAD     → real round-trip + transient length=1
  , -- PUSH1 0x42; PUSH1 0x00; SSTORE; PUSH1 0x00; PUSH1 0x00; REVERT.
    -- SSTORE appends entry (log_length 0→1). REVERT body restores
    -- persistent log_length from checkpoint (= 0). Returndata is
    -- empty (size=0); halt_kind=2. Persistent log_length back to 0.
    { name                        := "sstore_revert_rolls_back"
      bytecode                    := "0x60, 0x42, 0x60, 0x00, 0x55, 0x60, 0x00, 0x60, 0x00, 0xfd"
      expectedOutHex              := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind            := "0200000000000000"
      expectedPersistentLogLength := "0000000000000000" }
  , -- PUSH1 0x42; PUSH1 0x00; SSTORE; STOP.
    -- SSTORE appends entry (log_length 0→1). STOP commits — no
    -- rollback. Result is the post-SSTORE stack top (stack empty,
    -- evm_stack_top region is .zero-initialised so the 32 bytes
    -- read are all zero). Halt_kind=0. Persistent log_length=1.
    { name                        := "sstore_no_revert_commits"
      bytecode                    := "0x60, 0x42, 0x60, 0x00, 0x55, 0x00"
      expectedOutHex              := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind            := "0000000000000000"
      expectedPersistentLogLength := "0100000000000000" }
  , -- PUSH1 0x42; PUSH1 0x00; TSTORE; PUSH1 0x00; TLOAD; STOP.
    -- TSTORE appends transient entry (transient_log_length 0→1).
    -- TLOAD scans transient log, finds entry, pushes 0x42 onto stack.
    -- STOP surfaces stack top = 0x42. **Proves TLOAD/TSTORE moved
    -- off the M17 no-op into real Option A semantics.**
    { name                       := "tstore_tload_round_trip"
      bytecode                   := "0x60, 0x42, 0x60, 0x00, 0x5d, 0x60, 0x00, 0x5c, 0x00"
      expectedOutHex             := "4200000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind           := "0000000000000000"
      expectedTransientLogLength := "0100000000000000" }
  ]

/-- Find a test case by name. -/
def lookupTestCase (name : String) : Option OpcodeTestCase :=
  opcodeTestCases.find? (fun tc => tc.name == name)

/-- All test case names, one per line — emitted by
    `--list-test-cases` for the bash runner to enumerate. -/
def testCaseNames : List String :=
  opcodeTestCases.map OpcodeTestCase.name

/-- Build a `BuildUnit` that runs `tc.bytecode` through the M5b
    dispatcher (`tinyInterpRegistry`). The exit body is
    `evmAddEpilogue`, which copies the 32 bytes at `[x12]` (the post-
    STOP stack top) to `OUTPUT_ADDR`. -/
def buildTestCaseUnit (tc : OpcodeTestCase) : BuildUnit :=
  buildDispatchUnit tinyInterpRegistry evmAddEpilogue tc.bytecode

end EvmAsm.Codegen.Tests
