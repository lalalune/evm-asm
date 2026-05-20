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

/-- Registry of test cases. M5a/M5b's two original bytecodes are
    migrated here; they keep the original expected hex strings so
    the new harness cross-checks against the existing per-bytecode
    scripts. -/
def opcodeTestCases : List OpcodeTestCase :=
  [ -- PUSH1 0xFF; PUSH1 0x01; ADD; STOP → 0x100, LE limbs [0x100, 0, 0, 0]
    { name           := "add_basic"
      bytecode       := "0x60, 0xff, 0x60, 0x01, 0x01, 0x00"
      expectedOutHex := "0001000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x10; PUSH1 0x20; ADD; PUSH1 0x30; ADD; STOP → 0x60
    { name           := "add_chain"
      bytecode       := "0x60, 0x10, 0x60, 0x20, 0x01, 0x60, 0x30, 0x01, 0x00"
      expectedOutHex := "6000000000000000000000000000000000000000000000000000000000000000" }
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
