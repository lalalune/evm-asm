/-
  EvmAsm.Codegen.Programs

  Registry of programs the codegen tool knows how to emit.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Evm64.Add.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- M0 smoke target. Loads two immediates, adds them, falls through to the
    halt stub appended by `emitTextUnit`. Expected post-state: `x12 = 100`. -/
def smoke : Program :=
  LI .x10 (42 : Word) ;;
  LI .x11 (58 : Word) ;;
  ADD .x12 .x10 .x11

/-- Look up a program by name. Returns `none` for unknown names so the CLI
    can produce a clean error. -/
def lookupProgram : String → Option Program
  | "smoke"   => some smoke
  | "evm_add" => some EvmAsm.Evm64.evm_add
  | _         => none

/-- List of known program names, for use in CLI usage strings. -/
def knownProgramNames : List String := ["smoke", "evm_add"]

end EvmAsm.Codegen
