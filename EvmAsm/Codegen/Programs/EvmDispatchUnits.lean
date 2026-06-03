/-
  EvmAsm.Codegen.Programs.EvmDispatchUnits

  Dispatch BuildUnit definitions extracted from Programs/Evm.lean to
  satisfy the 1500-line file-size cap.
-/

import EvmAsm.Codegen.Programs.Evm

namespace EvmAsm.Codegen

def tinyInterpDispatchAddUnit : BuildUnit :=
  buildDispatchUnit tinyInterpRegistry evmAddEpilogue tinyInterpAddBytecode

def tinyInterpDispatchAdd2Unit : BuildUnit :=
  buildDispatchUnit tinyInterpRegistry evmAddEpilogue tinyInterpAdd2Bytecode

/-! ## runtime_dispatcher — M8.5 runtime-bytecode dispatcher

    Same `tinyInterpRegistry` and `evmAddEpilogue` as the
    `tiny_interp_dispatch_*` units, but the dispatcher prologue
    reads `x10` from `INPUT_ADDR + INPUT_DATA_OFFSET = 0x40000010`
    instead of an in-`.data` label. One ELF runs any bytecode; the
    bash test harness packs each per-case bytecode into a
    ziskemu `-i <file>` payload and reuses the same dispatcher
    ELF for every case.

    See `EvmAsm/Codegen/Dispatch.lean` for `buildRuntimeDispatchUnit`
    and the runtime prologue/data-section helpers. -/
def runtimeDispatcherUnit : BuildUnit :=
  buildRuntimeDispatchUnit tinyInterpRegistry evmAddEpilogue

end EvmAsm.Codegen
