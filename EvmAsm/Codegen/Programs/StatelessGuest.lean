/-
  EvmAsm.Codegen.Programs.StatelessGuest

  BuildUnit wiring for the stateless guest body, epilogue, and data section.
-/

import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.StatelessGuestData
import EvmAsm.Codegen.Programs.StatelessGuestEpilogue
import EvmAsm.Codegen.Programs.BlockVerdictV2
import EvmAsm.Stateless.Entry

namespace EvmAsm.Codegen

/-- Stateless guest program with the codegen epilogue and guest data section. -/
def statelessGuestUnit : BuildUnit := {
  body        := EvmAsm.Stateless.run_stateless_guest
  epilogueAsm := statelessGuestEpilogue
  -- guest scratch + the Step-2 verdict's data (zk3_state / rfu_* are dedup'd out
  -- of the guest section since the appended verdict section provides them).
  dataAsm     := statelessGuestDataSection ++ "\n" ++ statelessVerdictV2GuestData
}

end EvmAsm.Codegen
