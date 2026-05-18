/-
  EvmAsm.Codegen

  Umbrella re-export for the codegen tool. See CODEGEN.md for the M0–M5
  roadmap. Codegen is purely additive — it does not modify the verified core
  and carries no proofs.
-/

import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs
import EvmAsm.Codegen.Driver
import EvmAsm.Codegen.Cli
import EvmAsm.Codegen.RoundTripTests
