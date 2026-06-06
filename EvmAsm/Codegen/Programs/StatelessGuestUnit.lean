/- EvmAsm.Codegen.Programs.StatelessGuestUnit
  Forwarding shim — `statelessGuestUnit` is now defined in
  `EvmAsm.Codegen.Programs.RegistryMain` as part of the registry split.
-/
import EvmAsm.Codegen.Dispatch
import EvmAsm.Stateless.Entry
import EvmAsm.Codegen.Programs.StatelessGuestData
import EvmAsm.Codegen.Programs.StatelessGuestEpilogue
import EvmAsm.Codegen.Programs.BlockVerdictV2
  Forwarding shim — the canonical definition of `statelessGuestUnit`
  has moved to `EvmAsm.Codegen.Programs.StatelessGuest`.
-/
import EvmAsm.Codegen.Programs.StatelessGuest
