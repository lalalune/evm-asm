/-
  EvmAsm.Evm64.SMod.Compose.Base

  Shared composition infrastructure for SMOD: `smodCode` (the union of
  all sub-block `CodeReq`s), subsumption helpers tying sub-block codes
  back to `smodCode`, and shared length lemmas.

  This module re-exports the first concrete SMOD compose scaffolding:
  wrapper offsets, code handles, and top-level code subsumption lemmas.
-/

import EvmAsm.Evm64.SMod.LimbSpec
import EvmAsm.Evm64.SMod.AddrNorm
import EvmAsm.Evm64.SMod.Compose.BaseOffsets
import EvmAsm.Evm64.SMod.Compose.CodeHandles
import EvmAsm.Evm64.SMod.Compose.BaseCode
import EvmAsm.Evm64.SMod.Compose.DispatchReadyPost
import EvmAsm.Evm64.SMod.Compose.ModCallCallable

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Rv64

end EvmAsm.Evm64.SMod.Compose
