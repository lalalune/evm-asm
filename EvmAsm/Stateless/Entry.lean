/-
  EvmAsm.Stateless.Entry

  Top-level `run_stateless_guest` Program. Mirrors the Python
  `execution-specs/src/ethereum/forks/amsterdam/stateless_guest.py:33`
  entry point.

  Once `Stateless.SSZ.Decode`, `Stateless.Headers`, `Stateless.Witness`,
  `Stateless.Block`, `Stateless.Transaction`, and `Stateless.VM` are
  populated, this file will compose them in the canonical order:

  ```
  read_input from INPUT_ADDR + INPUT_DATA_OFFSET
      |
      v
  Stateless.SSZ.Decode.deserialize_stateless_input
      |
      v
  Stateless.Headers.validate_headers
      |
      v
  Stateless.Witness.{NodeDb,CodeDb}.build
      |
      v
  Stateless.ExecutionEngine.execute_new_payload_request
      | (recursively into Block / Transaction / VM)
      v
  Stateless.SSZ.Encode.serialize_stateless_output
      |
      v
  write_output to OUTPUT_ADDR + 0
      |
      v
  HALT
  ```

  ## Memory layout (preconditions)
  - `INPUT_ADDR + INPUT_DATA_OFFSET` holds the host-supplied
    SSZ-encoded `SszStatelessInput`.
  - All RAM in `STATELESS_WORK_BASE .. STATELESS_WORK_BASE + 0x20000000`
    is available for scratch (see `MemoryLayout.lean`).

  ## Side effects (postconditions when fully implemented)
  - Writes the SSZ encoding of `StatelessValidationResult` to
    `OUTPUT_ADDR + 0..N`.
  - Halts with the codegen halt stub.

  ## PR3 status

  Decode (`Stateless.SSZ.Decode.read_chain_id`) reads `chain_id` from
  the host-supplied `SszStatelessInput` on `INPUT_ADDR`; encode
  (`Stateless.SSZ.Encode.serialize_stateless_output`) writes the
  41-byte SSZ encoding of
  `StatelessValidationResult(root = 0, valid = false,
                             chain_id = <decoded>)`
  at `OUTPUT_ADDR`. The rest of the pipeline (header validation,
  witness DBs, STF execution) is still stubbed.

  Module paths that aren't implemented yet still call
  `EvmAsm.Stateless.unimplemented_exit` with a distinct reason code
  (precompiles, missing witness nodes, etc.) -- see
  `EvmAsm/Stateless/Unimplemented.lean`.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Stateless.SSZ.Decode.Program
import EvmAsm.Stateless.SSZ.Encode.Program

namespace EvmAsm.Stateless

open EvmAsm.Rv64

/-- PR3 body: decode `chain_id` from `INPUT_ADDR`, then encode the
    `StatelessValidationResult` (with `root = 0`, `valid = false`,
    and the decoded `chain_id`) at `OUTPUT_ADDR`. Falls through to the
    halt stub appended by `emitBuildUnit`.

    Replaced in successor PRs by the full decode → validate → execute
    → encode pipeline. -/
def run_stateless_guest : Program :=
  EvmAsm.Stateless.SSZ.Decode.read_chain_id ++
  EvmAsm.Stateless.SSZ.Encode.serialize_stateless_output

end EvmAsm.Stateless
