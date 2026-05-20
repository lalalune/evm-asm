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

  ## PR2 stub

  The decode / validate / execute pipeline is not yet implemented;
  the body is just `serialize_stateless_output_stub`, which writes the
  41-byte SSZ encoding of
  `StatelessValidationResult(root = 0, valid = false, chain_id = 1)`
  at `OUTPUT_ADDR`, then falls through to the codegen halt stub. This
  is enough for a Python harness to diff `ziskemu`'s public output
  against the reference SSZ encoder.

  Module paths that aren't implemented yet still call
  `EvmAsm.Stateless.unimplemented_exit` with a distinct reason code
  (precompiles, missing witness nodes, etc.) -- see
  `EvmAsm/Stateless/Unimplemented.lean`.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Stateless.SSZ.Encode.Program

namespace EvmAsm.Stateless

open EvmAsm.Rv64

/-- PR2 stub: emit the 41-byte stub `StatelessValidationResult` to
    `OUTPUT_ADDR` and fall through to the halt stub. Replaced in
    successor PRs by the full decode → validate → execute → encode
    pipeline. -/
def run_stateless_guest : Program :=
  EvmAsm.Stateless.SSZ.Encode.serialize_stateless_output_stub

end EvmAsm.Stateless
