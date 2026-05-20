/-
  EvmAsm.Stateless.SSZ.Encode.Program

  Serializer for `SszStatelessValidationResult` -- 41 bytes of fixed-size
  SSZ Container.

  Reference: `execution-specs/src/ethereum/forks/amsterdam/stateless_ssz.py`
  (`class SszStatelessValidationResult(Container)`,
   `class SszChainConfig(Container)`).

  ## SSZ wire layout (all fixed-size, plain concatenation)

  | Offset  | Size | Field                       | Type       |
  |---------|------|-----------------------------|------------|
  |  0..32  |   32 | `new_payload_request_root`  | `Bytes32`  |
  |     32  |    1 | `successful_validation`     | `boolean`  |
  | 33..41  |    8 | `chain_config.chain_id`     | `uint64`   |

  Total: 41 bytes.

  ## Caller contract (PR3)

  Caller places the `chain_id` to encode in `x10` (u64). Other fields
  are still stubbed in this PR:

      new_payload_request_root = 0x00...00  (32 zero bytes)
      successful_validation    = false        (one zero byte at offset 32)
      chain_id                 = x10          (LE bytes at offset 33..41)

  PR3 wires `x10` from `Stateless.SSZ.Decode.read_chain_id`, so the
  decoded `chain_id` from `INPUT_ADDR` flows through to `OUTPUT_ADDR`
  unchanged. Later PRs replace the zero `root` (PR5: SSZ
  `hash_tree_root`) and the `false` flag (PR7+: STF verdict).

  ## Memory layout

  - **Preconditions**:
    - `OUTPUT_BASE = 0xa0010000` is ziskemu's public-output region
      (mirrors `EvmAsm.Codegen.OUTPUT_ADDR`).
    - `[OUTPUT_BASE, OUTPUT_BASE + 41)` lies inside the RAM zone
      (`RAM_MEM_START..RAM_MEM_END`) and is accepted by
      `isValidMemAddr` per issue #5164.
    - `x10` holds the u64 `chain_id` to encode.
  - **Postconditions**: 41 bytes at `OUTPUT_BASE` carry the SSZ
    encoding of `StatelessValidationResult(root = 0, valid = false,
    chain_id = x10)`.
  - **Clobbers**: `x6` (base pointer), `x7` (shifted chain_id work).
  - **Exit**: falls through to the caller's halt stub.

  ## Frame

  9 instructions: 1 LI (base) + 4 SD (zero hash) + 1 SLLI + 1 SD
  (packed bool || low-7 chain bytes) + 1 SRLI + 1 SB (high chain
  byte).

  ## Encoding math

  Let `c = chain_id` (u64). LE encoding writes bytes
  `c & 0xff`, `(c >> 8) & 0xff`, ..., `(c >> 56) & 0xff`
  at positions 33, 34, ..., 40 respectively.

  We need bytes 32..40 to be `0 || c[0..7]` (bool=false then first 7
  LE bytes of `c`). As a u64 stored LE at offset 32, that value is
  exactly `c << 8`:

      ((c << 8) >> ( 0 * 8)) & 0xff = 0          (the bool)
      ((c << 8) >> ( 1 * 8)) & 0xff = c & 0xff   (LE byte 0 of c)
      ((c << 8) >> ( 2 * 8)) & 0xff = (c >> 8) & 0xff
      ...
      ((c << 8) >> ( 7 * 8)) & 0xff = (c >> 48) & 0xff

  Byte 40 is then `c >> 56` (the high LE byte), emitted with a
  separate `SB`.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Stateless.MemoryLayout

namespace EvmAsm.Stateless.SSZ.Encode

open EvmAsm.Rv64

/-- Output region base address. Duplicated from
    `EvmAsm.Codegen.Programs.OUTPUT_ADDR` so `EvmAsm/Stateless/` stays
    free of the codegen umbrella. -/
def OUTPUT_BASE : Word := 0xa0010000

/-- Parameterized serializer Program.

    Caller contract: `x10` holds the u64 `chain_id` to encode. The
    body writes the 41-byte SSZ encoding of `StatelessValidationResult`
    at `OUTPUT_BASE` and falls through to the caller's halt stub. -/
def serialize_stateless_output : Program :=
  LI .x6 OUTPUT_BASE ;;
  SD .x6 .x0 0  ;;
  SD .x6 .x0 8  ;;
  SD .x6 .x0 16 ;;
  SD .x6 .x0 24 ;;
  SLLI .x7 .x10 8 ;;
  SD .x6 .x7 32 ;;
  SRLI .x7 .x10 56 ;;
  SB .x6 .x7 40

end EvmAsm.Stateless.SSZ.Encode
