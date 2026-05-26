/-
  EvmAsm.Stateless.SSZ.Encode.Program

  Serializer for `SszStatelessValidationResult` -- the NEW (post-
  zkevm-projects/d7fe16ab8) variable-size SSZ Container.

  Reference: `execution-specs/src/ethereum/forks/amsterdam/stateless_ssz.py`
  (`class SszStatelessValidationResult(Container)`,
   `class SszChainConfig(Container)`,
   `class SszForkConfig(Container)`).

  ## SSZ wire layout (73 bytes for empty active_fork)

  Outer container `SszStatelessValidationResult`:
  | Offset  | Size | Field                       | Type             |
  |---------|------|-----------------------------|------------------|
  |  0..32  |   32 | `new_payload_request_root`  | `Bytes32`        |
  |     32  |    1 | `successful_validation`     | `boolean`        |
  | 33..37  |    4 | offset of `chain_config`    | u32 LE = 37      |
  | 37..73  |   36 | `chain_config` SSZ          | nested container |

  Inside `SszChainConfig` (bytes 37..73):
  | Offset  | Size | Field                       | Type             |
  |---------|------|-----------------------------|------------------|
  | 37..45  |    8 | `chain_id`                  | `uint64`         |
  | 45..49  |    4 | offset of `active_fork`     | u32 LE = 12      |
  | 49..73  |   24 | `active_fork` SSZ           | nested container |

  Inside `SszForkConfig` (bytes 49..73):
  | Offset  | Size | Field                       | Type             |
  |---------|------|-----------------------------|------------------|
  | 49..57  |    8 | `fork`                      | `uint64` = 0     |
  | 57..61  |    4 | offset of `activation`      | u32 LE = 16      |
  | 61..65  |    4 | offset of `blob_schedule`   | u32 LE = 24      |
  | 65..73  |    8 | `activation` SSZ            | nested container |
  | 73..73  |    0 | `blob_schedule` (empty list)| `SszList[..,1]`  |

  Inside `SszForkActivation` (bytes 65..73):
  | Offset  | Size | Field                       | Type             |
  |---------|------|-----------------------------|------------------|
  | 65..69  |    4 | offset of `block_number`    | u32 LE = 8       |
  | 69..73  |    4 | offset of `timestamp`       | u32 LE = 8       |
  | 73..73  |    0 | `block_number` (empty list) | `SszList[u64,1]` |
  | 73..73  |    0 | `timestamp` (empty list)    | `SszList[u64,1]` |

  Total: 73 bytes (the smallest valid encoding; non-empty active_fork
  variants append further bytes past byte 73, but this Lean encoder
  always emits the empty-active_fork variant -- a real STF wiring is
  a follow-up).

  ## Caller contract

  Caller places both SSZ fields in registers:

      x10 : chain_id              (u64 at output bytes 37..45)
      x11 : successful_validation (low byte at output byte 32)

  The encoder must only see `0` or `1` in `x11`'s low byte; the
  decoder's `decode_validation_bit` guarantees that.

  Bytes 0..32 are zeroed here as a stub; the `stateless_guest`
  caller's epilogue overwrites them with `hash_tree_root(witness)`.

  ## Memory layout

  - **Preconditions**:
    - `OUTPUT_BASE = 0xa0010000` is ziskemu's public-output region
      (mirrors `EvmAsm.Codegen.OUTPUT_ADDR`).
    - `[OUTPUT_BASE, OUTPUT_BASE + 73)` lies inside the RAM zone
      (`RAM_MEM_START..RAM_MEM_END`) and is accepted by
      `isValidMemAddr` per issue #5164.
    - `x10` holds the u64 `chain_id` to encode.
  - **Postconditions**: 73 bytes at `OUTPUT_BASE` carry the SSZ
    encoding of `SszStatelessValidationResult(root = 0,
    successful_validation = x11&1, chain_config = SszChainConfig(
    chain_id = x10, active_fork = SszForkConfig(fork = 0,
    activation = SszForkActivation(empty, empty),
    blob_schedule = empty)))`.
  - **Clobbers**: `x5` (constant scratch), `x6` (base pointer),
    `x7` (packed word work).
  - **Exit**: falls through to the caller's halt stub.

  ## Alignment

  Every store is u64-aligned (offsets 0, 8, 16, 24, 32, 40, 48, 56,
  64) or a single byte (offset 72). No unaligned word/double store
  -- consistent with the verified RV64 subset already used by the
  rest of `EvmAsm/Stateless/`.

  ## Packed-u64 layout (constants at byte positions inside each store)

  - byte 32 (SD): `[b, 0x25, 0, 0, 0, c[0], c[1], c[2]]`
  - byte 40 (SD): `[c[3], c[4], c[5], c[6], c[7], 0x0c, 0, 0]`
  - byte 48 (SD): all zero (offset_active_fork high + fork low 7)
  - byte 56 (SD): `[0, 0x10, 0, 0, 0, 0x18, 0, 0]`
  - byte 64 (SD): `[0, 0x08, 0, 0, 0, 0x08, 0, 0]`
  - byte 72 (SB): zero (high byte of offset_ts = 8)

  ## Frame

  21 instructions: 1 LI base + 4 SD (zero hash) + (3 + 1 OR + 1 SD)
  bytes32 + (2 + 1 OR + 1 SD) bytes40 + 1 SD (zero) bytes48 + 2
  bytes56 + 2 bytes64 + 1 SB byte72.
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

    Caller contract:
      - `x10` holds the u64 `chain_id` to encode.
      - `x11` holds `successful_validation` (low byte = 0 or 1).
      - `x12` holds `active_fork.fork` (u64) to encode at bytes 49..57.

    The body writes exactly 73 bytes (SSZ encoding of
    `SszStatelessValidationResult` with empty `activation` +
    `blob_schedule`) at `OUTPUT_BASE`, and falls through to the
    caller's halt stub. -/
def serialize_stateless_output : Program :=
  LI .x6 OUTPUT_BASE ;;
  -- bytes [0..32) hash zero-stub (epilogue overwrites)
  SD .x6 .x0 0  ;;
  SD .x6 .x0 8  ;;
  SD .x6 .x0 16 ;;
  SD .x6 .x0 24 ;;
  -- bytes [32..40): bool || offset_chain_config=37 || chain_id_lo3
  SLLI .x7 .x10 40 ;;
  LI .x5 0x2500 ;;
  OR' .x7 .x7 .x5 ;;
  OR' .x7 .x7 .x11 ;;
  SD .x6 .x7 32 ;;
  -- bytes [40..48): chain_id_hi5 || offset_active_fork=12
  SRLI .x7 .x10 24 ;;
  LI .x5 0xc0000000000 ;;
  OR' .x7 .x7 .x5 ;;
  SD .x6 .x7 40 ;;
  -- bytes [48..56): offset_active_fork high (0) || fork low 7 bytes
  SLLI .x7 .x12 8 ;;
  SD .x6 .x7 48 ;;
  -- bytes [56..64): fork high byte || offset_activation=16 || offset_blob_schedule_lo3
  SRLI .x7 .x12 56 ;;
  LI .x5 0x180000001000 ;;
  OR' .x7 .x7 .x5 ;;
  SD .x6 .x7 56 ;;
  -- bytes [64..72): offset_blob_schedule high (0) || offset_bn=8 || offset_ts_lo3
  LI .x7 0x80000000800 ;;
  SD .x6 .x7 64 ;;
  -- byte 72: offset_ts high (0)
  SB .x6 .x0 72

end EvmAsm.Stateless.SSZ.Encode
