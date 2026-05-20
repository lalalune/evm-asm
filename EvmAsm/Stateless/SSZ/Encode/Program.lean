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

  ## PR2 stub values

  Until the SSZ *decoder* lands and feeds real values, this serializer
  hard-codes:

      new_payload_request_root = 0x00...00  (32 zero bytes)
      successful_validation    = false        (one zero byte at offset 32)
      chain_id                 = 1            (LE: [01, 00, 00, ..., 00])

  This lets a Python-side harness diff `ziskemu`'s public-output bytes
  against the same 41-byte sequence computed via the reference
  `SszStatelessValidationResult.encode_bytes()`. Once the decoder lands
  the stub goes away and `chain_id` flows from the decoded input.

  ## Memory layout

  - **Preconditions**:
    - `OUTPUT_BASE = 0xa0010000` is ziskemu's public-output region
      (mirrors `EvmAsm.Codegen.OUTPUT_ADDR`).
    - `[OUTPUT_BASE, OUTPUT_BASE + 41)` lies inside the RAM zone
      (`RAM_MEM_START..RAM_MEM_END`) and is accepted by
      `isValidMemAddr` per issue #5164.
  - **Postconditions**: 41 bytes at `OUTPUT_BASE` carry the SSZ encoding
    of the stub `StatelessValidationResult`.
  - **Clobbers**: `x6` (base pointer), `x7` (packed bool || low-7-byte
    chain_id word).
  - **Exit**: falls through to the caller's halt stub.

  ## Frame

  8 instructions: 1 LI + 4 SD (zero hash) + 1 LI + 1 SD (packed
  bool/chain) + 1 SB (high chain byte).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Stateless.MemoryLayout

namespace EvmAsm.Stateless.SSZ.Encode

open EvmAsm.Rv64

/-- Output region base address. Duplicated from
    `EvmAsm.Codegen.Programs.OUTPUT_ADDR` so `EvmAsm/Stateless/` stays
    free of the codegen umbrella. -/
def OUTPUT_BASE : Word := 0xa0010000

/-- PR2 stub `chain_id`. -/
def STUB_CHAIN_ID : Word := 0x1

/-- Packed `(bool=0) || first-7-LE-bytes-of-STUB_CHAIN_ID`, ready for a
    single SD at offset 32.

    For `STUB_CHAIN_ID = 1` the LE bytes of `chain_id` are
    `[0x01, 0x00, ..., 0x00]`. Byte 32 (bool) is `0x00`, bytes 33..39
    are the first 7 LE bytes of `chain_id` (`[0x01, 0x00, ..., 0x00]`).
    The u64 stored at `[OUTPUT_BASE + 32]` is therefore
    `0x00_00_00_00_00_00_01_00 = 256`. -/
def STUB_BOOL_AND_CHAIN_LOW7 : Word := 0x100

/-- Serializer Program (PR2 stub). Writes the 41-byte SSZ encoding of
    `StatelessValidationResult(root = 0, valid = false, chain_id = 1)`
    at `OUTPUT_BASE`, then falls through to the caller's halt stub. -/
def serialize_stateless_output_stub : Program :=
  LI .x6 OUTPUT_BASE ;;
  SD .x6 .x0 0  ;;
  SD .x6 .x0 8  ;;
  SD .x6 .x0 16 ;;
  SD .x6 .x0 24 ;;
  LI .x7 STUB_BOOL_AND_CHAIN_LOW7 ;;
  SD .x6 .x7 32 ;;
  SB .x6 .x0 40

end EvmAsm.Stateless.SSZ.Encode
