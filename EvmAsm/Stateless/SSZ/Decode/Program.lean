/-
  EvmAsm.Stateless.SSZ.Decode.Program

  Minimal SSZ decoder slice (PR3): read `chain_config.chain_id` from a
  host-supplied `SszStatelessInput` blob on `INPUT_ADDR`.

  Reference: `execution-specs/src/ethereum/forks/amsterdam/stateless_ssz.py`
  (`class SszStatelessInput(Container)`,
   `class SszChainConfig(Container)`).

  ## SSZ wire layout of `SszStatelessInput`

  Container fixed-header section (20 bytes):

  | Offset | Size | Field                              | Wire form     |
  |--------|------|------------------------------------|---------------|
  |  0..4  |    4 | `new_payload_request` offset       | uint32 LE     |
  |  4..8  |    4 | `witness` offset                   | uint32 LE     |
  |  8..16 |    8 | `chain_config.chain_id` (inline)   | uint64 LE     |
  | 16..20 |    4 | `public_keys` offset               | uint32 LE     |

  The variable-size body follows the header. PR3 only reads
  `chain_id`; the offsets / variable body are ignored for now.

  ## ziskemu input-buffer layout

  Per `EvmAsm/Codegen/Programs.lean`:

      INPUT_ADDR +  0..8   : ziskemu metadata (zero)
      INPUT_ADDR +  8..16  : LE u64 length of the SSZ blob
      INPUT_ADDR + 16..    : SSZ-encoded SszStatelessInput

  So `chain_id` lives at `INPUT_ADDR + 16 + 8 = INPUT_ADDR + 24`. The
  base address is 8-byte aligned (`INPUT_ADDR = 0x40000000`), and
  `24 mod 8 = 0`, so an `LD` at offset 24 satisfies
  `isValidDwordAccess`.

  ## Memory layout (preconditions)
  - `INPUT_BASE = 0x40000000` (matches `EvmAsm.Codegen.INPUT_ADDR`).
  - `[INPUT_BASE + 24, INPUT_BASE + 32)` lies inside the input zone
    (`INPUT_MEM_START..INPUT_MEM_END`, see issue #5164).
  - The host writes a length-prefixed SSZ blob of at least 16 data
    bytes (header through `chain_id` field).

  ## Side effects
  - Loads `chain_id` (u64 LE) into `x10`.
  - Clobbers `x11` (input-buffer base pointer).

  ## Frame
  - 2 instructions: 1 LI + 1 LD.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Stateless.MemoryLayout

namespace EvmAsm.Stateless.SSZ.Decode

open EvmAsm.Rv64

/-- ziskemu private-input region base. Mirrors
    `EvmAsm.Codegen.Programs.INPUT_ADDR`. -/
def INPUT_BASE : Word := 0x40000000

/-- Byte offset (from `INPUT_BASE`) of `chain_config.chain_id` in the
    SSZ-encoded `SszStatelessInput`:

        INPUT_DATA_OFFSET (16, see Codegen) + SSZ header offset (8) = 24
-/
def CHAIN_ID_BYTE_OFFSET : BitVec 12 := 24

/-- Read `chain_config.chain_id` from `INPUT_BASE` into `x10`.

    Postcondition: `x10` holds the host-supplied `chain_id` as a u64.
    Clobbers `x11`. -/
def read_chain_id : Program :=
  LI .x11 INPUT_BASE ;;
  LD .x10 .x11 CHAIN_ID_BYTE_OFFSET

end EvmAsm.Stateless.SSZ.Decode
