/-
  EvmAsm.Stateless.MemoryLayout

  Single source of truth for the address-space layout used by the
  stateless-guest port of `run_stateless_guest`
  (`execution-specs/src/ethereum/forks/amsterdam/stateless_guest.py`).

  All RISC-V modules under `EvmAsm/Stateless/` agree on the constants
  declared here. Treat this file as the contract: any new module must
  document, in its file header, which regions it reads, writes, and
  leaves untouched, plus which exit ECALLs it can take. Mirrors the
  "memory layout + side effects" convention already used by
  `EvmAsm/Evm64/DivMod/AddrNorm.lean` and the Keccak ECALL bridge.

  ## Top-level map (RV64IM, ZisK host-IO compatible)

  ```
  0x00000020 .. 0x40000000   .text + .rodata + .bss
  0x40000000 .. 0x40002000   INPUT_ADDR  (8 KiB, host-supplied SSZ input)
                               [+ 0..8]   ZisK metadata (zero)
                               [+ 8..16]  LE u64 length of first record
                               [+16..]    SSZ-encoded SszStatelessInput
  0x80000000 .. 0xa0000000   working RAM (decoded structures, DBs, frames)
  0xa0010000 .. 0xa0020000   OUTPUT_ADDR (64 KiB, public output)
                               [+ 0..N]   SSZ-encoded
                                          SszStatelessValidationResult
  0xa0020000 .. 0xc0000000   spare RAM
  ```

  `INPUT_ADDR`, `INPUT_DATA_OFFSET`, and `OUTPUT_ADDR` mirror the
  constants in `EvmAsm/Codegen/Programs.lean`; do not duplicate the
  numeric values here -- the working-RAM sub-region anchors below are
  the new contribution.

  ## Working-RAM sub-regions (0x80000000 .. 0xa0000000)

  Each anchor is the start of a region whose size is sized at codegen
  time. Sizes will be tightened as modules land; for now we reserve
  generous slabs so successive PRs do not have to reflow addresses.

  | Anchor                       | Address          | Size budget |
  |------------------------------|------------------|-------------|
  | `STATELESS_WORK_BASE`        | `0x80000000`     | base ref    |
  | `SSZ_INPUT_DECODED`          | `0x80000000`     | 64 KiB      |
  | `EXECUTION_WITNESS_AREA`     | `0x80010000`     | 1 MiB       |
  | `NODE_DB_BUCKETS`            | `0x80110000`     | 4 MiB       |
  | `CODE_DB_BUCKETS`            | `0x80510000`     | 1 MiB       |
  | `STATE_TRACKER_AREA`         | `0x80610000`     | 4 MiB       |
  | `EVM_FRAME_STACK`            | `0x80a10000`     | 256 KiB     |
  | `EVM_VALUE_STACK`            | `0x80a50000`     | 1 MiB       |
  | `EVM_MEMORY_AREA`            | `0x80b50000`     | 16 MiB      |
  | `KECCAK_SCRATCH`             | `0x81b50000`     | 64 KiB      |
  | `ECRECOVER_SCRATCH`          | `0x81b60000`     | 64 KiB      |
  | `SHA256_SCRATCH`             | `0x81b70000`     | 64 KiB      |

  ## Calling convention (non-leaf stateless code)

  The existing opcode handlers are leaf functions. The stateless guest
  is deeply nested, so non-leaf code in `EvmAsm/Stateless/` follows a
  standard RV64 ABI:

  - `x1 (ra)`           : return address
  - `x2 (sp)`           : RV64 call stack pointer (distinct from EVM
                          value-stack `x12`)
  - `x10..x17 (a0..a7)` : args / returns
  - `x12`               : EVM value-stack pointer (preserved across
                          opcode handler calls, saved/restored at
                          message-frame boundaries)
  - `x18..x27 (s2..s11)`: callee-saved
  - Each non-leaf entry sets up an explicit `sp` adjust; the per-module
    frame size is documented at the top of that module's `Program.lean`.
-/

import EvmAsm.Rv64.Basic

namespace EvmAsm.Stateless

open EvmAsm.Rv64

/-! ## Working-RAM anchors (see table above). -/

def STATELESS_WORK_BASE     : Word := 0x80000000
def SSZ_INPUT_DECODED       : Word := 0x80000000
def EXECUTION_WITNESS_AREA  : Word := 0x80010000
def NODE_DB_BUCKETS         : Word := 0x80110000
def CODE_DB_BUCKETS         : Word := 0x80510000
def STATE_TRACKER_AREA      : Word := 0x80610000
def EVM_FRAME_STACK         : Word := 0x80a10000
def EVM_VALUE_STACK         : Word := 0x80a50000
def EVM_MEMORY_AREA         : Word := 0x80b50000
def KECCAK_SCRATCH          : Word := 0x81b50000
def ECRECOVER_SCRATCH       : Word := 0x81b60000
def SHA256_SCRATCH          : Word := 0x81b70000

end EvmAsm.Stateless
