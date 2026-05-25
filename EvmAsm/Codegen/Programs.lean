/-
  EvmAsm.Codegen.Programs

  Registry of programs the codegen tool knows how to emit, each as a
  `BuildUnit` (verified body + optional wrapping).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Evm64.Add.Program
import EvmAsm.Evm64.AddMod.Program
import EvmAsm.Evm64.And.Program
import EvmAsm.Evm64.Byte.Program
import EvmAsm.Evm64.DivMod.Callable
import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Evm64.Dup.Program
import EvmAsm.Evm64.Eq.Program
-- EXP wrapper is parametric over caller-saved registers (x6, x16)
-- that mul_callable clobbers; deferred until upstream lands a
-- fully callee-saved variant. import re-added when wiring lands.
-- import EvmAsm.Evm64.Exp.Program
import EvmAsm.Evm64.Gt.Program
import EvmAsm.Evm64.IsZero.Program
import EvmAsm.Evm64.Lt.Program
import EvmAsm.Evm64.MLoad.Program
import EvmAsm.Evm64.MStore.Program
import EvmAsm.Evm64.MStore8.Program
-- import EvmAsm.Evm64.Multiply.Callable -- only needed by EXP (deferred)
import EvmAsm.Evm64.Multiply.Program
import EvmAsm.Evm64.Not.Program
import EvmAsm.Evm64.Or.Program
import EvmAsm.Evm64.Pop.Program
import EvmAsm.Evm64.Push.Program
import EvmAsm.Evm64.SDiv.Program
import EvmAsm.Evm64.SMod.Program
import EvmAsm.Evm64.Sgt.Program
import EvmAsm.Evm64.Shift.Program
import EvmAsm.Evm64.SignExtend.Program
import EvmAsm.Evm64.Slt.Program
import EvmAsm.Evm64.Sub.Program
import EvmAsm.Evm64.Swap.Program
import EvmAsm.Evm64.Xor.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Dispatch
import EvmAsm.Stateless.Entry
import EvmAsm.Stateless.SSZ.HashTreeRoot.Program

import EvmAsm.Codegen.Programs.Evm
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.MptEncode
import EvmAsm.Codegen.Programs.MptInternal
import EvmAsm.Codegen.Programs.Ssz
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.TxDecode
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.Bloom
import EvmAsm.Codegen.Programs.Block
import EvmAsm.Codegen.Programs.BlockBody
import EvmAsm.Codegen.Programs.BlockValidate
import EvmAsm.Codegen.Programs.Account
import EvmAsm.Codegen.Programs.AccountFields
import EvmAsm.Codegen.Programs.BlockRoots
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.HeaderBaseFee
import EvmAsm.Codegen.Programs.HeaderChain
import EvmAsm.Codegen.Programs.Chain
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.BlockHashPredicates
import EvmAsm.Codegen.Programs.HeadersKeccak
import EvmAsm.Codegen.Programs.HeaderU64
import EvmAsm.Codegen.Programs.Receipt
import EvmAsm.Codegen.Programs.State
import EvmAsm.Codegen.Programs.TxSignature
import EvmAsm.Codegen.Programs.Withdrawal
import EvmAsm.Codegen.Programs.Address

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## stateless_guest — PR2 SSZ-output stub

    See the definition of `statelessGuestUnit` below
    (after `zkvmKeccak256Function`, which the epilogue inlines). -/

/-! ## zisk_keccak_probe — PR-K1 ziskemu Keccak-f[1600] intrinsic probe

    Emits a raw-asm probe that triggers ziskemu's built-in
    Keccak-f[1600] accelerator (`_opcode_keccak` in
    `~/.zisk/zisk/emulator-asm/src/emu.c:507`). The accelerator is
    invoked by writing the state pointer into a non-standard CSR at
    address 0x800 -- which is the syscall ID the Zisk compiler
    expects, per `ziskos/entrypoint/src/syscalls/keccakf.rs` (uses
    `csrs 0x800, <reg>` via the `ziskos_syscall!` macro).

    GNU-as `csrs csr, rs1` expands to `csrrs x0, csr, rs1`. The
    32-bit encoding for `csrs 0x800, a0`:

      csr(0x800)    rs1(x10=01010)  f3(010)  rd(x0)    op(0x73)
      [31..20]      [19..15]        [14..12] [11..7]   [6..0]
      = 0x80052073

    We emit this as a raw `.4byte` directive rather than the
    `csrs` mnemonic so the existing
    `riscv64-unknown-elf-as -march=rv64imac` toolchain string
    works without enabling the `Zicsr` extension. The 32-bit value
    is what `as -march=rv64imac_zicsr` produces for the same
    mnemonic; pinning it here is the whole point of PR-K1.

    Probe sequence:
      la a0, zisk_keccak_state    # state pointer
      .4byte 0x80052073           # csrs 0x800, a0 -> _opcode_keccak
      <copy 200 bytes to OUTPUT_ADDR>
      <halt>

    Verified Program body is a single NOP -- everything observable
    happens in raw asm, so the verified semantics carry no claim
    about the probe yet. PR-K2 wires this through verified Instrs
    once the CSR instruction is added to `Rv64.Instr`. -/

/-- Asm prologue: probe the keccak intrinsic and stream the
    post-permutation 200-byte state to ziskemu's public-output
    region. Hard-codes `OUTPUT_ADDR = 0xa0010000` (mirrors the
    constant above). -/
def ziskKeccakProbePrologue : String :=
  "  la a0, zisk_keccak_state\n" ++
  "  .4byte 0x80052073           # csrs 0x800, a0\n" ++
  "  li t0, 0xa0010000\n" ++
  "  li t1, 25\n" ++
  ".Lzkp_copy_loop:\n" ++
  "  ld t2, 0(a0)\n" ++
  "  sd t2, 0(t0)\n" ++
  "  addi a0, a0, 8\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, .Lzkp_copy_loop"

/-- `.data` section: 200 zero bytes labeled `zisk_keccak_state`.
    Lands in ziskemu RAM (0xa0000000..0xc0000000) via the standard
    `-Tdata=0xa0000000` link flag from `Codegen/Driver.lean`. -/
def ziskKeccakProbeDataSection : String :=
  ".section .data\n" ++
  "zisk_keccak_state:\n" ++
  "  .zero 200"

def ziskKeccakProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskKeccakProbePrologue
  dataAsm     := ziskKeccakProbeDataSection
}

/-! ## zisk_keccak256_empty — PR-K2 keccak256 sponge over empty input

    First wrapper around PR-K1's intrinsic: the keccak256 sponge
    construction applied to a zero-byte message. Concretely:

      1. Zero the 200-byte state buffer.
      2. Pad: set byte 0 = 0x01, byte 135 = 0x80
         (Ethereum Keccak padding; rate = 1088 bits = 136 bytes).
      3. Trigger `_opcode_keccak` (csrs 0x800, a0).
      4. Copy the first 32 bytes of state to OUTPUT_ADDR -- those
         are the 256-bit hash digest.

    Expected output (32 bytes):
      c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

    Matches the canonical keccak256("") hash and the value produced
    by `eth_utils.keccak(b"")` / `Cryptodome.Hash.keccak.new(...).digest()`.
    This is the simplest possible exercise of the full sponge wrapper:
    no input blocks to absorb, just the final padded block. Future
    PRs extend this to one-block ("abc") and multi-block inputs. -/

/-- Asm prologue: zero state, apply Ethereum Keccak padding for the
    empty-message case, call the keccak-f intrinsic, copy the 32-byte
    digest to OUTPUT_ADDR. -/
def ziskKeccak256EmptyPrologue : String :=
  "  la s0, k256e_state\n" ++
  "  # zero state (25 × u64)\n" ++
  "  mv t3, s0\n" ++
  "  li t4, 25\n" ++
  ".Lk256e_zero:\n" ++
  "  sd zero, 0(t3)\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lk256e_zero\n" ++
  "  # apply Ethereum Keccak padding to empty message\n" ++
  "  li t0, 0x01\n" ++
  "  sb t0, 0(s0)              # state[0] = 0x01\n" ++
  "  li t0, 0x80\n" ++
  "  sb t0, 135(s0)            # state[135] = 0x80\n" ++
  "  # call keccak-f via PR-K1 intrinsic (csrs 0x800, a0)\n" ++
  "  mv a0, s0\n" ++
  "  .4byte 0x80052073\n" ++
  "  # copy first 32 bytes of state to OUTPUT_ADDR\n" ++
  "  li t0, 0xa0010000         # OUTPUT_ADDR\n" ++
  "  ld t1, 0(s0);  sd t1, 0(t0)\n" ++
  "  ld t1, 8(s0);  sd t1, 8(t0)\n" ++
  "  ld t1, 16(s0); sd t1, 16(t0)\n" ++
  "  ld t1, 24(s0); sd t1, 24(t0)"

def ziskKeccak256EmptyDataSection : String :=
  ".section .data\n" ++
  "k256e_state:\n" ++
  "  .zero 200"

def ziskKeccak256EmptyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskKeccak256EmptyPrologue
  dataAsm     := ziskKeccak256EmptyDataSection
}

/-! ## zisk_keccak256_abc — PR-K2a single-block input

    Same sponge skeleton as PR-K2 but with the 3-byte input "abc"
    (RFC test vector) XORed into state positions 0..3 before the
    padding bytes (`0x01` at byte 3, `0x80` at byte 135). Single
    absorb block, single keccak-f call, then squeeze.

    Expected:
      keccak256(b"abc") =
        4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45

    Demonstrates the single-block absorb path (input ≤ rate). The
    multi-block path lands in a follow-up. -/
def ziskKeccak256AbcPrologue : String :=
  "  la s0, k256a_state\n" ++
  "  # zero state\n" ++
  "  mv t3, s0\n" ++
  "  li t4, 25\n" ++
  ".Lk256a_zero:\n" ++
  "  sd zero, 0(t3)\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lk256a_zero\n" ++
  "  # input \"abc\" at state[0..3]\n" ++
  "  li t0, 0x61; sb t0, 0(s0)\n" ++
  "  li t0, 0x62; sb t0, 1(s0)\n" ++
  "  li t0, 0x63; sb t0, 2(s0)\n" ++
  "  # Ethereum Keccak padding (length 3 < rate 136)\n" ++
  "  li t0, 0x01; sb t0, 3(s0)\n" ++
  "  li t0, 0x80; sb t0, 135(s0)\n" ++
  "  # call keccak-f\n" ++
  "  mv a0, s0\n" ++
  "  .4byte 0x80052073\n" ++
  "  # squeeze 32 bytes to OUTPUT_ADDR\n" ++
  "  li t0, 0xa0010000\n" ++
  "  ld t1, 0(s0);  sd t1, 0(t0)\n" ++
  "  ld t1, 8(s0);  sd t1, 8(t0)\n" ++
  "  ld t1, 16(s0); sd t1, 16(t0)\n" ++
  "  ld t1, 24(s0); sd t1, 24(t0)"

def ziskKeccak256AbcDataSection : String :=
  ".section .data\n" ++
  "k256a_state:\n" ++
  "  .zero 200"

def ziskKeccak256AbcProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskKeccak256AbcPrologue
  dataAsm     := ziskKeccak256AbcDataSection
}

/-! ## zisk_sha256_probe_le — PR-K15 SHA-256 intrinsic probe (LE-u32 layout)

    Earlier PR-S1 v1 (`task #17`) tried the SHA-256 intrinsic at
    CSR `0x805` with the 0.15.0-documented BE-per-u64 packing
    (state[0] = (h0 BE-u32 << 32) | h1 BE-u32, stored LE as a
    single u64). Output didn't match `sha256(b"")`.

    Hypothesis: the installed ziskemu (0.18.0) uses a different
    state packing -- specifically LE-u32 within u64 (state bytes
    are u32 BE in spec, stored as LE u32s -- so the 64-bit memory
    layout is `LE(h0) || LE(h1)` = bytes `67 e6 09 6a 85 ae 67 bb`
    for the first u64). As a u64 value this is
    `0xbb67ae856a09e667`.

    Probe re-runs the empty-message compression with this
    alternative layout. If it matches `sha256(b"")`, the 0.18.0
    intrinsic layout is pinned; if not, document further.

    Expected on success (SHA-256("") in LE-u32 packed memory):
      67 e6 09 6a 85 ae 67 bb 72 f3 6e 3c 3a f5 4f a5
      7f 52 0e 51 8c 68 05 9b ab d9 83 1f 19 cd e0 5b
    Then post-compression state should be SHA-256("")'s words
    packed the same way:
      sha256(empty) = e3 b0 c4 42 98 fc 1c 14 9a fb f4 c8 99 6f
                      b9 24 27 ae 41 e4 64 9b 93 4c a4 95 99 1b
                      78 52 b8 55
    As LE-u32 within u64 (per-byte memory order):
      42 c4 b0 e3 14 1c fc 98 c8 f4 fb 9a 24 b9 6f 99
      e4 41 ae 27 4c 93 9b 64 1b 99 95 a4 55 b8 52 78
-/
def ziskSha256ProbeLePrologue : String :=
  "  la a0, sha256_le_params\n" ++
  "  .4byte 0x80552073           # csrs 0x805, a0\n" ++
  "  # copy 32-byte post-compression state to OUTPUT_ADDR\n" ++
  "  la t0, sha256_le_state\n" ++
  "  li t1, 0xa0010000\n" ++
  "  ld t2, 0(t0);  sd t2, 0(t1)\n" ++
  "  ld t2, 8(t0);  sd t2, 8(t1)\n" ++
  "  ld t2, 16(t0); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t0); sd t2, 24(t1)"

def ziskSha256ProbeLeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_le_state:\n" ++
  "  # state[0..4] = LE-u32-pack (each u32 stored LE in memory)\n" ++
  "  .quad 0xbb67ae856a09e667    # LE(h0) || LE(h1)\n" ++
  "  .quad 0xa54ff53a3c6ef372    # LE(h2) || LE(h3)\n" ++
  "  .quad 0x9b05688c510e527f    # LE(h4) || LE(h5)\n" ++
  "  .quad 0x5be0cd191f83d9ab    # LE(h6) || LE(h7)\n" ++
  ".balign 8\n" ++
  "sha256_le_input:\n" ++
  "  # input[0] = LE-u32-pack of message u32[0..2]\n" ++
  "  # padded empty: u32[0] = 0x80 (LE bytes [80 00 00 00]) || u32[1] = 0\n" ++
  "  .quad 0x80\n" ++
  "  .quad 0\n" ++
  "  .quad 0\n" ++
  "  .quad 0\n" ++
  "  .quad 0\n" ++
  "  .quad 0\n" ++
  "  .quad 0\n" ++
  "  .quad 0                     # u32[15] = length BE bits = 0\n" ++
  ".balign 8\n" ++
  "sha256_le_params:\n" ++
  "  .quad sha256_le_state\n" ++
  "  .quad sha256_le_input"

def ziskSha256ProbeLeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSha256ProbeLePrologue
  dataAsm     := ziskSha256ProbeLeDataSection
}

/-! ## zkvm_sha256 — PR-S2 Merkle-Damgård wrapper

    Parameterised SHA-256 callable matching the zkvm-standards C
    signature:

        zkvm_status zkvm_sha256(const uint8_t* data, size_t len,
                                zkvm_sha256_hash* output);

    Sister to PR-K3's `zkvm_keccak256`. Composes the LE-u32
    intrinsic pinned in PR-S1 (#5286) with the FIPS 180-4
    Merkle-Damgård wrapper:

      1. Initialise state to the SHA-256 IV (LE-u32 packing).
      2. For each full 64-byte input block: copy into the
         intrinsic's `sha256_input` buffer, `csrs 0x805, a0` to
         compress.
      3. Final block: copy <64 remainder bytes, append 0x80,
         append 8-byte big-endian bit-length at offset 56..64.
         If remainder >= 56, use two blocks (current + a fresh
         length-only block).
      4. Squeeze: byte-swap each u32 of the LE-packed state to
         produce canonical SHA-256 wire bytes
         (`e3b0c442 98fc1c14 ...` byte order). The byte-swap uses
         the `xori 3` index trick (within each 4-byte group,
         byte j maps to byte (3 ^ j)).

    Calling convention (RV64 ABI, mirrors `zkvm_keccak256`):
      a0 = data ptr; a1 = len; a2 = output ptr;
      ra = return; returns a0 = ZKVM_EOK = 0. -/


def ziskZkvmSha256Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  # call 1: sha256(empty)\n" ++
  "  la a0, zsha_empty\n" ++
  "  li a1, 0\n" ++
  "  li a2, 0xa0010000\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  # call 2: sha256(\"abc\")\n" ++
  "  la a0, zsha_abc\n" ++
  "  li a1, 3\n" ++
  "  li a2, 0xa0010020\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  # call 3: sha256(0xaa × 200)\n" ++
  "  la a0, zsha_aa\n" ++
  "  li a1, 200\n" ++
  "  li a2, 0xa0010040\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  j .Lzkv_sha_done\n" ++
  zkvmSha256Function ++ "\n" ++
  ".Lzkv_sha_done:"

def ziskZkvmSha256DataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667    # LE(h0) || LE(h1)\n" ++
  "  .quad 0xa54ff53a3c6ef372    # LE(h2) || LE(h3)\n" ++
  "  .quad 0x9b05688c510e527f    # LE(h4) || LE(h5)\n" ++
  "  .quad 0x5be0cd191f83d9ab    # LE(h6) || LE(h7)\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n" ++
  "zsha_empty:\n" ++
  "  .byte 0\n" ++
  "zsha_abc:\n" ++
  "  .ascii \"abc\"\n" ++
  "zsha_aa:\n" ++
  "  .fill 200, 1, 0xaa"

def ziskZkvmSha256ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskZkvmSha256Prologue
  dataAsm     := ziskZkvmSha256DataSection
}

/-! ## zisk_sha256_from_input — PR-S3 host-supplied input

    Mirror of PR-K4 `zisk_keccak256_from_input` for SHA-256:
    hash whatever's at `INPUT_ADDR + 16` (length given at
    `INPUT_ADDR + 8` per ziskemu's input-region layout) and
    write the 32-byte digest to `OUTPUT_ADDR + 0..32`.

    Uses PR-S2's `zkvm_sha256` (the Merkle-Damgård wrapper)
    inlined per-BuildUnit. Test exercises arbitrary input
    lengths via the Python harness (`--shape header` for an
    RLP-encoded amsterdam Header ~658 bytes, `--shape long`
    for 1024 bytes of 0x55). -/
def ziskSha256FromInputPrologue : String :=
  "  # set up stack\n" ++
  "  li sp, 0xa0050000\n" ++
  "  # read length and data ptr from ziskemu input region\n" ++
  "  li a3, 0x40000000           # INPUT_ADDR\n" ++
  "  ld a1, 8(a3)                # a1 = length (u64 LE at INPUT_ADDR + 8)\n" ++
  "  addi a0, a3, 16             # a0 = data ptr (INPUT_ADDR + 16)\n" ++
  "  li a2, 0xa0010000           # a2 = OUTPUT_ADDR\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  j .Lzks_done\n" ++
  zkvmSha256Function ++ "\n" ++
  ".Lzks_done:"

def ziskSha256FromInputDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input"

def ziskSha256FromInputProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSha256FromInputPrologue
  dataAsm     := ziskSha256FromInputDataSection
}

/-! ## zisk_zkvm_keccak256 — PR-K3 parameterised wrapper

    Refactors the three hardcoded sponge probes (PR-K2 empty,
    PR-K2a "abc", PR-K2b multi-block) into a single jal-callable
    function matching the zkvm-standards C signature:

        zkvm_status zkvm_keccak256(const uint8_t* data, size_t len,
                                   zkvm_keccak256_hash* output);

    Calling convention (RV64 ABI):
      a0 = data ptr
      a1 = len
      a2 = output ptr (32 bytes will be written)
      ra = return address
      returns: a0 = 0 on success (ZKVM_EOK = 0)

    Internally clobbers t0..t6, a0..a2. Saves s0/s1/s2/s4 on the
    stack and restores them before returning. Caller is
    responsible for sp pointing at usable RAM.

    The build unit's test driver initialises sp, then makes three
    calls (empty / "abc" / 200×0xaa) writing the three 32-byte
    digests to OUTPUT[0..96]. After the third call, jumps past
    the function definition and falls through to halt.

    Expected OUTPUT[0..96]:
      0..32  : keccak256(b"")               = c5d2460186f7233c...
      32..64 : keccak256(b"abc")            = 4e03657aea45a94f...
      64..96 : keccak256(b"\xaa" * 200)     = ebad1a3694934 0cb... -/

/-- Test driver: initialises sp, calls `zkvm_keccak256` three times
    with the empty / abc / 200×0xaa inputs, then jumps over the
    function definition so we fall through to halt. -/
def ziskZkvmKeccak256Prologue : String :=
  "  # set up a usable stack pointer in RAM\n" ++
  "  li sp, 0xa0050000\n" ++
  "  # call 1: keccak256(empty)\n" ++
  "  la a0, zk3_empty_marker\n" ++
  "  li a1, 0\n" ++
  "  li a2, 0xa0010000\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # call 2: keccak256(\"abc\")\n" ++
  "  la a0, zk3_abc_input\n" ++
  "  li a1, 3\n" ++
  "  li a2, 0xa0010020\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # call 3: keccak256(0xaa × 200)\n" ++
  "  la a0, zk3_aa_input\n" ++
  "  li a1, 200\n" ++
  "  li a2, 0xa0010040\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # skip over the function definition, fall through to halt\n" ++
  "  j .Lzk3_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  ".Lzk3_done:"

def ziskZkvmKeccak256DataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "zk3_empty_marker:\n" ++
  "  .byte 0\n" ++
  "zk3_abc_input:\n" ++
  "  .ascii \"abc\"\n" ++
  "zk3_aa_input:\n" ++
  "  .fill 200, 1, 0xaa"

def ziskZkvmKeccak256ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskZkvmKeccak256Prologue
  dataAsm     := ziskZkvmKeccak256DataSection
}

/-! ## zisk_keccak256_from_input — PR-K4 host-supplied input

    First real-shape consumer of the parameterised
    `zkvm_keccak256` from PR-K3: hash an arbitrary byte buffer
    that the host streamed in via `ziskemu -i <file>`. ziskemu
    places file bytes 0..8 (the u64 LE length prefix) at
    `INPUT_ADDR + 8..16` and file bytes 8.. (the data) at
    `INPUT_ADDR + 16..`. The probe reads the length, points at
    the data, calls `zkvm_keccak256`, writes the 32-byte digest
    at OUTPUT_ADDR.

    Designed to test header-shaped inputs (typical Ethereum
    header RLP is ~530-540 bytes), but accepts any byte stream.
    The Python harness (`scripts/keccak256-gen-input.py`)
    SSZ/RLP-encodes a real Header dataclass and emits the
    ziskemu-formatted input file. The test script runs ziskemu,
    diffs the OUTPUT digest against the Python-computed
    reference hash. -/
def ziskKeccak256FromInputPrologue : String :=
  "  # set up stack\n" ++
  "  li sp, 0xa0050000\n" ++
  "  # read length and data ptr from ziskemu input region\n" ++
  "  li a3, 0x40000000           # INPUT_ADDR\n" ++
  "  ld a1, 8(a3)                # a1 = length (u64 LE at INPUT_ADDR + 8)\n" ++
  "  addi a0, a3, 16             # a0 = data ptr (INPUT_ADDR + 16)\n" ++
  "  li a2, 0xa0010000           # a2 = OUTPUT_ADDR\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  j .Lzk4_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  ".Lzk4_done:"

/-- `.data` for the from-input probe: 200-byte state buffer used
    by `zkvm_keccak256`. Input data lives in the
    `INPUT_ADDR` region (host-supplied via `ziskemu -i`), not in
    `.data`. -/
def ziskKeccak256FromInputDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskKeccak256FromInputProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskKeccak256FromInputPrologue
  dataAsm     := ziskKeccak256FromInputDataSection
}

/-! ## access_list_count -- PR-K48 EIP-2930+ access-list cardinality

    Walk an RLP-encoded EIP-2930+ access_list and return
    `(num_addresses, num_storage_keys)`. These are the two
    inputs to the EIP-2930+ intrinsic-gas formula:

      gas_access_list = 2400 × num_addresses + 1900 × num_storage_keys

    Access-list shape:

      access_list = [
        [address (20 B), [slot1 (32 B), slot2 (32 B), ...]],
        ...
      ]

    Both `access_list` and each per-address `[slots...]` sub-list
    are RLP lists. This helper composes:

      1. PR-K47 `rlp_list_count_items` on the outer access_list to
         get N = num_addresses (and validate the outer shape).
      2. PR-K20 `rlp_list_nth_item` to extract each entry's bounds.
      3. PR-K20 `rlp_list_nth_item` on each entry to get field 1
         (the slots sub-list).
      4. PR-K47 `rlp_list_count_items` on the slots sub-list to add
         to num_storage_keys.

    Empty access_list (`0xc0`) → (0, 0).

    Calling convention:
      a0 (input)  : access_list bytes ptr (whole encoded item incl.
                    outer RLP list prefix)
      a1 (input)  : access_list byte length
      a2 (input)  : u64 out ptr for num_addresses
      a3 (input)  : u64 out ptr for num_storage_keys
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail.

    Uses three 8-byte `.data` scratch slots
    (`alc_scratch`, `alc_entry_offset`, `alc_entry_length`,
    `alc_keys_offset`, `alc_keys_length`). -/
def accessListCountFunction : String :=
  "access_list_count:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # outer list ptr\n" ++
  "  mv s1, a1                   # outer list len\n" ++
  "  mv s2, a2                   # num_addresses out\n" ++
  "  mv s3, a3                   # num_storage_keys out\n" ++
  "  sd zero, 0(s2); sd zero, 0(s3)\n" ++
  "  # Step 1: outer count → s4 = N.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, alc_scratch\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lalc_fail\n" ++
  "  la t0, alc_scratch; ld s4, 0(t0)\n" ++
  "  beqz s4, .Lalc_done\n" ++
  "  # Step 2: iterate entries 0..N-1.\n" ++
  "  li s5, 0                    # entry index\n" ++
  ".Lalc_loop:\n" ++
  "  beq s5, s4, .Lalc_done\n" ++
  "  # Fetch entry s5 bounds in the outer list.\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s5\n" ++
  "  la a3, alc_entry_offset\n" ++
  "  la a4, alc_entry_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lalc_fail\n" ++
  "  # entry_ptr = outer_ptr + entry_offset.\n" ++
  "  la t0, alc_entry_offset; ld t1, 0(t0)\n" ++
  "  la t0, alc_entry_length; ld t2, 0(t0)\n" ++
  "  add a0, s0, t1              # entry_ptr\n" ++
  "  mv a1, t2                   # entry_len\n" ++
  "  # Fetch entry field 1 (the slots sub-list) bounds.\n" ++
  "  li a2, 1\n" ++
  "  la a3, alc_keys_offset\n" ++
  "  la a4, alc_keys_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lalc_fail\n" ++
  "  # keys_ptr = outer_ptr + entry_offset + keys_offset.\n" ++
  "  la t0, alc_entry_offset; ld t1, 0(t0)\n" ++
  "  la t0, alc_keys_offset; ld t3, 0(t0)\n" ++
  "  add t1, t1, t3\n" ++
  "  add a0, s0, t1              # keys_ptr\n" ++
  "  la t0, alc_keys_length; ld a1, 0(t0)\n" ++
  "  la a2, alc_scratch\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lalc_fail\n" ++
  "  la t0, alc_scratch; ld t1, 0(t0)\n" ++
  "  ld t2, 0(s3)\n" ++
  "  add t2, t2, t1\n" ++
  "  sd t2, 0(s3)\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lalc_loop\n" ++
  ".Lalc_done:\n" ++
  "  sd s4, 0(s2)                # num_addresses = N\n" ++
  "  li a0, 0\n" ++
  "  j .Lalc_ret\n" ++
  ".Lalc_fail:\n" ++
  "  sd zero, 0(s2); sd zero, 0(s3)\n" ++
  "  li a0, 1\n" ++
  ".Lalc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_access_list_count`: probe BuildUnit. Reads (list_len,
    list_bytes) from host input, writes (status, num_addresses,
    num_storage_keys) to OUTPUT. -/
def ziskAccessListCountPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # list_len\n" ++
  "  addi a0, a4, 16             # list ptr\n" ++
  "  li a2, 0xa0010008           # num_addresses out\n" ++
  "  li a3, 0xa0010010           # num_storage_keys out\n" ++
  "  sd zero, 0(a2); sd zero, 0(a3)\n" ++
  "  jal ra, access_list_count\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lalc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  accessListCountFunction ++ "\n" ++
  ".Lalc_pdone:"

def ziskAccessListCountDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "alc_scratch:\n" ++
  "  .zero 8\n" ++
  "alc_entry_offset:\n" ++
  "  .zero 8\n" ++
  "alc_entry_length:\n" ++
  "  .zero 8\n" ++
  "alc_keys_offset:\n" ++
  "  .zero 8\n" ++
  "alc_keys_length:\n" ++
  "  .zero 8"

def ziskAccessListCountProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccessListCountPrologue
  dataAsm     := ziskAccessListCountDataSection
}

/-! ## K64 blob_gas_used_from_versioned_hashes — moved to `Programs/Tx.lean` (file-size hard cap). -/

/-! ## MPT helpers K21-K26 — moved to `Programs/Mpt.lean` (file-size hard cap). -/

/-! ## rlp-field shims + account extractors + legacy-tx decoders / sig extractors (PR-K34/K121/K35/K120/K123/K36/K37/K138/K139)
    Function + probe defs moved to `Programs/Tx.lean` (see file-size hard cap at the bottom of this file). -/


/-! ## Header decoders + validators + K81/K82 account-gas (K38/K39/K55/K90/K93/K95/K43/K72/K63/K67/K68/K81/K82/K73/K74/K75) — moved to `Programs/Header.lean` (file-size hard cap). -/


/-! ## K71 tx_cost_compute + K79 validate_transaction_balance — moved to `Programs/Tx.lean` (file-size hard cap). -/

/-! ## u256-BE truncation + tx type/extract/EIP-decode family + intrinsic-gas + validate-transaction (PR-K57/K40/K102/K101/K103/K104/K108/K41/K42/K44/K45/K87/K88/K92/K46/K66/K76/K80)
    Function + probe defs moved to `Programs/Tx.lean` (see file-size hard cap at the bottom of this file). -/

/-! ## withdrawal + block-body cluster (K49/K65/K77/K78/K83-K91/K97/K124/K125) — moved to `Programs/Block.lean` (file-size hard cap). -/


/-! ## bloom atoms K148-K154 — moved to `Programs/Bloom.lean` (file-size hard cap). -/


/-! ## MPT encoders K157/K162-K167 — moved to `Programs/Mpt.lean` (file-size hard cap). -/

/-! ## block-level bloom composites K158-K159 — moved to `Programs/Bloom.lean` (file-size hard cap). -/

/-! ## header_root_is_empty_trie -- PR-K161

    Predicate: does `header.field[i]` equal `EMPTY_TRIE_ROOT`?

      EMPTY_TRIE_ROOT = keccak256(rlp(b''))
                      = 0x56e81f171bcc55a6ff8345e692c0f86e5b48e
                          01b996cadc001622fb5e363b421

    The header carries several 32-byte trie-root fields:

      field 4  : transactions_root
      field 5  : receipts_root
      field 16 : withdrawals_root (post-Shanghai)

    Each of these equals `EMPTY_TRIE_ROOT` exactly when the
    corresponding logical list (transactions / receipts /
    withdrawals) is empty. Common cases:

      * Empty block (no txs): `transactions_root` ==
        EMPTY_TRIE_ROOT.
      * Withdrawal-free post-Shanghai block: `withdrawals_root`
        == EMPTY_TRIE_ROOT.
      * Receipt-free block (impossible for a non-empty block,
        but the predicate is still defined): `receipts_root`
        == EMPTY_TRIE_ROOT.

    The verifier uses this to short-circuit MPT-root recomputation
    for the common empty-list case rather than running the
    full multi-leaf builder against an empty list.

    Composes:
      - PR-K20 `rlp_list_nth_item` on the supplied field index

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : field index (u64; typically 4 / 5 / 16)
      a3 (input)  : u64 out ptr
                    (1 if root == EMPTY_TRIE_ROOT, else 0)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        1 : RLP parse failure / field missing
        2 : field length != 32 -/
def headerRootIsEmptyTrieFunction : String :=
  "header_root_is_empty_trie:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # header_rlp ptr\n" ++
  "  mv s1, a1                   # header_rlp len\n" ++
  "  mv s2, a3                   # is_equal out ptr\n" ++
  "  # ---- Extract field i ----\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  # a2 is already the field index\n" ++
  "  la a3, hriet_offset; la a4, hriet_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhriet_fail\n" ++
  "  la t0, hriet_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhriet_size_fail\n" ++
  "  la t0, hriet_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1                              # &root bytes\n" ++
  "  # ---- Compare 4 × 8-byte words to EMPTY_TRIE_ROOT ----\n" ++
  "  la t4, hriet_empty_trie_root\n" ++
  "  ld t5,  0(t3); ld t6,  0(t4); bne t5, t6, .Lhriet_neq\n" ++
  "  ld t5,  8(t3); ld t6,  8(t4); bne t5, t6, .Lhriet_neq\n" ++
  "  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Lhriet_neq\n" ++
  "  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Lhriet_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhriet_ret\n" ++
  ".Lhriet_neq:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhriet_ret\n" ++
  ".Lhriet_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhriet_ret\n" ++
  ".Lhriet_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhriet_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_root_is_empty_trie`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : header_rlp_len
      bytes  8..16 : field_index (u64 LE)
      bytes 16..   : header_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : is_equal_to_empty_trie_root (1 or 0) -/
def ziskHeaderRootIsEmptyTriePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # header_rlp_len\n" ++
  "  ld a2, 16(a4)               # field_index\n" ++
  "  addi a0, a4, 24             # header_rlp ptr\n" ++
  "  li a3, 0xa0010008           # is_equal out\n" ++
  "  jal ra, header_root_is_empty_trie\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhriet_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerRootIsEmptyTrieFunction ++ "\n" ++
  ".Lhriet_pdone:"

def ziskHeaderRootIsEmptyTrieDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "hriet_offset:\n" ++
  "  .zero 8\n" ++
  "hriet_length:\n" ++
  "  .zero 8\n" ++
  "hriet_empty_trie_root:\n" ++
  "  .byte 0x56,0xe8,0x1f,0x17,0x1b,0xcc,0x55,0xa6\n" ++
  "  .byte 0xff,0x83,0x45,0xe6,0x92,0xc0,0xf8,0x6e\n" ++
  "  .byte 0x5b,0x48,0xe0,0x1b,0x99,0x6c,0xad,0xc0\n" ++
  "  .byte 0x01,0x62,0x2f,0xb5,0xe3,0x63,0xb4,0x21"

def ziskHeaderRootIsEmptyTrieProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderRootIsEmptyTriePrologue
  dataAsm     := ziskHeaderRootIsEmptyTrieDataSection
}

/-! ## calldata_byte_counts -- PR-K105

    Count zero and non-zero bytes in an arbitrary byte buffer.
    Used by intrinsic-gas pricing across all post-Istanbul forks:

      EIP-2028 standard pricing:
        data_cost = zero_count × 4  +  non_zero_count × 16
      EIP-7623 calldata-floor pricing (Pectra+):
        floor_cost = zero_count × 10  +  non_zero_count × 40

    A pure-leaf helper: no callee-saved registers used (apart from
    saving s0..s1 so the loop is human-readable), no scratch
    memory, no transitive calls. Returns both counts in one pass.

    Calling convention:
      a0 (input)  : bytes ptr
      a1 (input)  : byte length
      a2 (input)  : u64 out ptr (zero_count)
      a3 (input)  : u64 out ptr (non_zero_count)
      ra (input)  : return
      a0 (output) : 0 (always succeeds — total over the buffer).

    `zero_count + non_zero_count == byte_length` exactly. -/
def calldataByteCountsFunction : String :=
  "calldata_byte_counts:\n" ++
  "  # Pure-leaf, but we read into t-regs and update in-place; no\n" ++
  "  # callee-saved usage needed.\n" ++
  "  li t0, 0                    # zero_count\n" ++
  "  li t1, 0                    # non_zero_count\n" ++
  "  mv t2, a0                   # cursor\n" ++
  "  mv t3, a1                   # remaining bytes\n" ++
  ".Lcbc_loop:\n" ++
  "  beqz t3, .Lcbc_done\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  bnez t4, .Lcbc_nz\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lcbc_step\n" ++
  ".Lcbc_nz:\n" ++
  "  addi t1, t1, 1\n" ++
  ".Lcbc_step:\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lcbc_loop\n" ++
  ".Lcbc_done:\n" ++
  "  sd t0, 0(a2)\n" ++
  "  sd t1, 0(a3)\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_calldata_byte_counts`: probe BuildUnit. Reads
    (length, bytes) from host input, writes (status,
    zero_count, non_zero_count) to OUTPUT (24 bytes total). -/
def ziskCalldataByteCountsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # byte length\n" ++
  "  addi a0, a4, 16             # bytes ptr\n" ++
  "  li a2, 0xa0010008           # zero_count out\n" ++
  "  li a3, 0xa0010010           # non_zero_count out\n" ++
  "  jal ra, calldata_byte_counts\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcbc_pdone\n" ++
  calldataByteCountsFunction ++ "\n" ++
  ".Lcbc_pdone:"

def ziskCalldataByteCountsDataSection : String :=
  ".section .data\n" ++
  "cbc_scratch:\n" ++
  "  .zero 8"

def ziskCalldataByteCountsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCalldataByteCountsPrologue
  dataAsm     := ziskCalldataByteCountsDataSection
}

/-! ## intrinsic_gas_calldata_floor_eip7623 -- PR-K106

    Compute the EIP-7623 calldata-floor gas cost for a tx, in
    closed form:

      tokens     = zero_count + 4 × non_zero_count
      floor_cost = tokens × GAS_TX_DATA_TOKEN_FLOOR  +  GAS_TX_BASE
                 = tokens × 10                       +  21000

    This is the lower bound on a tx's overall gas charge per
    EIP-7623; the actual charged amount is
    `max(intrinsic + execution, floor)`. PR-K46 covers the
    standard intrinsic-gas computation; K106 covers the floor
    side so callers can take the `max` cheaply.

    The Amsterdam constants are passed as arguments so the helper
    works across forks that re-cost the floor.

    Calling convention:
      a0 (input)  : data ptr
      a1 (input)  : data byte length
      a2 (input)  : floor_gas_per_token (10 on Amsterdam mainnet)
      a3 (input)  : token_per_nonzero (4 on Amsterdam mainnet)
      a4 (input)  : base_gas (21000 on mainnet)
      a5 (input)  : u64 out ptr (floor_cost)
      ra (input)  : return
      a0 (output) : 0 (always succeeds — total function).

    Pure-leaf semantics: no scratch memory, no transitive calls. -/
def intrinsicGasCalldataFloorEip7623Function : String :=
  "intrinsic_gas_calldata_floor_eip7623:\n" ++
  "  # Count zeros and non-zeros in one pass.\n" ++
  "  li t0, 0                    # zero_count\n" ++
  "  li t1, 0                    # non_zero_count\n" ++
  "  mv t2, a0                   # cursor\n" ++
  "  mv t3, a1                   # remaining\n" ++
  ".Ligcf_loop:\n" ++
  "  beqz t3, .Ligcf_done\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  bnez t4, .Ligcf_nz\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Ligcf_step\n" ++
  ".Ligcf_nz:\n" ++
  "  addi t1, t1, 1\n" ++
  ".Ligcf_step:\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Ligcf_loop\n" ++
  ".Ligcf_done:\n" ++
  "  # tokens = zero + non_zero × token_per_nonzero\n" ++
  "  mul t5, t1, a3              # non_zero × token_per_nz\n" ++
  "  add t5, t5, t0              # tokens\n" ++
  "  # floor = tokens × floor_gas_per_token + base_gas\n" ++
  "  mul t6, t5, a2\n" ++
  "  add t6, t6, a4\n" ++
  "  sd t6, 0(a5)\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_intrinsic_gas_calldata_floor_eip7623`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : data length
      bytes  8..16 : floor_gas_per_token
      bytes 16..24 : token_per_nonzero
      bytes 24..32 : base_gas
      bytes 32..   : data bytes
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : floor_cost (u64 LE) -/
def ziskIntrinsicGasCalldataFloorEip7623Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # data length\n" ++
  "  ld a2, 16(a6)               # floor_gas_per_token\n" ++
  "  ld a3, 24(a6)               # token_per_nonzero\n" ++
  "  ld a4, 32(a6)               # base_gas\n" ++
  "  addi a0, a6, 40             # data ptr\n" ++
  "  li a5, 0xa0010008           # floor_cost out\n" ++
  "  jal ra, intrinsic_gas_calldata_floor_eip7623\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Ligcf_pdone\n" ++
  intrinsicGasCalldataFloorEip7623Function ++ "\n" ++
  ".Ligcf_pdone:"

def ziskIntrinsicGasCalldataFloorEip7623DataSection : String :=
  ".section .data\n" ++
  "igcf_scratch:\n" ++
  "  .zero 8"

def ziskIntrinsicGasCalldataFloorEip7623ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskIntrinsicGasCalldataFloorEip7623Prologue
  dataAsm     := ziskIntrinsicGasCalldataFloorEip7623DataSection
}

/-! ## init_code_cost -- PR-K107

    Compute the EIP-3860 init-code gas cost for a contract-creation
    tx's init bytecode:

      init_code_cost = GAS_CODE_INIT_PER_WORD × ceil(len / 32)
                     = 2 × ((len + 31) ÷ 32)        (mainnet)

    Used inside `calculate_intrinsic_cost(tx)` whenever
    `tx.to == empty` (CREATE-shaped tx); pre-EIP-3860 forks
    skip this term.

    The `gas_per_word` constant is passed in so the helper works
    across forks that adjust it.

    Calling convention:
      a0 (input)  : init_code_length (u64)
      a1 (input)  : gas_per_word (u64; 2 on mainnet)
      a2 (input)  : u64 out ptr (init_code_cost)
      ra (input)  : return
      a0 (output) : 0 (always succeeds — total function).

    Pure-leaf semantics: no scratch memory, no transitive calls.
    The arithmetic stays in u64; for any `init_code_length` within
    the EIP-3860 cap (`MAX_INIT_CODE_SIZE = 49_152`) and any
    `gas_per_word ≤ 2^48`, the cost fits in u64. -/
def initCodeCostFunction : String :=
  "init_code_cost:\n" ++
  "  addi t0, a0, 31             # len + 31\n" ++
  "  srli t0, t0, 5              # / 32 → ceil(len/32)\n" ++
  "  mul t0, t0, a1              # × gas_per_word\n" ++
  "  sd t0, 0(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_init_code_cost`: probe BuildUnit. Reads
    (init_code_length, gas_per_word) from host input, writes
    (status, init_code_cost) to OUTPUT (16 bytes total).
    Input layout:
      bytes  0.. 8 : init_code_length
      bytes  8..16 : gas_per_word -/
def ziskInitCodeCostPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a0, 8(a3)                # init_code_length\n" ++
  "  ld a1, 16(a3)               # gas_per_word\n" ++
  "  li a2, 0xa0010008           # cost out\n" ++
  "  jal ra, init_code_cost\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Licc_pdone\n" ++
  initCodeCostFunction ++ "\n" ++
  ".Licc_pdone:"

def ziskInitCodeCostDataSection : String :=
  ".section .data\n" ++
  "icc_scratch:\n" ++
  "  .zero 8"

def ziskInitCodeCostProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskInitCodeCostPrologue
  dataAsm     := ziskInitCodeCostDataSection
}


/-! ## MPT branch helpers K117 / K118 — moved to `Programs/Mpt.lean` (file-size hard cap). -/

/-! ## stateless_guest body — PR-K5 keccak hash field

    Replaces the zero-stub `new_payload_request_root` field in
    `Stateless.Entry.run_stateless_guest`'s SSZ output with the
    keccak256 of the entire SSZ-input byte string the host
    streamed in via `ziskemu -i`. Concretely:

    - Body: the unchanged `Stateless.Entry.run_stateless_guest`
      Program. It writes:
        bytes  0..32 : zero hash (placeholder)
        byte      32 : successful_validation (PR4/PR5 derived)
        bytes 33..41 : chain_id (PR3 from-decode)
        bytes 41..48 : zero gap
        bytes 48..56 : header_count diagnostic (PR6 from-decode)
    - Epilogue (raw asm): set up sp, load (data ptr, len) from
      INPUT_ADDR + (16, 8), set output = OUTPUT_ADDR + 0, and
      `jal ra, zkvm_keccak256`. The function overwrites
      OUTPUT[0..32] with keccak256(input bytes), clobbering the
      zero stub.

    The host-side `compute_new_payload_request_root` per the spec
    is SSZ `hash_tree_root` (SHA-256), not Keccak. PR-K5 stamps a
    *content-dependent* hash there so the test harness has a
    non-trivial value to verify and the keccak bridge is wired
    into the encoder pipeline end-to-end. Once PR-S series lands,
    the SHA-256 hash_tree_root replaces this keccak. -/
def statelessGuestEpilogue : String :=
  "  # PR-S12: overwrite OUTPUT[0..32] with the SSZ\n" ++
  "  # `hash_tree_root` of the entire `witness:\n" ++
  "  # ExecutionWitness` field -- a 3-field Container holding\n" ++
  "  # state / codes / headers lists.\n" ++
  "  # \n" ++
  "  # SSZ algorithm (Container, NO mix_in_length):\n" ++
  "  #   state_root   = hash_tree_root(List[ByteList[2^20], 2^20])\n" ++
  "  #   codes_root   = hash_tree_root(List[ByteList[2^24], 2^16])\n" ++
  "  #   headers_root = hash_tree_root(List[ByteList[2^10], 2^8])\n" ++
  "  #   root         = merkleize([state_root, codes_root,\n" ++
  "  #                             headers_root], log2=2)\n" ++
  "  # \n" ++
  "  # Per-field caps: each list's N ≤ 32 (inherited from\n" ++
  "  # PR-S11's `ssz_hash_tree_root_list_bytelist`). Test\n" ++
  "  # fixtures stay well below.\n" ++
  "  # \n" ++
  "  # Navigation: chase the outer SSZ offset chain to find\n" ++
  "  # the bounds of the `witness` field within the SSZ-encoded\n" ++
  "  # `SszStatelessInput`, then delegate the per-sub-field\n" ++
  "  # walk + recursive hashing to\n" ++
  "  # `ssz_hash_tree_root_execution_witness`.\n" ++
  "  li sp, 0xa0050000\n" ++
  "  li t3, 0x40000000\n" ++
  "  addi t3, t3, 16             # t3 = ssz_start\n" ++
  "  lwu t4, 4(t3)               # outer offset_1 (witness offset)\n" ++
  "  add a0, t3, t4              # a0 = witness_start (section ptr)\n" ++
  "  lwu t5, 16(t3)              # outer offset_3 (witness end)\n" ++
  "  add t5, t3, t5              # witness_end\n" ++
  "  sub a1, t5, a0              # a1 = witness section_len\n" ++
  "  li a2, 0xa0010000           # a2 = OUTPUT_ADDR (hash field)\n" ++
  "  jal ra, ssz_hash_tree_root_execution_witness\n" ++
  "  j .Lsg_done\n" ++
  zkvmSha256Function ++ "\n" ++
  sszPackBytesFunction ++ "\n" ++
  sszMerkleizePow2Function ++ "\n" ++
  sszMerkleizeFunction ++ "\n" ++
  sszHashTreeRootBytesFunction ++ "\n" ++
  sszHashTreeRootListByteListFunction ++ "\n" ++
  sszHashTreeRootExecutionWitnessFunction ++ "\n" ++
  ".Lsg_done:"

def statelessGuestDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_scratch:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_padded:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_partial:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "ssz_hb_chunks:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_hb_partial:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "ssz_hb_mix:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "ssz_ltb_child_roots:\n" ++
  "  .zero 1024\n" ++
  ".balign 32\n" ++
  "ssz_ltb_partial:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "ssz_ltb_mix:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "ssz_ew_field_roots:\n" ++
  "  .zero 96\n" ++
  sszZeroHashesDataSection

def statelessGuestUnit : BuildUnit := {
  body        := EvmAsm.Stateless.run_stateless_guest
  epilogueAsm := statelessGuestEpilogue
  dataAsm     := statelessGuestDataSection
}

/-! ## registry -/

/-- Second half of the program lookup, split off `lookupProgram` to
    keep the C-emitted match below clang's default 256 bracket-nesting
    limit. New PRs append arms here, not to `lookupProgram`. -/
def lookupProgramTail : String → Option BuildUnit
  | "zisk_bloom_eq" => some ziskBloomEqProbeUnit
  | "zisk_rlp_encode_u64" => some ziskRlpEncodeU64ProbeUnit
  | "zisk_receipt_encode" => some ziskReceiptEncodeProbeUnit
  | "zisk_single_leaf_trie_root" => some ziskSingleLeafTrieRootProbeUnit
  | "zisk_mpt_leaf_node_encode" => some ziskMptLeafNodeEncodeProbeUnit
  | "zisk_mpt_node_slot_encode" => some ziskMptNodeSlotEncodeProbeUnit
  | "zisk_mpt_extension_node_encode" => some ziskMptExtensionNodeEncodeProbeUnit
  | "zisk_mpt_branch_node_encode" => some ziskMptBranchNodeEncodeProbeUnit
  | "zisk_nibbles_common_prefix_len" => some ziskNibblesCommonPrefixLenProbeUnit
  | "zisk_mpt_branch_payload_two_slots" => some ziskMptBranchPayloadTwoSlotsProbeUnit
  | "zisk_mpt_leaf_node_encode_from_nibbles" => some ziskMptLeafNodeEncodeFromNibblesProbeUnit
  | "zisk_mpt_branch_node_keccak" => some ziskMptBranchNodeKeccakProbeUnit
  | "zisk_mpt_two_leaf_root_indexed" => some ziskMptTwoLeafRootIndexedProbeUnit
  | "zisk_mpt_one_leaf_root_indexed" => some ziskMptOneLeafRootIndexedProbeUnit
  | "zisk_block_validate_transactions_root_one_tx" => some ziskBlockValidateTransactionsRootOneTxProbeUnit
  | "zisk_block_validate_withdrawals_root_one_w" => some ziskBlockValidateWithdrawalsRootOneWProbeUnit
  | "zisk_block_validate_withdrawals_root_two_w" => some ziskBlockValidateWithdrawalsRootTwoWProbeUnit
  | "zisk_block_validate_receipts_root_one_receipt" => some ziskBlockValidateReceiptsRootOneReceiptProbeUnit
  | "zisk_block_validate_receipts_root_two_receipts" => some ziskBlockValidateReceiptsRootTwoReceiptsProbeUnit
  | "zisk_block_validate_transactions_root_two_tx" => some ziskBlockValidateTransactionsRootTwoTxProbeUnit
  | "zisk_block_hash_from_header" => some ziskBlockHashFromHeaderProbeUnit
  | "zisk_validate_parent_hash_link" => some ziskValidateParentHashLinkProbeUnit
  | "zisk_validate_header_pair" => some ziskValidateHeaderPairProbeUnit
  | "zisk_validate_header_chain" => some ziskValidateHeaderChainProbeUnit
  | "zisk_block_hash_array_from_chain" => some ziskBlockHashArrayFromChainProbeUnit
  | "zisk_validate_block_hash_chain_match" => some ziskValidateBlockHashChainMatchProbeUnit
  | "zisk_chain_compute_total_gas_used" => some ziskChainComputeTotalGasUsedProbeUnit
  | "zisk_chain_extract_number_range" => some ziskChainExtractNumberRangeProbeUnit
  | "zisk_header_extract_basefee" => some ziskHeaderExtractBasefeeProbeUnit
  | "zisk_chain_extract_basefee_range" => some ziskChainExtractBasefeeRangeProbeUnit
  | "zisk_chain_block_hashes_commitment" => some ziskChainBlockHashesCommitmentProbeUnit
  | "zisk_header_extract_state_root" => some ziskHeaderExtractStateRootProbeUnit
  | "zisk_header_extract_parent_hash" => some ziskHeaderExtractParentHashProbeUnit
  | "zisk_header_extract_receipts_root" => some ziskHeaderExtractReceiptsRootProbeUnit
  | "zisk_header_extract_transactions_root" => some ziskHeaderExtractTransactionsRootProbeUnit
  | "zisk_header_extract_withdrawals_root" => some ziskHeaderExtractWithdrawalsRootProbeUnit
  | "zisk_header_extract_ommers_hash" => some ziskHeaderExtractOmmersHashProbeUnit
  | "zisk_header_extract_prev_randao" => some ziskHeaderExtractPrevRandaoProbeUnit
  | "zisk_header_extract_beneficiary" => some ziskHeaderExtractBeneficiaryProbeUnit
  | "zisk_block_hash_matches" => some ziskBlockHashMatchesProbeUnit
  | "zisk_header_extract_gas_used" => some ziskHeaderExtractGasUsedProbeUnit
  | "zisk_header_extract_gas_limit" => some ziskHeaderExtractGasLimitProbeUnit
  | "zisk_block_validate_block_hash_pair" => some ziskBlockValidateBlockHashPairProbeUnit
  | "zisk_block_hash_and_extract_number" => some ziskBlockHashAndExtractNumberProbeUnit
  | "zisk_header_compute_summary_struct" => some ziskHeaderComputeSummaryStructProbeUnit
  | "zisk_header_extract_difficulty" => some ziskHeaderExtractDifficultyProbeUnit
  | "zisk_header_extract_extra_data" => some ziskHeaderExtractExtraDataProbeUnit
  | "zisk_header_extract_nonce" => some ziskHeaderExtractNonceProbeUnit
  | "zisk_header_validate_nonce_zero" => some ziskHeaderValidateNonceZeroProbeUnit
  | "zisk_header_validate_difficulty_zero" => some ziskHeaderValidateDifficultyZeroProbeUnit
  | "zisk_validate_header_post_merge_zeros" => some ziskValidateHeaderPostMergeZerosProbeUnit
  | "zisk_chain_validate_post_merge_zeros" => some ziskChainValidatePostMergeZerosProbeUnit
  | "zisk_chain_validate_full" => some ziskChainValidateFullProbeUnit
  | "zisk_chain_validate_increasing_timestamps" => some ziskChainValidateIncreasingTimestampsProbeUnit
  | "zisk_chain_validate_consecutive_numbers" => some ziskChainValidateConsecutiveNumbersProbeUnit
  | "zisk_chain_compute_total_blob_gas" => some ziskChainComputeTotalBlobGasProbeUnit
  | "zisk_header_extract_timestamp" => some ziskHeaderExtractTimestampProbeUnit
  | "zisk_header_extract_number" => some ziskHeaderExtractNumberProbeUnit
  | "zisk_account_validate_code_hash_empty" => some ziskAccountValidateCodeHashEmptyProbeUnit
  | "zisk_account_validate_storage_root_empty" => some ziskAccountValidateStorageRootEmptyProbeUnit
  | "zisk_chain_compute_max_gas_used" => some ziskChainComputeMaxGasUsedProbeUnit
  | "zisk_chain_compute_max_blob_gas_used" => some ziskChainComputeMaxBlobGasUsedProbeUnit
  | "zisk_chain_compute_min_gas_used" => some ziskChainComputeMinGasUsedProbeUnit
  | "zisk_chain_extract_timestamp_range" => some ziskChainExtractTimestampRangeProbeUnit
  | "zisk_chain_validate_gas_used_under_limit" => some ziskChainValidateGasUsedUnderLimitProbeUnit
  | "zisk_header_extract_blob_gas_used" => some ziskHeaderExtractBlobGasUsedProbeUnit
  | "zisk_account_validate_nonce_zero" => some ziskAccountValidateNonceZeroProbeUnit
  | "zisk_chain_compute_min_blob_gas_used" => some ziskChainComputeMinBlobGasUsedProbeUnit
  | "zisk_header_extract_excess_blob_gas" => some ziskHeaderExtractExcessBlobGasProbeUnit
  | "zisk_chain_extract_gas_used_range" => some ziskChainExtractGasUsedRangeProbeUnit
  | "zisk_chain_extract_blob_gas_used_range" => some ziskChainExtractBlobGasUsedRangeProbeUnit
  | "zisk_chain_extract_basefee_first_last" => some ziskChainExtractBasefeeFirstLastProbeUnit
  | "zisk_chain_compute_total_blob_count" => some ziskChainComputeTotalBlobCountProbeUnit
  | "zisk_block_validate_2tx_full" => some ziskBlockValidate2txFullProbeUnit
  | "zisk_block_body_extract_2tx" => some ziskBlockBodyExtract2txProbeUnit
  | "zisk_block_validate_2tx_full_with_body" => some ziskBlockValidate2txFullWithBodyProbeUnit
  | "zisk_block_validate_empty_ommers_hash" => some ziskBlockValidateEmptyOmmersHashProbeUnit
  | "zisk_block_validate_no_withdrawals_pair" => some ziskBlockValidateNoWithdrawalsPairProbeUnit
  | "zisk_block_body_extract_1tx" => some ziskBlockBodyExtract1txProbeUnit
  | "zisk_block_validate_1tx_full" => some ziskBlockValidate1txFullProbeUnit
  | "zisk_block_validate_1tx_full_with_body" => some ziskBlockValidate1txFullWithBodyProbeUnit
  | "zisk_block_validate_empty_receipts_root" => some ziskBlockValidateEmptyReceiptsRootProbeUnit
  | "zisk_block_validate_empty_block" => some ziskBlockValidateEmptyBlockProbeUnit
  | "zisk_validate_empty_block_with_parent" => some ziskValidateEmptyBlockWithParentProbeUnit
  | "zisk_validate_empty_block_chain" => some ziskValidateEmptyBlockChainProbeUnit
  | "zisk_block_body_extract_tx_count" => some ziskBlockBodyExtractTxCountProbeUnit
  | "zisk_block_body_extract_withdrawal_count" => some ziskBlockBodyExtractWithdrawalCountProbeUnit
  | "zisk_block_body_summary" => some ziskBlockBodySummaryProbeUnit
  | "zisk_block_body_validate_empty" => some ziskBlockBodyValidateEmptyProbeUnit
  | "zisk_chain_body_total_tx_count" => some ziskChainBodyTotalTxCountProbeUnit
  | "zisk_chain_body_total_withdrawal_count" => some ziskChainBodyTotalWithdrawalCountProbeUnit
  | "zisk_block_logs_bloom_from_receipts_list" => some ziskBlockLogsBloomFromReceiptsListProbeUnit
  | "zisk_block_validate_logs_bloom" => some ziskBlockValidateLogsBloomProbeUnit
  | "zisk_header_root_is_empty_trie" => some ziskHeaderRootIsEmptyTrieProbeUnit
  | "zisk_calldata_byte_counts" => some ziskCalldataByteCountsProbeUnit
  | "zisk_intrinsic_gas_calldata_floor_eip7623" => some ziskIntrinsicGasCalldataFloorEip7623ProbeUnit
  | "zisk_init_code_cost"       => some ziskInitCodeCostProbeUnit
  | "zisk_mpt_nibbles_to_compact" => some ziskMptNibblesToCompactProbeUnit
  | "zisk_mpt_compact_to_nibbles" => some ziskMptCompactToNibblesProbeUnit
  | "zisk_mpt_node_classify"      => some ziskMptNodeClassifyProbeUnit
  | "zisk_mpt_encode_internal_node" => some ziskMptEncodeInternalNodeProbeUnit
  | "zisk_mpt_branch_get_child" => some ziskMptBranchGetChildProbeUnit
  | "zisk_mpt_branch_get_value" => some ziskMptBranchGetValueProbeUnit
  | "zisk_mpt_leaf_extract"     => some ziskMptLeafExtractProbeUnit
  | "zisk_mpt_extension_extract" => some ziskMptExtensionExtractProbeUnit
  | "zisk_mpt_branch_used_count" => some ziskMptBranchUsedCountProbeUnit
  | "zisk_mpt_branch_first_used_index" => some ziskMptBranchFirstUsedIndexProbeUnit
  | "zisk_sha256_from_input"    => some ziskSha256FromInputProbeUnit
  | "zisk_ssz_pair_hash"        => some ziskSszPairHashProbeUnit
  | "zisk_ssz_zero_hashes"      => some ziskSszZeroHashesProbeUnit
  | "zisk_ssz_merkleize_pow2"   => some ziskSszMerkleizePow2ProbeUnit
  | "zisk_ssz_merkleize"        => some ziskSszMerkleizeProbeUnit
  | "zisk_ssz_pack_bytes"       => some ziskSszPackBytesProbeUnit
  | "zisk_ssz_hash_tree_root_bytes" => some ziskSszHashTreeRootBytesProbeUnit
  | "zisk_ssz_hash_tree_root_list_bytelist" => some ziskSszHashTreeRootListByteListProbeUnit
  | "zisk_ssz_hash_tree_root_execution_witness" => some ziskSszHashTreeRootExecutionWitnessProbeUnit
  | _                           => none

/-- Look up a program by name. Returns `none` for unknown names so the CLI
    can produce a clean error. -/
def lookupProgram : String → Option BuildUnit
  | "smoke"                     => some smokeUnit
  | "evm_add"                   => some evmAddUnit
  | "evm_div"                   => some evmDivUnit
  | "evm_div_from_input"        => some evmDivFromInputUnit
  | "evm_mod"                   => some evmModUnit
  | "evm_mod_from_input"        => some evmModFromInputUnit
  | "evm_sdiv"                  => some evmSdivV4Unit
  | "evm_sdiv_from_input"       => some evmSdivV4FromInputUnit
  | "evm_sdiv_v4"               => some evmSdivV4Unit
  | "evm_sdiv_v4_from_input"    => some evmSdivV4FromInputUnit
  | "evm_smod"                  => some evmSmodUnit
  | "evm_smod_from_input"       => some evmSmodFromInputUnit
  | "evm_smod_v4"               => some evmSmodV4Unit
  | "evm_smod_v4_from_input"    => some evmSmodV4FromInputUnit
  | "input_echo"                => some inputEchoUnit
  | "evm_add_from_input"        => some evmAddFromInputUnit
  | "tiny_interp_add"           => some tinyInterpAddUnit
  | "tiny_interp_add2"          => some tinyInterpAdd2Unit
  | "tiny_interp_dispatch_add"  => some tinyInterpDispatchAddUnit
  | "tiny_interp_dispatch_add2" => some tinyInterpDispatchAdd2Unit
  | "runtime_dispatcher"        => some runtimeDispatcherUnit
  | "stateless_guest"           => some statelessGuestUnit
  | "zisk_keccak_probe"         => some ziskKeccakProbeUnit
  | "zisk_keccak256_empty"      => some ziskKeccak256EmptyProbeUnit
  | "zisk_keccak256_abc"        => some ziskKeccak256AbcProbeUnit
  | "zisk_zkvm_keccak256"       => some ziskZkvmKeccak256ProbeUnit
  | "zisk_sha256_probe_le"      => some ziskSha256ProbeLeUnit
  | "zisk_zkvm_sha256"          => some ziskZkvmSha256ProbeUnit
  | "zisk_keccak256_from_input" => some ziskKeccak256FromInputProbeUnit
  | "zisk_headers_keccak_chain" => some ziskHeadersKeccakChainProbeUnit
  | "zisk_headers_keccak_array" => some ziskHeadersKeccakArrayProbeUnit
  | "zisk_headers_parent_hash"  => some ziskHeadersParentHashProbeUnit
  | "zisk_header_validate_parent_hash" => some ziskHeaderValidateParentHashProbeUnit
  | "zisk_header_chain_walk_step" => some ziskHeaderChainWalkStepProbeUnit
  | "zisk_account_validate_code_hash" => some ziskAccountValidateCodeHashProbeUnit
  | "zisk_account_storage_root_eq" => some ziskAccountStorageRootEqProbeUnit
  | "zisk_account_code_hash_eq" => some ziskAccountCodeHashEqProbeUnit
  | "zisk_account_nonce_eq" => some ziskAccountNonceEqProbeUnit
  | "zisk_account_is_eip161_empty" => some ziskAccountIsEip161EmptyProbeUnit
  | "zisk_account_extract_storage_root" => some ziskAccountExtractStorageRootProbeUnit
  | "zisk_account_extract_balance" => some ziskAccountExtractBalanceProbeUnit
  | "zisk_account_extract_nonce" => some ziskAccountExtractNonceProbeUnit
  | "zisk_account_extract_code_hash" => some ziskAccountExtractCodeHashProbeUnit
  | "zisk_account_is_empty"     => some ziskAccountIsEmptyProbeUnit
  | "zisk_account_has_empty_code" => some ziskAccountHasEmptyCodeProbeUnit
  | "zisk_account_storage_root_is_empty" => some ziskAccountStorageRootIsEmptyProbeUnit
  | "zisk_address_from_pubkey"  => some ziskAddressFromPubkeyProbeUnit
  | "zisk_address_compute_create2" => some ziskAddressComputeCreate2ProbeUnit
  | "zisk_address_compute_create" => some ziskAddressComputeCreateProbeUnit
  | "zisk_mpt_account_path_nibbles" => some ziskMptAccountPathNibblesProbeUnit
  | "zisk_headers_validate_chain" => some ziskHeadersValidateChainProbeUnit
  | "zisk_witness_lookup_by_hash" => some ziskWitnessLookupByHashProbeUnit
  | "zisk_rlp_list_nth_item"    => some ziskRlpListNthItemProbeUnit
  | "zisk_rlp_list_count_items" => some ziskRlpListCountItemsProbeUnit
  | "zisk_access_list_count"    => some ziskAccessListCountProbeUnit
  | "zisk_blob_gas_used_from_versioned_hashes" => some ziskBlobGasUsedFromVersionedHashesProbeUnit
  | "zisk_mpt_node_kind"        => some ziskMptNodeKindProbeUnit
  | "zisk_mpt_branch_child"     => some ziskMptBranchChildProbeUnit
  | "zisk_hp_decode_nibbles"    => some ziskHpDecodeNibblesProbeUnit
  | "zisk_mpt_walk"             => some ziskMptWalkProbeUnit
  | "zisk_bytes_to_nibbles"     => some ziskBytesToNibblesProbeUnit
  | "zisk_mpt_lookup_by_key"    => some ziskMptLookupByKeyProbeUnit
  | "zisk_account_decode"       => some ziskAccountDecodeProbeUnit
  | "zisk_account_at_address"   => some ziskAccountAtAddressProbeUnit
  | "zisk_slot_at_index"        => some ziskSlotAtIndexProbeUnit
  | "zisk_rlp_encode_uint_be"   => some ziskRlpEncodeUintBeProbeUnit
  | "zisk_rlp_encode_bytes"     => some ziskRlpEncodeBytesProbeUnit
  | "zisk_rlp_encode_list_prefix" => some ziskRlpEncodeListPrefixProbeUnit
  | "zisk_withdrawal_rlp_encode" => some ziskWithdrawalRlpEncodeProbeUnit
  | "zisk_withdrawal_compute_hash" => some ziskWithdrawalComputeHashProbeUnit
  | "zisk_account_encode"       => some ziskAccountEncodeProbeUnit
  | "zisk_hp_encode_nibbles"    => some ziskHpEncodeNibblesProbeUnit
  | "zisk_state_root_single_account" => some ziskStateRootSingleAccountProbeUnit
  | "zisk_rlp_field_to_u64"     => some ziskRlpFieldToU64ProbeUnit
  | "zisk_rlp_field_to_u256_be" => some ziskRlpFieldToU256BeProbeUnit
  | "zisk_tx_legacy_decode"     => some ziskTxLegacyDecodeProbeUnit
  | "zisk_tx_eip1559_decode"    => some ziskTxEip1559DecodeProbeUnit
  | "zisk_derive_chain_id_from_v" => some ziskDeriveChainIdFromVProbeUnit
  | "zisk_tx_legacy_extract_signature" => some ziskTxLegacyExtractSignatureProbeUnit
  | "zisk_tx_eip1559_extract_signature" => some ziskTxEip1559ExtractSignatureProbeUnit
  | "zisk_tx_eip2930_extract_signature" => some ziskTxEip2930ExtractSignatureProbeUnit
  | "zisk_tx_eip4844_extract_signature" => some ziskTxEip4844ExtractSignatureProbeUnit
  | "zisk_tx_eip7702_extract_signature" => some ziskTxEip7702ExtractSignatureProbeUnit
  | "zisk_eip7702_authorization_extract_signature" => some ziskEip7702AuthorizationExtractSignatureProbeUnit
  | "zisk_rlp_list_truncate_to_n_fields" => some ziskRlpListTruncateToNFieldsProbeUnit
  | "zisk_tx_signing_hash" => some ziskTxSigningHashProbeUnit
  | "zisk_tx_signing_hash_legacy_eip155" => some ziskTxSigningHashLegacyEip155ProbeUnit
  | "zisk_eip7702_authorization_signing_hash" => some ziskEip7702AuthorizationSigningHashProbeUnit
  | "zisk_header_minimal_decode" => some ziskHeaderMinimalDecodeProbeUnit
  | "zisk_header_extended_decode" => some ziskHeaderExtendedDecodeProbeUnit
  | "zisk_coinbase_extract_from_header" => some ziskCoinbaseExtractFromHeaderProbeUnit
  | "zisk_header_extract_blob_gas_pair" => some ziskHeaderExtractBlobGasPairProbeUnit
  | "zisk_block_validate_blob_gas_max_cap" => some ziskBlockValidateBlobGasMaxCapProbeUnit
  | "zisk_header_extract_block_roots" => some ziskHeaderExtractBlockRootsProbeUnit
  | "zisk_validate_header_basic" => some ziskValidateHeaderBasicProbeUnit
  | "zisk_check_gas_limit"      => some ziskCheckGasLimitProbeUnit
  | "zisk_tx_validate_against_block" => some ziskTxValidateAgainstBlockProbeUnit
  | "zisk_calc_excess_blob_gas" => some ziskCalcExcessBlobGasProbeUnit
  | "zisk_header_validate_post_merge" => some ziskHeaderValidatePostMergeProbeUnit
  | "zisk_header_validate_extra_data_length" => some ziskHeaderValidateExtraDataLengthProbeUnit
  | "zisk_u256_add_be"          => some ziskU256AddBeProbeUnit
  | "zisk_u256_lt_be"           => some ziskU256LtBeProbeUnit
  | "zisk_u256_sub_be"          => some ziskU256SubBeProbeUnit
  | "zisk_u256_eq"              => some ziskU256EqProbeUnit
  | "zisk_u256_mul_u64_be"      => some ziskU256MulU64BeProbeUnit
  | "zisk_account_charge_gas_pre_exec" => some ziskAccountChargeGasPreExecProbeUnit
  | "zisk_account_refund_gas_post_exec" => some ziskAccountRefundGasPostExecProbeUnit
  | "zisk_eip1559_calc_base_fee_per_gas" => some ziskEip1559CalcBaseFeePerGasProbeUnit
  | "zisk_header_validate_base_fee" => some ziskHeaderValidateBaseFeeProbeUnit
  | "zisk_validate_header_full" => some ziskValidateHeaderFullProbeUnit
  | "zisk_u256_from_u64_be"     => some ziskU256FromU64BeProbeUnit
  | "zisk_u256_to_u64_be"       => some ziskU256ToU64BeProbeUnit
  | "zisk_u256_is_zero"         => some ziskU256IsZeroProbeUnit
  | "zisk_u256_min"             => some ziskU256MinProbeUnit
  | "zisk_u256_max"             => some ziskU256MaxProbeUnit
  | "zisk_u256_div_u64_be"      => some ziskU256DivU64BeProbeUnit
  | "zisk_priority_fee_per_gas_eip1559" => some ziskPriorityFeePerGasEip1559ProbeUnit
  | "zisk_effective_gas_price_eip1559" => some ziskEffectiveGasPriceEip1559ProbeUnit
  | "zisk_tx_cost_compute"      => some ziskTxCostComputeProbeUnit
  | "zisk_validate_transaction_balance" => some ziskValidateTransactionBalanceProbeUnit
  | "zisk_tx_type_dispatch"     => some ziskTxTypeDispatchProbeUnit
  | "zisk_tx_extract_nonce_and_gas" => some ziskTxExtractNonceAndGasProbeUnit
  | "zisk_tx_extract_to_address" => some ziskTxExtractToAddressProbeUnit
  | "zisk_tx_extract_value"     => some ziskTxExtractValueProbeUnit
  | "zisk_tx_extract_data_section" => some ziskTxExtractDataSectionProbeUnit
  | "zisk_tx_extract_gas_pricing"  => some ziskTxExtractGasPricingProbeUnit
  | "zisk_tx_eip2930_decode"    => some ziskTxEip2930DecodeProbeUnit
  | "zisk_tx_eip7702_decode"    => some ziskTxEip7702DecodeProbeUnit
  | "zisk_tx_eip4844_decode"    => some ziskTxEip4844DecodeProbeUnit
  | "zisk_tx_eip4844_compute_blob_gas" => some ziskTxEip4844ComputeBlobGasProbeUnit
  | "zisk_tx_calculate_total_blob_gas" => some ziskTxCalculateTotalBlobGasProbeUnit
  | "zisk_block_body_blob_gas_total" => some ziskBlockBodyBlobGasTotalProbeUnit
  | "zisk_block_validate_blob_gas_consistency" => some ziskBlockValidateBlobGasConsistencyProbeUnit
  | "zisk_tx_decode_dispatch"   => some ziskTxDecodeDispatchProbeUnit
  | "zisk_intrinsic_gas_legacy" => some ziskIntrinsicGasLegacyProbeUnit
  | "zisk_tx_validate_intrinsic_gas_legacy" => some ziskTxValidateIntrinsicGasLegacyProbeUnit
  | "zisk_validate_transaction_basic" => some ziskValidateTransactionBasicProbeUnit
  | "zisk_validate_transaction_full" => some ziskValidateTransactionFullProbeUnit
  | "zisk_withdrawal_decode"    => some ziskWithdrawalDecodeProbeUnit
  | "zisk_block_body_decode"    => some ziskBlockBodyDecodeProbeUnit
  | "zisk_block_validate_ommers_empty" => some ziskBlockValidateOmmersEmptyProbeUnit
  | "zisk_process_withdrawal"   => some ziskProcessWithdrawalProbeUnit
  | "zisk_process_withdrawals_block" => some ziskProcessWithdrawalsBlockProbeUnit
  | "zisk_withdrawals_sum_amounts" => some ziskWithdrawalsSumAmountsProbeUnit
  | "zisk_block_withdrawals_total" => some ziskBlockWithdrawalsTotalProbeUnit
  | "zisk_block_count_withdrawals" => some ziskBlockCountWithdrawalsProbeUnit
  | "zisk_block_count_transactions" => some ziskBlockCountTransactionsProbeUnit
  | "zisk_block_summary"        => some ziskBlockSummaryProbeUnit
  | "zisk_block_compute_tx_hashes" => some ziskBlockComputeTxHashesProbeUnit
  | "zisk_bloom_add_value" => some ziskBloomAddValueProbeUnit
  | "zisk_log_bloom_add" => some ziskLogBloomAddProbeUnit
  | "zisk_logs_list_bloom_add" => some ziskLogsListBloomAddProbeUnit
  | "zisk_bloom_or_into" => some ziskBloomOrIntoProbeUnit
  | "zisk_receipt_extract_logs_bloom" => some ziskReceiptExtractLogsBloomProbeUnit
  | "zisk_header_extract_logs_bloom" => some ziskHeaderExtractLogsBloomProbeUnit
  | s                           => lookupProgramTail s

/-- List of known program names, for use in CLI usage strings. -/
def knownProgramNames : List String :=
  ["smoke", "evm_add", "evm_div", "evm_mod", "evm_sdiv", "evm_sdiv_v4", "input_echo",
   "evm_add_from_input", "evm_div_from_input", "evm_mod_from_input",
   "evm_sdiv_from_input", "evm_sdiv_v4_from_input",
   "evm_smod", "evm_smod_from_input",
   "evm_smod_v4", "evm_smod_v4_from_input",
   "tiny_interp_add", "tiny_interp_add2",
   "tiny_interp_dispatch_add", "tiny_interp_dispatch_add2",
   "runtime_dispatcher",
   "stateless_guest",
   "zisk_keccak_probe",
   "zisk_keccak256_empty",
   "zisk_keccak256_abc",
   "zisk_zkvm_keccak256",
   "zisk_sha256_probe_le",
   "zisk_zkvm_sha256",
   "zisk_keccak256_from_input",
   "zisk_headers_keccak_chain",
   "zisk_headers_keccak_array",
   "zisk_headers_parent_hash",
   "zisk_header_validate_parent_hash",
   "zisk_header_chain_walk_step",
   "zisk_account_validate_code_hash",
   "zisk_account_storage_root_eq",
   "zisk_account_code_hash_eq",
   "zisk_account_nonce_eq",
   "zisk_account_is_eip161_empty",
   "zisk_account_extract_storage_root",
   "zisk_account_extract_balance",
   "zisk_account_extract_nonce",
   "zisk_account_extract_code_hash",
   "zisk_account_is_empty",
   "zisk_account_has_empty_code",
   "zisk_account_storage_root_is_empty",
   "zisk_address_from_pubkey",
   "zisk_address_compute_create2",
   "zisk_address_compute_create",
   "zisk_mpt_account_path_nibbles",
   "zisk_headers_validate_chain",
   "zisk_witness_lookup_by_hash",
   "zisk_rlp_list_nth_item",
   "zisk_rlp_list_count_items",
   "zisk_access_list_count",
   "zisk_blob_gas_used_from_versioned_hashes",
   "zisk_mpt_node_kind",
   "zisk_mpt_branch_child",
   "zisk_hp_decode_nibbles",
   "zisk_mpt_walk",
   "zisk_bytes_to_nibbles",
   "zisk_mpt_lookup_by_key",
   "zisk_account_decode",
   "zisk_account_at_address",
   "zisk_slot_at_index",
   "zisk_rlp_encode_uint_be",
   "zisk_rlp_encode_bytes",
   "zisk_rlp_encode_list_prefix",
   "zisk_withdrawal_rlp_encode",
   "zisk_withdrawal_compute_hash",
   "zisk_account_encode",
   "zisk_hp_encode_nibbles",
   "zisk_state_root_single_account",
   "zisk_rlp_field_to_u64",
   "zisk_rlp_field_to_u256_be",
   "zisk_tx_legacy_decode",
   "zisk_tx_eip1559_decode",
   "zisk_derive_chain_id_from_v",
   "zisk_tx_legacy_extract_signature",
   "zisk_tx_eip1559_extract_signature",
   "zisk_tx_eip2930_extract_signature",
   "zisk_tx_eip4844_extract_signature",
   "zisk_tx_eip7702_extract_signature",
   "zisk_eip7702_authorization_extract_signature",
   "zisk_rlp_list_truncate_to_n_fields",
   "zisk_tx_signing_hash",
   "zisk_tx_signing_hash_legacy_eip155",
   "zisk_eip7702_authorization_signing_hash",
   "zisk_header_minimal_decode",
   "zisk_header_extended_decode",
   "zisk_coinbase_extract_from_header",
   "zisk_header_extract_blob_gas_pair",
   "zisk_block_validate_blob_gas_max_cap",
   "zisk_header_extract_block_roots",
   "zisk_validate_header_basic",
   "zisk_check_gas_limit",
   "zisk_tx_validate_against_block",
   "zisk_calc_excess_blob_gas",
   "zisk_header_validate_post_merge",
   "zisk_header_validate_extra_data_length",
   "zisk_u256_add_be",
   "zisk_u256_lt_be",
   "zisk_u256_sub_be",
   "zisk_u256_eq",
   "zisk_u256_mul_u64_be",
   "zisk_account_charge_gas_pre_exec",
   "zisk_account_refund_gas_post_exec",
   "zisk_eip1559_calc_base_fee_per_gas",
   "zisk_header_validate_base_fee",
   "zisk_validate_header_full",
   "zisk_u256_from_u64_be",
   "zisk_u256_to_u64_be",
   "zisk_u256_is_zero",
   "zisk_u256_min",
   "zisk_u256_max",
   "zisk_u256_div_u64_be",
   "zisk_priority_fee_per_gas_eip1559",
   "zisk_effective_gas_price_eip1559",
   "zisk_tx_cost_compute",
   "zisk_validate_transaction_balance",
   "zisk_tx_type_dispatch",
   "zisk_tx_extract_nonce_and_gas",
   "zisk_tx_extract_to_address",
   "zisk_tx_extract_value",
   "zisk_tx_extract_data_section",
   "zisk_tx_extract_gas_pricing",
   "zisk_tx_eip2930_decode",
   "zisk_tx_eip7702_decode",
   "zisk_tx_eip4844_decode",
   "zisk_tx_eip4844_compute_blob_gas",
   "zisk_tx_calculate_total_blob_gas",
   "zisk_block_body_blob_gas_total",
   "zisk_block_validate_blob_gas_consistency",
   "zisk_tx_decode_dispatch",
   "zisk_intrinsic_gas_legacy",
   "zisk_tx_validate_intrinsic_gas_legacy",
   "zisk_validate_transaction_basic",
   "zisk_validate_transaction_full",
   "zisk_withdrawal_decode",
   "zisk_block_body_decode",
   "zisk_block_validate_ommers_empty",
   "zisk_process_withdrawal",
   "zisk_process_withdrawals_block",
   "zisk_withdrawals_sum_amounts",
   "zisk_block_withdrawals_total",
   "zisk_block_count_withdrawals",
   "zisk_block_count_transactions",
   "zisk_block_summary",
   "zisk_block_compute_tx_hashes",
   "zisk_bloom_add_value",
   "zisk_log_bloom_add",
   "zisk_logs_list_bloom_add",
   "zisk_bloom_or_into",
   "zisk_receipt_extract_logs_bloom",
   "zisk_header_extract_logs_bloom",
   "zisk_bloom_eq",
   "zisk_rlp_encode_u64",
   "zisk_receipt_encode",
   "zisk_single_leaf_trie_root",
   "zisk_mpt_leaf_node_encode",
   "zisk_mpt_node_slot_encode",
   "zisk_mpt_extension_node_encode",
   "zisk_mpt_branch_node_encode",
   "zisk_nibbles_common_prefix_len",
   "zisk_mpt_branch_payload_two_slots",
   "zisk_mpt_leaf_node_encode_from_nibbles",
   "zisk_mpt_branch_node_keccak",
   "zisk_mpt_two_leaf_root_indexed",
   "zisk_mpt_one_leaf_root_indexed",
   "zisk_block_validate_transactions_root_one_tx",
   "zisk_block_validate_withdrawals_root_one_w",
   "zisk_block_validate_withdrawals_root_two_w",
   "zisk_block_validate_receipts_root_one_receipt",
   "zisk_block_validate_receipts_root_two_receipts",
   "zisk_block_validate_transactions_root_two_tx",
   "zisk_block_hash_from_header",
   "zisk_validate_parent_hash_link",
   "zisk_validate_header_pair",
   "zisk_validate_header_chain",
   "zisk_block_hash_array_from_chain",
   "zisk_validate_block_hash_chain_match",
   "zisk_chain_compute_total_gas_used",
   "zisk_chain_extract_number_range",
   "zisk_header_extract_basefee",
   "zisk_chain_extract_basefee_range",
   "zisk_chain_block_hashes_commitment",
   "zisk_header_extract_state_root",
   "zisk_header_extract_parent_hash",
   "zisk_header_extract_receipts_root",
   "zisk_header_extract_transactions_root",
   "zisk_header_extract_withdrawals_root",
   "zisk_header_extract_ommers_hash",
   "zisk_header_extract_prev_randao",
   "zisk_header_extract_beneficiary",
   "zisk_block_hash_matches",
   "zisk_header_extract_gas_used",
   "zisk_header_extract_gas_limit",
   "zisk_block_validate_block_hash_pair",
   "zisk_block_hash_and_extract_number",
   "zisk_header_compute_summary_struct",
   "zisk_header_extract_difficulty",
   "zisk_header_extract_extra_data",
   "zisk_header_extract_nonce",
   "zisk_header_validate_nonce_zero",
   "zisk_header_validate_difficulty_zero",
   "zisk_validate_header_post_merge_zeros",
   "zisk_chain_validate_post_merge_zeros",
   "zisk_chain_validate_full",
   "zisk_chain_validate_increasing_timestamps",
   "zisk_chain_validate_consecutive_numbers",
   "zisk_chain_compute_total_blob_gas",
   "zisk_header_extract_timestamp",
   "zisk_header_extract_number",
   "zisk_account_validate_code_hash_empty",
   "zisk_account_validate_storage_root_empty",
   "zisk_chain_compute_max_gas_used",
   "zisk_chain_compute_max_blob_gas_used",
   "zisk_chain_compute_min_gas_used",
   "zisk_chain_extract_timestamp_range",
   "zisk_chain_validate_gas_used_under_limit",
   "zisk_header_extract_blob_gas_used",
   "zisk_account_validate_nonce_zero",
   "zisk_chain_compute_min_blob_gas_used",
   "zisk_header_extract_excess_blob_gas",
   "zisk_chain_extract_gas_used_range",
   "zisk_chain_extract_blob_gas_used_range",
   "zisk_chain_extract_basefee_first_last",
   "zisk_chain_compute_total_blob_count",
   "zisk_block_validate_2tx_full",
   "zisk_block_body_extract_2tx",
   "zisk_block_validate_2tx_full_with_body",
   "zisk_block_validate_empty_ommers_hash",
   "zisk_block_validate_no_withdrawals_pair",
   "zisk_block_body_extract_1tx",
   "zisk_block_validate_1tx_full",
   "zisk_block_validate_1tx_full_with_body",
   "zisk_block_validate_empty_receipts_root",
   "zisk_block_validate_empty_block",
   "zisk_validate_empty_block_with_parent",
   "zisk_validate_empty_block_chain",
   "zisk_block_body_extract_tx_count",
   "zisk_block_body_extract_withdrawal_count",
   "zisk_block_body_summary",
   "zisk_block_body_validate_empty",
   "zisk_chain_body_total_tx_count",
   "zisk_chain_body_total_withdrawal_count",
   "zisk_block_logs_bloom_from_receipts_list",
   "zisk_block_validate_logs_bloom",
   "zisk_header_root_is_empty_trie",
   "zisk_calldata_byte_counts",
   "zisk_intrinsic_gas_calldata_floor_eip7623",
   "zisk_init_code_cost",
   "zisk_mpt_nibbles_to_compact",
   "zisk_mpt_compact_to_nibbles",
   "zisk_mpt_node_classify",
   "zisk_mpt_encode_internal_node",
   "zisk_mpt_branch_get_child",
   "zisk_mpt_branch_get_value",
   "zisk_mpt_leaf_extract",
   "zisk_mpt_extension_extract",
   "zisk_mpt_branch_used_count",
   "zisk_mpt_branch_first_used_index",
   "zisk_sha256_from_input",
   "zisk_ssz_pair_hash",
   "zisk_ssz_zero_hashes",
   "zisk_ssz_merkleize_pow2",
   "zisk_ssz_merkleize",
   "zisk_ssz_pack_bytes",
   "zisk_ssz_hash_tree_root_bytes",
   "zisk_ssz_hash_tree_root_list_bytelist",
   "zisk_ssz_hash_tree_root_execution_witness"]

end EvmAsm.Codegen

/-! ## File-size guard

    Hard cap on `Programs.lean` and every sibling under
    `EvmAsm/Codegen/Programs/`, to keep the registry hub and the
    extracted submodules from spiralling. The cap **monotonically
    decreases** as files shrink: every time this guard trips, the
    response is to split AND lower `hardCap` by at least the size
    of the carved-out chunk. The long-term floor is `1500`.

    Established splits so far:
      * PR-#5870 carved `Evm.lean` / `HashBridge.lean` / `Ssz.lean`.
      * PR-#5900 carved `RlpRead.lean` / `Mpt.lean`.
      * This PR carves `Tx.lean` and renames `softCap` → `hardCap`.

    When this guard trips:
      1. Pick a cluster of `*Function` / `zisk*` defs in the
         offending file.
      2. Lift them into a new (or existing) submodule under
         `EvmAsm/Codegen/Programs/`.
      3. Add the submodule to the `paths` list below and to
         `Programs.lean`'s imports.
      4. **Lower `hardCap`** by at least the line-count you just
         removed. Never raise it. The floor is 1500.

    Runs at elaboration time via `#eval`; adds zero runtime cost. -/

#eval show IO Unit from do
  let hardCap := 1957
  let paths := [
    "EvmAsm/Codegen/Programs.lean",
    "EvmAsm/Codegen/Programs/Account.lean",
    "EvmAsm/Codegen/Programs/AccountFields.lean",
    "EvmAsm/Codegen/Programs/Address.lean",
    "EvmAsm/Codegen/Programs/Block.lean",
    "EvmAsm/Codegen/Programs/BlockBody.lean",
    "EvmAsm/Codegen/Programs/BlockRoots.lean",
    "EvmAsm/Codegen/Programs/BlockValidate.lean",
    "EvmAsm/Codegen/Programs/Chain.lean",
    "EvmAsm/Codegen/Programs/Bloom.lean",
    "EvmAsm/Codegen/Programs/Evm.lean",
    "EvmAsm/Codegen/Programs/HashBridge.lean",
    "EvmAsm/Codegen/Programs/Header.lean",
    "EvmAsm/Codegen/Programs/HeaderBaseFee.lean",
    "EvmAsm/Codegen/Programs/HeaderChain.lean",
    "EvmAsm/Codegen/Programs/HeaderFields.lean",
    "EvmAsm/Codegen/Programs/BlockHashPredicates.lean",
    "EvmAsm/Codegen/Programs/HeadersKeccak.lean",
    "EvmAsm/Codegen/Programs/HeaderU64.lean",
    "EvmAsm/Codegen/Programs/Mpt.lean",
    "EvmAsm/Codegen/Programs/MptEncode.lean",
    "EvmAsm/Codegen/Programs/MptInternal.lean",
    "EvmAsm/Codegen/Programs/Receipt.lean",
    "EvmAsm/Codegen/Programs/State.lean",
    "EvmAsm/Codegen/Programs/RlpRead.lean",
    "EvmAsm/Codegen/Programs/Ssz.lean",
    "EvmAsm/Codegen/Programs/Tx.lean",
    "EvmAsm/Codegen/Programs/TxDecode.lean",
    "EvmAsm/Codegen/Programs/TxExtract.lean",
    "EvmAsm/Codegen/Programs/TxSignature.lean",
    "EvmAsm/Codegen/Programs/U256.lean",
    "EvmAsm/Codegen/Programs/Withdrawal.lean"
  ]
  for path in paths do
    let contents ← IO.FS.readFile path
    let lineCount := (contents.splitOn "\n").length
    if lineCount > hardCap then
      throw <| IO.userError <|
        s!"{path} has {lineCount} lines; hard cap is {hardCap}. " ++
        "Extract a helper cluster into a new submodule under " ++
        "EvmAsm/Codegen/Programs/ (see PR #5870 and PR #5900 for the " ++
        "established pattern). Then LOWER `hardCap` in the guard at " ++
        "the bottom of Programs.lean by at least the size of the " ++
        "carved-out chunk -- the cap monotonically decreases toward " ++
        "the 1500-line floor. Never raise it."
