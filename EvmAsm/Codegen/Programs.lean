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
import EvmAsm.Codegen.Programs.Ssz
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.Bloom
import EvmAsm.Codegen.Programs.Block
import EvmAsm.Codegen.Programs.Header
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

/-! ## headers_keccak_chain -- PR-K15 walk an SSZ list section,
    keccak each element, return the last digest + count.

    Walks the SSZ inner-offset table to derive per-element
    bounds (same parsing shape as the SSZ list-merkleize work),
    then calls `zkvm_keccak256(el_i_start, el_i_len, out_ptr)`
    for each element. The output buffer is overwritten on every
    iteration; after the loop, it holds the LAST element's
    digest. Returns the element count `N` in `a0`.

    Calling convention:
      a0 (input)  : SSZ list section ptr (read-only)
      a1 (input)  : section_len (0 ⇒ empty list)
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) : N (element count)
      32 bytes at *a2 : keccak256(element[N-1]) if N > 0, else 0.

    No per-element scratch; works for any N. -/
def headersKeccakChainFunction : String :=
  "headers_keccak_chain:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                  # s0 = section ptr\n" ++
  "  mv s1, a1                  # s1 = section_len\n" ++
  "  mv s2, a2                  # s2 = output ptr\n" ++
  "  beqz s1, .Lhkc_n0          # empty section ⇒ N = 0\n" ++
  "  lwu t0, 0(s0)              # offset_0 = 4 * N\n" ++
  "  srli s3, t0, 2             # s3 = N\n" ++
  "  li s4, 0                   # s4 = i\n" ++
  ".Lhkc_loop:\n" ++
  "  beq s4, s3, .Lhkc_done\n" ++
  "  slli t0, s4, 2             # 4*i\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  add a0, s0, t2             # el_i_start\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lhkc_use_end\n" ++
  "  slli t3, t3, 2             # 4*(i+1)\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # el_i_end\n" ++
  "  j .Lhkc_have_end\n" ++
  ".Lhkc_use_end:\n" ++
  "  add t4, s0, s1             # el_i_end = section_end\n" ++
  ".Lhkc_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  mv a2, s2                  # output (overwritten each iter)\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lhkc_loop\n" ++
  ".Lhkc_n0:\n" ++
  "  sd zero,  0(s2)\n" ++
  "  sd zero,  8(s2)\n" ++
  "  sd zero, 16(s2)\n" ++
  "  sd zero, 24(s2)\n" ++
  "  li s3, 0                   # N = 0\n" ++
  ".Lhkc_done:\n" ++
  "  mv a0, s3                  # return N\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_headers_keccak_chain`: probe BuildUnit that reads an
    SSZ list section from host input and writes the count + last
    digest to OUTPUT.
    Input layout:
      bytes  0.. 8 : section_len (u64)
      bytes  8..   : SSZ list section bytes
    Output layout:
      bytes  0.. 8 : N (u64 LE)
      bytes  8..40 : keccak256(element[N-1]) or 0 if N=0 -/
def ziskHeadersKeccakChainPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # section_len\n" ++
  "  addi a0, a3, 16             # section ptr\n" ++
  "  li a2, 0xa0010008           # last_hash output (OUTPUT + 8)\n" ++
  "  jal ra, headers_keccak_chain\n" ++
  "  li t0, 0xa0010000           # write N at OUTPUT + 0\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhkc_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersKeccakChainFunction ++ "\n" ++
  ".Lhkc_pdone:"

def ziskHeadersKeccakChainDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskHeadersKeccakChainProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeadersKeccakChainPrologue
  dataAsm     := ziskHeadersKeccakChainDataSection
}

/-! ## headers_keccak_array -- PR-K16 walk SSZ list section,
    keccak each element, store every digest in caller table.

    Sibling of `headers_keccak_chain` (PR-K15): same SSZ-list
    parsing loop, but each iteration writes the digest to
    `table[i]` instead of overwriting the same slot. Returns the
    element count `N`.

    Calling convention:
      a0 (input)  : section ptr (read-only)
      a1 (input)  : section_len (0 = empty list)
      a2 (input)  : table base ptr (must hold N*32 bytes)
      ra (input)  : return
      a0 (output) : N (element count)
      32 bytes at *(table + 32*i) = keccak256(element[i])
        for each i in 0..N. -/
def headersKeccakArrayFunction : String :=
  "headers_keccak_array:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                  # s0 = section ptr\n" ++
  "  mv s1, a1                  # s1 = section_len\n" ++
  "  mv s2, a2                  # s2 = table base\n" ++
  "  beqz s1, .Lhka_n0\n" ++
  "  lwu t0, 0(s0)\n" ++
  "  srli s3, t0, 2             # s3 = N\n" ++
  "  li s4, 0                   # s4 = i\n" ++
  ".Lhka_loop:\n" ++
  "  beq s4, s3, .Lhka_done\n" ++
  "  slli t0, s4, 2             # 4*i\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  add a0, s0, t2             # el_i_start\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lhka_use_end\n" ++
  "  slli t3, t3, 2             # 4*(i+1)\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # el_i_end\n" ++
  "  j .Lhka_have_end\n" ++
  ".Lhka_use_end:\n" ++
  "  add t4, s0, s1             # el_i_end = section_end\n" ++
  ".Lhka_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  slli t0, s4, 5             # 32*i\n" ++
  "  add a2, s2, t0             # a2 = &table[i]\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lhka_loop\n" ++
  ".Lhka_n0:\n" ++
  "  li s3, 0\n" ++
  ".Lhka_done:\n" ++
  "  mv a0, s3                  # return N\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_headers_keccak_array`: probe BuildUnit that reads an
    SSZ list section from host input and writes (count, table)
    to OUTPUT, capped at N ≤ 7 to fit ziskemu's 256-byte output
    channel.
    Input layout:
      bytes  0.. 8 : section_len (u64)
      bytes  8..   : SSZ list section bytes
    Output layout:
      bytes  0.. 8     : N (u64 LE)
      bytes  8..8+32*N : N digests of 32 bytes each -/
def ziskHeadersKeccakArrayPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # section_len\n" ++
  "  addi a0, a3, 16             # section ptr\n" ++
  "  li a2, 0xa0010008           # table at OUTPUT + 8\n" ++
  "  jal ra, headers_keccak_array\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # write N at OUTPUT + 0\n" ++
  "  j .Lhka_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersKeccakArrayFunction ++ "\n" ++
  ".Lhka_pdone:"

def ziskHeadersKeccakArrayDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskHeadersKeccakArrayProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeadersKeccakArrayPrologue
  dataAsm     := ziskHeadersKeccakArrayDataSection
}

/-! ## headers_parent_hash -- PR-K17 RLP-walk to extract the
    first 32-byte field of an RLP-encoded Ethereum header
    (`parent_hash`).

    Skips the outer list prefix (0xc0..0xc0+55 short form, 0xf8
    1-byte-length, or 0xf9 2-byte-length forms), expects a
    0xa0 Bytes32 string prefix, then copies the 32 raw bytes
    to the caller's output.

    Calling convention:
      a0 (input)  : RLP-encoded header ptr (read-only)
      a1 (input)  : header byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 on success; 32 bytes at *a2 = parent_hash
        1 on RLP parse failure

    Pure register arithmetic; no scratch memory, no callee-saved
    registers used. Leaf-callable. -/
def headersParentHashFunction : String :=
  "headers_parent_hash:\n" ++
  "  # a0 = header ptr, a1 = header_len, a2 = out ptr\n" ++
  "  lbu t0, 0(a0)                # first byte\n" ++
  "  li t1, 0xc0\n" ++
  "  bltu t0, t1, .Lhph_fail      # not an RLP list (< 0xc0)\n" ++
  "  li t1, 0xf8\n" ++
  "  bltu t0, t1, .Lhph_short     # 0xc0..0xf7 → short list, 1-byte prefix\n" ++
  "  # long list: t0 in [0xf8..0xff].\n" ++
  "  # length_of_length = t0 - 0xf7. Outer prefix = 1 + length_of_length bytes.\n" ++
  "  li t1, 0xf7\n" ++
  "  sub t2, t0, t1               # length_of_length\n" ++
  "  li t3, 2                     # cap: support 0xf8 (LoL=1), 0xf9 (LoL=2)\n" ++
  "  bltu t3, t2, .Lhph_fail      # LoL > 2 → unsupported\n" ++
  "  addi t2, t2, 1               # prefix bytes = LoL + 1\n" ++
  "  add a0, a0, t2               # skip prefix\n" ++
  "  sub a1, a1, t2\n" ++
  "  j .Lhph_after_prefix\n" ++
  ".Lhph_short:\n" ++
  "  addi a0, a0, 1               # skip 1-byte prefix\n" ++
  "  addi a1, a1, -1\n" ++
  ".Lhph_after_prefix:\n" ++
  "  # Expect 0xa0 Bytes32 prefix.\n" ++
  "  li t0, 33\n" ++
  "  bltu a1, t0, .Lhph_fail      # not enough bytes for 0xa0 + 32\n" ++
  "  lbu t1, 0(a0)\n" ++
  "  li t2, 0xa0\n" ++
  "  bne t1, t2, .Lhph_fail       # not a Bytes32 string\n" ++
  "  # Copy 32 bytes from a0+1 to a2.\n" ++
  "  ld t0,  1(a0); sd t0,  0(a2)\n" ++
  "  ld t0,  9(a0); sd t0,  8(a2)\n" ++
  "  ld t0, 17(a0); sd t0, 16(a2)\n" ++
  "  ld t0, 25(a0); sd t0, 24(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lhph_fail:\n" ++
  "  li a0, 1\n" ++
  "  ret"

/-- `zisk_headers_parent_hash`: probe BuildUnit that reads an
    RLP-encoded header from host input and writes
    `(status, parent_hash)` to OUTPUT.
    Input layout:
      bytes  0.. 8 : header_len (u64)
      bytes  8..   : RLP-encoded header bytes
    Output layout:
      bytes  0.. 8 : status (u64 LE; 0 = ok, 1 = parse fail)
      bytes  8..40 : parent_hash (32 bytes; meaningful only on
                     status=0; on failure, contains zeros) -/
def ziskHeadersParentHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  li a2, 0xa0010008           # parent_hash output (OUTPUT + 8)\n" ++
  "  # Pre-zero output[8..40] so a parse failure surfaces as zeros.\n" ++
  "  sd zero,  0(a2); sd zero,  8(a2); sd zero, 16(a2); sd zero, 24(a2)\n" ++
  "  jal ra, headers_parent_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # write status at OUTPUT + 0\n" ++
  "  j .Lhph_pdone\n" ++
  headersParentHashFunction ++ "\n" ++
  ".Lhph_pdone:"

def ziskHeadersParentHashDataSection : String :=
  ".section .data\n" ++
  "hph_scratch:\n" ++
  "  .zero 8"

def ziskHeadersParentHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeadersParentHashPrologue
  dataAsm     := ziskHeadersParentHashDataSection
}

/-! ## header_validate_parent_hash -- PR-K94

    Per-header parent-hash continuity check from `validate_header`
    in `forks/amsterdam/fork.py`:

      block_parent_hash = keccak256(rlp.encode(parent_header))
      if header.parent_hash != block_parent_hash:
          raise InvalidBlock

    The single-pair check that anchors a block to its parent. Used
    by `validate_header` directly; the multi-header walk in
    `validate_headers(headers, parent_header)` consists of K18-style
    pairwise iterations of exactly this primitive (K18 already
    handles the iteration via the SSZ digest table, but expects a
    pre-computed digest array; K94 is the standalone form that
    callers without that pipeline can use).

    Composes:
      - PR-K17 `headers_parent_hash`  — extract this header's
                                        parent_hash field (RLP[0])
      - PR-K3  `zkvm_keccak256`       — Keccak-f[1600] sponge

    Calling convention:
      a0 (input)  : this_header_rlp ptr
      a1 (input)  : this_header_rlp byte length
      a2 (input)  : parent_header_rlp ptr
      a3 (input)  : parent_header_rlp byte length
      ra (input)  : return
      a0 (output) :
        0 : match — parent_hash field == keccak256(parent_rlp)
        1 : RLP parse failure of this_header (field 0 not 32 B)
        2 : mismatch — both decode/hash succeeded, values differ

    Uses 64 bytes of `.data` scratch (`hvph_claimed` 32 B +
    `hvph_computed` 32 B). -/
def headerValidateParentHashFunction : String :=
  "header_validate_parent_hash:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a2                   # parent_rlp ptr (stash)\n" ++
  "  mv s1, a3                   # parent_rlp_len (stash)\n" ++
  "  # Step 1: extract this header's parent_hash (field 0).\n" ++
  "  la a2, hvph_claimed\n" ++
  "  jal ra, headers_parent_hash\n" ++
  "  beqz a0, .Lhvph_hash\n" ++
  "  li a0, 1\n" ++
  "  j .Lhvph_ret\n" ++
  ".Lhvph_hash:\n" ++
  "  # Step 2: keccak256(parent_rlp) → hvph_computed.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, hvph_computed\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # zkvm_keccak256 always returns 0 (ZKVM_EOK).\n" ++
  "  # Step 3: byte-by-byte compare (32 bytes via 4 × dword).\n" ++
  "  la t0, hvph_claimed\n" ++
  "  la t1, hvph_computed\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lhvph_diff\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lhvph_diff\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lhvph_diff\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lhvph_diff\n" ++
  "  li a0, 0\n" ++
  "  j .Lhvph_ret\n" ++
  ".Lhvph_diff:\n" ++
  "  li a0, 2\n" ++
  ".Lhvph_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_validate_parent_hash`: probe BuildUnit. Reads
    (this_len, parent_len, this_bytes ‖ parent_bytes) from host
    input, writes 8-byte status to OUTPUT.
    Input layout:
      bytes  0.. 8 : this_header_len
      bytes  8..16 : parent_header_len
      bytes 16..   : this_header_rlp ‖ parent_header_rlp -/
def ziskHeaderValidateParentHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # this_header_len\n" ++
  "  ld a3, 16(a4)               # parent_header_len\n" ++
  "  addi a0, a4, 24             # this_header_ptr\n" ++
  "  add a2, a0, a1              # parent_header_ptr\n" ++
  "  jal ra, header_validate_parent_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lhvph_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersParentHashFunction ++ "\n" ++
  headerValidateParentHashFunction ++ "\n" ++
  ".Lhvph_pdone:"

def ziskHeaderValidateParentHashDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "hvph_claimed:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "hvph_computed:\n" ++
  "  .zero 32"

def ziskHeaderValidateParentHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderValidateParentHashPrologue
  dataAsm     := ziskHeaderValidateParentHashDataSection
}

/-! ## header_chain_walk_step -- PR-K96

    Per-step primitive for chain validation: given the previous
    block's hash and a candidate child header's RLP, verify
    `child.parent_hash == previous_hash` and compute
    `keccak256(child_rlp)` as the new running hash.

    A caller iterating over N headers does N calls; at the end
    `*new_hash` holds the latest block's hash, and any mid-chain
    mismatch returns status 2.

    PR-K18 `headers_validate_chain` already implements the chain
    walk on top of a pre-computed SSZ digest table; K96 is the
    standalone per-step that works without that pipeline (raw
    RLP-encoded headers in, no precomputed digest array required).

    Composes:
      - PR-K17 `headers_parent_hash` — extract child's parent_hash
      - PR-K3  `zkvm_keccak256`      — compute child's hash

    Calling convention:
      a0 (input)  : prev_hash ptr (32 B, caller-supplied)
      a1 (input)  : child_header_rlp ptr
      a2 (input)  : child_header_rlp byte length
      a3 (input)  : 32-byte out ptr (receives child's hash on
                    success, zeros on failure)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : child header parse failed (field 0 not 32 B)
        2 : mismatch — child.parent_hash != prev_hash

    Uses 32 bytes of `.data` scratch (`hcws_claimed`). -/
def headerChainWalkStepFunction : String :=
  "header_chain_walk_step:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # prev_hash ptr\n" ++
  "  mv s1, a1                   # child_rlp ptr\n" ++
  "  mv s2, a2                   # child_len\n" ++
  "  mv s3, a3                   # out ptr\n" ++
  "  # Step 1: extract child's parent_hash → hcws_claimed.\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  la a2, hcws_claimed\n" ++
  "  jal ra, headers_parent_hash\n" ++
  "  beqz a0, .Lhcws_compare\n" ++
  "  li a0, 1\n" ++
  "  j .Lhcws_zero_out\n" ++
  ".Lhcws_compare:\n" ++
  "  # Compare prev_hash (s0) to claimed (hcws_claimed) byte-by-byte.\n" ++
  "  la t0, hcws_claimed\n" ++
  "  ld t1,  0(s0); ld t2,  0(t0); bne t1, t2, .Lhcws_diff\n" ++
  "  ld t1,  8(s0); ld t2,  8(t0); bne t1, t2, .Lhcws_diff\n" ++
  "  ld t1, 16(s0); ld t2, 16(t0); bne t1, t2, .Lhcws_diff\n" ++
  "  ld t1, 24(s0); ld t2, 24(t0); bne t1, t2, .Lhcws_diff\n" ++
  "  # Match — compute child hash → *out.\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  j .Lhcws_ret\n" ++
  ".Lhcws_diff:\n" ++
  "  li a0, 2\n" ++
  ".Lhcws_zero_out:\n" ++
  "  # Zero the output on any failure.\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  ".Lhcws_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_header_chain_walk_step`: probe BuildUnit. Reads
    (child_len, prev_hash[32], child_rlp) from host input, writes
    (status, child_hash[32]) to OUTPUT.
    Input layout:
      bytes  0.. 8 : child_header_len
      bytes  8..40 : prev_hash (32 B)
      bytes 40..   : child_header_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..40 : child block hash on success, zero otherwise -/
def ziskHeaderChainWalkStepPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a2, 8(a4)                # child_header_len\n" ++
  "  addi a0, a4, 16             # prev_hash ptr\n" ++
  "  addi a1, a4, 48             # child_rlp ptr\n" ++
  "  li a3, 0xa0010008           # child_hash output (OUTPUT + 8)\n" ++
  "  jal ra, header_chain_walk_step\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lhcws_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersParentHashFunction ++ "\n" ++
  headerChainWalkStepFunction ++ "\n" ++
  ".Lhcws_pdone:"

def ziskHeaderChainWalkStepDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "hcws_claimed:\n" ++
  "  .zero 32"

def ziskHeaderChainWalkStepProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderChainWalkStepPrologue
  dataAsm     := ziskHeaderChainWalkStepDataSection
}

/-! ## K99 / K126 / K127 address-derivation cluster — moved to `Programs/Address.lean` (file-size hard cap). -/
/-! ## K100 mpt_account_path_nibbles — moved to `Programs/Mpt.lean` (file-size hard cap). -/


/-! ## headers_validate_chain -- PR-K18 parent_hash chain check

    Composes PR-K16 `headers_keccak_array` (build per-header
    digest table) with PR-K17 `headers_parent_hash` (RLP-extract
    each header's first 32-byte field) to verify the
    `validate_headers` invariant:

        header[i].parent_hash == keccak256(header[i-1])
            for every i in 1..N

    matches the Python check in
    `execution-specs/.../stateless.py::validate_headers`.

    Calling convention:
      a0 (input)  : SSZ list section ptr (witness.headers)
      a1 (input)  : section_len (0 = empty list)
      a2 (input)  : 8-byte output ptr (receives N as u64 LE)
      ra (input)  : return
      a0 (output) : 0 on success (chain valid) or N ≤ 1
                    1 on mismatch / RLP-decode failure

    Walks the list using the same SSZ inner-offset table as
    PR-K15/K16. Caps at N ≤ 256 (matches `MAX_WITNESS_HEADERS`).

    Uses two `.data` scratch buffers:
      vh_keccak_table          : 256 × 32 = 8 KB
      vh_extracted_parent_hash : 32 B
-/
def headersValidateChainFunction : String :=
  "headers_validate_chain:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                  # s0 = section ptr\n" ++
  "  mv s1, a1                  # s1 = section_len\n" ++
  "  mv s2, a2                  # s2 = N out ptr\n" ++
  "  # Step 1: keccak each header into vh_keccak_table.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, vh_keccak_table\n" ++
  "  jal ra, headers_keccak_array\n" ++
  "  mv s3, a0                  # s3 = N\n" ++
  "  sd s3, 0(s2)               # *N_out = N\n" ++
  "  # If N ≤ 1, no chain links to check → ok.\n" ++
  "  li t0, 2\n" ++
  "  bltu s3, t0, .Lvh_ok\n" ++
  "  # Loop i = 1..N.\n" ++
  "  li s4, 1\n" ++
  ".Lvh_loop:\n" ++
  "  beq s4, s3, .Lvh_ok\n" ++
  "  # Find element i bounds from inner-offset table.\n" ++
  "  slli t0, s4, 2             # 4*i\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  add a0, s0, t2             # el_i_start\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lvh_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4\n" ++
  "  j .Lvh_have_end\n" ++
  ".Lvh_use_end:\n" ++
  "  add t4, s0, s1\n" ++
  ".Lvh_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  la a2, vh_extracted_parent_hash\n" ++
  "  jal ra, headers_parent_hash\n" ++
  "  bnez a0, .Lvh_fail         # RLP parse failed\n" ++
  "  # Compare extracted parent_hash against vh_keccak_table[i-1].\n" ++
  "  la t0, vh_keccak_table\n" ++
  "  addi t1, s4, -1\n" ++
  "  slli t1, t1, 5             # (i-1) * 32\n" ++
  "  add t0, t0, t1             # &table[i-1]\n" ++
  "  la t1, vh_extracted_parent_hash\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lvh_fail\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lvh_fail\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lvh_fail\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lvh_fail\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lvh_loop\n" ++
  ".Lvh_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Lvh_ret\n" ++
  ".Lvh_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lvh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_headers_validate_chain`: probe BuildUnit that reads an
    SSZ list of RLP-encoded headers from host input and writes
    (status, N) to OUTPUT.
    Input layout:
      bytes  0.. 8 : section_len (u64)
      bytes  8..   : SSZ list section bytes
    Output layout:
      bytes  0.. 8 : status (u64 LE; 0 ok / 1 mismatch)
      bytes  8..16 : N (u64 LE; element count) -/
def ziskHeadersValidateChainPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # section_len\n" ++
  "  addi a0, a3, 16             # section ptr\n" ++
  "  li a2, 0xa0010008           # N out ptr (OUTPUT + 8)\n" ++
  "  jal ra, headers_validate_chain\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Lvh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersKeccakArrayFunction ++ "\n" ++
  headersParentHashFunction ++ "\n" ++
  headersValidateChainFunction ++ "\n" ++
  ".Lvh_pdone:"

def ziskHeadersValidateChainDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "vh_keccak_table:\n" ++
  "  .zero 8192                 # 256 × 32-byte digests\n" ++
  ".balign 32\n" ++
  "vh_extracted_parent_hash:\n" ++
  "  .zero 32"

def ziskHeadersValidateChainProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeadersValidateChainPrologue
  dataAsm     := ziskHeadersValidateChainDataSection
}

/-! ## K19 witness_lookup_by_hash — moved to `Programs/Mpt.lean` (file-size hard cap). -/

/-! ## account_validate_code_hash -- PR-K98

    Verify that an account's `code_hash` field matches the
    keccak256 of a claimed bytecode buffer:

      account.code_hash == keccak256(claimed_code)

    Used during witness validation to assert that the contract
    code supplied by the host matches the `code_hash` committed in
    the account trie leaf. EOAs (no contract) carry the canonical
    empty-code hash `EMPTY_CODE_HASH`:

      keccak256(b'') ==
        0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

    A `claimed_code_len == 0` reproduces this exact value.

    Composes:
      - PR-K20 `rlp_list_nth_item` — extract field 3 (code_hash)
      - PR-K3  `zkvm_keccak256`    — compute claimed digest

    Account RLP layout (4 items):
      field 0 : nonce        (uint)
      field 1 : balance      (uint)
      field 2 : storage_root (32-byte string)
      field 3 : code_hash    (32-byte string)

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : claimed_code ptr (may be unused when len == 0)
      a3 (input)  : claimed_code byte length
      ra (input)  : return
      a0 (output) :
        0 : match
        1 : account RLP parse failure (field 3 not 32 B)
        2 : mismatch — both succeeded, digests differ

    Uses 64 bytes of `.data` scratch (`avch_claimed` 32 B +
    `avch_computed` 32 B), plus K20's offset/length slots. -/
def accountValidateCodeHashFunction : String :=
  "account_validate_code_hash:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s2, a0                   # account_ptr (stash)\n" ++
  "  mv s3, a1                   # account_len (stash)\n" ++
  "  mv s0, a2                   # claimed_code ptr\n" ++
  "  mv s1, a3                   # claimed_code_len\n" ++
  "  # Step 1: extract account.code_hash (field 3, 32 B).\n" ++
  "  mv a0, s2\n" ++
  "  mv a1, s3\n" ++
  "  li a2, 3\n" ++
  "  la a3, avch_offset\n" ++
  "  la a4, avch_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lavch_fail\n" ++
  "  la t0, avch_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lavch_fail\n" ++
  "  # Copy 32 bytes from (account_ptr + offset) to avch_claimed.\n" ++
  "  la t0, avch_offset; ld t4, 0(t0)\n" ++
  "  add t3, s2, t4\n" ++
  "  la t5, avch_claimed\n" ++
  "  ld t0,  0(t3); sd t0,  0(t5)\n" ++
  "  ld t0,  8(t3); sd t0,  8(t5)\n" ++
  "  ld t0, 16(t3); sd t0, 16(t5)\n" ++
  "  ld t0, 24(t3); sd t0, 24(t5)\n" ++
  "  # Step 2: keccak256(claimed_code) → avch_computed.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, avch_computed\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # Step 3: compare avch_claimed vs avch_computed.\n" ++
  "  la t0, avch_claimed\n" ++
  "  la t1, avch_computed\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lavch_diff\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lavch_diff\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lavch_diff\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lavch_diff\n" ++
  "  li a0, 0\n" ++
  "  j .Lavch_ret\n" ++
  ".Lavch_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lavch_ret\n" ++
  ".Lavch_diff:\n" ++
  "  li a0, 2\n" ++
  ".Lavch_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_account_validate_code_hash`: probe BuildUnit. Reads
    (account_len, code_len, account_rlp ‖ code_bytes) from host
    input, writes 8-byte status to OUTPUT.
    Input layout:
      bytes  0.. 8 : account_rlp_len
      bytes  8..16 : code_len
      bytes 16..   : account_rlp ‖ code_bytes -/
def ziskAccountValidateCodeHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # account_rlp_len\n" ++
  "  ld a3, 16(a4)               # code_len\n" ++
  "  addi a0, a4, 24             # account_rlp_ptr\n" ++
  "  add a2, a0, a1              # code_ptr = account_ptr + account_len\n" ++
  "  jal ra, account_validate_code_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lavch_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountValidateCodeHashFunction ++ "\n" ++
  ".Lavch_pdone:"

def ziskAccountValidateCodeHashDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "avch_offset:\n" ++
  "  .zero 8\n" ++
  "avch_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "avch_claimed:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "avch_computed:\n" ++
  "  .zero 32"

def ziskAccountValidateCodeHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountValidateCodeHashPrologue
  dataAsm     := ziskAccountValidateCodeHashDataSection
}

/-! ## account_storage_root_eq -- PR-K134

    Generic equality check on an account's `storage_root` field:
    does it equal the 32-byte hash passed in as `expected`?

    Used during witness validation to assert that the storage trie
    pointed at by an account matches a claimed root (e.g., the
    pre-state root in a stateless witness's account proof). The
    narrower PR-K133 `account_storage_root_is_empty` is the
    specialization where the expected value is `EMPTY_TRIE_ROOT`.

    Composes:
      - PR-K20 `rlp_list_nth_item` — field 2 bounds

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : expected_root ptr (32 bytes)      a3 (input)  : u64 out ptr (1 if equal, 0 if not)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written
        1 : RLP parse failure / field 2 missing
        2 : field 2 length != 32 -/
def accountStorageRootEqFunction : String :=
  "account_storage_root_eq:\n" ++  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # account_ptr\n" ++
  "  mv s1, a1                   # account_len\n" ++
  "  mv s2, a2                   # expected_root ptr\n" ++
  "  mv s3, a3                   # u64 out ptr\n" ++
  "  sd zero, 0(s3)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  la a3, asre_offset; la a4, asre_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lasre_parse_fail\n" ++
  "  la t0, asre_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lasre_size_fail\n" ++
  "  la t0, asre_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  ld t5,  0(t3); ld t6,  0(s2); bne t5, t6, .Lasre_neq\n" ++
  "  ld t5,  8(t3); ld t6,  8(s2); bne t5, t6, .Lasre_neq\n" ++
  "  ld t5, 16(t3); ld t6, 16(s2); bne t5, t6, .Lasre_neq\n" ++
  "  ld t5, 24(t3); ld t6, 24(s2); bne t5, t6, .Lasre_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lasre_ret\n" ++
  ".Lasre_neq:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lasre_ret\n" ++
  ".Lasre_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lasre_ret\n" ++
  ".Lasre_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lasre_ret:\n" ++  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_account_storage_root_eq`: probe BuildUnit. Reads
    (account_len, expected_root[32], account_bytes), writes
    (status, is_equal) to OUTPUT (16 bytes total).
    Input layout:
      bytes  0.. 8 : account_len
      bytes  8..40 : expected_root (32 bytes)
      bytes 40..   : account_rlp -/
def ziskAccountStorageRootEqPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # account_rlp_len\n" ++
  "  addi a2, a4, 16             # expected_root ptr\n" ++
  "  addi a0, a4, 48             # account_rlp ptr\n" ++
  "  li a3, 0xa0010008           # is_equal out\n" ++
  "  jal ra, account_storage_root_eq\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lasre_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountStorageRootEqFunction ++ "\n" ++
  ".Lasre_pdone:"

def ziskAccountStorageRootEqDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "asre_offset:\n" ++
  "  .zero 8\n" ++
  "asre_length:\n" ++
  "  .zero 8"

def ziskAccountStorageRootEqProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountStorageRootEqPrologue
  dataAsm     := ziskAccountStorageRootEqDataSection
}



/-! ## account_code_hash_eq -- PR-K135

    Generic equality check on an account's `code_hash` field:
    does it equal the 32-byte hash passed in as `expected`?

    PR-K98 `account_validate_code_hash` *computes* the expected
    digest from a bytecode buffer; K135 simply *compares* against
    a caller-supplied digest. Use K98 when the bytecode is known
    locally and we need an integrity check; use K135 when the
    expected hash is already in hand (e.g., from a code-DB lookup
    in a stateless witness, where the bytecode lives elsewhere).

    Companion to PR-K131 `account_has_empty_code` (the specialised
    EMPTY_CODE_HASH variant) and PR-K134
    `account_storage_root_eq` (the storage-side equivalent).

    Composes:
      - PR-K20 `rlp_list_nth_item` — field 3 bounds

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : expected_hash ptr (32 bytes)      a3 (input)  : u64 out ptr (1 if equal, 0 if not)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written
        1 : RLP parse failure / field 3 missing
        2 : field 3 length != 32 -/
def accountCodeHashEqFunction : String :=
  "account_code_hash_eq:\n" ++  "  addi sp, sp, -48\n" ++  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # account_ptr\n" ++
  "  mv s1, a1                   # account_len\n" ++
  "  mv s2, a2                   # expected_hash ptr\n" ++
  "  mv s3, a3                   # u64 out ptr\n" ++
  "  sd zero, 0(s3)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  la a3, ache_offset; la a4, ache_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lache_parse_fail\n" ++
  "  la t0, ache_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lache_size_fail\n" ++
  "  la t0, ache_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  ld t5,  0(t3); ld t6,  0(s2); bne t5, t6, .Lache_neq\n" ++
  "  ld t5,  8(t3); ld t6,  8(s2); bne t5, t6, .Lache_neq\n" ++
  "  ld t5, 16(t3); ld t6, 16(s2); bne t5, t6, .Lache_neq\n" ++
  "  ld t5, 24(t3); ld t6, 24(s2); bne t5, t6, .Lache_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lache_ret\n" ++
  ".Lache_neq:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lache_ret\n" ++
  ".Lache_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lache_ret\n" ++
  ".Lache_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lache_ret:\n" ++  "  ld ra,  0(sp)\n" ++  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_account_code_hash_eq`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : account_rlp_len
      bytes  8..40 : expected_hash (32 bytes)
      bytes 40..   : account_rlp -/
def ziskAccountCodeHashEqPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # account_rlp_len\n" ++
  "  addi a2, a4, 16             # expected_hash ptr\n" ++
  "  addi a0, a4, 48             # account_rlp ptr\n" ++
  "  li a3, 0xa0010008           # is_equal out\n" ++
  "  jal ra, account_code_hash_eq\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lache_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountCodeHashEqFunction ++ "\n" ++
  ".Lache_pdone:"

def ziskAccountCodeHashEqDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ache_offset:\n" ++
  "  .zero 8\n" ++
  "ache_length:\n" ++
  "  .zero 8"

def ziskAccountCodeHashEqProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountCodeHashEqPrologue
  dataAsm     := ziskAccountCodeHashEqDataSection
}

/-! ## account_nonce_eq -- PR-K136

    Narrow equality predicate on an account's `nonce` field:
    does `RLP-decoded(account.nonce) == expected_nonce` ?

    Field 0 of `[nonce, balance, storage_root, code_hash]` is the
    RLP-canonical big-endian encoding of the account nonce. EOA
    nonces fit comfortably in u64 — the RLP-canonical encoding
    omits leading zeros, so the encoded length is in `0..8` for any
    realistic account. K27 `account_decode` already big-endian-
    decodes this field to a u64 as part of full-record extraction;
    K136 is the narrower accessor for callers that only need the
    equality check and don't want to allocate the 96-byte struct.

    Used by:
      * sender-validation in `check_transaction` (asserts
        `tx.nonce == account.nonce` before charging gas)
      * EIP-7702 authorization-list checks
        (`authorization.nonce == account.nonce`)
      * post-tx state validation (asserts the post-state account
        has the bumped nonce)

    Composes:
      - PR-K20 `rlp_list_nth_item` — field 0 bounds

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : expected_nonce (u64, native)      a3 (input)  : u64 out ptr (1 if equal, 0 if not)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written
        1 : RLP parse failure / field 0 missing / nonce > 8 bytes -/
def accountNonceEqFunction : String :=
  "account_nonce_eq:\n" ++  "  addi sp, sp, -48\n" ++  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # account_ptr\n" ++
  "  mv s1, a1                   # account_len\n" ++
  "  mv s2, a2                   # expected_nonce\n" ++
  "  mv s3, a3                   # is_equal out\n" ++
  "  sd zero, 0(s3)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0\n" ++
  "  la a3, ane_offset; la a4, ane_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lane_fail\n" ++
  "  la t0, ane_length; ld t1, 0(t0)\n" ++
  "  li t2, 8\n" ++
  "  bgtu t1, t2, .Lane_fail      # nonce > 8 bytes\n" ++
  "  la t0, ane_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  li t2, 0                    # u64 accumulator\n" ++
  ".Lane_loop:\n" ++
  "  beqz t1, .Lane_done\n" ++
  "  slli t2, t2, 8\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  or t2, t2, t4\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lane_loop\n" ++
  ".Lane_done:\n" ++
  "  bne t2, s2, .Lane_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lane_ret\n" ++
  ".Lane_neq:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lane_ret\n" ++
  ".Lane_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lane_ret:\n" ++  "  ld ra,  0(sp)\n" ++  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_account_nonce_eq`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : account_rlp_len
      bytes  8..16 : expected_nonce (u64 LE)
      bytes 16..   : account_rlp -/
def ziskAccountNonceEqPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # account_rlp_len\n" ++
  "  ld a2, 16(a4)               # expected_nonce\n" ++
  "  addi a0, a4, 24             # account_rlp ptr\n" ++
  "  li a3, 0xa0010008           # is_equal out\n" ++
  "  jal ra, account_nonce_eq\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lane_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountNonceEqFunction ++ "\n" ++
  ".Lane_pdone:"

def ziskAccountNonceEqDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ane_offset:\n" ++
  "  .zero 8\n" ++
  "ane_length:\n" ++
  "  .zero 8"

def ziskAccountNonceEqProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountNonceEqPrologue
  dataAsm     := ziskAccountNonceEqDataSection}
/-! ## account_is_eip161_empty -- PR-K137

    EIP-161 empty-account predicate:

      is_empty ⇐ nonce == 0
              ∧  balance == 0
              ∧  code_hash == EMPTY_CODE_HASH

    where

      EMPTY_CODE_HASH =
        0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

    Drives EIP-161 deletion: an account that satisfies this
    predicate after a transaction is removed from the state trie
    (i.e., its slot in the state MPT is deleted, not retained
    with a zero-balance leaf). Also used by:
      * SELFDESTRUCT recipient handling (re-creation of an empty
        beneficiary)
      * fee-charging paths in apply_body that decide whether the
        sender account becomes empty post-tx and so must be
        removed from the trie.

    Strict reading of the EIP-161 spec compares Uint values, not
    RLP-canonical byte patterns. We therefore accept both
    canonical empty-byte and non-canonical zero-byte encodings:
      * nonce: length ≤ 8, BE-decoded value == 0
      * balance: length ≤ 32, all bytes == 0 (cheaper than full
        32-byte decode + compare)
      * code_hash: length == 32, bytes match EMPTY_CODE_HASH

    Companions:
      - PR-K131 `account_has_empty_code` (only the code_hash side)
      - PR-K133 `account_storage_root_is_empty`
      - PR-K136 `account_nonce_eq` (specialised to expected==0
        when caller knows the strict predicate)

    Composes:
      - PR-K20 `rlp_list_nth_item` — field 0/1/3 bounds

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : u64 out ptr (1 if empty, 0 if not)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written
        1 : RLP parse failure / nonce > 8 bytes / balance > 32 bytes
        2 : code_hash field length != 32 -/
def accountIsEip161EmptyFunction : String :=
  "account_is_eip161_empty:\n" ++
  "  addi sp, sp, -40\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # account_ptr\n" ++
  "  mv s1, a1                   # account_len\n" ++
  "  mv s2, a2                   # is_empty out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # ---- Field 0: nonce ---- BE-decode and check == 0\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0\n" ++
  "  la a3, aie_offset; la a4, aie_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Laie_fail\n" ++
  "  la t0, aie_length; ld t1, 0(t0)\n" ++
  "  li t2, 8\n" ++
  "  bgtu t1, t2, .Laie_fail      # nonce > 8 bytes\n" ++
  "  la t0, aie_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  li t2, 0\n" ++
  ".Laie_nloop:\n" ++
  "  beqz t1, .Laie_ndone\n" ++
  "  slli t2, t2, 8\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  or t2, t2, t4\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Laie_nloop\n" ++
  ".Laie_ndone:\n" ++
  "  bnez t2, .Laie_not_empty     # nonce != 0\n" ++
  "  # ---- Field 1: balance ---- check all bytes == 0\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  la a3, aie_offset; la a4, aie_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Laie_fail\n" ++
  "  la t0, aie_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bgtu t1, t2, .Laie_fail      # balance > 32 bytes\n" ++
  "  la t0, aie_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  ".Laie_bloop:\n" ++
  "  beqz t1, .Laie_bdone\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  bnez t4, .Laie_not_empty     # balance non-zero byte\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Laie_bloop\n" ++
  ".Laie_bdone:\n" ++
  "  # ---- Field 3: code_hash ---- length == 32 and bytes match\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  la a3, aie_offset; la a4, aie_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Laie_fail\n" ++
  "  la t0, aie_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Laie_sizefail\n" ++
  "  la t0, aie_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  la t6, aie_empty_code_hash\n" ++
  "  ld t5,  0(t3); ld t4,  0(t6); bne t5, t4, .Laie_not_empty\n" ++
  "  ld t5,  8(t3); ld t4,  8(t6); bne t5, t4, .Laie_not_empty\n" ++
  "  ld t5, 16(t3); ld t4, 16(t6); bne t5, t4, .Laie_not_empty\n" ++
  "  ld t5, 24(t3); ld t4, 24(t6); bne t5, t4, .Laie_not_empty\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Laie_ret\n" ++
  ".Laie_not_empty:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Laie_ret\n" ++
  ".Laie_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Laie_ret\n" ++
  ".Laie_sizefail:\n" ++
  "  li a0, 2\n" ++
  ".Laie_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 40\n" ++
  "  ret"

/-- `zisk_account_is_eip161_empty`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : account_rlp_len
      bytes  8..   : account_rlp -/
def ziskAccountIsEip161EmptyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # account_rlp_len\n" ++
  "  addi a0, a4, 16             # account_rlp ptr\n" ++
  "  li a2, 0xa0010008           # is_empty out\n" ++
  "  jal ra, account_is_eip161_empty\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Laie_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountIsEip161EmptyFunction ++ "\n" ++
  ".Laie_pdone:"

def ziskAccountIsEip161EmptyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "aie_offset:\n" ++
  "  .zero 8\n" ++
  "aie_length:\n" ++
  "  .zero 8\n" ++
  "aie_empty_code_hash:\n" ++
  "  .byte 0xc5,0xd2,0x46,0x01,0x86,0xf7,0x23,0x3c\n" ++
  "  .byte 0x92,0x7e,0x7d,0xb2,0xdc,0xc7,0x03,0xc0\n" ++
  "  .byte 0xe5,0x00,0xb6,0x53,0xca,0x82,0x27,0x3b\n" ++
  "  .byte 0x7b,0xfa,0xd8,0x04,0x5d,0x85,0xa4,0x70"

def ziskAccountIsEip161EmptyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountIsEip161EmptyPrologue
  dataAsm     := ziskAccountIsEip161EmptyDataSection
}

/-! ## account_extract_storage_root -- PR-K119

    Extract the 32-byte `storage_root` field (RLP field 2) from a
    fully RLP-encoded Ethereum account:

      account = [nonce, balance, storage_root, code_hash]

    The storage_root is the MPT root of this account's per-account
    storage trie (keccak256 of the empty trie's RLP encoding,
    a.k.a. `EMPTY_TRIE_ROOT`, for EOAs and unused contracts):

      EMPTY_TRIE_ROOT =
        0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421

    Direct input to per-account storage trie walks
    (`mpt_lookup_by_key` for SLOAD) and to state-root recomputation
    after SSTORE writes.

    K27 `account_decode` already extracts the full account record;
    K119 is the narrower accessor for callers that only need the
    storage root and don't want to allocate the 96-byte struct.

    Composes:
      - PR-K20 `rlp_list_nth_item` — field 2 bounds

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 2 missing
        2 : field 2 length != 32

    Output zeroed on failure. Uses two 8-byte `.data` scratch slots
    (`aesr_offset`, `aesr_length`). -/
/-! ## account_extract_code_hash -- PR-K122

    Extract the 32-byte `code_hash` field (RLP field 3) from a
    fully RLP-encoded Ethereum account:

      account = [nonce, balance, storage_root, code_hash]

    The storage_root is the MPT root of this account's per-account
    storage trie (keccak256 of the empty trie's RLP encoding,
    a.k.a. `EMPTY_TRIE_ROOT`, for EOAs and unused contracts):

      EMPTY_TRIE_ROOT =
        0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421

    Direct input to per-account storage trie walks
    (`mpt_lookup_by_key` for SLOAD) and to state-root recomputation
    after SSTORE writes.

    K27 `account_decode` already extracts the full account record;
    K119 is the narrower accessor for callers that only need the
    storage root and don't want to allocate the 96-byte struct.

    Composes:
      - PR-K20 `rlp_list_nth_item` — field 2 bounds
    The code_hash is the keccak256 of this account's bytecode.
    For EOAs and accounts that have never been touched as
    contracts, code_hash equals the canonical empty-code hash:

      EMPTY_CODE_HASH =
        0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

    Direct input to:
    - EOA detection (compare against EMPTY_CODE_HASH)
    - EXTCODEHASH opcode evaluation
    - Per-account contract-code lookup (use code_hash as DB key)

    K98 `account_validate_code_hash` *verifies* this field against
    a claimed bytecode buffer (computing the keccak256 inline);
    K122 simply *returns* it. Use K98 when the bytecode is known
    and we want a yes/no integrity check; use K122 when we want to
    keep the hash for later use (e.g. as a code-DB index key).

    Completes the per-field accessor set for accounts (alongside
    PR-K119 storage_root, K120 balance, K121 nonce).

    Composes:
      - PR-K20 `rlp_list_nth_item` — field 3 bounds

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 2 missing
        2 : field 2 length != 32

    Output zeroed on failure. Uses two 8-byte `.data` scratch slots
    (`aesr_offset`, `aesr_length`). -/
def accountExtractStorageRootFunction : String :=
  "account_extract_storage_root:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # account_rlp ptr\n" ++
  "  mv s1, a1                   # account_len\n" ++
  "  mv s2, a2                   # 32B output ptr\n" ++
  "  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)\n" ++
  "  # Extract field 2 (storage_root).\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  la a3, aesr_offset; la a4, aesr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Laesr_parse_fail\n" ++
  "  la t0, aesr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Laesr_size_fail\n" ++
  "  la t0, aesr_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Laesr_ret\n" ++
  ".Laesr_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Laesr_ret\n" ++
  ".Laesr_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Laesr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

def accountExtractCodeHashFunction : String :=
  "account_extract_code_hash:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # account_rlp ptr\n" ++
  "  mv s1, a1                   # account_len\n" ++
  "  mv s2, a2                   # 32B output ptr\n" ++
  "  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)\n" ++
  "  # Extract field 2 (storage_root).\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  la a3, aesr_offset; la a4, aesr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Laesr_parse_fail\n" ++
  "  la t0, aesr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Laesr_size_fail\n" ++
  "  la t0, aesr_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  # Extract field 3 (code_hash).\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  la a3, aech_offset; la a4, aech_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Laech_parse_fail\n" ++
  "  la t0, aech_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Laech_size_fail\n" ++
  "  la t0, aech_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Laesr_ret\n" ++
  ".Laesr_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Laesr_ret\n" ++
  ".Laesr_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Laesr_ret:\n" ++
  "  j .Laech_ret\n" ++
  ".Laech_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Laech_ret\n" ++
  ".Laech_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Laech_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_account_extract_storage_root`: probe BuildUnit. Reads
    (account_len, account_bytes), writes (status, 32-byte
    storage_root) to OUTPUT (40 bytes total). -/
def ziskAccountExtractStorageRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # account_rlp_len\n" ++
  "  addi a0, a3, 16             # account_rlp ptr\n" ++
  "  li a2, 0xa0010008           # 32B output\n" ++
  "  jal ra, account_extract_storage_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Laesr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountExtractStorageRootFunction ++ "\n" ++
  ".Laesr_pdone:"

def ziskAccountExtractStorageRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "aesr_offset:\n" ++
  "  .zero 8\n" ++
  "aesr_length:\n" ++
  "  .zero 8"

def ziskAccountExtractStorageRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountExtractStorageRootPrologue
  dataAsm     := ziskAccountExtractStorageRootDataSection
}

/-- `zisk_account_extract_code_hash`: probe BuildUnit. Reads
    (account_len, account_bytes), writes (status, 32-byte
    code_hash) to OUTPUT (40 bytes). -/
def ziskAccountExtractCodeHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # account_rlp_len\n" ++
  "  addi a0, a3, 16             # account_rlp ptr\n" ++
  "  li a2, 0xa0010008           # 32B output\n" ++
  "  jal ra, account_extract_code_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Laech_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountExtractCodeHashFunction ++ "\n" ++
  ".Laech_pdone:"

def ziskAccountExtractCodeHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "aech_offset:\n" ++
  "  .zero 8\n" ++
  "aech_length:\n" ++
  "  .zero 8"

def ziskAccountExtractCodeHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountExtractCodeHashPrologue
  dataAsm     := ziskAccountExtractCodeHashDataSection
}

/-! ## account_has_empty_code -- PR-K131

    Predicate: does this account's `code_hash` field equal
    `EMPTY_CODE_HASH = keccak256(b'')`?

      EMPTY_CODE_HASH =
        0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

    A `true` result means the account has no associated bytecode
    — i.e., it is an EOA (or an unfilled contract slot). Distinct
    from PR-K123 `account_is_empty`, which additionally requires
    `nonce == 0` and `balance == 0` per EIP-161.

    Used by:
    - CALL / DELEGATECALL / STATICCALL paths to detect EOA targets
      (no code → no execution, refund or fall-through)
    - EXTCODECOPY / EXTCODESIZE fast paths
    - state-tracker bookkeeping (touch behaviour differs for
      empty-code accounts)

    Composes:
      - PR-K20 `rlp_list_nth_item` — field 3 bounds

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : u64 out ptr (1 if EOA, 0 if contract)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written
        1 : RLP parse failure / field 3 missing
        2 : field 3 length != 32 -/
def accountHasEmptyCodeFunction : String :=
  "account_has_empty_code:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # account_ptr\n" ++
  "  mv s1, a1                   # account_len\n" ++
  "  mv s2, a2                   # u64 out ptr\n" ++
  "  sd zero, 0(s2)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  la a3, ahec_offset; la a4, ahec_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lahec_parse_fail\n" ++
  "  la t0, ahec_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lahec_size_fail\n" ++
  "  la t0, ahec_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  la t4, ahec_empty_code_hash\n" ++
  "  ld t5,  0(t3); ld t6,  0(t4); bne t5, t6, .Lahec_neq\n" ++
  "  ld t5,  8(t3); ld t6,  8(t4); bne t5, t6, .Lahec_neq\n" ++
  "  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Lahec_neq\n" ++
  "  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Lahec_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lahec_ret\n" ++
  ".Lahec_neq:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lahec_ret\n" ++
  ".Lahec_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lahec_ret\n" ++
  ".Lahec_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lahec_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"
/-! ## rlp_list_count_items -- PR-K47
    The function body now lives in `EvmAsm/Codegen/Programs/RlpRead.lean`
    (see PR #5900). Only the zisk probe BuildUnit remains here. -/

/-- `zisk_account_has_empty_code`: probe BuildUnit. -/
def ziskAccountHasEmptyCodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # account_rlp_len\n" ++
  "  addi a0, a3, 16             # account_rlp ptr\n" ++
  "  li a2, 0xa0010008           # is_eoa out\n" ++
  "  jal ra, account_has_empty_code\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lahec_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountHasEmptyCodeFunction ++ "\n" ++
  ".Lahec_pdone:"

def ziskAccountHasEmptyCodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ahec_offset:\n" ++
  "  .zero 8\n" ++
  "ahec_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "ahec_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"

def ziskAccountHasEmptyCodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountHasEmptyCodePrologue
  dataAsm     := ziskAccountHasEmptyCodeDataSection
}

/-! ## account_storage_root_is_empty -- PR-K133

    Predicate: does this account's `storage_root` field equal
    `EMPTY_TRIE_ROOT = keccak256(rlp.encode(b''))`?

      EMPTY_TRIE_ROOT =
        0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421

    A `true` result means the account has no storage entries
    (its storage trie is empty). EOAs and untouched contracts
    carry this canonical empty value.

    Companion to PR-K131 `account_has_empty_code` (the code-side
    EOA predicate) and PR-K123 `account_is_empty` (the EIP-161
    nonce+balance+code variant — but explicitly *not* requiring
    empty storage).

    Composes:
      - PR-K20 `rlp_list_nth_item` — field 2 bounds

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : u64 out ptr (1 if storage_root == EMPTY_TRIE_ROOT,
                                 0 otherwise)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written
        1 : RLP parse failure / field 2 missing
        2 : field 2 length != 32 -/
def accountStorageRootIsEmptyFunction : String :=
  "account_storage_root_is_empty:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # account_ptr\n" ++
  "  mv s1, a1                   # account_len\n" ++
  "  mv s2, a2                   # u64 out ptr\n" ++
  "  sd zero, 0(s2)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  la a3, asrie_offset; la a4, asrie_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lasrie_parse_fail\n" ++
  "  la t0, asrie_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lasrie_size_fail\n" ++
  "  la t0, asrie_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  la t4, asrie_empty_trie_root\n" ++
  "  ld t5,  0(t3); ld t6,  0(t4); bne t5, t6, .Lasrie_neq\n" ++
  "  ld t5,  8(t3); ld t6,  8(t4); bne t5, t6, .Lasrie_neq\n" ++
  "  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Lasrie_neq\n" ++
  "  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Lasrie_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lasrie_ret\n" ++
  ".Lasrie_neq:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lasrie_ret\n" ++
  ".Lasrie_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lasrie_ret\n" ++
  ".Lasrie_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lasrie_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_account_storage_root_is_empty`: probe BuildUnit. -/
def ziskAccountStorageRootIsEmptyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # account_rlp_len\n" ++
  "  addi a0, a3, 16             # account_rlp ptr\n" ++
  "  li a2, 0xa0010008           # is_empty out\n" ++
  "  jal ra, account_storage_root_is_empty\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lasrie_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountStorageRootIsEmptyFunction ++ "\n" ++
  ".Lasrie_pdone:"

def ziskAccountStorageRootIsEmptyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "asrie_offset:\n" ++
  "  .zero 8\n" ++
  "asrie_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "asrie_empty_trie_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21"

def ziskAccountStorageRootIsEmptyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountStorageRootIsEmptyPrologue
  dataAsm     := ziskAccountStorageRootIsEmptyDataSection
}

/-! ## rlp_list_count_items -- PR-K47
    The function body now lives in `EvmAsm/Codegen/Programs/RlpRead.lean`
    (see PR #5900). Only the zisk probe BuildUnit remains here. -//-- `zisk_rlp_list_count_items`: probe BuildUnit. Reads
    (list_len, list_bytes) from host input, writes
    (status, count) to OUTPUT. -/
def ziskRlpListCountItemsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # list_len\n" ++
  "  addi a0, a3, 16             # list ptr\n" ++
  "  li a2, 0xa0010008           # count out at OUTPUT + 8\n" ++
  "  sd zero, 0(a2)\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lrlc_pdone\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  ".Lrlc_pdone:"

def ziskRlpListCountItemsDataSection : String :=
  ".section .data\n" ++
  "rlc_pad:\n" ++
  "  .zero 8"

def ziskRlpListCountItemsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRlpListCountItemsPrologue
  dataAsm     := ziskRlpListCountItemsDataSection
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

/-! ## account_decode -- PR-K27 RLP splitter for Account records

    Decode an RLP-encoded Ethereum Account (the value bytes
    that `mpt_lookup_by_key` returns for state-trie addresses)
    into four caller-supplied output slots.

    Calling convention:
      a0 (input)  : account RLP bytes ptr
      a1 (input)  : account RLP byte length
      a2 (input)  : u64 nonce out ptr (8 bytes; written LE u64)
      a3 (input)  : u256 balance out ptr (32 bytes; written BE,
                    left-zero-padded for values < 32 bytes)
      a4 (input)  : storage_root out ptr (32 bytes)
      a5 (input)  : code_hash out ptr (32 bytes)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail

    Composes PR-K20 `rlp_list_nth_item` four times. Field types
    enforced:
      * nonce / balance : variable-length BE big-int (length
                          in [0, 8] for nonce, [0, 32] for balance)
      * storage_root / code_hash : exactly 32 bytes each. -/
def accountDecodeFunction : String :=
  "account_decode:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                  # account ptr\n" ++
  "  mv s1, a1                  # account_len\n" ++
  "  mv s2, a2                  # nonce out\n" ++
  "  mv s3, a3                  # balance out\n" ++
  "  mv s4, a4                  # storage_root out\n" ++
  "  mv s5, a5                  # code_hash out\n" ++
  "  # Field 0: nonce (u64 BE → LE store)\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  li a2, 0\n" ++
  "  la a3, ad_offset\n" ++
  "  la a4, ad_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lad_fail\n" ++
  "  la t0, ad_length; ld t1, 0(t0)\n" ++
  "  li t2, 8\n" ++
  "  bgtu t1, t2, .Lad_fail      # nonce > 8 bytes\n" ++
  "  la t0, ad_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  li t2, 0                   # accumulator\n" ++
  ".Lad_nonce_loop:\n" ++
  "  beqz t1, .Lad_nonce_done\n" ++
  "  slli t2, t2, 8\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  or t2, t2, t4\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lad_nonce_loop\n" ++
  ".Lad_nonce_done:\n" ++
  "  sd t2, 0(s2)               # nonce_out (LE u64)\n" ++
  "  # Field 1: balance (u256 BE → BE 32-byte buffer)\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  li a2, 1\n" ++
  "  la a3, ad_offset\n" ++
  "  la a4, ad_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lad_fail\n" ++
  "  la t0, ad_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bgtu t1, t2, .Lad_fail      # balance > 32 bytes\n" ++
  "  # Zero balance_out\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  # Right-align: write to s3 + (32 - length)\n" ++
  "  sub t2, t2, t1             # 32 - length\n" ++
  "  add t4, s3, t2             # dst\n" ++
  "  la t0, ad_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  ".Lad_bal_loop:\n" ++
  "  beqz t1, .Lad_bal_done\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb  t5, 0(t4)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lad_bal_loop\n" ++
  ".Lad_bal_done:\n" ++
  "  # Field 2: storage_root (must be exactly 32 bytes)\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  li a2, 2\n" ++
  "  la a3, ad_offset\n" ++
  "  la a4, ad_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lad_fail\n" ++
  "  la t0, ad_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lad_fail\n" ++
  "  la t0, ad_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  ld t4,  0(t3); sd t4,  0(s4)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s4)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s4)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s4)\n" ++
  "  # Field 3: code_hash (must be exactly 32 bytes)\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  li a2, 3\n" ++
  "  la a3, ad_offset\n" ++
  "  la a4, ad_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lad_fail\n" ++
  "  la t0, ad_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lad_fail\n" ++
  "  la t0, ad_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  ld t4,  0(t3); sd t4,  0(s5)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s5)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s5)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s5)\n" ++
  "  li a0, 0\n" ++
  "  j .Lad_ret\n" ++
  ".Lad_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lad_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_account_decode`: probe BuildUnit. Reads
    (account_len, account_bytes) from host input, writes
    (status, nonce, balance, storage_root, code_hash) to OUTPUT.
    Input layout:
      bytes  0.. 8 : account_len (u64)
      bytes  8..   : account RLP bytes
    Output layout:
      bytes   0.. 8 : status (u64)
      bytes   8..16 : nonce (u64 LE)
      bytes  16..48 : balance (u256 BE)
      bytes  48..80 : storage_root
      bytes  80..112: code_hash -/
def ziskAccountDecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # account_len\n" ++
  "  addi a0, a6, 16             # account ptr\n" ++
  "  li a2, 0xa0010008\n" ++
  "  li a3, 0xa0010010\n" ++
  "  li a4, 0xa0010030\n" ++
  "  li a5, 0xa0010050\n" ++
  "  # Pre-zero all outputs so a parse failure surfaces as zeros.\n" ++
  "  sd zero, 0(a2)\n" ++
  "  sd zero,  0(a3); sd zero,  8(a3); sd zero, 16(a3); sd zero, 24(a3)\n" ++
  "  sd zero,  0(a4); sd zero,  8(a4); sd zero, 16(a4); sd zero, 24(a4)\n" ++
  "  sd zero,  0(a5); sd zero,  8(a5); sd zero, 16(a5); sd zero, 24(a5)\n" ++
  "  jal ra, account_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lad_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountDecodeFunction ++ "\n" ++
  ".Lad_pdone:"

def ziskAccountDecodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ad_offset:\n" ++
  "  .zero 8\n" ++
  "ad_length:\n" ++
  "  .zero 8"

def ziskAccountDecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountDecodePrologue
  dataAsm     := ziskAccountDecodeDataSection
}

/-! ## account_at_address -- PR-K28 compose lookup + decode

    Take a raw Ethereum address, walk the state trie, decode
    the resulting Account RLP into its four fields. The
    cleanest top-of-K-stack abstraction: caller sees only
    `(address, state_root, witness) → fields`.

    Output struct layout (104 bytes at caller-supplied ptr):
      offset  0..  8 : nonce (u64 LE)
      offset  8.. 40 : balance (u256 BE, left-zero-padded)
      offset 40.. 72 : storage_root (32 B)
      offset 72..104 : code_hash (32 B)

    Calling convention:
      a0 (input)  : address bytes ptr
      a1 (input)  : address byte length (typically 20)
      a2 (input)  : state_root ptr (32 bytes)
      a3 (input)  : witness section ptr
      a4 (input)  : witness section_len
      a5 (input)  : output struct ptr (104 bytes)
      ra (input)  : return

      a0 (output) :
        0 = found and decoded
        1 = not found in trie     (output zeroed)
        2 = mpt_walk parse error  (output zeroed)
        3 = account_decode failure (output zeroed)

    Internal:
      Step 1: mpt_lookup_by_key(addr, ..., aa_value_scratch).
      Step 2: account_decode(scratch_val, scratch_len, ...).
    Reuses the K-stack primitive scratches. -/
def accountAtAddressFunction : String :=
  "account_at_address:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a5                   # output struct ptr\n" ++
  "  # Step 1: mpt_lookup_by_key.\n" ++
  "  la a5, aa_value_scratch\n" ++
  "  la a6, aa_value_len\n" ++
  "  jal ra, mpt_lookup_by_key\n" ++
  "  mv s1, a0                   # save lookup status\n" ++
  "  beqz a0, .Laa_lookup_ok\n" ++
  "  # Not found / parse error: zero the output struct.\n" ++
  "  sd zero,  0(s0); sd zero,  8(s0); sd zero, 16(s0); sd zero, 24(s0)\n" ++
  "  sd zero, 32(s0); sd zero, 40(s0); sd zero, 48(s0); sd zero, 56(s0)\n" ++
  "  sd zero, 64(s0); sd zero, 72(s0); sd zero, 80(s0); sd zero, 88(s0)\n" ++
  "  sd zero, 96(s0)\n" ++
  "  mv a0, s1\n" ++
  "  j .Laa_ret\n" ++
  ".Laa_lookup_ok:\n" ++
  "  la a0, aa_value_scratch\n" ++
  "  la t0, aa_value_len; ld a1, 0(t0)\n" ++
  "  mv a2, s0                   # nonce at struct + 0\n" ++
  "  addi a3, s0, 8              # balance at struct + 8\n" ++
  "  addi a4, s0, 40             # storage_root at struct + 40\n" ++
  "  addi a5, s0, 72             # code_hash at struct + 72\n" ++
  "  jal ra, account_decode\n" ++
  "  beqz a0, .Laa_done\n" ++
  "  # account_decode failed: zero struct, return 3.\n" ++
  "  sd zero,  0(s0); sd zero,  8(s0); sd zero, 16(s0); sd zero, 24(s0)\n" ++
  "  sd zero, 32(s0); sd zero, 40(s0); sd zero, 48(s0); sd zero, 56(s0)\n" ++
  "  sd zero, 64(s0); sd zero, 72(s0); sd zero, 80(s0); sd zero, 88(s0)\n" ++
  "  sd zero, 96(s0)\n" ++
  "  li a0, 3\n" ++
  "  j .Laa_ret\n" ++
  ".Laa_done:\n" ++
  "  li a0, 0\n" ++
  ".Laa_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_account_at_address`: probe BuildUnit. Reads
    (witness_len, addr_len, state_root, addr, witness) from
    host input. Writes (status, nonce, balance, storage_root,
    code_hash) to OUTPUT.
    Output layout:
      bytes   0.. 8 : status
      bytes   8..16 : nonce
      bytes  16..48 : balance
      bytes  48..80 : storage_root
      bytes  80..112: code_hash -/
def ziskAccountAtAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld t6, 8(a7)                # witness_len\n" ++
  "  ld t5, 16(a7)               # addr_len\n" ++
  "  addi a2, a7, 24             # state_root ptr\n" ++
  "  addi a0, a7, 56             # address ptr\n" ++
  "  mv a1, t5                   # addr_len\n" ++
  "  add a3, a0, t5              # witness ptr = address + addr_len\n" ++
  "  mv a4, t6                   # witness_len\n" ++
  "  li a5, 0xa0010008           # output struct at OUTPUT + 8\n" ++
  "  # Pre-zero 104 bytes of output struct so a failure surfaces as zeros.\n" ++
  "  sd zero, 0(a5); sd zero, 8(a5); sd zero, 16(a5); sd zero, 24(a5)\n" ++
  "  sd zero, 32(a5); sd zero, 40(a5); sd zero, 48(a5); sd zero, 56(a5)\n" ++
  "  sd zero, 64(a5); sd zero, 72(a5); sd zero, 80(a5); sd zero, 88(a5)\n" ++
  "  sd zero, 96(a5)\n" ++
  "  jal ra, account_at_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Laa_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  accountDecodeFunction ++ "\n" ++
  accountAtAddressFunction ++ "\n" ++
  ".Laa_pdone:"

def ziskAccountAtAddressDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8\n" ++
  "mbc_offset:\n" ++
  "  .zero 8\n" ++
  "mbc_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_lookup_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_lookup_offset:\n" ++
  "  .zero 8\n" ++
  "mw_lookup_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_child_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_path_offset:\n" ++
  "  .zero 8\n" ++
  "mw_path_length:\n" ++
  "  .zero 8\n" ++
  "mw_child_offset:\n" ++
  "  .zero 8\n" ++
  "mw_child_length:\n" ++
  "  .zero 8\n" ++
  "mw_value_offset:\n" ++
  "  .zero 8\n" ++
  "mw_value_length:\n" ++
  "  .zero 8\n" ++
  "mw_nibble_count:\n" ++
  "  .zero 8\n" ++
  "mw_is_leaf:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_nibble_buf:\n" ++
  "  .zero 128\n" ++
  ".balign 32\n" ++
  "mlk_keccak_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "mlk_nibble_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "ad_offset:\n" ++
  "  .zero 8\n" ++
  "ad_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aa_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aa_value_scratch:\n" ++
  "  .zero 256"

def ziskAccountAtAddressProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountAtAddressPrologue
  dataAsm     := ziskAccountAtAddressDataSection
}

/-! ## slot_at_index -- PR-K29 storage trie lookup

    Storage-trie counterpart to `account_at_address`. Takes a
    32-byte slot index (big-endian u256) and walks the
    per-account storage trie, decoding the looked-up value as
    a u256.

    Per `execution-specs/.../trie.py::encode_node`, the value
    stored in the storage trie is `rlp.encode(slot_value:U256)`
    -- one RLP layer on top of the canonical leading-zero-
    stripped big-int. `mpt_walk` strips the leaf's outer item-1
    string prefix (one layer), so the value bytes we receive
    are exactly `rlp.encode(slot_value)`. We then apply one
    more layer of RLP decoding to recover the u256.

    Encoding cheat-sheet for slot values:
      slot_value = 0          → 0x80         (RLP empty)
      slot_value = 1          → 0x01         (single byte)
      slot_value = 0x7f       → 0x7f
      slot_value = 0x80       → 0x81 0x80    (1-byte string)
      slot_value = 0x0100     → 0x82 0x01 0x00 (2-byte string)
      slot_value = 2^256 - 1  → 0xa0 + 32 × 0xff

    Calling convention:
      a0 (input)  : slot_idx bytes ptr (32-byte big-endian u256)
      a1 (input)  : slot_idx byte length (typically 32)
      a2 (input)  : storage_root ptr (32 bytes)
      a3 (input)  : witness section ptr
      a4 (input)  : witness section_len
      a5 (input)  : output u256 BE ptr (32 bytes)
      ra (input)  : return

      a0 (output) :
        0 found and decoded
        1 not found (output zeroed)
        2 mpt_walk parse error (output zeroed)
        3 RLP-u256 decode failure (output zeroed)

    Internal: `mpt_lookup_by_key(slot_idx, ..., si_value_scratch)`
    then `slot_decode_u256` over the looked-up bytes. -/
def slotDecodeU256Function : String :=
  "slot_decode_u256:\n" ++
  "  # a0 = val_bytes ptr, a1 = val_len, a2 = 32-byte BE out ptr.\n" ++
  "  # Returns 0 (ok) / 1 (fail). Output is zeroed on every path.\n" ++
  "  sd zero,  0(a2); sd zero,  8(a2); sd zero, 16(a2); sd zero, 24(a2)\n" ++
  "  beqz a1, .Lsdu_fail        # empty input: malformed encoded value\n" ++
  "  lbu t0, 0(a0)\n" ++
  "  li t1, 0x80\n" ++
  "  bltu t0, t1, .Lsdu_single  # b0 < 0x80: single byte\n" ++
  "  beq t0, t1, .Lsdu_zero     # b0 == 0x80: empty string ⇒ 0\n" ++
  "  li t1, 0xa1\n" ++
  "  bgeu t0, t1, .Lsdu_fail    # b0 ≥ 0xa1: too long for a u256\n" ++
  "  # Short string of n bytes (1 ≤ n ≤ 32).\n" ++
  "  li t1, 0x80\n" ++
  "  sub t2, t0, t1             # n\n" ++
  "  addi t3, a1, -1\n" ++
  "  bltu t3, t2, .Lsdu_fail    # not enough bytes for declared length\n" ++
  "  li t4, 32\n" ++
  "  sub t4, t4, t2             # 32 - n\n" ++
  "  add t5, a2, t4             # dst (right-aligned)\n" ++
  "  addi t6, a0, 1             # src\n" ++
  "  mv t3, t2                  # remaining\n" ++
  ".Lsdu_copy:\n" ++
  "  beqz t3, .Lsdu_ok\n" ++
  "  lbu t1, 0(t6)\n" ++
  "  sb  t1, 0(t5)\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t6, t6, 1\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lsdu_copy\n" ++
  ".Lsdu_single:\n" ++
  "  sb t0, 31(a2)              # write u256 = b0 at byte 31 (BE LSB)\n" ++
  ".Lsdu_zero:\n" ++
  ".Lsdu_ok:\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lsdu_fail:\n" ++
  "  li a0, 1\n" ++
  "  ret"

def slotAtIndexFunction : String :=
  "slot_at_index:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a5                  # u256 out ptr\n" ++
  "  la a5, si_value_scratch\n" ++
  "  la a6, si_value_len\n" ++
  "  jal ra, mpt_lookup_by_key\n" ++
  "  mv s1, a0\n" ++
  "  beqz a0, .Lsi_decode\n" ++
  "  sd zero,  0(s0); sd zero,  8(s0); sd zero, 16(s0); sd zero, 24(s0)\n" ++
  "  mv a0, s1\n" ++
  "  j .Lsi_ret\n" ++
  ".Lsi_decode:\n" ++
  "  la a0, si_value_scratch\n" ++
  "  la t0, si_value_len; ld a1, 0(t0)\n" ++
  "  mv a2, s0\n" ++
  "  jal ra, slot_decode_u256\n" ++
  "  beqz a0, .Lsi_done\n" ++
  "  sd zero,  0(s0); sd zero,  8(s0); sd zero, 16(s0); sd zero, 24(s0)\n" ++
  "  li a0, 3\n" ++
  "  j .Lsi_ret\n" ++
  ".Lsi_done:\n" ++
  "  li a0, 0\n" ++
  ".Lsi_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_slot_at_index`: probe BuildUnit. Reads
    (witness_len, slot_len, storage_root, slot_idx, witness)
    from host input. Writes (status, u256) to OUTPUT. -/
def ziskSlotAtIndexPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld t6, 8(a7)                # witness_len\n" ++
  "  ld t5, 16(a7)               # slot_len\n" ++
  "  addi a2, a7, 24             # storage_root ptr\n" ++
  "  addi a0, a7, 56             # slot_idx ptr\n" ++
  "  mv a1, t5                   # slot_len\n" ++
  "  add a3, a0, t5              # witness ptr = slot_idx + slot_len\n" ++
  "  mv a4, t6                   # witness_len\n" ++
  "  li a5, 0xa0010008           # u256 out at OUTPUT + 8\n" ++
  "  sd zero, 0(a5); sd zero, 8(a5); sd zero, 16(a5); sd zero, 24(a5)\n" ++
  "  jal ra, slot_at_index\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsi_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  slotDecodeU256Function ++ "\n" ++
  slotAtIndexFunction ++ "\n" ++
  ".Lsi_pdone:"

def ziskSlotAtIndexDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8\n" ++
  "mbc_offset:\n" ++
  "  .zero 8\n" ++
  "mbc_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_lookup_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_lookup_offset:\n" ++
  "  .zero 8\n" ++
  "mw_lookup_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_child_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_path_offset:\n" ++
  "  .zero 8\n" ++
  "mw_path_length:\n" ++
  "  .zero 8\n" ++
  "mw_child_offset:\n" ++
  "  .zero 8\n" ++
  "mw_child_length:\n" ++
  "  .zero 8\n" ++
  "mw_value_offset:\n" ++
  "  .zero 8\n" ++
  "mw_value_length:\n" ++
  "  .zero 8\n" ++
  "mw_nibble_count:\n" ++
  "  .zero 8\n" ++
  "mw_is_leaf:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_nibble_buf:\n" ++
  "  .zero 128\n" ++
  ".balign 32\n" ++
  "mlk_keccak_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "mlk_nibble_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "si_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "si_value_scratch:\n" ++
  "  .zero 256"

def ziskSlotAtIndexProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSlotAtIndexPrologue
  dataAsm     := ziskSlotAtIndexDataSection
}

/-! ## rlp_encode_uint_be -- PR-K30 — def moved to `Programs/RlpRead.lean`. -/


/-- `zisk_rlp_encode_uint_be`: probe BuildUnit. Reads
    (src_len, src_bytes) from host input, writes
    (bytes_written, encoded_bytes) to OUTPUT. -/
def ziskRlpEncodeUintBePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # src_len\n" ++
  "  addi a0, a3, 16             # src ptr\n" ++
  "  li a2, 0xa0010008           # output at OUTPUT + 8\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # bytes_written at OUTPUT + 0\n" ++
  "  j .Lreu_pdone\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  ".Lreu_pdone:"

def ziskRlpEncodeUintBeDataSection : String :=
  ".section .data\n" ++
  "reu_pad:\n" ++
  "  .zero 8"

def ziskRlpEncodeUintBeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRlpEncodeUintBePrologue
  dataAsm     := ziskRlpEncodeUintBeDataSection
}

/-! ## K128 rlp_encode_bytes — moved to `Programs/RlpRead.lean` (file-size hard cap). -/

/-! ## rlp_encode_list_prefix -- PR-K129 — def moved to `Programs/RlpRead.lean`. -/


/-- `zisk_rlp_encode_list_prefix`: probe BuildUnit. Reads
    (payload_length,) from host input, writes (status, out_len,
    prefix_bytes...) to OUTPUT. -/
def ziskRlpEncodeListPrefixPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a0, 8(a3)                # payload_length\n" ++
  "  li a1, 0xa0010010           # out bytes\n" ++
  "  li a2, 0xa0010008           # out_len out\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lrelp_pdone\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  ".Lrelp_pdone:"

def ziskRlpEncodeListPrefixDataSection : String :=
  ".section .data\n" ++
  "relp_scratch:\n" ++
  "  .zero 8"

def ziskRlpEncodeListPrefixProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRlpEncodeListPrefixPrologue
  dataAsm     := ziskRlpEncodeListPrefixDataSection
}

/-! ## K130 withdrawal_rlp_encode / K132 withdrawal_compute_hash — moved to `Programs/Withdrawal.lean` (file-size hard cap). -/


/-! ## account_encode -- PR-K31 mutating side of account_decode

    Encode (nonce, balance, storage_root, code_hash) into the
    canonical 4-field RLP list bytes used as the value of a
    state-trie leaf node. The inverse of PR-K27 account_decode.

    Composition:
      payload = rlp_encode_uint_be(nonce_be, 8) +
                rlp_encode_uint_be(balance_be, 32) +
                0xa0 + storage_root +
                0xa0 + code_hash
      out = 0xf8 + len(payload) + payload

    The 0xf8 prefix is correct because the payload is always
    > 55 bytes (storage_root + code_hash already total 66 bytes,
    plus at least 2 bytes for nonce/balance encodings).

    Calling convention:
      a0 (input)  : nonce 8-byte BE ptr
      a1 (input)  : balance 32-byte BE ptr
      a2 (input)  : storage_root ptr (32 bytes)
      a3 (input)  : code_hash ptr (32 bytes)
      a4 (input)  : output buffer ptr (≥ 128 bytes)
      a5 (input)  : u64 out ptr (bytes_written)
      ra (input)  : return
      a0 (output) : 0 (always success; cap fixed by caller)

    Scratch: ae_scratch (64 bytes) for staging nonce_rlp +
    balance_rlp before they're copied to the output buffer. -/
def accountEncodeFunction : String :=
  "account_encode:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # nonce_be ptr\n" ++
  "  mv s1, a1                   # balance_be ptr\n" ++
  "  mv s2, a2                   # storage_root ptr\n" ++
  "  mv s3, a3                   # code_hash ptr\n" ++
  "  mv s4, a4                   # output buf\n" ++
  "  mv s5, a5                   # bytes_written out\n" ++
  "  # Step 1: rlp_encode_uint_be(nonce_be, 8) → ae_scratch.\n" ++
  "  mv a0, s0\n" ++
  "  li a1, 8\n" ++
  "  la a2, ae_scratch\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  la t0, ae_nonce_len; sd a0, 0(t0)\n" ++
  "  # Step 2: rlp_encode_uint_be(balance_be, 32) → ae_scratch + nonce_len.\n" ++
  "  la t0, ae_nonce_len; ld t1, 0(t0)\n" ++
  "  la t2, ae_scratch\n" ++
  "  add a2, t2, t1\n" ++
  "  mv a0, s1\n" ++
  "  li a1, 32\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  la t0, ae_balance_len; sd a0, 0(t0)\n" ++
  "  # Step 3: payload_len = nonce_len + balance_len + 33 + 33.\n" ++
  "  la t0, ae_nonce_len; ld t1, 0(t0)\n" ++
  "  la t0, ae_balance_len; ld t2, 0(t0)\n" ++
  "  add t3, t1, t2\n" ++
  "  addi t3, t3, 66            # + 33 + 33 (storage_root + code_hash)\n" ++
  "  # Step 4: write outer prefix 0xf8 + payload_len.\n" ++
  "  mv t4, s4                  # cursor\n" ++
  "  li t5, 0xf8\n" ++
  "  sb t5, 0(t4)\n" ++
  "  sb t3, 1(t4)\n" ++
  "  addi t4, t4, 2\n" ++
  "  # Step 5: copy nonce_rlp (t1 bytes) from ae_scratch to t4.\n" ++
  "  la t5, ae_scratch\n" ++
  "  mv t6, t1                  # remaining\n" ++
  ".Lae_copy_nonce:\n" ++
  "  beqz t6, .Lae_copy_balance_init\n" ++
  "  lbu t1, 0(t5)\n" ++
  "  sb  t1, 0(t4)\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t6, t6, -1\n" ++
  "  j .Lae_copy_nonce\n" ++
  ".Lae_copy_balance_init:\n" ++
  "  # Step 6: copy balance_rlp from ae_scratch + nonce_len. t5 is already there.\n" ++
  "  la t0, ae_balance_len; ld t6, 0(t0)\n" ++
  ".Lae_copy_balance:\n" ++
  "  beqz t6, .Lae_copy_storage_root\n" ++
  "  lbu t1, 0(t5)\n" ++
  "  sb  t1, 0(t4)\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t6, t6, -1\n" ++
  "  j .Lae_copy_balance\n" ++
  ".Lae_copy_storage_root:\n" ++
  "  # Step 7: write 0xa0 + storage_root (32 bytes).\n" ++
  "  li t5, 0xa0\n" ++
  "  sb t5, 0(t4)\n" ++
  "  addi t4, t4, 1\n" ++
  "  ld t5,  0(s2); sd t5,  0(t4)\n" ++
  "  ld t5,  8(s2); sd t5,  8(t4)\n" ++
  "  ld t5, 16(s2); sd t5, 16(t4)\n" ++
  "  ld t5, 24(s2); sd t5, 24(t4)\n" ++
  "  addi t4, t4, 32\n" ++
  "  # Step 8: write 0xa0 + code_hash.\n" ++
  "  li t5, 0xa0\n" ++
  "  sb t5, 0(t4)\n" ++
  "  addi t4, t4, 1\n" ++
  "  ld t5,  0(s3); sd t5,  0(t4)\n" ++
  "  ld t5,  8(s3); sd t5,  8(t4)\n" ++
  "  ld t5, 16(s3); sd t5, 16(t4)\n" ++
  "  ld t5, 24(s3); sd t5, 24(t4)\n" ++
  "  addi t4, t4, 32\n" ++
  "  # bytes_written = (t4 - s4)\n" ++
  "  sub t4, t4, s4\n" ++
  "  sd t4, 0(s5)\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_account_encode`: probe BuildUnit. Reads
    (nonce_be8, balance_be32, storage_root, code_hash) from
    host input (104 bytes total). Writes (bytes_written, RLP)
    to OUTPUT.
    Input layout:
      bytes  0.. 8 : nonce (8-byte BE)
      bytes  8..40 : balance (32-byte BE)
      bytes 40..72 : storage_root (32 B)
      bytes 72..104: code_hash (32 B) -/
def ziskAccountEncodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  addi a0, a6, 8              # nonce_be\n" ++
  "  addi a1, a6, 16             # balance_be\n" ++
  "  addi a2, a6, 48             # storage_root\n" ++
  "  addi a3, a6, 80             # code_hash\n" ++
  "  li a4, 0xa0010008           # output RLP at OUTPUT + 8\n" ++
  "  li a5, 0xa0010000           # bytes_written at OUTPUT + 0\n" ++
  "  jal ra, account_encode\n" ++
  "  j .Lae_pdone\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  accountEncodeFunction ++ "\n" ++
  ".Lae_pdone:"

def ziskAccountEncodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ae_nonce_len:\n" ++
  "  .zero 8\n" ++
  "ae_balance_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "ae_scratch:\n" ++
  "  .zero 64"

def ziskAccountEncodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountEncodePrologue
  dataAsm     := ziskAccountEncodeDataSection
}

/-! ## K32 hp_encode_nibbles — moved to `Programs/Mpt.lean` (file-size hard cap). -/

/-! ## state_root_single_account -- PR-K33 end-to-end recompute

    Compute the state-trie root for a trie containing exactly
    one account. Composes every mutating primitive shipped so
    far:

      keccak(address)                       (PR-K3)
      bytes_to_nibbles → 64-nibble path     (PR-K25)
      hp_encode_nibbles(path, leaf=true)    (PR-K32)
      account_encode(nonce, balance,
                     storage_root,
                     code_hash)             (PR-K31)
      leaf_rlp = rlp([hp_bytes, account_rlp_bytes])
      state_root = keccak(leaf_rlp)

    This is the smallest useful "compute state_root from
    fields" operation. Future PRs scale to multi-account tries
    by composing branch / extension node builders on top.

    Calling convention:
      a0 (input)  : address bytes ptr
      a1 (input)  : address byte length (typically 20)
      a2 (input)  : nonce 8-byte BE ptr
      a3 (input)  : balance 32-byte BE ptr
      a4 (input)  : storage_root ptr (32 bytes)
      a5 (input)  : code_hash ptr (32 bytes)
      a6 (input)  : state_root output ptr (32 bytes)
      ra (input)  : return
      a0 (output) : 0 success

    Reuses K-stack primitive functions. New scratches:
      srsa_keccak_buf  (32 B)
      srsa_nibble_buf  (64 B)
      srsa_hp_buf      (33 B)  -- 64-nibble path HP-encodes to 33 bytes
      srsa_acc_buf     (128 B) -- account RLP, typically 70..104 B
      srsa_acc_len     (8 B)
      srsa_leaf_buf    (256 B) -- leaf RLP -/
def stateRootSingleAccountFunction : String :=
  "state_root_single_account:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a2                   # nonce_be ptr\n" ++
  "  mv s1, a3                   # balance_be ptr\n" ++
  "  mv s2, a4                   # storage_root ptr\n" ++
  "  mv s3, a5                   # code_hash ptr\n" ++
  "  mv s4, a6                   # state_root output ptr\n" ++
  "  # Step 1: keccak(address) → srsa_keccak_buf.\n" ++
  "  la a2, srsa_keccak_buf\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # Step 2: bytes_to_nibbles → srsa_nibble_buf (64 nibbles).\n" ++
  "  la a0, srsa_keccak_buf\n" ++
  "  li a1, 32\n" ++
  "  la a2, srsa_nibble_buf\n" ++
  "  jal ra, bytes_to_nibbles\n" ++
  "  # Step 3: hp_encode → srsa_hp_buf (33 bytes for 64-nibble leaf).\n" ++
  "  la a0, srsa_nibble_buf\n" ++
  "  li a1, 64\n" ++
  "  li a2, 1\n" ++
  "  la a3, srsa_hp_buf\n" ++
  "  jal ra, hp_encode_nibbles\n" ++
  "  # Step 4: account_encode → srsa_acc_buf.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s2\n" ++
  "  mv a3, s3\n" ++
  "  la a4, srsa_acc_buf\n" ++
  "  la a5, srsa_acc_len\n" ++
  "  jal ra, account_encode\n" ++
  "  # Step 5: build leaf RLP at srsa_leaf_buf.\n" ++
  "  la t0, srsa_acc_len; ld t1, 0(t0)\n" ++
  "  # payload_len = 34 (hp) + (1 or 2) prefix + acc_len\n" ++
  "  # For acc_len ≥ 56: acc prefix = 2 bytes (0xb8 + len). 0xa1 + 33 hp = 34. Total 34 + 2 + acc_len.\n" ++
  "  li t2, 56\n" ++
  "  bltu t1, t2, .Lsrsa_acc_short\n" ++
  "  addi t2, t1, 36              # payload = 34 + 2 + acc_len\n" ++
  "  j .Lsrsa_have_payload\n" ++
  ".Lsrsa_acc_short:\n" ++
  "  addi t2, t1, 35              # payload = 34 + 1 + acc_len\n" ++
  ".Lsrsa_have_payload:\n" ++
  "  # Write outer prefix: 0xf8 + payload_len.\n" ++
  "  la t3, srsa_leaf_buf\n" ++
  "  li t4, 0xf8\n" ++
  "  sb t4, 0(t3)\n" ++
  "  sb t2, 1(t3)\n" ++
  "  addi t3, t3, 2\n" ++
  "  # Write 0xa1 + 33 hp bytes.\n" ++
  "  li t4, 0xa1\n" ++
  "  sb t4, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  "  la t5, srsa_hp_buf\n" ++
  "  li t6, 33\n" ++
  ".Lsrsa_copy_hp:\n" ++
  "  beqz t6, .Lsrsa_hp_done\n" ++
  "  lbu t4, 0(t5)\n" ++
  "  sb  t4, 0(t3)\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t6, t6, -1\n" ++
  "  j .Lsrsa_copy_hp\n" ++
  ".Lsrsa_hp_done:\n" ++
  "  # Write account_rlp prefix.\n" ++
  "  li t4, 56\n" ++
  "  bltu t1, t4, .Lsrsa_acc_short_pfx\n" ++
  "  li t4, 0xb8\n" ++
  "  sb t4, 0(t3)\n" ++
  "  sb t1, 1(t3)\n" ++
  "  addi t3, t3, 2\n" ++
  "  j .Lsrsa_acc_copy\n" ++
  ".Lsrsa_acc_short_pfx:\n" ++
  "  li t4, 0x80\n" ++
  "  add t4, t4, t1\n" ++
  "  sb t4, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  ".Lsrsa_acc_copy:\n" ++
  "  la t5, srsa_acc_buf\n" ++
  "  mv t6, t1\n" ++
  ".Lsrsa_copy_acc:\n" ++
  "  beqz t6, .Lsrsa_acc_done\n" ++
  "  lbu t4, 0(t5)\n" ++
  "  sb  t4, 0(t3)\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t6, t6, -1\n" ++
  "  j .Lsrsa_copy_acc\n" ++
  ".Lsrsa_acc_done:\n" ++
  "  # leaf_len = t3 - srsa_leaf_buf; keccak the leaf into s4.\n" ++
  "  la t5, srsa_leaf_buf\n" ++
  "  sub a1, t3, t5\n" ++
  "  mv a0, t5\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_state_root_single_account`: probe BuildUnit. Reads
    (addr_len, address, nonce_be, balance_be, storage_root,
     code_hash) from host input, writes the 32-byte state_root
    to OUTPUT. -/
def ziskStateRootSingleAccountPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld t6, 8(a7)                # addr_len\n" ++
  "  addi a0, a7, 16             # addr ptr\n" ++
  "  mv a1, t6\n" ++
  "  add a2, a0, t6              # nonce_be at addr + addr_len\n" ++
  "  addi a3, a2, 8              # balance_be at +8\n" ++
  "  addi a4, a3, 32             # storage_root at +32\n" ++
  "  addi a5, a4, 32             # code_hash at +32\n" ++
  "  li a6, 0xa0010000           # state_root out at OUTPUT + 0\n" ++
  "  jal ra, state_root_single_account\n" ++
  "  j .Lsrsa_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  accountEncodeFunction ++ "\n" ++
  stateRootSingleAccountFunction ++ "\n" ++
  ".Lsrsa_pdone:"

def ziskStateRootSingleAccountDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "srsa_keccak_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "srsa_nibble_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "srsa_hp_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "srsa_acc_buf:\n" ++
  "  .zero 128\n" ++
  ".balign 8\n" ++
  "srsa_acc_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "ae_nonce_len:\n" ++
  "  .zero 8\n" ++
  "ae_balance_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "ae_scratch:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "srsa_leaf_buf:\n" ++
  "  .zero 256"

def ziskStateRootSingleAccountProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskStateRootSingleAccountPrologue
  dataAsm     := ziskStateRootSingleAccountDataSection
}

/-! ## rlp-field shims + account extractors + legacy-tx decoders / sig extractors (PR-K34/K121/K35/K120/K123/K36/K37/K138/K139)
    Function + probe defs moved to `Programs/Tx.lean` (see file-size hard cap at the bottom of this file). -/


/-! ## Header decoders + validators + K81/K82 account-gas (K38/K39/K55/K90/K93/K95/K43/K72/K63/K67/K68/K81/K82/K73/K74/K75) — moved to `Programs/Header.lean` (file-size hard cap). -/


/-! ## K71 tx_cost_compute + K79 validate_transaction_balance — moved to `Programs/Tx.lean` (file-size hard cap). -/

/-! ## u256-BE truncation + tx type/extract/EIP-decode family + intrinsic-gas + validate-transaction (PR-K57/K40/K102/K101/K103/K104/K108/K41/K42/K44/K45/K87/K88/K92/K46/K66/K76/K80)
    Function + probe defs moved to `Programs/Tx.lean` (see file-size hard cap at the bottom of this file). -/

/-! ## withdrawal + block-body cluster (K49/K65/K77/K78/K83-K91/K97/K124/K125) — moved to `Programs/Block.lean` (file-size hard cap). -/


/-! ## bloom atoms K148-K154 — moved to `Programs/Bloom.lean` (file-size hard cap). -/

/-! ## rlp_encode_u64 -- PR-K155

    Encode a `u64` register value as canonical RLP. A convenience
    wrapper that takes the integer directly rather than the BE
    byte buffer that PR-K30 `rlp_encode_uint_be` requires:

      value == 0       -> 0x80                       (1 byte)
      value < 0x80     -> single byte = value        (1 byte)
      else             -> 0x80 + effective_len + BE bytes
                          (effective_len in 1..8)    (2..9 bytes)

    Pure register arithmetic, leaf-callable, no scratch memory.
    Use cases where K30 with a stack-allocated BE buffer is
    awkward boilerplate -- typical example is receipt encoding:

      rlp_encode_u64(status, buf + cursor, &written); cursor += written
      rlp_encode_u64(cumulative_gas, buf + cursor, &written); cursor += written
      ...

    Calling convention:
      a0 (input)  : value (u64)
      a1 (input)  : output buffer ptr (caller supplies >= 9 bytes)
      a2 (input)  : u64 out length ptr (bytes written; 1..9)
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def rlpEncodeU64Function : String :=
  "rlp_encode_u64:\n" ++
  "  beqz a0, .Lreu64_zero\n" ++
  "  li t0, 0x80\n" ++
  "  bgeu a0, t0, .Lreu64_multi\n" ++
  "  # Single-byte form (value in 0x01..0x7f).\n" ++
  "  sb a0, 0(a1)\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lreu64_zero:\n" ++
  "  li t0, 0x80\n" ++
  "  sb t0, 0(a1)\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lreu64_multi:\n" ++
  "  # Compute effective byte length (1..8) by finding the top non-zero byte.\n" ++
  "  # We already know value >= 0x80, so len >= 1.\n" ++
  "  li t0, 1                   # effective_len candidate\n" ++
  "  li t1, 0x100\n" ++
  "  bltu a0, t1, .Lreu64_have_len\n" ++
  "  li t0, 2\n" ++
  "  slli t1, t1, 8\n" ++
  "  bltu a0, t1, .Lreu64_have_len\n" ++
  "  li t0, 3\n" ++
  "  slli t1, t1, 8\n" ++
  "  bltu a0, t1, .Lreu64_have_len\n" ++
  "  li t0, 4\n" ++
  "  slli t1, t1, 8\n" ++
  "  bltu a0, t1, .Lreu64_have_len\n" ++
  "  li t0, 5\n" ++
  "  slli t1, t1, 8\n" ++
  "  bltu a0, t1, .Lreu64_have_len\n" ++
  "  li t0, 6\n" ++
  "  slli t1, t1, 8\n" ++
  "  bltu a0, t1, .Lreu64_have_len\n" ++
  "  li t0, 7\n" ++
  "  slli t1, t1, 8\n" ++
  "  bltu a0, t1, .Lreu64_have_len\n" ++
  "  li t0, 8\n" ++
  ".Lreu64_have_len:\n" ++
  "  # Write prefix 0x80 + effective_len.\n" ++
  "  addi t2, t0, 0x80\n" ++
  "  sb t2, 0(a1)\n" ++
  "  # Write effective_len BE bytes of value into a1+1..a1+1+len.\n" ++
  "  addi t3, a1, 1                 # dst cursor\n" ++
  "  addi t4, t0, -1                # shift_byte_index = len - 1\n" ++
  ".Lreu64_emit:\n" ++
  "  bltz t4, .Lreu64_done\n" ++
  "  slli t5, t4, 3                 # bit shift = 8 * byte_index\n" ++
  "  srl t6, a0, t5\n" ++
  "  sb t6, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lreu64_emit\n" ++
  ".Lreu64_done:\n" ++
  "  addi t1, t0, 1                 # bytes_written = 1 + effective_len\n" ++
  "  sd t1, 0(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_rlp_encode_u64`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : value (u64)
    Output layout:
      bytes  0.. 8 : status (always 0)
      bytes  8..16 : bytes_written
      bytes 16..25 : encoded RLP (up to 9 bytes) -/
def ziskRlpEncodeU64Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a0, 8(a3)                # value\n" ++
  "  li a1, 0xa0010010           # output buffer ptr\n" ++
  "  li a2, 0xa0010008           # out length ptr\n" ++
  "  jal ra, rlp_encode_u64\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lreu64_pdone\n" ++
  rlpEncodeU64Function ++ "\n" ++
  ".Lreu64_pdone:"

def ziskRlpEncodeU64DataSection : String :=
  ".section .data\n" ++
  "reu64_pad:\n" ++
  "  .zero 8"

def ziskRlpEncodeU64ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRlpEncodeU64Prologue
  dataAsm     := ziskRlpEncodeU64DataSection
}

/-! ## receipt_encode -- PR-K156

    Encode an Ethereum tx receipt as RLP:

      receipt = rlp([status, cumulative_gas_used,
                     logs_bloom (256 B), logs])

    This is the encoder side of PR-K152 `receipt_extract_logs_bloom`,
    and the input to receipts-trie / receipts-root computation.
    For typed receipts (EIP-2718), the caller prepends the
    `0x<type>` byte to the output of this helper; the wire-format
    typed receipt is `type_byte || rlp(inner)`.

    Algorithm:
      1. Write status (u64) at receipt_pl_buf[0..]    via K155.
      2. Write cumulative_gas (u64) at next slot      via K155.
      3. Write logs_bloom (256 B as RLP string) at
         next slot                                    via K128.
      4. Copy logs_rlp (pre-encoded list) verbatim    (memcpy).
      5. Compute total payload length.
      6. Write outer list prefix to output[0..]       via K129.
      7. Copy receipt_pl_buf[..total_payload] to
         output[prefix_len..].

    Composes:
      - PR-K155 `rlp_encode_u64`        -- status / gas
      - PR-K128 `rlp_encode_bytes`      -- logs_bloom
      - PR-K129 `rlp_encode_list_prefix`-- outer list prefix

    Calling convention:
      a0 (input)  : status (u64)
      a1 (input)  : cumulative_gas_used (u64)
      a2 (input)  : logs_bloom ptr (exactly 256 bytes)
      a3 (input)  : logs_rlp ptr (pre-encoded list, copied verbatim)
      a4 (input)  : logs_rlp byte length
      a5 (input)  : output buffer ptr
      a6 (input)  : u64 out length ptr (total bytes written)
      ra (input)  : return
      a0 (output) : 0 (always succeeds).

    Uses a 16 KiB scratch buffer `re_payload_buf` in `.data` for
    the intermediate payload. Should comfortably hold mainnet
    receipt payloads (logs_bloom is 257 RLP bytes, status/gas
    add <= 18 bytes, logs section is variable but typically
    KBs at most). -/
def receiptEncodeFunction : String :=
  "receipt_encode:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # status\n" ++
  "  mv s1, a1                   # cumulative_gas\n" ++
  "  mv s2, a2                   # bloom ptr\n" ++
  "  mv s3, a3                   # logs_rlp ptr\n" ++
  "  mv s4, a4                   # logs_rlp len\n" ++
  "  mv s5, a5                   # output ptr\n" ++
  "  mv s6, a6                   # out_length ptr\n" ++
  "  # The running cursor (payload offset within re_payload_buf) is\n" ++
  "  # stashed to `re_cursor` across `jal` calls since t-registers are\n" ++
  "  # caller-saved and the encode helpers clobber them.\n" ++
  "  la t0, re_cursor; sd zero, 0(t0)\n" ++
  "  # ---- Step 1: encode status into re_payload_buf[0..] ----\n" ++
  "  mv a0, s0\n" ++
  "  la a1, re_payload_buf\n" ++
  "  la a2, re_field_len\n" ++
  "  jal ra, rlp_encode_u64\n" ++
  "  la t0, re_field_len; ld t1, 0(t0)         # status_len\n" ++
  "  la t0, re_cursor; sd t1, 0(t0)            # cursor = status_len\n" ++
  "  # ---- Step 2: encode cumulative_gas at re_payload_buf[cursor] ----\n" ++
  "  la t0, re_cursor; ld t2, 0(t0)\n" ++
  "  mv a0, s1\n" ++
  "  la a1, re_payload_buf; add a1, a1, t2\n" ++
  "  la a2, re_field_len\n" ++
  "  jal ra, rlp_encode_u64\n" ++
  "  la t0, re_field_len; ld t1, 0(t0)         # gas_len\n" ++
  "  la t0, re_cursor; ld t2, 0(t0)\n" ++
  "  add t2, t2, t1\n" ++
  "  la t0, re_cursor; sd t2, 0(t0)\n" ++
  "  # ---- Step 3: encode bloom (256 B) ----\n" ++
  "  mv a0, s2; li a1, 256\n" ++
  "  la a2, re_payload_buf; add a2, a2, t2\n" ++
  "  la a3, re_field_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, re_field_len; ld t1, 0(t0)         # bloom_enc_len\n" ++
  "  la t0, re_cursor; ld t2, 0(t0)\n" ++
  "  add t2, t2, t1\n" ++
  "  # ---- Step 4: copy logs_rlp verbatim ----\n" ++
  "  la t3, re_payload_buf; add t3, t3, t2     # dst\n" ++
  "  mv t4, s3                                 # src\n" ++
  "  mv t5, s4                                 # remaining bytes\n" ++
  ".Lre_logs_cp:\n" ++
  "  beqz t5, .Lre_logs_done\n" ++
  "  lbu t6, 0(t4)\n" ++
  "  sb t6, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t5, t5, -1\n" ++
  "  j .Lre_logs_cp\n" ++
  ".Lre_logs_done:\n" ++
  "  add t2, t2, s4                            # total payload len\n" ++
  "  # Stash total_payload before the next jal clobbers caller-saved t2.\n" ++
  "  la t0, re_total_payload; sd t2, 0(t0)\n" ++
  "  # ---- Step 5: write outer list prefix at output[0..] ----\n" ++
  "  mv a0, t2; mv a1, s5\n" ++
  "  la a2, re_field_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  la t0, re_field_len; ld t1, 0(t0)        # outer_prefix_len\n" ++
  "  # ---- Step 6: copy re_payload_buf[..total_payload] to output[prefix_len..] ----\n" ++
  "  # Total payload was last stashed in t2; restore via .data\n" ++
  "  # Actually we lost t2 across jal. Re-derive: total_payload =\n" ++
  "  # bytes_written - bytes_p, but cleaner to re-compute it from\n" ++
  "  # re_payload_buf metadata. Save total_payload before jal next time.\n" ++
  "  # Use the stashed value: we'll save t2 to .data BEFORE the\n" ++
  "  # rlp_encode_list_prefix call.\n" ++
  "  # (Fixed by re-reading the saved payload total below.)\n" ++
  "  la t0, re_total_payload; ld t2, 0(t0)\n" ++
  "  add t3, s5, t1                            # dst = output + prefix_len\n" ++
  "  la t4, re_payload_buf                     # src\n" ++
  "  mv t5, t2                                 # remaining\n" ++
  ".Lre_body_cp:\n" ++
  "  beqz t5, .Lre_body_done\n" ++
  "  lbu t6, 0(t4)\n" ++
  "  sb t6, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t5, t5, -1\n" ++
  "  j .Lre_body_cp\n" ++
  ".Lre_body_done:\n" ++
  "  # total_written = outer_prefix_len + total_payload\n" ++
  "  add t1, t1, t2\n" ++
  "  sd t1, 0(s6)\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_receipt_encode`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : status (u64 LE)
      bytes  8..16 : cumulative_gas (u64 LE)
      bytes 16..272: logs_bloom (256 bytes)
      bytes 272..280: logs_rlp_len (u64 LE)
      bytes 280..   : logs_rlp
    Output layout (256 B ziskemu cap):
      bytes  0.. 8 : status (always 0)
      bytes  8..16 : encoded receipt total length
      bytes 16..   : encoded receipt bytes (truncated to fit) -/
def ziskReceiptEncodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)                # status\n" ++
  "  ld a1, 16(a7)               # cumulative_gas\n" ++
  "  addi a2, a7, 24             # logs_bloom ptr (256 B)\n" ++
  "  ld a4, 280(a7)              # logs_rlp_len\n" ++
  "  addi a3, a7, 288            # logs_rlp ptr\n" ++
  "  li a5, 0xa0010010           # output ptr\n" ++
  "  li a6, 0xa0010008           # out length ptr\n" ++
  "  jal ra, receipt_encode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lre_pdone\n" ++
  rlpEncodeU64Function ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  receiptEncodeFunction ++ "\n" ++
  ".Lre_pdone:"

def ziskReceiptEncodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "re_field_len:\n" ++
  "  .zero 8\n" ++
  "re_cursor:\n" ++
  "  .zero 8\n" ++
  "re_total_payload:\n" ++
  "  .zero 8\n" ++
  "re_payload_buf:\n" ++
  "  .zero 16384"

def ziskReceiptEncodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskReceiptEncodePrologue
  dataAsm     := ziskReceiptEncodeDataSection
}

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
  let hardCap := 5150
  let paths := [
    "EvmAsm/Codegen/Programs.lean",
    "EvmAsm/Codegen/Programs/Address.lean",
    "EvmAsm/Codegen/Programs/Block.lean",
    "EvmAsm/Codegen/Programs/Bloom.lean",
    "EvmAsm/Codegen/Programs/Evm.lean",
    "EvmAsm/Codegen/Programs/HashBridge.lean",
    "EvmAsm/Codegen/Programs/Header.lean",
    "EvmAsm/Codegen/Programs/Mpt.lean",
    "EvmAsm/Codegen/Programs/RlpRead.lean",
    "EvmAsm/Codegen/Programs/Ssz.lean",
    "EvmAsm/Codegen/Programs/Tx.lean",
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
