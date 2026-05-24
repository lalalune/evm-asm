/-
  EvmAsm.Codegen.Programs.Address

  Ethereum address-derivation helpers extracted from
  `EvmAsm.Codegen.Programs` per the file-size hard cap. Hosts the
  three canonical address builders:

    K99   address_from_pubkey
    K126  address_compute_create2
    K127  address_compute_create

  All three are `keccak256`-based; the new module only needs the
  `Rv64.Program` core, `Codegen.Layout`, and the `HashBridge` for
  the keccak intrinsic wrapper.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## address_from_pubkey -- PR-K99

    Compute an Ethereum address from an uncompressed secp256k1
    public key:

      address = keccak256(pubkey_x ‖ pubkey_y)[12:32]   (20 bytes)

    This is the canonical 20-byte address derivation used by:
    - secp256k1 ecrecover (the final step after curve recovery)
    - CREATE / CREATE2 address computation (with different inputs)
    - Account address generation from a key

    Input layout (64 bytes, big-endian):
       0..32  : X coordinate
      32..64  : Y coordinate

    Output (20 bytes): the rightmost 20 bytes of keccak256 of the
    above. The leading 12 bytes of the digest are discarded.

    Composes PR-K3 `zkvm_keccak256`. Uses 32 bytes of `.data`
    scratch (`afp_digest`).

    Calling convention:
      a0 (input)  : pubkey ptr (64 bytes, x ‖ y BE)
      a1 (input)  : 20-byte output ptr
      ra (input)  : return
      a0 (output) : 0 (always succeeds; keccak is total). -/
def addressFromPubkeyFunction : String :=
  "address_from_pubkey:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  mv s0, a1                   # output ptr (stash)\n" ++
  "  # keccak256(pubkey, 64) → afp_digest\n" ++
  "  li a1, 64\n" ++
  "  la a2, afp_digest\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # Copy digest[12..32] (20 bytes) to output.\n" ++
  "  la t0, afp_digest\n" ++
  "  # 20 bytes = 8 + 8 + 4. Loads may be unaligned (offset 12).\n" ++
  "  ld t1, 12(t0); sd t1,  0(s0)\n" ++
  "  ld t1, 20(t0); sd t1,  8(s0)\n" ++
  "  lwu t1, 28(t0); sw t1, 16(s0)\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_address_from_pubkey`: probe BuildUnit. Reads 64 bytes
    of pubkey from host input, writes (status, 20-byte address +
    4 byte padding) to OUTPUT (32 bytes total). -/
def ziskAddressFromPubkeyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 16             # pubkey ptr\n" ++
  "  li a1, 0xa0010008           # 20B address output\n" ++
  "  sd zero, 0(a1); sd zero, 8(a1); sw zero, 16(a1)\n" ++
  "  jal ra, address_from_pubkey\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lafp_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  addressFromPubkeyFunction ++ "\n" ++
  ".Lafp_pdone:"

def ziskAddressFromPubkeyDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "afp_digest:\n" ++
  "  .zero 32"

def ziskAddressFromPubkeyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAddressFromPubkeyPrologue
  dataAsm     := ziskAddressFromPubkeyDataSection
}

/-! ## address_compute_create2 -- PR-K126

    Compute the CREATE2 contract address per EIP-1014:

      address = keccak256(0xff || sender || salt || keccak256(init_code))[12:32]

    Preimage is exactly 85 bytes laid out as:
       0       :  0xff (single byte marker)
       1..21   :  sender (20 bytes)
       21..53  :  salt (32 bytes, BE)
       53..85  :  inner_hash = keccak256(init_code) (32 bytes)

    Used by the EVM's `CREATE2` opcode and by off-chain tooling
    that needs deterministic deploy addresses. Sister primitive to
    PR-K99 `address_from_pubkey` (the ECRECOVER trailing step) and
    a future `address_compute_create` (for the non-deterministic
    nonce-based form).

    Composes PR-K3 `zkvm_keccak256` (called twice — once over
    `init_code` and once over the 85-byte preimage).

    Calling convention:
      a0 (input)  : sender ptr (20 B, big-endian)
      a1 (input)  : salt ptr   (32 B, big-endian)
      a2 (input)  : init_code ptr
      a3 (input)  : init_code byte length
      a4 (input)  : 20-byte output ptr
      ra (input)  : return
      a0 (output) : 0 (always succeeds; keccak is total).

    Uses 85 + 32 + 32 = 149 bytes of `.data` scratch
    (`ac2_preimage` 85 B + `ac2_inner_digest` 32 B + `ac2_outer_digest`
    32 B), plus the keccak sponge state (`zk3_state`, 200 B). -/
def addressComputeCreate2Function : String :=
  "address_compute_create2:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # sender ptr\n" ++
  "  mv s1, a1                   # salt ptr\n" ++
  "  mv s4, a4                   # output ptr (stash)\n" ++
  "  # Step 1: inner = keccak256(init_code).\n" ++
  "  # init_code ptr/len already in (a2, a3); rotate into (a0, a1).\n" ++
  "  mv a0, a2\n" ++
  "  mv a1, a3\n" ++
  "  la a2, ac2_inner_digest\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # Step 2: build preimage.\n" ++
  "  la s2, ac2_preimage\n" ++
  "  li t0, 0xff\n" ++
  "  sb t0, 0(s2)\n" ++
  "  # Copy sender 20 B → preimage[1..21] (8 + 8 + 4).\n" ++
  "  ld t0,  0(s0); sd t0,  1(s2)\n" ++
  "  ld t0,  8(s0); sd t0,  9(s2)\n" ++
  "  lwu t0, 16(s0); sw t0, 17(s2)\n" ++
  "  # Copy salt 32 B → preimage[21..53] (8 × 4).\n" ++
  "  ld t0,  0(s1); sd t0, 21(s2)\n" ++
  "  ld t0,  8(s1); sd t0, 29(s2)\n" ++
  "  ld t0, 16(s1); sd t0, 37(s2)\n" ++
  "  ld t0, 24(s1); sd t0, 45(s2)\n" ++
  "  # Copy inner digest 32 B → preimage[53..85].\n" ++
  "  la t1, ac2_inner_digest\n" ++
  "  ld t0,  0(t1); sd t0, 53(s2)\n" ++
  "  ld t0,  8(t1); sd t0, 61(s2)\n" ++
  "  ld t0, 16(t1); sd t0, 69(s2)\n" ++
  "  ld t0, 24(t1); sd t0, 77(s2)\n" ++
  "  # Step 3: outer = keccak256(preimage, 85).\n" ++
  "  mv a0, s2\n" ++
  "  li a1, 85\n" ++
  "  la a2, ac2_outer_digest\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # Step 4: copy outer[12..32] (20 B) → out.\n" ++
  "  la t0, ac2_outer_digest\n" ++
  "  ld t1, 12(t0); sd t1,  0(s4)\n" ++
  "  ld t1, 20(t0); sd t1,  8(s4)\n" ++
  "  lwu t1, 28(t0); sw t1, 16(s4)\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_address_compute_create2`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : init_code length
      bytes  8..28 : sender (20 bytes)
      bytes 28..60 : salt (32 bytes)
      bytes 60..   : init_code bytes
    Output layout:
      bytes  0.. 8 : status
      bytes  8..28 : 20-byte address
      bytes 28..32 : padding -/
def ziskAddressComputeCreate2Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a3, 8(a5)                # init_code length\n" ++
  "  addi a0, a5, 16             # sender ptr\n" ++
  "  addi a1, a5, 36             # salt ptr\n" ++
  "  addi a2, a5, 68             # init_code ptr\n" ++
  "  li a4, 0xa0010008           # 20B address output\n" ++
  "  sd zero, 0(a4); sd zero, 8(a4); sw zero, 16(a4)\n" ++
  "  jal ra, address_compute_create2\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lac2_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  addressComputeCreate2Function ++ "\n" ++
  ".Lac2_pdone:"

def ziskAddressComputeCreate2DataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "ac2_inner_digest:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ac2_outer_digest:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ac2_preimage:\n" ++
  "  .zero 88"  -- 85 + 3 padding for 8-byte alignment of next

def ziskAddressComputeCreate2ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAddressComputeCreate2Prologue
  dataAsm     := ziskAddressComputeCreate2DataSection
}

/-! ## address_compute_create -- PR-K127

    Compute the CREATE contract address (non-deterministic form):

      address = keccak256(rlp.encode([sender, nonce]))[12:32]

    Used by:
    - the EVM's `CREATE` opcode (when a contract creates another)
    - the tx-level contract-creation path (when `tx.to == empty`),
      where `sender` is the tx sender (recovered via ECRECOVER)
      and `nonce` is the sender's pre-tx account nonce.

    Sister primitive to PR-K126 `address_compute_create2` (the
    deterministic salt-based form). EIP-2681 caps `nonce` at
    `2^64 - 1` so the u64 input always fits the RLP encoding's
    1+8-byte upper bound.

    RLP encoding of `[sender, nonce]`:
      [0]   : list prefix = 0xc0 + payload_len
      [1]   : sender prefix = 0x94 (20-byte string marker)
      [2..22] : sender 20 bytes
      [22..] : nonce RLP, one of:
        nonce == 0       : single byte 0x80
        nonce in 1..127  : single byte = nonce
        nonce >= 128     : 0x80 + bc, then `bc` BE-encoded bytes,
                           where `bc ∈ {1..8}` (= effective byte
                           count, no leading zeros)

    Payload (sender_rlp + nonce_rlp) is at most 21 + 9 = 30 bytes,
    so the list prefix is always the short form `0xc0..0xde`.

    Composes PR-K3 `zkvm_keccak256`. Uses 32 + 8 + 32 bytes of
    `.data` scratch (`ac_buffer` for the RLP, `ac_nonce_be` for
    long-form byte counting, `ac_digest` for keccak output).

    Calling convention:
      a0 (input)  : sender ptr (20 B, big-endian)
      a1 (input)  : nonce (u64)
      a2 (input)  : 20-byte output ptr
      ra (input)  : return
      a0 (output) : 0 (always succeeds; keccak is total). -/
def addressComputeCreateFunction : String :=
  "address_compute_create:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # sender ptr\n" ++
  "  mv s1, a1                   # nonce\n" ++
  "  mv s2, a2                   # output ptr\n" ++
  "  la t0, ac_buffer\n" ++
  "  li t1, 0x94\n" ++
  "  sb t1, 1(t0)\n" ++
  "  ld t1,  0(s0); sd t1,  2(t0)\n" ++
  "  ld t1,  8(s0); sd t1, 10(t0)\n" ++
  "  lwu t1, 16(s0); sw t1, 18(t0)\n" ++
  "  beqz s1, .Lac_nonce_zero\n" ++
  "  li t1, 128\n" ++
  "  bgeu s1, t1, .Lac_nonce_long\n" ++
  "  # nonce in 1..127: single byte = nonce.\n" ++
  "  sb s1, 22(t0)\n" ++
  "  li t2, 1\n" ++
  "  j .Lac_have_nonce_len\n" ++
  ".Lac_nonce_zero:\n" ++
  "  li t1, 0x80\n" ++
  "  sb t1, 22(t0)\n" ++
  "  li t2, 1\n" ++
  "  j .Lac_have_nonce_len\n" ++
  ".Lac_nonce_long:\n" ++
  "  la t3, ac_nonce_be\n" ++
  "  srli t4, s1, 56; sb t4, 0(t3)\n" ++
  "  srli t4, s1, 48; sb t4, 1(t3)\n" ++
  "  srli t4, s1, 40; sb t4, 2(t3)\n" ++
  "  srli t4, s1, 32; sb t4, 3(t3)\n" ++
  "  srli t4, s1, 24; sb t4, 4(t3)\n" ++
  "  srli t4, s1, 16; sb t4, 5(t3)\n" ++
  "  srli t4, s1,  8; sb t4, 6(t3)\n" ++
  "  sb s1, 7(t3)\n" ++
  "  li t4, 0                    # leading zero count\n" ++
  ".Lac_find_nz:\n" ++
  "  add t5, t3, t4\n" ++
  "  lbu t6, 0(t5)\n" ++
  "  bnez t6, .Lac_found\n" ++
  "  addi t4, t4, 1\n" ++
  "  j .Lac_find_nz\n" ++
  ".Lac_found:\n" ++
  "  li t5, 8\n" ++
  "  sub t2, t5, t4\n" ++
  "  # Write prefix byte 0x80 + byte_count at offset 22.\n" ++
  "  addi t5, t2, 0x80\n" ++
  "  sb t5, 22(t0)\n" ++
  "  addi t6, t0, 23             # dst cursor\n" ++
  "  add t5, t3, t4              # src cursor\n" ++
  "  mv t1, t2                   # remaining\n" ++
  ".Lac_copy_nz:\n" ++
  "  beqz t1, .Lac_have_nonce_len_pp\n" ++
  "  lbu t4, 0(t5)\n" ++
  "  sb t4, 0(t6)\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t6, t6, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lac_copy_nz\n" ++
  ".Lac_have_nonce_len_pp:\n" ++
  "  # In the long path, t2 = data byte count. Add 1 for the prefix.\n" ++
  "  addi t2, t2, 1\n" ++
  ".Lac_have_nonce_len:\n" ++
  "  # payload_len = 21 (sender_rlp) + nonce_rlp_len (t2)\n" ++
  "  addi t1, t2, 21\n" ++
  "  # list prefix = 0xc0 + payload_len\n" ++
  "  addi t3, t1, 0xc0\n" ++
  "  sb t3, 0(t0)\n" ++
  "  # Total length = 1 + payload_len = 22 + nonce_rlp_len.\n" ++
  "  addi a1, t2, 22\n" ++
  "  mv a0, t0\n" ++
  "  la a2, ac_digest\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  la t0, ac_digest\n" ++
  "  ld t1, 12(t0); sd t1,  0(s2)\n" ++
  "  ld t1, 20(t0); sd t1,  8(s2)\n" ++
  "  lwu t1, 28(t0); sw t1, 16(s2)\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_address_compute_create`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : nonce (u64)
      bytes  8..28 : sender (20 bytes)
    Output layout:
      bytes  0.. 8 : status
      bytes  8..28 : 20-byte address
      bytes 28..32 : padding -/
def ziskAddressComputeCreatePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # nonce\n" ++
  "  addi a0, a3, 16             # sender ptr\n" ++
  "  li a2, 0xa0010008           # 20B address output\n" ++
  "  sd zero, 0(a2); sd zero, 8(a2); sw zero, 16(a2)\n" ++
  "  jal ra, address_compute_create\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lac_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  addressComputeCreateFunction ++ "\n" ++
  ".Lac_pdone:"

def ziskAddressComputeCreateDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "ac_buffer:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ac_nonce_be:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "ac_digest:\n" ++
  "  .zero 32"

def ziskAddressComputeCreateProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAddressComputeCreatePrologue
  dataAsm     := ziskAddressComputeCreateDataSection
}


end EvmAsm.Codegen
