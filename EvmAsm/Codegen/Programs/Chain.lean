/-
  EvmAsm.Codegen.Programs.Chain

  Chain-level header aggregators and validators carved out of
  `EvmAsm.Codegen.Programs.Header` per the file-size hard cap.
  Hosts:

    K196  chain_compute_total_gas_used
    K197  chain_extract_number_range
    K198  header_extract_basefee
    K199  chain_extract_basefee_range
    K200  chain_block_hashes_commitment
    K229  chain_validate_increasing_timestamps
    K230  chain_validate_consecutive_numbers
    K231  chain_compute_total_blob_gas

  All eight operate on an N-element header chain (or a single
  header in K198's case, kept here for adjacency with K199).
  They compose K20 / K34 RLP helpers plus K172
  `block_hash_from_header` (for K200), which remain in
  `Programs/Header.lean`. `Chain.lean` imports `Header.lean`.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.Header

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## chain_compute_total_gas_used -- PR-K196

    Aggregate `gas_used` (header field 10) across an N-element
    header chain into a single u64 sum. Useful for chain-state
    commitments and protocol-level invariants such as
    \"this chain segment burned at most G gas total\".

    No chain validation is performed here -- the caller is
    responsible for combining this with K175 (or K195) for
    chain integrity. K196 is purely an aggregator over the
    headers; the inputs and accumulator math are kept in plain
    u64, so the sum saturates / wraps modulo 2^64 like any
    RISC-V add.

    For real mainnet blocks, gas_used <= ~30M and N <= ~256 in
    a single witness; the sum stays well below 2^64.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr (u64[N])
      a2 (input)  : headers ptr (concatenated)
      a3 (input)  : u64 out (total_gas_used; running sum)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse error on some header (sum is partial,
            up to the failing header)
        2 : a header's gas_used field exceeds 8 bytes BE -/
def chainComputeTotalGasUsedFunction : String :=
  "chain_compute_total_gas_used:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # N\n" ++
  "  mv s1, a1                   # header_lengths ptr\n" ++
  "  mv s2, a2                   # headers ptr\n" ++
  "  mv s3, a3                   # out ptr\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0                    # i = 0\n" ++
  "  beqz s0, .Lccgu_done\n" ++
  ".Lccgu_loop:\n" ++
  "  beq s4, s0, .Lccgu_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)                # header_len\n" ++
  "  mv a0, s2                   # header_ptr\n" ++
  "  li a2, 10                   # field 10 = gas_used\n" ++
  "  la a3, ccgu_field\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lccgu_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lccgu_size_fail\n" ++
  "  # Accumulate\n" ++
  "  la t0, ccgu_field; ld t1, 0(t0)\n" ++
  "  ld t2, 0(s3)\n" ++
  "  add t2, t2, t1\n" ++
  "  sd t2, 0(s3)\n" ++
  "  # Advance to next header\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lccgu_loop\n" ++
  ".Lccgu_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lccgu_ret\n" ++
  ".Lccgu_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lccgu_ret\n" ++
  ".Lccgu_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lccgu_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_chain_compute_total_gas_used`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : N
      bytes  8..8+8N : header_lengths
      bytes  8+8N.. : concatenated header RLPs
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : total_gas_used -/
def ziskChainComputeTotalGasUsedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)                # N\n" ++
  "  addi a1, a7, 16             # header_lengths ptr\n" ++
  "  slli t0, a0, 3              # 8*N\n" ++
  "  add a2, a1, t0              # headers ptr\n" ++
  "  li a3, 0xa0010008           # total_gas_used out\n" ++
  "  jal ra, chain_compute_total_gas_used\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccgu_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainComputeTotalGasUsedFunction ++ "\n" ++
  ".Lccgu_pdone:"

def ziskChainComputeTotalGasUsedDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ccgu_field:\n" ++
  "  .zero 8"

def ziskChainComputeTotalGasUsedProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainComputeTotalGasUsedPrologue
  dataAsm     := ziskChainComputeTotalGasUsedDataSection
}

/-! ## chain_extract_number_range -- PR-K197

    Extract `(min_number, max_number)` from an N-element header
    chain. With K175 validated parent-hash invariants, the chain
    has strictly increasing numbers, so this is simply
    `(headers[0].number, headers[N-1].number)`. We return both
    edges so callers can verify `max - min + 1 == N` (the chain
    is dense) or directly use the range as a chain-segment
    identifier.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : u64 out (min_number)
      a4 (input)  : u64 out (max_number)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse failure on some header
        3 : a header's number field exceeds 8 bytes BE -/
def chainExtractNumberRangeFunction : String :=
  "chain_extract_number_range:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # N\n" ++
  "  mv s1, a1                   # header_lengths\n" ++
  "  mv s2, a2                   # headers\n" ++
  "  mv s3, a3                   # min out\n" ++
  "  mv s4, a4                   # max out\n" ++
  "  beqz s0, .Lcenr_empty\n" ++
  "  # min = headers[0].number\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  li a2, 8                    # field 8 = number\n" ++
  "  mv a3, s3\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcenr_propagate\n" ++
  "  # Advance to last header: skip the first (N-1) headers\n" ++
  "  mv t1, s2\n" ++
  "  mv t2, s1\n" ++
  "  addi t3, s0, -1             # iterations = N-1\n" ++
  ".Lcenr_skip:\n" ++
  "  beqz t3, .Lcenr_at_last\n" ++
  "  ld t4, 0(t2)\n" ++
  "  add t1, t1, t4\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lcenr_skip\n" ++
  ".Lcenr_at_last:\n" ++
  "  ld a1, 0(t2)                # length of last header\n" ++
  "  mv a0, t1\n" ++
  "  li a2, 8\n" ++
  "  mv a3, s4\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcenr_propagate\n" ++
  "  li a0, 0\n" ++
  "  j .Lcenr_ret\n" ++
  ".Lcenr_empty:\n" ++
  "  li a0, 1\n" ++
  "  j .Lcenr_ret\n" ++
  ".Lcenr_propagate:\n" ++
  "  addi a0, a0, 1              # remap rlp_field_to_u64 1/2 -> 2/3\n" ++
  ".Lcenr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_chain_extract_number_range`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : N
      bytes  8..8+8N : header_lengths
      bytes  8+8N.. : concatenated headers
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : min_number
      bytes 16..24 : max_number -/
def ziskChainExtractNumberRangePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)                # N\n" ++
  "  addi a1, a7, 16             # header_lengths\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0              # headers\n" ++
  "  li a3, 0xa0010008           # min out\n" ++
  "  li a4, 0xa0010010           # max out\n" ++
  "  jal ra, chain_extract_number_range\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcenr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainExtractNumberRangeFunction ++ "\n" ++
  ".Lcenr_pdone:"

def ziskChainExtractNumberRangeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskChainExtractNumberRangeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainExtractNumberRangePrologue
  dataAsm     := ziskChainExtractNumberRangeDataSection
}

/-! ## header_extract_basefee -- PR-K198

    Extract `base_fee_per_gas` (field 15, present from London
    onwards) from a header RLP. Returns the value as a u64; the
    EIP-1559 base_fee is bounded by `2^256-1` in principle but
    in practice never exceeds u64 in any chain we care about.
    Callers that need the full uint256 form should use the more
    general `rlp_field_to_u256` (not yet implemented) instead.

    Field index 15 is the **first** post-London field; on
    pre-London headers (`len(fields) <= 15`) the call yields
    a parse-failure status.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : u64 out (base_fee_per_gas)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 15 missing (pre-London)
        2 : base_fee field exceeds 8 bytes BE -/
def headerExtractBasefeeFunction : String :=
  "header_extract_basefee:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  # rlp_field_to_u64(a0=header_ptr, a1=len, a2=15, a3=output_ptr)\n" ++
  "  mv a3, a2                   # output ptr (caller-supplied) -> a3\n" ++
  "  li a2, 15                   # field index = 15 (base_fee)\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_header_extract_basefee`: probe BuildUnit.
    Input layout:
      bytes 0..8  : header_rlp_len
      bytes 8..   : header_rlp
    Output layout:
      bytes 0..8  : status
      bytes 8..16 : base_fee_per_gas -/
def ziskHeaderExtractBasefeePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_rlp_len\n" ++
  "  addi a0, a7, 16             # header_rlp ptr\n" ++
  "  li a2, 0xa0010008           # base_fee out\n" ++
  "  jal ra, header_extract_basefee\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lheb_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractBasefeeFunction ++ "\n" ++
  ".Lheb_pdone:"

def ziskHeaderExtractBasefeeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractBasefeeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractBasefeePrologue
  dataAsm     := ziskHeaderExtractBasefeeDataSection
}

/-! ## chain_extract_basefee_range -- PR-K199

    Walk an N-element header chain and compute `(min, max)` of
    `base_fee_per_gas` (field 15). London+ only. Useful for
    chain-level base_fee bounds analysis.

    Returns vacuous `(0, 0)` on N == 0.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : u64 out (min)
      a4 (input)  : u64 out (max)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : a header parse failure (e.g., pre-London header)
        2 : a base_fee field exceeds 8 bytes BE -/
def chainExtractBasefeeRangeFunction : String :=
  "chain_extract_basefee_range:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # N\n" ++
  "  mv s1, a1                   # header_lengths\n" ++
  "  mv s2, a2                   # headers\n" ++
  "  mv s3, a3                   # min out\n" ++
  "  mv s4, a4                   # max out\n" ++
  "  sd zero, 0(s3)\n" ++
  "  sd zero, 0(s4)\n" ++
  "  beqz s0, .Lcebr_done\n" ++
  "  # Initialize min/max with headers[0].basefee\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_basefee\n" ++
  "  bnez a0, .Lcebr_ret\n" ++
  "  ld t0, 0(s3)\n" ++
  "  sd t0, 0(s4)                # max = min = first value\n" ++
  "  # Walk remaining headers\n" ++
  "  ld t1, 0(s1)\n" ++
  "  add t2, s2, t1              # next header ptr\n" ++
  "  addi t3, s1, 8              # next length ptr\n" ++
  "  li t4, 1                    # i\n" ++
  ".Lcebr_loop:\n" ++
  "  beq t4, s0, .Lcebr_done\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, t2\n" ++
  "  la a2, cebr_cur\n" ++
  "  # Stash t2/t3/t4 in s-regs since rlp_field_to_u64 will\n" ++
  "  # save/restore s0..s4 around it; pin them here.\n" ++
  "  # Actually simpler: keep t2/t3/t4 across the call by\n" ++
  "  # using callee-saved regs. We'll re-derive them after.\n" ++
  "  jal ra, header_extract_basefee\n" ++
  "  bnez a0, .Lcebr_ret\n" ++
  "  # cur < min -> update min; cur > max -> update max\n" ++
  "  la t0, cebr_cur; ld t1, 0(t0)\n" ++
  "  ld t5, 0(s3)\n" ++
  "  bgeu t1, t5, .Lcebr_skip_min\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lcebr_skip_min:\n" ++
  "  ld t5, 0(s4)\n" ++
  "  bleu t1, t5, .Lcebr_skip_max\n" ++
  "  sd t1, 0(s4)\n" ++
  ".Lcebr_skip_max:\n" ++
  "  # Re-derive iteration state. Since we don't have callee-\n" ++
  "  # saved scratch left (s0..s4 all used), maintain t-regs\n" ++
  "  # before the call by stashing on .data.\n" ++
  "  la t0, cebr_i; ld t4, 0(t0)\n" ++
  "  la t0, cebr_hdr_ptr; ld t2, 0(t0)\n" ++
  "  la t0, cebr_len_ptr; ld t3, 0(t0)\n" ++
  "  ld t1, 0(t3)\n" ++
  "  add t2, t2, t1\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t4, t4, 1\n" ++
  "  la t0, cebr_i;        sd t4, 0(t0)\n" ++
  "  la t0, cebr_hdr_ptr;  sd t2, 0(t0)\n" ++
  "  la t0, cebr_len_ptr;  sd t3, 0(t0)\n" ++
  "  j .Lcebr_loop\n" ++
  ".Lcebr_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcebr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_chain_extract_basefee_range`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : N
      bytes  8..8+8N : header_lengths
      bytes  8+8N.. : concatenated headers
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : min_basefee
      bytes 16..24 : max_basefee -/
def ziskChainExtractBasefeeRangePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)                # N\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  # Pre-init iteration scratch only when N > 0.\n" ++
  "  beqz a0, .Lcebr_skip_init\n" ++
  "  ld t1, 0(a1)                # first header_len\n" ++
  "  add t2, a2, t1              # second header ptr\n" ++
  "  addi t3, a1, 8\n" ++
  "  la t0, cebr_hdr_ptr; sd t2, 0(t0)\n" ++
  "  la t0, cebr_len_ptr; sd t3, 0(t0)\n" ++
  "  la t0, cebr_i; li t4, 1; sd t4, 0(t0)\n" ++
  ".Lcebr_skip_init:\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_extract_basefee_range\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcebr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractBasefeeFunction ++ "\n" ++
  chainExtractBasefeeRangeFunction ++ "\n" ++
  ".Lcebr_pdone:"

def ziskChainExtractBasefeeRangeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cebr_cur:\n" ++
  "  .zero 8\n" ++
  "cebr_hdr_ptr:\n" ++
  "  .zero 8\n" ++
  "cebr_len_ptr:\n" ++
  "  .zero 8\n" ++
  "cebr_i:\n" ++
  "  .zero 8"

def ziskChainExtractBasefeeRangeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainExtractBasefeeRangePrologue
  dataAsm     := ziskChainExtractBasefeeRangeDataSection
}

/-! ## chain_block_hashes_commitment -- PR-K200

    Compute a 32-byte commitment over the block_hashes of an
    N-element header chain:

      commitment = keccak256( H[0] || H[1] || ... || H[N-1] )

    where `H[i] = keccak256(headers[i])`. This is the natural
    succinct commitment to a chain of block hashes, useful for
    bridges, light clients, and inter-prover commitments.

    For N == 0 the commitment is `keccak256("")` (the empty-
    string hash), which equals
    `0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470`.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : 32-byte output ptr (commitment)
      ra (input)  : return
      a0 (output) :
        0 : success

    Uses a scratch buffer (`cbhc_concat_buf`) of size 32*MAX_N
    bytes for the intermediate concatenation. MAX_N is fixed
    at 64 in this implementation (sufficient for typical
    stateless witnesses of ~32 headers). -/
def chainBlockHashesCommitmentFunction : String :=
  "chain_block_hashes_commitment:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # N\n" ++
  "  mv s1, a1                   # header_lengths\n" ++
  "  mv s2, a2                   # headers\n" ++
  "  mv s3, a3                   # output ptr\n" ++
  "  la s4, cbhc_concat_buf      # concat buffer start\n" ++
  "  # Walk and hash each header into the concat buffer.\n" ++
  "  li t6, 0                    # i = 0\n" ++
  "  mv t5, s2                   # current header ptr\n" ++
  "  la t4, cbhc_concat_buf\n" ++
  ".Lcbhc_loop:\n" ++
  "  beq t6, s0, .Lcbhc_done\n" ++
  "  # Stash iteration state into .data\n" ++
  "  la t0, cbhc_i; sd t6, 0(t0)\n" ++
  "  la t0, cbhc_hdr_ptr; sd t5, 0(t0)\n" ++
  "  la t0, cbhc_concat_cursor; sd t4, 0(t0)\n" ++
  "  slli t0, t6, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)                # header_len\n" ++
  "  mv a0, t5\n" ++
  "  mv a2, t4                   # write into concat buf\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  # Reload iteration state\n" ++
  "  la t0, cbhc_i; ld t6, 0(t0)\n" ++
  "  la t0, cbhc_hdr_ptr; ld t5, 0(t0)\n" ++
  "  la t0, cbhc_concat_cursor; ld t4, 0(t0)\n" ++
  "  # Advance: concat += 32; header += header_len; i += 1\n" ++
  "  slli t0, t6, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add t5, t5, t1\n" ++
  "  addi t4, t4, 32\n" ++
  "  addi t6, t6, 1\n" ++
  "  j .Lcbhc_loop\n" ++
  ".Lcbhc_done:\n" ++
  "  # commit = keccak256(concat buf, 32*N) -> output\n" ++
  "  la a0, cbhc_concat_buf\n" ++
  "  slli a1, s0, 5              # 32*N\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_chain_block_hashes_commitment`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : N
      bytes  8..8+8N : header_lengths
      bytes  8+8N.. : concatenated headers
    Output layout:
      bytes 0..32 : 32-byte commitment -/
def ziskChainBlockHashesCommitmentPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)                # N\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010000           # 32 B commitment out\n" ++
  "  jal ra, chain_block_hashes_commitment\n" ++
  "  j .Lcbhc_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  chainBlockHashesCommitmentFunction ++ "\n" ++
  ".Lcbhc_pdone:"

def ziskChainBlockHashesCommitmentDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "cbhc_concat_buf:\n" ++
  "  .zero 2048                  # 32 * 64 = 2048\n" ++
  "cbhc_i:\n" ++
  "  .zero 8\n" ++
  "cbhc_hdr_ptr:\n" ++
  "  .zero 8\n" ++
  "cbhc_concat_cursor:\n" ++
  "  .zero 8"

def ziskChainBlockHashesCommitmentProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainBlockHashesCommitmentPrologue
  dataAsm     := ziskChainBlockHashesCommitmentDataSection
}

/-! ## chain_validate_increasing_timestamps -- PR-K229

    Verify that an N-element header chain has strictly
    increasing `timestamp` fields: `headers[i+1].timestamp >
    headers[i].timestamp` for every adjacent pair. Pure
    timestamp-only check; no parent_hash / number / gas_limit
    invariants. The K174 pair check enforces this as part of
    the four-invariant bundle -- K229 is the tight standalone.

    Vacuous-true on N <= 1.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr (concatenated)
      a3 (input)  : u64 out (is_valid)
      a4 (input)  : u64 out (first_bad_index)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure on some header
        2 : timestamp field > 8 bytes BE on some header -/
def chainValidateIncreasingTimestampsFunction : String :=
  "chain_validate_increasing_timestamps:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3); sd zero, 0(s4)\n" ++
  "  li t0, 2\n" ++
  "  bltu s0, t0, .Lcvit_done\n" ++
  "  # Extract headers[0].timestamp into s5 (prev_ts)\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  li a2, 11\n" ++
  "  la a3, cvit_ts\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcvit_propagate\n" ++
  "  la t0, cvit_ts; ld s5, 0(t0)\n" ++
  "  # Walk: parent_ptr = headers[0]; for i in [0, N-1): parent=headers[i], child=headers[i+1]\n" ++
  "  ld t0, 0(s1)\n" ++
  "  add t1, s2, t0              # child_ptr starts at headers[1]\n" ++
  "  li t2, 1                    # i = 1\n" ++
  ".Lcvit_loop:\n" ++
  "  beq t2, s0, .Lcvit_done\n" ++
  "  la t0, cvit_iter_child; sd t1, 0(t0)\n" ++
  "  la t0, cvit_iter_i;     sd t2, 0(t0)\n" ++
  "  la t0, cvit_iter_prev;  sd s5, 0(t0)\n" ++
  "  slli t3, t2, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)                # header_len\n" ++
  "  mv a0, t1\n" ++
  "  li a2, 11\n" ++
  "  la a3, cvit_ts\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcvit_propagate\n" ++
  "  la t0, cvit_ts;          ld t3, 0(t0)\n" ++
  "  la t0, cvit_iter_prev;   ld t4, 0(t0)\n" ++
  "  bgeu t4, t3, .Lcvit_pred_false\n" ++
  "  # advance\n" ++
  "  la t0, cvit_iter_child;  ld t1, 0(t0)\n" ++
  "  la t0, cvit_iter_i;      ld t2, 0(t0)\n" ++
  "  mv s5, t3                   # prev_ts = current\n" ++
  "  slli t5, t2, 3\n" ++
  "  add t5, s1, t5\n" ++
  "  ld t6, 0(t5)\n" ++
  "  add t1, t1, t6\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lcvit_loop\n" ++
  ".Lcvit_pred_false:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  la t0, cvit_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcvit_ret\n" ++
  ".Lcvit_propagate:\n" ++
  "  la t0, cvit_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  j .Lcvit_ret\n" ++
  ".Lcvit_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcvit_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainValidateIncreasingTimestampsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_increasing_timestamps\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvit_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainValidateIncreasingTimestampsFunction ++ "\n" ++
  ".Lcvit_pdone:"

def ziskChainValidateIncreasingTimestampsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvit_ts:\n" ++
  "  .zero 8\n" ++
  "cvit_iter_child:\n" ++
  "  .zero 8\n" ++
  "cvit_iter_i:\n" ++
  "  .zero 8\n" ++
  "cvit_iter_prev:\n" ++
  "  .zero 8"

def ziskChainValidateIncreasingTimestampsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainValidateIncreasingTimestampsPrologue
  dataAsm     := ziskChainValidateIncreasingTimestampsDataSection
}

/-! ## chain_validate_consecutive_numbers -- PR-K230

    Verify the chain has strictly consecutive block numbers:
    `headers[i+1].number == headers[i].number + 1`. Pure
    number-only check; analogue of K229 for the `number` field
    (field 8) instead of `timestamp` (field 11), and with `==
    prev + 1` instead of `> prev`.

    Vacuous-true on N <= 1.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : u64 out (is_valid)
      a4 (input)  : u64 out (first_bad_index)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure
        2 : number field > 8 bytes BE -/
def chainValidateConsecutiveNumbersFunction : String :=
  "chain_validate_consecutive_numbers:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3); sd zero, 0(s4)\n" ++
  "  li t0, 2\n" ++
  "  bltu s0, t0, .Lcvcn_done\n" ++
  "  # headers[0].number -> s5 (prev_num)\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2; li a2, 8\n" ++
  "  la a3, cvcn_num\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcvcn_propagate\n" ++
  "  la t0, cvcn_num; ld s5, 0(t0)\n" ++
  "  ld t0, 0(s1)\n" ++
  "  add t1, s2, t0              # child_ptr\n" ++
  "  li t2, 1\n" ++
  ".Lcvcn_loop:\n" ++
  "  beq t2, s0, .Lcvcn_done\n" ++
  "  la t0, cvcn_iter_child; sd t1, 0(t0)\n" ++
  "  la t0, cvcn_iter_i;     sd t2, 0(t0)\n" ++
  "  la t0, cvcn_iter_prev;  sd s5, 0(t0)\n" ++
  "  slli t3, t2, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, t1; li a2, 8\n" ++
  "  la a3, cvcn_num\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcvcn_propagate\n" ++
  "  la t0, cvcn_num;        ld t3, 0(t0)\n" ++
  "  la t0, cvcn_iter_prev;  ld t4, 0(t0)\n" ++
  "  addi t4, t4, 1\n" ++
  "  bne t4, t3, .Lcvcn_pred_false\n" ++
  "  la t0, cvcn_iter_child; ld t1, 0(t0)\n" ++
  "  la t0, cvcn_iter_i;     ld t2, 0(t0)\n" ++
  "  mv s5, t3\n" ++
  "  slli t5, t2, 3\n" ++
  "  add t5, s1, t5\n" ++
  "  ld t6, 0(t5)\n" ++
  "  add t1, t1, t6\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lcvcn_loop\n" ++
  ".Lcvcn_pred_false:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  la t0, cvcn_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcvcn_ret\n" ++
  ".Lcvcn_propagate:\n" ++
  "  la t0, cvcn_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  j .Lcvcn_ret\n" ++
  ".Lcvcn_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcvcn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainValidateConsecutiveNumbersPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_consecutive_numbers\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvcn_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainValidateConsecutiveNumbersFunction ++ "\n" ++
  ".Lcvcn_pdone:"

def ziskChainValidateConsecutiveNumbersDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvcn_num:\n" ++
  "  .zero 8\n" ++
  "cvcn_iter_child:\n" ++
  "  .zero 8\n" ++
  "cvcn_iter_i:\n" ++
  "  .zero 8\n" ++
  "cvcn_iter_prev:\n" ++
  "  .zero 8"

def ziskChainValidateConsecutiveNumbersProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainValidateConsecutiveNumbersPrologue
  dataAsm     := ziskChainValidateConsecutiveNumbersDataSection
}

/-! ## chain_compute_total_blob_gas -- PR-K231

    Aggregate `blob_gas_used` (header field 17, EIP-4844
    Cancun+) across an N-element header chain into a single u64
    sum. Pre-Cancun headers (≤17 fields) yield a parse-failure
    status and the sum is partial.

    Useful for blob-gas market monitoring across a chain segment.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : u64 out (total_blob_gas_used)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (pre-Cancun header in the chain)
        2 : blob_gas_used field > 8 bytes BE -/
def chainComputeTotalBlobGasFunction : String :=
  "chain_compute_total_blob_gas:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lcctbg_done\n" ++
  ".Lcctbg_loop:\n" ++
  "  beq s4, s0, .Lcctbg_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 17\n" ++
  "  la a3, cctbg_field\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lcctbg_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lcctbg_size_fail\n" ++
  "  la t0, cctbg_field; ld t1, 0(t0)\n" ++
  "  ld t2, 0(s3); add t2, t2, t1; sd t2, 0(s3)\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lcctbg_loop\n" ++
  ".Lcctbg_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lcctbg_ret\n" ++
  ".Lcctbg_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lcctbg_ret\n" ++
  ".Lcctbg_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lcctbg_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeTotalBlobGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_total_blob_gas\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcctbg_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainComputeTotalBlobGasFunction ++ "\n" ++
  ".Lcctbg_pdone:"

def ziskChainComputeTotalBlobGasDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cctbg_field:\n" ++
  "  .zero 8"

def ziskChainComputeTotalBlobGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainComputeTotalBlobGasPrologue
  dataAsm     := ziskChainComputeTotalBlobGasDataSection
}

/-! ## chain_compute_max_blob_gas_used -- PR-K237

    Find max(header.blob_gas_used) (field 17, EIP-4844 Cancun+)
    across an N-element header chain. Peak blob-congestion
    monitor, complementing K231 chain_compute_total_blob_gas.

    Pre-Cancun headers (≤17 fields) yield parse-failure status;
    the max is the partial accumulator up to the failure point.
    Vacuous on empty chain: max = 0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (max blob_gas_used)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (pre-Cancun header in chain)
        2 : blob_gas_used field > 8 bytes BE -/
def chainComputeMaxBlobGasUsedFunction : String :=
  "chain_compute_max_blob_gas_used:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lccmbgu_done\n" ++
  ".Lccmbgu_loop:\n" ++
  "  beq s4, s0, .Lccmbgu_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 17\n" ++
  "  la a3, ccmbgu_field\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lccmbgu_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lccmbgu_size_fail\n" ++
  "  la t0, ccmbgu_field; ld t1, 0(t0)\n" ++
  "  ld t2, 0(s3)\n" ++
  "  bgeu t2, t1, .Lccmbgu_no_update\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lccmbgu_no_update:\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lccmbgu_loop\n" ++
  ".Lccmbgu_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lccmbgu_ret\n" ++
  ".Lccmbgu_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lccmbgu_ret\n" ++
  ".Lccmbgu_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lccmbgu_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeMaxBlobGasUsedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_max_blob_gas_used\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccmbgu_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainComputeMaxBlobGasUsedFunction ++ "\n" ++
  ".Lccmbgu_pdone:"

def ziskChainComputeMaxBlobGasUsedDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ccmbgu_field:\n" ++
  "  .zero 8"

def ziskChainComputeMaxBlobGasUsedProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainComputeMaxBlobGasUsedPrologue
  dataAsm     := ziskChainComputeMaxBlobGasUsedDataSection
}

/-! ## chain_compute_min_gas_used -- PR-K238

    Find min(header.gas_used) (field 10) across an N-element
    header chain. Lowest-throughput / liveness monitor that
    complements K236 chain_compute_max_gas_used (max) and K196
    chain_compute_total_gas_used (sum).

    Vacuous on empty chain: min = 0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (min)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (in any header)
        2 : gas_used field > 8 bytes BE -/
def chainComputeMinGasUsedFunction : String :=
  "chain_compute_min_gas_used:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lccming_done\n" ++
  ".Lccming_loop:\n" ++
  "  beq s4, s0, .Lccming_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 10\n" ++
  "  la a3, ccming_field\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lccming_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lccming_size_fail\n" ++
  "  la t0, ccming_field; ld t1, 0(t0)\n" ++
  "  beqz s4, .Lccming_first\n" ++
  "  ld t2, 0(s3)\n" ++
  "  bgeu t1, t2, .Lccming_no_update\n" ++
  ".Lccming_first:\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lccming_no_update:\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lccming_loop\n" ++
  ".Lccming_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lccming_ret\n" ++
  ".Lccming_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lccming_ret\n" ++
  ".Lccming_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lccming_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeMinGasUsedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_min_gas_used\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccming_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainComputeMinGasUsedFunction ++ "\n" ++
  ".Lccming_pdone:"

def ziskChainComputeMinGasUsedDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ccming_field:\n" ++
  "  .zero 8"

def ziskChainComputeMinGasUsedProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainComputeMinGasUsedPrologue
  dataAsm     := ziskChainComputeMinGasUsedDataSection
}

/-! ## chain_extract_timestamp_range -- PR-K239

    Extract `(first_timestamp, last_timestamp)` from an N-element
    header chain. With K229 increasing-timestamps validated, the
    pair is monotonically non-decreasing; callers can use the
    range as a chain-segment duration or epoch identifier. The
    timestamp counterpart to K197 chain_extract_number_range.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : u64 out (first_timestamp)
      a4 (input)  : u64 out (last_timestamp)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse failure on some header
        3 : a header's timestamp field exceeds 8 bytes BE -/
def chainExtractTimestampRangeFunction : String :=
  "chain_extract_timestamp_range:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # N\n" ++
  "  mv s1, a1                   # header_lengths\n" ++
  "  mv s2, a2                   # headers\n" ++
  "  mv s3, a3                   # first out\n" ++
  "  mv s4, a4                   # last out\n" ++
  "  beqz s0, .Lcetr_empty\n" ++
  "  # first = headers[0].timestamp\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  li a2, 11                   # field 11 = timestamp\n" ++
  "  mv a3, s3\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcetr_propagate\n" ++
  "  # Advance to last header\n" ++
  "  mv t1, s2\n" ++
  "  mv t2, s1\n" ++
  "  addi t3, s0, -1\n" ++
  ".Lcetr_skip:\n" ++
  "  beqz t3, .Lcetr_at_last\n" ++
  "  ld t4, 0(t2)\n" ++
  "  add t1, t1, t4\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lcetr_skip\n" ++
  ".Lcetr_at_last:\n" ++
  "  ld a1, 0(t2)\n" ++
  "  mv a0, t1\n" ++
  "  li a2, 11\n" ++
  "  mv a3, s4\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcetr_propagate\n" ++
  "  li a0, 0\n" ++
  "  j .Lcetr_ret\n" ++
  ".Lcetr_empty:\n" ++
  "  li a0, 1\n" ++
  "  j .Lcetr_ret\n" ++
  ".Lcetr_propagate:\n" ++
  "  addi a0, a0, 1\n" ++
  ".Lcetr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainExtractTimestampRangePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_extract_timestamp_range\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcetr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainExtractTimestampRangeFunction ++ "\n" ++
  ".Lcetr_pdone:"

def ziskChainExtractTimestampRangeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskChainExtractTimestampRangeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainExtractTimestampRangePrologue
  dataAsm     := ziskChainExtractTimestampRangeDataSection
}

/-! ## chain_validate_gas_used_under_limit -- PR-K240

    Per-header invariant: `gas_used <= gas_limit` (header fields
    10 and 9 respectively). The block validator already enforces
    `gas_used <= gas_limit` in K72 `check_gas_limit` for adjacent
    pairs; K240 lifts the standalone per-block constraint to an
    N-element chain.

    Vacuous on empty chain: valid=1, bad_index=0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (valid: 1 = all OK)
      a4 (input)  : u64 out (bad_index = first violator, else 0)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written
        1 : RLP parse fail on some header
        2 : gas_used or gas_limit field > 8 bytes BE -/
def chainValidateGasUsedUnderLimitFunction : String :=
  "chain_validate_gas_used_under_limit:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3); sd zero, 0(s4)\n" ++
  "  li s5, 0\n" ++
  ".Lcvgul_loop:\n" ++
  "  beq s5, s0, .Lcvgul_done\n" ++
  "  la t0, cvgul_iter_ptr; sd s2, 0(t0)\n" ++
  "  la t0, cvgul_iter_i;   sd s5, 0(t0)\n" ++
  "  slli t3, s5, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, s2; li a2, 10\n" ++
  "  la a3, cvgul_gas_used\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcvgul_propagate\n" ++
  "  la t0, cvgul_iter_ptr; ld s2, 0(t0)\n" ++
  "  la t0, cvgul_iter_i;   ld s5, 0(t0)\n" ++
  "  slli t3, s5, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, s2; li a2, 9\n" ++
  "  la a3, cvgul_gas_limit\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcvgul_propagate\n" ++
  "  la t0, cvgul_iter_ptr; ld s2, 0(t0)\n" ++
  "  la t0, cvgul_iter_i;   ld s5, 0(t0)\n" ++
  "  la t0, cvgul_gas_used;  ld t1, 0(t0)\n" ++
  "  la t0, cvgul_gas_limit; ld t2, 0(t0)\n" ++
  "  bgtu t1, t2, .Lcvgul_violation\n" ++
  "  slli t3, s5, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld t4, 0(t3)\n" ++
  "  add s2, s2, t4\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lcvgul_loop\n" ++
  ".Lcvgul_violation:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  sd s5, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcvgul_ret\n" ++
  ".Lcvgul_propagate:\n" ++
  "  sd s5, 0(s4)\n" ++
  "  j .Lcvgul_ret\n" ++
  ".Lcvgul_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcvgul_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainValidateGasUsedUnderLimitPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_gas_used_under_limit\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvgul_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainValidateGasUsedUnderLimitFunction ++ "\n" ++
  ".Lcvgul_pdone:"

def ziskChainValidateGasUsedUnderLimitDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvgul_gas_used:\n" ++
  "  .zero 8\n" ++
  "cvgul_gas_limit:\n" ++
  "  .zero 8\n" ++
  "cvgul_iter_ptr:\n" ++
  "  .zero 8\n" ++
  "cvgul_iter_i:\n" ++
  "  .zero 8"

def ziskChainValidateGasUsedUnderLimitProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainValidateGasUsedUnderLimitPrologue
  dataAsm     := ziskChainValidateGasUsedUnderLimitDataSection
}

/-! ## chain_compute_min_blob_gas_used -- PR-K243

    Find min(header.blob_gas_used) (EIP-4844 Cancun+ field 17)
    across an N-element header chain. The min counterpart to
    K237 chain_compute_max_blob_gas_used; useful for spotting
    quiet blocks.

    Pre-Cancun headers (≤17 fields) yield parse-failure status;
    the min is the partial accumulator up to the failure point.
    Vacuous on empty chain: min = 0. First header initialises
    the accumulator; subsequent headers update only when smaller.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (min blob_gas_used)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (pre-Cancun header in chain)
        2 : blob_gas_used field > 8 bytes BE -/
def chainComputeMinBlobGasUsedFunction : String :=
  "chain_compute_min_blob_gas_used:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lccminbg_done\n" ++
  ".Lccminbg_loop:\n" ++
  "  beq s4, s0, .Lccminbg_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 17\n" ++
  "  la a3, ccminbg_field\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lccminbg_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lccminbg_size_fail\n" ++
  "  la t0, ccminbg_field; ld t1, 0(t0)\n" ++
  "  beqz s4, .Lccminbg_first\n" ++
  "  ld t2, 0(s3)\n" ++
  "  bgeu t1, t2, .Lccminbg_no_update\n" ++
  ".Lccminbg_first:\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lccminbg_no_update:\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lccminbg_loop\n" ++
  ".Lccminbg_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lccminbg_ret\n" ++
  ".Lccminbg_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lccminbg_ret\n" ++
  ".Lccminbg_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lccminbg_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeMinBlobGasUsedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_min_blob_gas_used\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccminbg_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainComputeMinBlobGasUsedFunction ++ "\n" ++
  ".Lccminbg_pdone:"

def ziskChainComputeMinBlobGasUsedDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ccminbg_field:\n" ++
  "  .zero 8"

def ziskChainComputeMinBlobGasUsedProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainComputeMinBlobGasUsedPrologue
  dataAsm     := ziskChainComputeMinBlobGasUsedDataSection
}

end EvmAsm.Codegen
