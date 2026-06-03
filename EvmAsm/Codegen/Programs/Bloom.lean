/-
  EvmAsm.Codegen.Programs.Bloom

  Bloom-filter cluster lifted out of `EvmAsm.Codegen.Programs`
  per the file-size hard cap. This module groups every atomic
  bloom helper plus the per-block accumulators and the
  end-to-end validation composite.

  Slab 1 (K148-K154): atomic primitives
    K148 bloom_add_value         - single value (address/topic)
    K149 log_bloom_add           - one log (address + topics)
    K150 logs_list_bloom_add     - one receipt's logs
    K151 bloom_or_into           - 256-byte in-place OR
    K152 receipt_extract_logs_bloom
    K153 header_extract_logs_bloom
    K154 bloom_eq                - 256-byte equality

  Slab 2 (K158, K159): block-level composites
    K158 block_logs_bloom_from_receipts_list
    K159 block_validate_logs_bloom (end-to-end)

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bloom_add_value -- PR-K148

    Add a single value to a 2048-bit (256-byte) Ethereum log
    bloom filter, following the yellow-paper / EIP-2718
    definition:

      1. h = keccak256(value)
      2. for idx in {0, 2, 4}:
           raw     = u16(h[idx..idx+2]) & 0x7FF      -- low 11 bits
           bit     = 0x7FF - raw                     -- inverted
           byte_i  = bit / 8
           bit_pos = 7 - (bit mod 8)                 -- MSB-first in byte
           bloom[byte_i] |= 1 << bit_pos

    Called twice for each log:
      * once with `value = log.address` (20 bytes)
      * once per topic with `value = topic` (32 bytes)

    Building block for `logs_bloom` construction in receipt
    encoding, which in turn feeds `block.bloom` (the per-block
    bloom = OR of every receipt's bloom). Used by:
      * `apply_body` when assembling each tx's receipt.
      * `block_validate_logs_bloom` to recompute the header's
        bloom field from receipts.

    Composes:
      - `zkvm_keccak256` (HashBridge) — hashes the value.

    Calling convention:
      a0 (input)  : bloom ptr (256 bytes, mutable, in-place OR)
      a1 (input)  : value ptr
      a2 (input)  : value byte length
      ra (input)  : return
      a0 (output) : 0 (always succeeds).

    Bloom is mutated in place; the caller owns the buffer and
    is responsible for zero-initialising it before the first
    `bloom_add_value` call of a logs sequence. -/
def bloomAddValueFunction : String :=
  "bloom_add_value:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # bloom ptr\n" ++
  "  mv s1, a1                   # value ptr\n" ++
  "  mv s2, a2                   # value len\n" ++
  "  # ---- Compute keccak256(value) → bav_hash ----\n" ++
  "  mv a0, s1; mv a1, s2\n" ++
  "  la a2, bav_hash\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # ---- Set three bits derived from h[0..6] ----\n" ++
  "  la t0, bav_hash\n" ++
  "  li t1, 0                    # idx loop counter (0, 2, 4)\n" ++
  ".Lbav_loop:\n" ++
  "  li t2, 6\n" ++
  "  bge t1, t2, .Lbav_done\n" ++
  "  add t3, t0, t1\n" ++
  "  lbu t4, 0(t3)               # hi byte\n" ++
  "  lbu t5, 1(t3)               # lo byte\n" ++
  "  slli t4, t4, 8\n" ++
  "  or  t4, t4, t5              # raw_word\n" ++
  "  li  t5, 0x7ff\n" ++
  "  and t4, t4, t5              # raw_bit (0..2047)\n" ++
  "  sub t4, t5, t4              # bit_index = 0x7ff - raw_bit\n" ++
  "  srli t5, t4, 3              # byte_index = bit_index / 8\n" ++
  "  andi t6, t4, 7              # bit_index mod 8\n" ++
  "  li  t4, 7\n" ++
  "  sub t6, t4, t6              # bit_pos = 7 - (bit_index mod 8)\n" ++
  "  li  t4, 1\n" ++
  "  sll t6, t4, t6              # bit_mask = 1 << bit_pos\n" ++
  "  add t5, s0, t5              # &bloom[byte_index]\n" ++
  "  lbu t4, 0(t5)\n" ++
  "  or  t4, t4, t6\n" ++
  "  sb  t4, 0(t5)\n" ++
  "  addi t1, t1, 2\n" ++
  "  j .Lbav_loop\n" ++
  ".Lbav_done:\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_bloom_add_value`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : value_len
      bytes  8..   : value bytes
    Output layout:
      bytes  0..256 : zero-initialised bloom, then bloom_add_value
                      run once on the supplied value. -/
def ziskBloomAddValuePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a2, 8(a3)                # value_len\n" ++
  "  addi a1, a3, 16             # value ptr\n" ++
  "  li a0, 0xa0010000           # output bloom ptr\n" ++
  "  jal ra, bloom_add_value\n" ++
  "  j .Lbav_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  bloomAddValueFunction ++ "\n" ++
  ".Lbav_pdone:"

def ziskBloomAddValueDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bav_hash:\n" ++
  "  .zero 32"

def ziskBloomAddValueProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBloomAddValuePrologue
  dataAsm     := ziskBloomAddValueDataSection
}

/-! ## log_bloom_add -- PR-K149

    Add a full log's bloom contributions to a 256-byte bloom
    filter, in place. A log is `rlp([address, topics, data])`
    where:
      * address : 20-byte string
      * topics  : RLP list of 32-byte hashes (0..4 entries; the
                  EVM opcodes LOG0..LOG4 enforce the upper bound)
      * data    : opaque bytes (NOT part of the bloom; only the
                  address and topics enter the filter)

    For each `value` in `{address, topic[0], …, topic[k-1]}`:
      bloom_add_value(bloom, value, len(value))

    Composes:
      - PR-K20 `rlp_list_nth_item`        — locate address /
        topics-list fields and individual topics
      - PR-K47 `rlp_list_count_items`     — topic-list cardinality
      - PR-K148 `bloom_add_value`         — bit-set per value
      - `zkvm_keccak256` (via K148)        — hashing

    Calling convention:
      a0 (input)  : bloom ptr (256 bytes, mutable, in-place OR)
      a1 (input)  : log_rlp ptr
      a2 (input)  : log_rlp byte length
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / log shape invalid
        2 : address field length != 20 bytes
        3 : topic field length != 32 bytes

    The data field is *not* part of the bloom, per the yellow
    paper; it's read and discarded. Caller zero-initialises the
    bloom buffer before the first call of a logs sequence. -/
def logBloomAddFunction : String :=
  "log_bloom_add:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # bloom ptr\n" ++
  "  mv s1, a1                   # log_rlp ptr\n" ++
  "  mv s2, a2                   # log_rlp len\n" ++
  "  # ---- Field 0: address (20 bytes) ----\n" ++
  "  mv a0, s1; mv a1, s2; li a2, 0\n" ++
  "  la a3, lba_offset; la a4, lba_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Llba_fail\n" ++
  "  la t0, lba_length; ld t1, 0(t0)\n" ++
  "  li t2, 20\n" ++
  "  bne t1, t2, .Llba_addr_size\n" ++
  "  la t0, lba_offset; ld t1, 0(t0)\n" ++
  "  add a1, s1, t1               # &address bytes\n" ++
  "  mv a0, s0; li a2, 20\n" ++
  "  jal ra, bloom_add_value\n" ++
  "  # ---- Field 1: topics list — get bounds (full encoded item) ----\n" ++
  "  mv a0, s1; mv a1, s2; li a2, 1\n" ++
  "  la a3, lba_topics_offset; la a4, lba_topics_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Llba_fail\n" ++
  "  la t0, lba_topics_offset; ld s3, 0(t0)        # topics absolute offset\n" ++
  "  la t0, lba_topics_length; ld s4, 0(t0)        # topics full encoded len\n" ++
  "  add t0, s1, s3                                # &topics_rlp\n" ++
  "  # ---- Count topics ----\n" ++
  "  mv a0, t0; mv a1, s4\n" ++
  "  la a2, lba_topic_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Llba_fail\n" ++
  "  la t0, lba_topic_count; ld s5, 0(t0)          # n_topics\n" ++
  "  # ---- For each topic i in 0..n_topics-1, add to bloom ----\n" ++
  "  li t6, 0                                      # i\n" ++
  ".Llba_topic_loop:\n" ++
  "  bge t6, s5, .Llba_topic_done\n" ++
  "  # Extract topic i bounds.\n" ++
  "  add a0, s1, s3                                # topics_rlp ptr\n" ++
  "  mv a1, s4                                     # topics_rlp len\n" ++
  "  mv a2, t6                                     # index\n" ++
  "  la a3, lba_offset; la a4, lba_length\n" ++
  "  # Save t6 across the call (caller-saved).\n" ++
  "  addi sp, sp, -8; sd t6, 0(sp)\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  ld t6, 0(sp); addi sp, sp, 8\n" ++
  "  bnez a0, .Llba_fail\n" ++
  "  la t0, lba_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Llba_topic_size\n" ++
  "  la t0, lba_offset; ld t1, 0(t0)               # offset (relative to topics_rlp)\n" ++
  "  add t1, t1, s3                                # absolute offset in log_rlp\n" ++
  "  add a1, s1, t1                                # &topic bytes\n" ++
  "  mv a0, s0; li a2, 32\n" ++
  "  addi sp, sp, -8; sd t6, 0(sp)\n" ++
  "  jal ra, bloom_add_value\n" ++
  "  ld t6, 0(sp); addi sp, sp, 8\n" ++
  "  addi t6, t6, 1\n" ++
  "  j .Llba_topic_loop\n" ++
  ".Llba_topic_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Llba_ret\n" ++
  ".Llba_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Llba_ret\n" ++
  ".Llba_addr_size:\n" ++
  "  li a0, 2\n" ++
  "  j .Llba_ret\n" ++
  ".Llba_topic_size:\n" ++
  "  li a0, 3\n" ++
  ".Llba_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_log_bloom_add`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : log_rlp_len
      bytes  8..   : log_rlp
    Output layout:
      bytes  0..256 : zero-initialised bloom, then log_bloom_add
                      applied once to the supplied log. -/
def ziskLogBloomAddPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a2, 8(a3)                # log_rlp_len\n" ++
  "  addi a1, a3, 16             # log_rlp ptr\n" ++
  "  li a0, 0xa0010000           # output bloom ptr\n" ++
  "  jal ra, log_bloom_add\n" ++
  "  j .Llba_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  bloomAddValueFunction ++ "\n" ++
  logBloomAddFunction ++ "\n" ++
  ".Llba_pdone:"

def ziskLogBloomAddDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bav_hash:\n" ++
  "  .zero 32\n" ++
  "lba_offset:\n" ++
  "  .zero 8\n" ++
  "lba_length:\n" ++
  "  .zero 8\n" ++
  "lba_topics_offset:\n" ++
  "  .zero 8\n" ++
  "lba_topics_length:\n" ++
  "  .zero 8\n" ++
  "lba_topic_count:\n" ++
  "  .zero 8"

def ziskLogBloomAddProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskLogBloomAddPrologue
  dataAsm     := ziskLogBloomAddDataSection
}

/-! ## logs_list_bloom_add -- PR-K150

    OR every log's bloom contribution from an RLP-encoded `logs`
    list into a 256-byte bloom buffer. This is what
    `apply_body` calls on each receipt's logs to compute the
    receipt's `logs_bloom` field, and what
    `block_compute_logs_bloom` (future) calls to assemble the
    block-level bloom from receipts (via repeated OR).

    Input list shape:

      logs = rlp([log_0, log_1, ..., log_{n-1}])
      log_i = rlp([address, topics, data])

    For each log_i, `logs_list_bloom_add` invokes K149
    `log_bloom_add` (which itself loops K148 `bloom_add_value`).
    Empty `logs` list (`0xc0`) is a valid input → bloom unchanged.

    Composes:
      - PR-K20 `rlp_list_nth_item`    -- walk each log_i
      - PR-K47 `rlp_list_count_items` -- list cardinality
      - PR-K149 `log_bloom_add`       -- per-log accumulation
      - PR-K148 `bloom_add_value`     -- (via K149)
      - `zkvm_keccak256`              -- (via K148)

    Calling convention:
      a0 (input)  : bloom ptr (256 bytes, mutable, in-place OR;
                    caller zero-inits before first call)
      a1 (input)  : logs_rlp ptr (RLP list of log entries)
      a2 (input)  : logs_rlp byte length
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure (logs_rlp not a list)
        2 : a log address field length != 20 (per K149)
        3 : a log topic field length != 32 (per K149) -/
def logsListBloomAddFunction : String :=
  "logs_list_bloom_add:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # bloom ptr\n" ++
  "  mv s1, a1                   # logs_rlp ptr\n" ++
  "  mv s2, a2                   # logs_rlp len\n" ++
  "  # ---- Count logs ----\n" ++
  "  mv a0, s1; mv a1, s2\n" ++
  "  la a2, llba_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lllba_parse_fail\n" ++
  "  la t0, llba_count; ld s3, 0(t0)              # n_logs\n" ++
  "  li s4, 0                                     # i\n" ++
  ".Lllba_loop:\n" ++
  "  bge s4, s3, .Lllba_done\n" ++
  "  # Extract log_i bounds (full encoded item).\n" ++
  "  mv a0, s1; mv a1, s2; mv a2, s4\n" ++
  "  la a3, llba_offset; la a4, llba_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lllba_parse_fail\n" ++
  "  la t0, llba_offset; ld t1, 0(t0)\n" ++
  "  la t0, llba_length; ld t2, 0(t0)\n" ++
  "  add a1, s1, t1                                # &log_i bytes\n" ++
  "  mv a2, t2                                     # log_i len\n" ++
  "  mv a0, s0                                     # bloom\n" ++
  "  jal ra, log_bloom_add\n" ++
  "  bnez a0, .Lllba_log_err                       # propagate child status\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lllba_loop\n" ++
  ".Lllba_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lllba_ret\n" ++
  ".Lllba_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lllba_ret\n" ++
  ".Lllba_log_err:\n" ++
  "  # a0 already carries the child status (2 = address size, 3 = topic size,\n" ++
  "  # 1 = parse fail). Pass through unchanged.\n" ++
  ".Lllba_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_logs_list_bloom_add`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : logs_rlp_len
      bytes  8..   : logs_rlp
    Output layout:
      bytes  0..256 : zero-initialised bloom, then
                      logs_list_bloom_add applied once. -/
def ziskLogsListBloomAddPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a2, 8(a3)                # logs_rlp_len\n" ++
  "  addi a1, a3, 16             # logs_rlp ptr\n" ++
  "  li a0, 0xa0010000           # output bloom ptr\n" ++
  "  jal ra, logs_list_bloom_add\n" ++
  "  j .Lllba_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  bloomAddValueFunction ++ "\n" ++
  logBloomAddFunction ++ "\n" ++
  logsListBloomAddFunction ++ "\n" ++
  ".Lllba_pdone:"

def ziskLogsListBloomAddDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bav_hash:\n" ++
  "  .zero 32\n" ++
  "lba_offset:\n" ++
  "  .zero 8\n" ++
  "lba_length:\n" ++
  "  .zero 8\n" ++
  "lba_topics_offset:\n" ++
  "  .zero 8\n" ++
  "lba_topics_length:\n" ++
  "  .zero 8\n" ++
  "lba_topic_count:\n" ++
  "  .zero 8\n" ++
  "llba_offset:\n" ++
  "  .zero 8\n" ++
  "llba_length:\n" ++
  "  .zero 8\n" ++
  "llba_count:\n" ++
  "  .zero 8"

def ziskLogsListBloomAddProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskLogsListBloomAddPrologue
  dataAsm     := ziskLogsListBloomAddDataSection
}

/-! ## captured_logs_bloom_add -- M26 receipt bridge

    Convert the dispatcher's bounded LOG event descriptors into a 256-byte
    receipt bloom. Each descriptor is 256 bytes:
      +0  topic count (u64, must be <= 4)
      +32..160 four 32-byte topic slots in EVM stack-word byte order
      +192..224 ADDRESS context word in EVM stack-word byte order

    Stack-word byte order is four little-endian u64 limbs, low limb first.
    Ethereum bloom hashing wants canonical byte order, so this helper reverses
    the low 20 address bytes and each 32-byte topic into scratch before calling
    `bloom_add_value`. Descriptor data bytes are intentionally ignored, as data
    is not part of the Ethereum logs_bloom.

    Calling convention:
      a0 (input)  : bloom ptr (256 bytes, mutable, in-place OR)
      a1 (input)  : descriptor base ptr
      a2 (input)  : descriptor count
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : descriptor count > 16
        2 : topic count > 4 -/
def capturedLogsBloomAddFunction : String :=
  "captured_logs_bloom_add:
" ++
  "  addi sp, sp, -64
" ++
  "  sd ra,  0(sp)
" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
" ++
  "  mv s0, a0                   # bloom ptr
" ++
  "  mv s1, a1                   # descriptor base
" ++
  "  mv s2, a2                   # descriptor count
" ++
  "  li t0, 16
" ++
  "  bgtu s2, t0, .Lclba_count_fail
" ++
  "  li s3, 0                    # descriptor index
" ++
  ".Lclba_log_loop:
" ++
  "  bgeu s3, s2, .Lclba_done
" ++
  "  slli t0, s3, 8              # i * 256
" ++
  "  add s4, s1, t0              # descriptor ptr
" ++
  "  ld s5, 0(s4)                # topic count
" ++
  "  li t0, 4
" ++
  "  bgtu s5, t0, .Lclba_topic_count_fail
" ++
  "  # ADDRESS word at descriptor+192. Bloom hashes the low 160 bits in
" ++
  "  # canonical big-endian order, so reverse descriptor bytes 0..19.
" ++
  "  addi t0, s4, 192
" ++
  "  addi t0, t0, 19
" ++
  "  la t1, clba_value
" ++
  "  li t2, 20
" ++
  ".Lclba_addr_rev:
" ++
  "  beqz t2, .Lclba_addr_hash
" ++
  "  lbu t3, 0(t0)
" ++
  "  sb t3, 0(t1)
" ++
  "  addi t0, t0, -1
" ++
  "  addi t1, t1, 1
" ++
  "  addi t2, t2, -1
" ++
  "  j .Lclba_addr_rev
" ++
  ".Lclba_addr_hash:
" ++
  "  mv a0, s0; la a1, clba_value; li a2, 20
" ++
  "  jal ra, bloom_add_value
" ++
  "  li s6, 0                    # topic index
" ++
  ".Lclba_topic_loop:
" ++
  "  bgeu s6, s5, .Lclba_next_log
" ++
  "  slli t0, s6, 5              # topic offset = 32 + 32*j
" ++
  "  addi t0, t0, 32
" ++
  "  add t0, s4, t0
" ++
  "  addi t0, t0, 31
" ++
  "  la t1, clba_value
" ++
  "  li t2, 32
" ++
  ".Lclba_topic_rev:
" ++
  "  beqz t2, .Lclba_topic_hash
" ++
  "  lbu t3, 0(t0)
" ++
  "  sb t3, 0(t1)
" ++
  "  addi t0, t0, -1
" ++
  "  addi t1, t1, 1
" ++
  "  addi t2, t2, -1
" ++
  "  j .Lclba_topic_rev
" ++
  ".Lclba_topic_hash:
" ++
  "  mv a0, s0; la a1, clba_value; li a2, 32
" ++
  "  jal ra, bloom_add_value
" ++
  "  addi s6, s6, 1
" ++
  "  j .Lclba_topic_loop
" ++
  ".Lclba_next_log:
" ++
  "  addi s3, s3, 1
" ++
  "  j .Lclba_log_loop
" ++
  ".Lclba_done:
" ++
  "  li a0, 0
" ++
  "  j .Lclba_ret
" ++
  ".Lclba_count_fail:
" ++
  "  li a0, 1
" ++
  "  j .Lclba_ret
" ++
  ".Lclba_topic_count_fail:
" ++
  "  li a0, 2
" ++
  ".Lclba_ret:
" ++
  "  ld ra,  0(sp)
" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
" ++
  "  addi sp, sp, 64
" ++
  "  ret"

/-- `zisk_captured_logs_bloom_add`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : descriptor_count
      bytes  8..   : descriptor_count * 256 bytes of captured LOG descriptors
    Output layout:
      success: bytes 0..256 are the computed bloom.
      failure: bytes 0..8 contain the nonzero status and the rest is zero. -/
def ziskCapturedLogsBloomAddPrologue : String :=
  "  li sp, 0xa0050000
" ++
  "  li a3, 0x40000000
" ++
  "  ld a2, 8(a3)                # descriptor_count
" ++
  "  addi a1, a3, 16             # descriptor base
" ++
  "  li a0, 0xa0010000           # output bloom ptr
" ++
  "  li t0, 32
" ++
  "  mv t1, a0
" ++
  ".Lclba_zero:
" ++
  "  beqz t0, .Lclba_zero_done
" ++
  "  sd x0, 0(t1)
" ++
  "  addi t1, t1, 8
" ++
  "  addi t0, t0, -1
" ++
  "  j .Lclba_zero
" ++
  ".Lclba_zero_done:
" ++
  "  jal ra, captured_logs_bloom_add
" ++
  "  beqz a0, .Lclba_pdone
" ++
  "  li t0, 0xa0010000
" ++
  "  sd a0, 0(t0)                # failure status; success leaves bloom intact
" ++
  "  j .Lclba_pdone
" ++
  zkvmKeccak256Function ++ "
" ++
  bloomAddValueFunction ++ "
" ++
  capturedLogsBloomAddFunction ++ "
" ++
  ".Lclba_pdone:"

def ziskCapturedLogsBloomAddDataSection : String :=
  ".section .data
" ++
  ".balign 8
" ++
  "zk3_state:
" ++
  "  .zero 200
" ++
  "bav_hash:
" ++
  "  .zero 32
" ++
  "clba_value:
" ++
  "  .zero 32"

def ziskCapturedLogsBloomAddProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCapturedLogsBloomAddPrologue
  dataAsm     := ziskCapturedLogsBloomAddDataSection
}

/-! ## bloom_or_into -- PR-K151

    In-place 256-byte bitwise OR: `dst[i] |= src[i]` for
    `i in 0..256`. Used to accumulate one bloom filter into
    another -- in particular, to fold each receipt's `logs_bloom`
    into the block-level `block.logs_bloom` field.

    A natural complement to:
      * PR-K148 `bloom_add_value`     -- single-value add
      * PR-K149 `log_bloom_add`       -- per-log accumulation
      * PR-K150 `logs_list_bloom_add` -- per-receipt accumulation
      * PR-K151 (this PR) `bloom_or_into` -- per-block accumulation

    Pure register arithmetic; processes 8 bytes per iteration
    (32 iterations total) using `ld` + `or` + `sd`. No external
    function calls.

    Calling convention:
      a0 (input)  : dst bloom ptr (256 bytes, mutable, in-place OR)
      a1 (input)  : src bloom ptr (256 bytes, read-only)
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def bloomOrIntoFunction : String :=
  "bloom_or_into:\n" ++
  "  li t0, 32                  # 256 bytes / 8 bytes per word\n" ++
  "  mv t1, a0                  # dst cursor\n" ++
  "  mv t2, a1                  # src cursor\n" ++
  ".Lboi_loop:\n" ++
  "  beqz t0, .Lboi_done\n" ++
  "  ld t3, 0(t1)\n" ++
  "  ld t4, 0(t2)\n" ++
  "  or t3, t3, t4\n" ++
  "  sd t3, 0(t1)\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t0, t0, -1\n" ++
  "  j .Lboi_loop\n" ++
  ".Lboi_done:\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_bloom_or_into`: probe BuildUnit.
    Input layout (after the host header):
      bytes  0..256 : src bloom
      bytes 256..512: dst bloom (will be OR-mutated)
    The probe runs `bloom_or_into(dst, src)` and emits the
    resulting dst bloom (256 bytes) as the output. -/
def ziskBloomOrIntoPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a1, a3, 16             # src bloom ptr (after host header)\n" ++
  "  addi a2, a3, 272            # dst bloom ptr (src + 256)\n" ++
  "  # Copy dst into the output region first, then OR src into it.\n" ++
  "  li t0, 0xa0010000\n" ++
  "  li t1, 32\n" ++
  ".Lboi_cp:\n" ++
  "  beqz t1, .Lboi_cp_done\n" ++
  "  ld t2, 0(a2)\n" ++
  "  sd t2, 0(t0)\n" ++
  "  addi a2, a2, 8\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lboi_cp\n" ++
  ".Lboi_cp_done:\n" ++
  "  li a0, 0xa0010000           # dst = output region\n" ++
  "  jal ra, bloom_or_into\n" ++
  "  j .Lboi_pdone\n" ++
  bloomOrIntoFunction ++ "\n" ++
  ".Lboi_pdone:"

def ziskBloomOrIntoDataSection : String :=
  ".section .data\n" ++
  "boi_pad:\n" ++
  "  .zero 8"

def ziskBloomOrIntoProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBloomOrIntoPrologue
  dataAsm     := ziskBloomOrIntoDataSection
}

/-! ## receipt_extract_logs_bloom -- PR-K152

    Extract the 256-byte `logs_bloom` field (field 2) from a
    receipt RLP. The receipt's inner shape (post-Byzantium,
    typed or untyped) is:

      receipt = rlp([status_or_postroot,
                     cumulative_gas_used,
                     logs_bloom (256 B fixed),
                     logs])

    For typed (EIP-2718) receipts on the wire, the caller is
    expected to have stripped the leading `0x<type>` byte, so
    `a0` points at the inner list's RLP prefix.

    Direct building block for block-level bloom validation: the
    block bloom is the OR-accumulation of every receipt's
    `logs_bloom`. With PR-K151 `bloom_or_into`, the loop becomes:

      bzero(block_bloom)
      for receipt in receipts:
        receipt_extract_logs_bloom(receipt, scratch)
        bloom_or_into(block_bloom, scratch)
      assert block_bloom == header.logs_bloom

    Composes:
      - PR-K20 `rlp_list_nth_item` on field 2

    Calling convention:
      a0 (input)  : receipt_rlp ptr (inner list, no type byte)
      a1 (input)  : receipt_rlp byte length
      a2 (input)  : 256-byte output bloom ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / fewer than 3 fields
        2 : logs_bloom field length != 256 -/
def receiptExtractLogsBloomFunction : String :=
  "receipt_extract_logs_bloom:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # receipt_rlp ptr\n" ++
  "  mv s1, a1                   # receipt_rlp len\n" ++
  "  mv s2, a2                   # output bloom ptr (256 B)\n" ++
  "  # ---- Field 2: logs_bloom (must be 256 bytes) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  la a3, relb_offset; la a4, relb_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lrelb_fail\n" ++
  "  la t0, relb_length; ld t1, 0(t0)\n" ++
  "  li t2, 256\n" ++
  "  bne t1, t2, .Lrelb_size_fail\n" ++
  "  la t0, relb_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1                              # src ptr\n" ++
  "  mv t4, s2                                   # dst ptr\n" ++
  "  li t5, 32                                   # 256 / 8 = 32 words\n" ++
  ".Lrelb_loop:\n" ++
  "  beqz t5, .Lrelb_done\n" ++
  "  ld t6, 0(t3)\n" ++
  "  sd t6, 0(t4)\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t4, t4, 8\n" ++
  "  addi t5, t5, -1\n" ++
  "  j .Lrelb_loop\n" ++
  ".Lrelb_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lrelb_ret\n" ++
  ".Lrelb_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lrelb_ret\n" ++
  ".Lrelb_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lrelb_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_receipt_extract_logs_bloom`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : receipt_rlp_len
      bytes  8..   : receipt_rlp (inner; no type byte)
    Output layout (256 B, exactly the ziskemu cap):
      bytes  0..256 : 256-byte logs_bloom -- on success.
                      On parse failure the helper writes nothing,
                      so callers must zero-init the output buffer
                      if they need to disambiguate. The fixture
                      script feeds well-formed inputs only and
                      relies on the bloom-byte equality for the
                      pass criterion. -/
def ziskReceiptExtractLogsBloomPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # receipt_rlp_len\n" ++
  "  addi a0, a3, 16             # receipt_rlp ptr\n" ++
  "  li a2, 0xa0010000           # output bloom ptr (256 B; full cap)\n" ++
  "  jal ra, receipt_extract_logs_bloom\n" ++
  "  j .Lrelb_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  receiptExtractLogsBloomFunction ++ "\n" ++
  ".Lrelb_pdone:"

def ziskReceiptExtractLogsBloomDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "relb_offset:\n" ++
  "  .zero 8\n" ++
  "relb_length:\n" ++
  "  .zero 8"

def ziskReceiptExtractLogsBloomProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskReceiptExtractLogsBloomPrologue
  dataAsm     := ziskReceiptExtractLogsBloomDataSection
}

/-! ## header_extract_logs_bloom -- PR-K153

    Extract the 256-byte `logs_bloom` field (field 6, 0-indexed)
    from a block header RLP. Header field layout from genesis on:

      [parent_hash, ommers_hash, coinbase,
       state_root, transactions_root, receipts_root,
       logs_bloom,                                   <-- field 6
       difficulty, number, gas_limit, gas_used,
       timestamp, extra_data, prev_randao / mix_hash,
       nonce, base_fee_per_gas?, withdrawals_root?,
       blob_gas_used?, excess_blob_gas?,
       parent_beacon_block_root?, requests_hash?]

    The bloom's position at field 6 is invariant across every
    fork from Frontier through Amsterdam; later forks only
    append new fields after it.

    Direct counterpart to PR-K152 `receipt_extract_logs_bloom`.
    Together with PR-K151 `bloom_or_into`, the verifier's
    `block_validate_logs_bloom` check becomes:

      header_extract_logs_bloom(header_rlp, header_bloom)
      bzero(computed_bloom)
      for receipt in receipts:
        receipt_extract_logs_bloom(receipt, scratch)
        bloom_or_into(computed_bloom, scratch)
      assert memcmp(header_bloom, computed_bloom) == 0

    Composes:
      - PR-K20 `rlp_list_nth_item` on field 6

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 256-byte output bloom ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / fewer than 7 fields
        2 : logs_bloom field length != 256 -/
def headerExtractLogsBloomFunction : String :=
  "header_extract_logs_bloom:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # header_rlp ptr\n" ++
  "  mv s1, a1                   # header_rlp len\n" ++
  "  mv s2, a2                   # output bloom ptr\n" ++
  "  # ---- Field 6: logs_bloom (must be 256 bytes) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 6\n" ++
  "  la a3, helb_offset; la a4, helb_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhelb_fail\n" ++
  "  la t0, helb_length; ld t1, 0(t0)\n" ++
  "  li t2, 256\n" ++
  "  bne t1, t2, .Lhelb_size_fail\n" ++
  "  la t0, helb_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1                              # src ptr\n" ++
  "  mv t4, s2                                   # dst ptr\n" ++
  "  li t5, 32                                   # 256 / 8 = 32 words\n" ++
  ".Lhelb_loop:\n" ++
  "  beqz t5, .Lhelb_done\n" ++
  "  ld t6, 0(t3)\n" ++
  "  sd t6, 0(t4)\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t4, t4, 8\n" ++
  "  addi t5, t5, -1\n" ++
  "  j .Lhelb_loop\n" ++
  ".Lhelb_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lhelb_ret\n" ++
  ".Lhelb_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhelb_ret\n" ++
  ".Lhelb_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhelb_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_extract_logs_bloom`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : header_rlp_len
      bytes  8..   : header_rlp
    Output layout (256 B, full ziskemu cap):
      bytes  0..256 : 256-byte logs_bloom on success;
                       caller-zeroed buffer on failure. -/
def ziskHeaderExtractLogsBloomPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_rlp_len\n" ++
  "  addi a0, a3, 16             # header_rlp ptr\n" ++
  "  li a2, 0xa0010000           # output bloom ptr (256 B)\n" ++
  "  jal ra, header_extract_logs_bloom\n" ++
  "  j .Lhelb_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractLogsBloomFunction ++ "\n" ++
  ".Lhelb_pdone:"

def ziskHeaderExtractLogsBloomDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "helb_offset:\n" ++
  "  .zero 8\n" ++
  "helb_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractLogsBloomProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractLogsBloomPrologue
  dataAsm     := ziskHeaderExtractLogsBloomDataSection
}

/-! ## bloom_eq -- PR-K154

    Byte-equal check between two 256-byte bloom filters. The
    final compare step in block-level bloom validation:

      assert bloom_eq(header.logs_bloom, computed_block_bloom)

    Returns the verdict as a u64 (1 if equal, 0 if not). The
    return code in `a0` is always 0 (the predicate result lives
    in the out pointer, not the status), so the caller can
    distinguish "predicate is false" from "the call itself
    failed" -- though here the call can never fail since there
    are no parse / boundary conditions to honour.

    Together with PR-K151 `bloom_or_into`, PR-K152
    `receipt_extract_logs_bloom`, and PR-K153
    `header_extract_logs_bloom`, this closes the
    block-level bloom-validation pipeline:

      header_extract_logs_bloom(header_rlp, header_bloom)
      bzero(computed_bloom)
      for receipt in receipts:
        receipt_extract_logs_bloom(receipt, scratch)
        bloom_or_into(computed_bloom, scratch)
      bloom_eq(header_bloom, computed_bloom, is_equal_out)
      assert is_equal_out == 1

    Pure register arithmetic; processes 8 bytes per iteration
    (32 iterations total) using `ld` + `xor` + `or`. Early-exit
    on first mismatch is intentionally avoided to keep the
    cycle count constant (256-byte compare is cheap and timing
    invariance is friendlier to gas-cost modeling).

    Calling convention:
      a0 (input)  : bloom_a ptr (256 bytes, read-only)
      a1 (input)  : bloom_b ptr (256 bytes, read-only)
      a2 (input)  : u64 out ptr (1 if equal, 0 if not)
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def bloomEqFunction : String :=
  "bloom_eq:\n" ++
  "  li t0, 32                  # 256 bytes / 8 bytes per word\n" ++
  "  mv t1, a0\n" ++
  "  mv t2, a1\n" ++
  "  li t5, 0                   # diff_accumulator\n" ++
  ".Lbeq_loop:\n" ++
  "  beqz t0, .Lbeq_done\n" ++
  "  ld t3, 0(t1)\n" ++
  "  ld t4, 0(t2)\n" ++
  "  xor t3, t3, t4\n" ++
  "  or  t5, t5, t3             # accumulate any nonzero diff\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t0, t0, -1\n" ++
  "  j .Lbeq_loop\n" ++
  ".Lbeq_done:\n" ++
  "  # is_equal = (diff_accumulator == 0)\n" ++
  "  seqz t5, t5\n" ++
  "  sd t5, 0(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_bloom_eq`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : pad
      bytes  8..264: bloom_a
      bytes 264..520: bloom_b
    Output layout:
      bytes  0.. 8 : status (always 0)
      bytes  8..16 : is_equal (u64; 1 if equal, 0 if not) -/
def ziskBloomEqPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 16             # bloom_a ptr (after 8B host-shift + 8B placeholder)\n" ++
  "  addi a1, a3, 272            # bloom_b ptr (a0 + 256)\n" ++
  "  li a2, 0xa0010008           # is_equal out\n" ++
  "  jal ra, bloom_eq\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbeq_pdone\n" ++
  bloomEqFunction ++ "\n" ++
  ".Lbeq_pdone:"

def ziskBloomEqDataSection : String :=
  ".section .data\n" ++
  "beq_pad:\n" ++
  "  .zero 8"

def ziskBloomEqProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBloomEqPrologue
  dataAsm     := ziskBloomEqDataSection
}

/-! ## block_logs_bloom_from_receipts_list -- PR-K158

    Given an RLP-encoded list of receipts, compute the block-level
    `logs_bloom` by OR-accumulating each receipt's `logs_bloom`
    field. End-to-end composite tying together the four atomic
    bloom helpers shipped in PR-K151..K154:

      bzero(block_bloom)
      for receipt in receipts:
        receipt_extract_logs_bloom(receipt, scratch)   # K152
        bloom_or_into(block_bloom, scratch)            # K151

    Used by `block_validate_logs_bloom` (combined with K153 to
    extract the header's claimed bloom and K154 to compare).

    Empty receipts list (`0xc0`) is valid and leaves the output
    bloom untouched. Per-receipt parse failures propagate via the
    return code.

    Composes:
      - PR-K20 `rlp_list_nth_item`       -- walk each receipt
      - PR-K47 `rlp_list_count_items`    -- list cardinality
      - PR-K152 `receipt_extract_logs_bloom`
      - PR-K151 `bloom_or_into`

    Calling convention:
      a0 (input)  : receipts_rlp_list ptr (RLP list of receipts)
      a1 (input)  : receipts_rlp_list byte length
      a2 (input)  : 256-byte output bloom ptr
                    (mutable, caller zero-inits)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure (outer list malformed or a
            receipt isn't a proper RLP list)
        2 : a receipt's `logs_bloom` field length != 256 -/
def blockLogsBloomFromReceiptsListFunction : String :=
  "block_logs_bloom_from_receipts_list:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # receipts list ptr\n" ++
  "  mv s1, a1                   # receipts list len\n" ++
  "  mv s2, a2                   # output bloom ptr\n" ++
  "  # ---- Count receipts ----\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, blbr_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lblbr_parse_fail\n" ++
  "  la t0, blbr_count; ld s3, 0(t0)              # n_receipts\n" ++
  "  li s4, 0                                     # i\n" ++
  ".Lblbr_loop:\n" ++
  "  bge s4, s3, .Lblbr_done\n" ++
  "  # Extract receipt_i bounds (full encoded item).\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s4\n" ++
  "  la a3, blbr_offset; la a4, blbr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lblbr_parse_fail\n" ++
  "  la t0, blbr_offset; ld t1, 0(t0)\n" ++
  "  la t0, blbr_length; ld t2, 0(t0)\n" ++
  "  add a0, s0, t1                                # receipt_i ptr\n" ++
  "  mv a1, t2                                    # receipt_i len\n" ++
  "  la a2, blbr_scratch_bloom\n" ++
  "  jal ra, receipt_extract_logs_bloom\n" ++
  "  bnez a0, .Lblbr_child_err                    # 1 or 2 -> propagate\n" ++
  "  # OR scratch_bloom into output bloom.\n" ++
  "  mv a0, s2\n" ++
  "  la a1, blbr_scratch_bloom\n" ++
  "  jal ra, bloom_or_into\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lblbr_loop\n" ++
  ".Lblbr_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lblbr_ret\n" ++
  ".Lblbr_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lblbr_ret\n" ++
  ".Lblbr_child_err:\n" ++
  "  # a0 carries the child's status (1 = parse fail, 2 = size fail).\n" ++
  ".Lblbr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_block_logs_bloom_from_receipts_list`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : receipts_list_rlp_len
      bytes  8..   : receipts_list_rlp
    Output layout (256 B, ziskemu cap):
      bytes  0..256 : accumulated logs_bloom (zero-initialised
                       by the probe before invoking the helper). -/
def ziskBlockLogsBloomFromReceiptsListPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # receipts_list_rlp_len\n" ++
  "  addi a0, a3, 16             # receipts_list_rlp ptr\n" ++
  "  li a2, 0xa0010000           # output bloom ptr (256 B)\n" ++
  "  # Zero output bloom (32 × sd zero).\n" ++
  "  mv t0, a2\n" ++
  "  li t1, 32\n" ++
  ".Lblbr_zero_loop:\n" ++
  "  beqz t1, .Lblbr_zero_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lblbr_zero_loop\n" ++
  ".Lblbr_zero_done:\n" ++
  "  jal ra, block_logs_bloom_from_receipts_list\n" ++
  "  j .Lblbr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  receiptExtractLogsBloomFunction ++ "\n" ++
  bloomOrIntoFunction ++ "\n" ++
  blockLogsBloomFromReceiptsListFunction ++ "\n" ++
  ".Lblbr_pdone:"

def ziskBlockLogsBloomFromReceiptsListDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "relb_offset:\n" ++
  "  .zero 8\n" ++
  "relb_length:\n" ++
  "  .zero 8\n" ++
  "blbr_count:\n" ++
  "  .zero 8\n" ++
  "blbr_offset:\n" ++
  "  .zero 8\n" ++
  "blbr_length:\n" ++
  "  .zero 8\n" ++
  "blbr_scratch_bloom:\n" ++
  "  .zero 256"

def ziskBlockLogsBloomFromReceiptsListProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockLogsBloomFromReceiptsListPrologue
  dataAsm     := ziskBlockLogsBloomFromReceiptsListDataSection
}

/-! ## block_validate_logs_bloom -- PR-K159

    End-to-end block-level `logs_bloom` validation: given the
    header RLP and the RLP list of receipts, recompute the
    block's bloom from receipts and check it byte-equals the
    header's claimed bloom.

      header_bloom = header_extract_logs_bloom(header_rlp)
      computed_bloom = block_logs_bloom_from_receipts_list(receipts)
      is_valid = bloom_eq(header_bloom, computed_bloom)

    Single-call entry point for callers that want the verdict
    without managing the scratch buffers themselves. The verdict
    is returned via an out pointer (1 if valid, 0 if not).

    Composes:
      - PR-K153 `header_extract_logs_bloom`        -- read header
      - PR-K158 `block_logs_bloom_from_receipts_list` -- recompute
      - PR-K154 `bloom_eq`                          -- compare

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : receipts_rlp_list ptr
      a3 (input)  : receipts_rlp_list byte length
      a4 (input)  : u64 out ptr (is_valid: 1 if matches, 0 if not)
      ra (input)  : return
      a0 (output) :
        0 : helpers succeeded -- predicate written
        1 : header parse failure / bloom field width != 256
        2 : receipts-list parse failure or receipt size failure
            (child status from PR-K158 propagated unchanged) -/
def blockValidateLogsBloomFunction : String :=
  "block_validate_logs_bloom:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # header_rlp ptr\n" ++
  "  mv s1, a1                   # header_rlp len\n" ++
  "  mv s2, a2                   # receipts list ptr\n" ++
  "  mv s3, a3                   # receipts list len\n" ++
  "  mv s4, a4                   # is_valid out\n" ++
  "  # ---- Extract header.logs_bloom into bvlb_header_bloom ----\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, bvlb_header_bloom\n" ++
  "  jal ra, header_extract_logs_bloom\n" ++
  "  bnez a0, .Lbvlb_header_fail\n" ++
  "  # ---- Zero bvlb_computed_bloom (256 B) ----\n" ++
  "  la t0, bvlb_computed_bloom\n" ++
  "  li t1, 32\n" ++
  ".Lbvlb_zero:\n" ++
  "  beqz t1, .Lbvlb_zero_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lbvlb_zero\n" ++
  ".Lbvlb_zero_done:\n" ++
  "  # ---- Compute block bloom from receipts list ----\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  la a2, bvlb_computed_bloom\n" ++
  "  jal ra, block_logs_bloom_from_receipts_list\n" ++
  "  bnez a0, .Lbvlb_receipts_fail\n" ++
  "  # ---- Compare the two blooms ----\n" ++
  "  la a0, bvlb_header_bloom\n" ++
  "  la a1, bvlb_computed_bloom\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, bloom_eq\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvlb_ret\n" ++
  ".Lbvlb_header_fail:\n" ++
  "  sd zero, 0(s4)\n" ++
  "  li a0, 1\n" ++
  "  j .Lbvlb_ret\n" ++
  ".Lbvlb_receipts_fail:\n" ++
  "  sd zero, 0(s4)\n" ++
  "  li a0, 2\n" ++
  ".Lbvlb_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_block_validate_logs_bloom`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : header_rlp_len
      bytes  8..16 : receipts_list_rlp_len
      bytes 16..   : header_rlp || receipts_list_rlp
        (the script appends them with no padding between; the
         prologue computes the second pointer from the first
         length).
    Output layout:
      bytes  0.. 8 : status (0=ok, 1=header fail, 2=receipts fail)
      bytes  8..16 : is_valid (1 if bloom matches, 0 otherwise) -/
def ziskBlockValidateLogsBloomPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # header_rlp_len\n" ++
  "  ld a3, 16(a5)               # receipts_list_rlp_len\n" ++
  "  addi a0, a5, 24             # header_rlp ptr\n" ++
  "  add a2, a0, a1              # receipts_list_rlp ptr\n" ++
  "  li a4, 0xa0010008           # is_valid out\n" ++
  "  jal ra, block_validate_logs_bloom\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbvlb_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  headerExtractLogsBloomFunction ++ "\n" ++
  receiptExtractLogsBloomFunction ++ "\n" ++
  bloomOrIntoFunction ++ "\n" ++
  bloomEqFunction ++ "\n" ++
  blockLogsBloomFromReceiptsListFunction ++ "\n" ++
  blockValidateLogsBloomFunction ++ "\n" ++
  ".Lbvlb_pdone:"

def ziskBlockValidateLogsBloomDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "helb_offset:\n" ++
  "  .zero 8\n" ++
  "helb_length:\n" ++
  "  .zero 8\n" ++
  "relb_offset:\n" ++
  "  .zero 8\n" ++
  "relb_length:\n" ++
  "  .zero 8\n" ++
  "blbr_count:\n" ++
  "  .zero 8\n" ++
  "blbr_offset:\n" ++
  "  .zero 8\n" ++
  "blbr_length:\n" ++
  "  .zero 8\n" ++
  "blbr_scratch_bloom:\n" ++
  "  .zero 256\n" ++
  "bvlb_header_bloom:\n" ++
  "  .zero 256\n" ++
  "bvlb_computed_bloom:\n" ++
  "  .zero 256"

def ziskBlockValidateLogsBloomProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateLogsBloomPrologue
  dataAsm     := ziskBlockValidateLogsBloomDataSection
}


end EvmAsm.Codegen
