/-
  EvmAsm.Codegen.Programs.ChainEndpoints

  Chain-segment trie-root endpoint commitments carved out of
  `EvmAsm.Codegen.Programs.Chain` per the file-size hard cap.
  Hosts:

    K250  chain_extract_first_last_state_root
    K252  chain_extract_first_last_receipts_root
    K253  chain_extract_first_last_transactions_root
    K254  chain_extract_first_last_withdrawals_root

  All four extract the 32-byte field at the head and tail of an
  N-element header chain — useful as compact endpoint commitments
  for proving state/receipts/txs/withdrawals trie audits across
  a chain range.

  Compose K201/K203/K204/K205 (HeaderFields.lean) + K20
  rlp_list_nth_item (RlpRead.lean).

  Companion endpoint primitives K251 (block hashes), K255
  (prev_randao), K256 (beneficiary) live in HeaderChain.lean
  and HeaderFields.lean respectively due to file-size routing.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.HeaderFields

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## chain_extract_first_last_state_root -- PR-K250

    Extract `(headers[0].state_root, headers[N-1].state_root)`
    from an N-element header chain. Useful as a compact
    chain-segment endpoint commitment for proving state
    transition across a range. Composes K201
    `header_extract_state_root` (HeaderFields.lean) at the head
    and tail headers.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : 32-byte out (first_state_root)
      a4 (input)  : 32-byte out (last_state_root)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse fail at head or tail header -/
def chainExtractFirstLastStateRootFunction : String :=
  "chain_extract_first_last_state_root:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  beqz s0, .Lceflsr_empty\n" ++
  "  # first = headers[0].state_root\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  bnez a0, .Lceflsr_parse_fail\n" ++
  "  # Advance to last header\n" ++
  "  mv t1, s2\n" ++
  "  mv t2, s1\n" ++
  "  addi t3, s0, -1\n" ++
  ".Lceflsr_skip:\n" ++
  "  beqz t3, .Lceflsr_at_last\n" ++
  "  ld t4, 0(t2)\n" ++
  "  add t1, t1, t4\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lceflsr_skip\n" ++
  ".Lceflsr_at_last:\n" ++
  "  ld a1, 0(t2)\n" ++
  "  mv a0, t1\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  bnez a0, .Lceflsr_parse_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lceflsr_ret\n" ++
  ".Lceflsr_empty:\n" ++
  "  li a0, 1\n" ++
  "  j .Lceflsr_ret\n" ++
  ".Lceflsr_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lceflsr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainExtractFirstLastStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010028\n" ++
  "  jal ra, chain_extract_first_last_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lceflsr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  chainExtractFirstLastStateRootFunction ++ "\n" ++
  ".Lceflsr_pdone:"

def ziskChainExtractFirstLastStateRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8"

def ziskChainExtractFirstLastStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainExtractFirstLastStateRootPrologue
  dataAsm     := ziskChainExtractFirstLastStateRootDataSection
}

/-! ## chain_extract_first_last_receipts_root -- PR-K252

    Extract `(headers[0].receipts_root, headers[N-1].receipts_root)`
    from an N-element header chain. Sister to K250
    `chain_extract_first_last_state_root`; receipts-trie endpoint
    commitment.

    Composes K203 `header_extract_receipts_root` (HeaderFields.lean)
    at the head and tail headers.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : 32-byte out (first_receipts_root)
      a4 (input)  : 32-byte out (last_receipts_root)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse fail at head or tail header -/
def chainExtractFirstLastReceiptsRootFunction : String :=
  "chain_extract_first_last_receipts_root:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  beqz s0, .Lceflrr_empty\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_receipts_root\n" ++
  "  bnez a0, .Lceflrr_parse_fail\n" ++
  "  mv t1, s2\n" ++
  "  mv t2, s1\n" ++
  "  addi t3, s0, -1\n" ++
  ".Lceflrr_skip:\n" ++
  "  beqz t3, .Lceflrr_at_last\n" ++
  "  ld t4, 0(t2)\n" ++
  "  add t1, t1, t4\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lceflrr_skip\n" ++
  ".Lceflrr_at_last:\n" ++
  "  ld a1, 0(t2)\n" ++
  "  mv a0, t1\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, header_extract_receipts_root\n" ++
  "  bnez a0, .Lceflrr_parse_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lceflrr_ret\n" ++
  ".Lceflrr_empty:\n" ++
  "  li a0, 1\n" ++
  "  j .Lceflrr_ret\n" ++
  ".Lceflrr_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lceflrr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainExtractFirstLastReceiptsRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010028\n" ++
  "  jal ra, chain_extract_first_last_receipts_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lceflrr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractReceiptsRootFunction ++ "\n" ++
  chainExtractFirstLastReceiptsRootFunction ++ "\n" ++
  ".Lceflrr_pdone:"

def ziskChainExtractFirstLastReceiptsRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "herr_offset:\n" ++
  "  .zero 8\n" ++
  "herr_length:\n" ++
  "  .zero 8"

def ziskChainExtractFirstLastReceiptsRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainExtractFirstLastReceiptsRootPrologue
  dataAsm     := ziskChainExtractFirstLastReceiptsRootDataSection
}

/-! ## chain_extract_first_last_transactions_root -- PR-K253

    Extract `(headers[0].transactions_root,
    headers[N-1].transactions_root)` from an N-element header
    chain. Completes the trie-endpoint family alongside K250
    (state_root field 3), K251 (block hashes), K252
    (receipts_root field 5). Useful as a compact endpoint
    commitment for txs-trie audit across a chain range.

    Composes K204 `header_extract_transactions_root`
    (HeaderFields.lean) at head and tail headers.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : 32-byte out (first_transactions_root)
      a4 (input)  : 32-byte out (last_transactions_root)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse fail at head or tail header -/
def chainExtractFirstLastTransactionsRootFunction : String :=
  "chain_extract_first_last_transactions_root:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  beqz s0, .Lcefltr_empty\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_transactions_root\n" ++
  "  bnez a0, .Lcefltr_parse_fail\n" ++
  "  mv t1, s2\n" ++
  "  mv t2, s1\n" ++
  "  addi t3, s0, -1\n" ++
  ".Lcefltr_skip:\n" ++
  "  beqz t3, .Lcefltr_at_last\n" ++
  "  ld t4, 0(t2)\n" ++
  "  add t1, t1, t4\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lcefltr_skip\n" ++
  ".Lcefltr_at_last:\n" ++
  "  ld a1, 0(t2)\n" ++
  "  mv a0, t1\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, header_extract_transactions_root\n" ++
  "  bnez a0, .Lcefltr_parse_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lcefltr_ret\n" ++
  ".Lcefltr_empty:\n" ++
  "  li a0, 1\n" ++
  "  j .Lcefltr_ret\n" ++
  ".Lcefltr_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lcefltr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainExtractFirstLastTransactionsRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010028\n" ++
  "  jal ra, chain_extract_first_last_transactions_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcefltr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractTransactionsRootFunction ++ "\n" ++
  chainExtractFirstLastTransactionsRootFunction ++ "\n" ++
  ".Lcefltr_pdone:"

def ziskChainExtractFirstLastTransactionsRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "hetr_offset:\n" ++
  "  .zero 8\n" ++
  "hetr_length:\n" ++
  "  .zero 8"

def ziskChainExtractFirstLastTransactionsRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainExtractFirstLastTransactionsRootPrologue
  dataAsm     := ziskChainExtractFirstLastTransactionsRootDataSection
}

/-! ## chain_extract_first_last_withdrawals_root -- PR-K254

    Extract `(headers[0].withdrawals_root,
    headers[N-1].withdrawals_root)` from an N-element header
    chain. Completes the trie-endpoint family alongside K250
    (state_root), K251 (block hashes), K252 (receipts_root),
    K253 (transactions_root). Withdrawals are Shanghai+; pre-
    Shanghai headers don't have field 16 and return parse-fail.

    Composes K205 `header_extract_withdrawals_root`
    (HeaderFields.lean) at head and tail headers.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : 32-byte out (first_withdrawals_root)
      a4 (input)  : 32-byte out (last_withdrawals_root)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse fail at head or tail header
            (pre-Shanghai header missing withdrawals_root) -/
def chainExtractFirstLastWithdrawalsRootFunction : String :=
  "chain_extract_first_last_withdrawals_root:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  beqz s0, .Lceflwr_empty\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_withdrawals_root\n" ++
  "  bnez a0, .Lceflwr_parse_fail\n" ++
  "  mv t1, s2\n" ++
  "  mv t2, s1\n" ++
  "  addi t3, s0, -1\n" ++
  ".Lceflwr_skip:\n" ++
  "  beqz t3, .Lceflwr_at_last\n" ++
  "  ld t4, 0(t2)\n" ++
  "  add t1, t1, t4\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lceflwr_skip\n" ++
  ".Lceflwr_at_last:\n" ++
  "  ld a1, 0(t2)\n" ++
  "  mv a0, t1\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, header_extract_withdrawals_root\n" ++
  "  bnez a0, .Lceflwr_parse_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lceflwr_ret\n" ++
  ".Lceflwr_empty:\n" ++
  "  li a0, 1\n" ++
  "  j .Lceflwr_ret\n" ++
  ".Lceflwr_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lceflwr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainExtractFirstLastWithdrawalsRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010028\n" ++
  "  jal ra, chain_extract_first_last_withdrawals_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lceflwr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractWithdrawalsRootFunction ++ "\n" ++
  chainExtractFirstLastWithdrawalsRootFunction ++ "\n" ++
  ".Lceflwr_pdone:"

def ziskChainExtractFirstLastWithdrawalsRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "hewr_offset:\n" ++
  "  .zero 8\n" ++
  "hewr_length:\n" ++
  "  .zero 8"

def ziskChainExtractFirstLastWithdrawalsRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainExtractFirstLastWithdrawalsRootPrologue
  dataAsm     := ziskChainExtractFirstLastWithdrawalsRootDataSection
}

/-! ## chain_extract_first_last_ommers_hash -- PR-K257

    Extract `(headers[0].ommers_hash, headers[N-1].ommers_hash)`
    from an N-element header chain. Post-merge, ommers_hash is
    always `EMPTY_OMMERS_HASH = keccak256(rlp([]))`; pre-merge it
    keccaks the (now-removed) ommers/uncles list. Useful as a
    consistency check that no header in the segment has uncles
    (paired with K222 chain_validate_full's K179 K84 invariants).

    Sister to K250-K256 endpoint family. Composes K206
    `header_extract_ommers_hash` at head and tail headers.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : 32-byte out (first_ommers_hash)
      a4 (input)  : 32-byte out (last_ommers_hash)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse fail at head or tail header -/
def chainExtractFirstLastOmmersHashFunction : String :=
  "chain_extract_first_last_ommers_hash:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  beqz s0, .Lcefloh_empty\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_ommers_hash\n" ++
  "  bnez a0, .Lcefloh_parse_fail\n" ++
  "  mv t1, s2\n" ++
  "  mv t2, s1\n" ++
  "  addi t3, s0, -1\n" ++
  ".Lcefloh_skip:\n" ++
  "  beqz t3, .Lcefloh_at_last\n" ++
  "  ld t4, 0(t2)\n" ++
  "  add t1, t1, t4\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lcefloh_skip\n" ++
  ".Lcefloh_at_last:\n" ++
  "  ld a1, 0(t2)\n" ++
  "  mv a0, t1\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, header_extract_ommers_hash\n" ++
  "  bnez a0, .Lcefloh_parse_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lcefloh_ret\n" ++
  ".Lcefloh_empty:\n" ++
  "  li a0, 1\n" ++
  "  j .Lcefloh_ret\n" ++
  ".Lcefloh_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lcefloh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainExtractFirstLastOmmersHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010028\n" ++
  "  jal ra, chain_extract_first_last_ommers_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcefloh_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractOmmersHashFunction ++ "\n" ++
  chainExtractFirstLastOmmersHashFunction ++ "\n" ++
  ".Lcefloh_pdone:"

def ziskChainExtractFirstLastOmmersHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "heoh_offset:\n" ++
  "  .zero 8\n" ++
  "heoh_length:\n" ++
  "  .zero 8"

def ziskChainExtractFirstLastOmmersHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainExtractFirstLastOmmersHashPrologue
  dataAsm     := ziskChainExtractFirstLastOmmersHashDataSection
}

/-! ## chain_extract_first_last_block_hash -- PR-K251

    Extract `(keccak256(headers[0]), keccak256(headers[N-1]))`
    from an N-element header chain. Useful as a compact
    chain-segment endpoint commitment (the consensus-visible
    block hashes at the chain tip and the chain start).
    Companion to K200 `chain_block_hashes_commitment` (which
    keccak-folds ALL block hashes); this is the lighter
    endpoints-only variant.

    Composes K172 `block_hash_from_header` (Header.lean) on the
    head and tail headers.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : 32-byte out (first_block_hash)
      a4 (input)  : 32-byte out (last_block_hash)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0) -/
def chainExtractFirstLastBlockHashFunction : String :=
  "chain_extract_first_last_block_hash:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  beqz s0, .Lceflbh_empty\n" ++
  "  # first = keccak256(headers[0])\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  # Advance to last header\n" ++
  "  mv t1, s2\n" ++
  "  mv t2, s1\n" ++
  "  addi t3, s0, -1\n" ++
  ".Lceflbh_skip:\n" ++
  "  beqz t3, .Lceflbh_at_last\n" ++
  "  ld t4, 0(t2)\n" ++
  "  add t1, t1, t4\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lceflbh_skip\n" ++
  ".Lceflbh_at_last:\n" ++
  "  ld a1, 0(t2)\n" ++
  "  mv a0, t1\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  li a0, 0\n" ++
  "  j .Lceflbh_ret\n" ++
  ".Lceflbh_empty:\n" ++
  "  li a0, 1\n" ++
  ".Lceflbh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainExtractFirstLastBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010028\n" ++
  "  jal ra, chain_extract_first_last_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lceflbh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  chainExtractFirstLastBlockHashFunction ++ "\n" ++
  ".Lceflbh_pdone:"

def ziskChainExtractFirstLastBlockHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskChainExtractFirstLastBlockHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainExtractFirstLastBlockHashPrologue
  dataAsm     := ziskChainExtractFirstLastBlockHashDataSection
}

/-! ## chain_extract_first_last_prev_randao -- PR-K255

    Extract `(headers[0].prev_randao, headers[N-1].prev_randao)`
    from an N-element header chain. The post-merge `prev_randao`
    field (header field 13, 32 B) is the value returned by the
    PREVRANDAO opcode and is committed to via the consensus
    beacon-chain randomness mix. Useful as an endpoint commitment
    for randomness-trace audits across a chain range.

    Sister to K250 (state_root), K251 (block hashes), K252
    (receipts_root), K253 (transactions_root), K254
    (withdrawals_root).

    Composes K207 `header_extract_prev_randao` (HeaderFields.lean)
    at head and tail headers.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : 32-byte out (first_prev_randao)
      a4 (input)  : 32-byte out (last_prev_randao)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse fail at head or tail header -/
def chainExtractFirstLastPrevRandaoFunction : String :=
  "chain_extract_first_last_prev_randao:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  beqz s0, .Lceflpr_empty\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_prev_randao\n" ++
  "  bnez a0, .Lceflpr_parse_fail\n" ++
  "  mv t1, s2\n" ++
  "  mv t2, s1\n" ++
  "  addi t3, s0, -1\n" ++
  ".Lceflpr_skip:\n" ++
  "  beqz t3, .Lceflpr_at_last\n" ++
  "  ld t4, 0(t2)\n" ++
  "  add t1, t1, t4\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lceflpr_skip\n" ++
  ".Lceflpr_at_last:\n" ++
  "  ld a1, 0(t2)\n" ++
  "  mv a0, t1\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, header_extract_prev_randao\n" ++
  "  bnez a0, .Lceflpr_parse_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lceflpr_ret\n" ++
  ".Lceflpr_empty:\n" ++
  "  li a0, 1\n" ++
  "  j .Lceflpr_ret\n" ++
  ".Lceflpr_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lceflpr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainExtractFirstLastPrevRandaoPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010028\n" ++
  "  jal ra, chain_extract_first_last_prev_randao\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lceflpr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractPrevRandaoFunction ++ "\n" ++
  chainExtractFirstLastPrevRandaoFunction ++ "\n" ++
  ".Lceflpr_pdone:"

def ziskChainExtractFirstLastPrevRandaoDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "hepr_offset:\n" ++
  "  .zero 8\n" ++
  "hepr_length:\n" ++
  "  .zero 8"

def ziskChainExtractFirstLastPrevRandaoProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainExtractFirstLastPrevRandaoPrologue
  dataAsm     := ziskChainExtractFirstLastPrevRandaoDataSection
}

end EvmAsm.Codegen
