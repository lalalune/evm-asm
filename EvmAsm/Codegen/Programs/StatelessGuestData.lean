/-
  EvmAsm.Codegen.Programs.StatelessGuestData

  `.data` section for the `stateless_guest` ELF.  Carved out of
  `Programs.lean` for the file-size hard cap; consumed by the
  registry hub via `statelessGuestDataSection`.

  Contains:
    * sha256 + keccak permutation scratch buffers (zkvm_sha256
      and zkvm_keccak256 require these by label).
    * SSZ merkleization scratch buffers (`ssz_merkleize_*`,
      `ssz_hb_*`, `ssz_ltb_*`, `ssz_ew_field_roots`).
    * `ssz_zero_hashes` lookup table (32 × 32 bytes).
    * Header-validator pipeline scratch (`sg_header_lengths`,
      `sg_kpr_valid`, `sg_kpr_bad_index`).
    * Shared K-PR scratch (`zk3_state`, `rfu_offset`,
      `rfu_length`) plus per-K-PR locals.
    * SSZ sub-tree constants used by the
      `compute_new_payload_request_root` computation at
      `.Lsg_hash`: `npr_node_0_15`, `npr_node_16_17`,
      `npr_versioned_hashes_root`, `npr_exec_requests_root`, and
      legacy `npr_left_subtree` / `empty_npr_root` (currently
      unreferenced but kept for context).
    * Two scratch buffers `npr_sha_input` (64 bytes) and
      `npr_sha_subtree` (32 bytes) plus `npr_exec_payload_root`
      / `npr_left_subtree_scratch` (32 bytes each) for the
      multi-step merkle computation.
-/
import EvmAsm.Codegen.Programs.Ssz

namespace EvmAsm.Codegen

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
  sszZeroHashesDataSection ++ "\n" ++
  -- Header-validator pipeline scratch:
  ".balign 8\n" ++
  "sg_header_lengths:\n" ++
  "  .zero 2048\n" ++          -- MAX_WITNESS_HEADERS (256) × 8 bytes
  "sg_kpr_valid:\n" ++
  "  .zero 8\n" ++
  "sg_kpr_bad_index:\n" ++
  "  .zero 8\n" ++
  -- Shared K-PR scratch (zk3_state / rfu_offset / rfu_length: used by
  -- rlp_list_nth_item + rlp_field_to_u64; same labels each K-PR
  -- declares, declared once here):
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  -- K290 chain_validate_post_merge_full scratch:
  "cvpmf_field:\n" ++
  "  .zero 8\n" ++
  "cvpmf_offset:\n" ++
  "  .zero 8\n" ++
  "cvpmf_length:\n" ++
  "  .zero 8\n" ++
  "cvpmf_iter_ptr:\n" ++
  "  .zero 8\n" ++
  "cvpmf_iter_i:\n" ++
  "  .zero 8\n" ++
  "cvpmf_empty_hash:\n" ++
  "  .byte 0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a\n" ++
  "  .byte 0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a\n" ++
  "  .byte 0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13\n" ++
  "  .byte 0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47\n" ++
  -- K291 chain_validate_extra_data_length scratch:
  "cvedl_offset:\n" ++
  "  .zero 8\n" ++
  "cvedl_length:\n" ++
  "  .zero 8\n" ++
  "cvedl_iter_ptr:\n" ++
  "  .zero 8\n" ++
  "cvedl_iter_i:\n" ++
  "  .zero 8\n" ++
  -- K240 chain_validate_gas_used_under_limit scratch:
  "cvgul_gas_used:\n" ++
  "  .zero 8\n" ++
  "cvgul_gas_limit:\n" ++
  "  .zero 8\n" ++
  "cvgul_iter_ptr:\n" ++
  "  .zero 8\n" ++
  "cvgul_iter_i:\n" ++
  "  .zero 8\n" ++
  -- K278 chain_validate_blob_gas_used_multiple scratch:
  "cvbgm_field:\n" ++
  "  .zero 8\n" ++
  "cvbgm_iter_ptr:\n" ++
  "  .zero 8\n" ++
  "cvbgm_iter_i:\n" ++
  "  .zero 8\n" ++
  -- K277 chain_validate_blob_gas_used_under_max scratch:
  "cvbgum_field:\n" ++
  "  .zero 8\n" ++
  "cvbgum_iter_ptr:\n" ++
  "  .zero 8\n" ++
  "cvbgum_iter_i:\n" ++
  "  .zero 8\n" ++
  -- K229 chain_validate_increasing_timestamps scratch:
  "cvit_ts:\n" ++
  "  .zero 8\n" ++
  "cvit_iter_child:\n" ++
  "  .zero 8\n" ++
  "cvit_iter_i:\n" ++
  "  .zero 8\n" ++
  "cvit_iter_prev:\n" ++
  "  .zero 8\n" ++
  -- K230 chain_validate_consecutive_numbers scratch:
  "cvcn_num:\n" ++
  "  .zero 8\n" ++
  "cvcn_iter_child:\n" ++
  "  .zero 8\n" ++
  "cvcn_iter_i:\n" ++
  "  .zero 8\n" ++
  "cvcn_iter_prev:\n" ++
  "  .zero 8\n" ++
  -- compute_new_payload_request_root(empty_input) -- the spec
  -- hash for an empty `SszNewPayloadRequest`, independent of
  -- chain_id. Was previously stamped at OUTPUT[0..32) by the
  -- epilogue; now derived dynamically via the
  -- exec_payload + NPR merkle computation in `.Lsg_hash`. Kept
  -- here as a reference value for diff context.
  -- (Verified against
  --  `execution-specs/.../stateless.compute_new_payload_request_root`
  --  on d7fe16ab8.)
  ".balign 8\n" ++
  "empty_npr_root:\n" ++
  "  .byte 0xf7, 0x83, 0x79, 0x28, 0xaf, 0x2f, 0xf9, 0x7a\n" ++
  "  .byte 0xdd, 0x39, 0x49, 0x6e, 0x3c, 0x72, 0xbc, 0xdf\n" ++
  "  .byte 0xba, 0xdf, 0xfc, 0x45, 0x3d, 0xee, 0x6a, 0x58\n" ++
  "  .byte 0x2c, 0xa2, 0xa5, 0xc7, 0xcc, 0x51, 0x2f, 0x71\n" ++
  -- SSZ field roots / merkle sub-trees for the NPR computation
  -- at `.Lsg_hash`. Under the currently-supported NPR class
  -- (default execution_payload modulo slot_number; default
  -- versioned_hashes; default execution_requests):
  --
  --   `npr_left_subtree` is sha256(field_root[execution_payload]
  --     || field_root[versioned_hashes]) for the empty case --
  --     LEGACY (was the precomputed left half before the
  --     dynamic exec_payload merkle path landed). Kept as
  --     unreferenced constant for context.
  --   `npr_versioned_hashes_root` is field_root[versioned_hashes]
  --     for the empty list; used as the right input to
  --     `left_subtree = sha256(exec_payload_root || vh_root)`.
  --   `npr_exec_requests_root` is field_root[execution_requests]
  --     for the empty case; used as the right input to
  --     `right_subtree = sha256(pbr || exec_requests_root)`.
  --   `npr_node_0_15` is the merkle root over the 16 left
  --     leaves of the default exec_payload Container (padded
  --     to 32 leaves).
  --   `npr_node_16_17` is sha256(leaf_16=ssz_zero_hash[0] ||
  --     leaf_17=block_access_list_root_for_empty).
  ".balign 8\n" ++
  "npr_left_subtree:\n" ++
  "  .byte 0x50, 0x57, 0xc2, 0x29, 0xce, 0xf7, 0x0b, 0x3d\n" ++
  "  .byte 0x2f, 0xe3, 0x46, 0xe2, 0xd6, 0x19, 0x8f, 0x3d\n" ++
  "  .byte 0xd5, 0x36, 0x5b, 0xd9, 0x65, 0x13, 0x22, 0xe8\n" ++
  "  .byte 0x81, 0xa0, 0x99, 0x4c, 0xbd, 0x34, 0x30, 0x57\n" ++
  ".balign 8\n" ++
  "npr_exec_requests_root:\n" ++
  "  .byte 0x85, 0xe2, 0x53, 0xb4, 0x05, 0x99, 0xd0, 0xdf\n" ++
  "  .byte 0x75, 0x6b, 0xe0, 0x43, 0xea, 0x69, 0x49, 0xe4\n" ++
  "  .byte 0x9a, 0x07, 0xe7, 0x56, 0xde, 0xef, 0x72, 0xb3\n" ++
  "  .byte 0x58, 0x8a, 0x4b, 0x05, 0x36, 0x22, 0x06, 0xb5\n" ++
  ".balign 8\n" ++
  "npr_sha_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "npr_sha_subtree:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "npr_node_0_15:\n" ++
  "  .byte 0x71, 0xfc, 0x71, 0x15, 0x80, 0xd1, 0x9a, 0x35\n" ++
  "  .byte 0x16, 0x98, 0xda, 0xb1, 0x39, 0x16, 0x66, 0xd8\n" ++
  "  .byte 0x49, 0xe0, 0x60, 0x9a, 0xea, 0x02, 0x09, 0x65\n" ++
  "  .byte 0x15, 0x6b, 0x5e, 0x8d, 0x8c, 0x83, 0xa2, 0xe7\n" ++
  ".balign 8\n" ++
  "npr_node_16_17:\n" ++
  "  .byte 0x95, 0xcc, 0x8c, 0xa6, 0xc4, 0xc1, 0x05, 0x66\n" ++
  "  .byte 0x41, 0xe5, 0xad, 0x8d, 0xc6, 0xe5, 0x66, 0xae\n" ++
  "  .byte 0x5e, 0x6f, 0xeb, 0x2c, 0x03, 0xde, 0x7a, 0xf8\n" ++
  "  .byte 0xfc, 0x95, 0x84, 0x0f, 0x55, 0xdf, 0x8b, 0x8c\n" ++
  ".balign 8\n" ++
  "npr_versioned_hashes_root:\n" ++
  "  .byte 0xdb, 0xa9, 0x67, 0x1b, 0xac, 0x95, 0x13, 0xc9\n" ++
  "  .byte 0x48, 0x2f, 0x14, 0x16, 0xa5, 0x3a, 0xab, 0xd2\n" ++
  "  .byte 0xc6, 0xce, 0x90, 0xd5, 0xa5, 0xf8, 0x65, 0xce\n" ++
  "  .byte 0x5a, 0x55, 0xc7, 0x75, 0x32, 0x5c, 0x91, 0x36\n" ++
  ".balign 8\n" ++
  "npr_exec_payload_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "npr_left_subtree_scratch:\n" ++
  "  .zero 32"

end EvmAsm.Codegen
