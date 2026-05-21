/-
  EvmAsm.Stateless.Witness.MPT.Decode

  RLP-decode a single MPT node. The wire format (Ethereum MPT) is
  one of three RLP shapes selected by item count + first nibble:

  - **Branch node**: 17-item RLP list. Items 0..16 are child
    references (32-byte hash or inlined RLP < 32 bytes). Item 16
    is the value at this prefix (often empty bytes).
  - **Extension node**: 2-item RLP list `[encoded_path,
    child_ref]`. The encoded_path is HP-encoded nibbles with
    flag bits in the first byte indicating "extension".
  - **Leaf node**: 2-item RLP list `[encoded_path, value]`. Same
    HP encoding as extension but with the "leaf" flag set.

  The decoder returns the node variant + decoded fields without
  copying — the input RLP buffer is in the node_db, and the
  decoder just records `(item_start, item_len)` offsets into a
  small node-shape struct in scratch RAM.

  ## PR-K20 status

  The first primitive lands: `rlp_list_nth_item` walks an
  RLP-encoded list to extract the N-th item's content bounds.
  Higher-level node decoding (variant classification + per-
  shape extraction) composes this primitive in follow-ups:

    - PR-K20 (this)  : `rlp_list_nth_item`
    - PR-K21+ (next) : `mpt_node_kind` (leaf / extension / branch
                       classification from item count + first
                       nibble of item 0)
    - PR-K22+        : `mpt_branch_child` wraps PR-K20 with
                       index in 0..15
    - PR-K23+        : `mpt_leaf_extract_value` / `mpt_extension_next`

  Calling convention for `rlp_list_nth_item`:

      Input:
        a0 (input)  : list bytes ptr (start of the outer RLP
                      list prefix)
        a1 (input)  : total list byte length
        a2 (input)  : index N (0-based)
        a3 (input)  : u64 out ptr (item N's *content* offset
                      within `list_bytes`, NOT including the
                      RLP type prefix)
        a4 (input)  : u64 out ptr (item N's content byte length)
        ra (input)  : return

      Output:
        a0 = 0  iff item N exists within the list
        a0 = 1  on parse error or N >= number_of_items.

  The "content" interpretation means:
    * Single byte (0x00..0x7f)           → offset points AT the byte; length = 1
    * Short string (0x80..0xb7)          → offset = item_start+1; length = b - 0x80
    * Long string (0xb8..0xbf)           → offset = item_start+1+lol; length = decoded
    * List items (0xc0..0xff)            → offset = item_start; length = full encoded length

  i.e. for byte-string items, the prefix is stripped; for sub-
  lists the full encoded form is returned so callers can recurse.

  ## Implementation shape

  `rlpListNthItemFunction` emits `rlp_list_nth_item:`. Pure
  register arithmetic; no scratch memory; leaf-callable.
-/

namespace EvmAsm.Stateless.Witness.MPT.Decode

-- TODO(stateless-witness): expose a `cpsTripleWithin` spec for
-- `rlp_list_nth_item` once the RLP semantics are formalised.

end EvmAsm.Stateless.Witness.MPT.Decode
