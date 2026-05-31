#!/usr/bin/env python3
"""Self-contained Merkle-Patricia-Trie reference for the stateless guest's
post-state-root recompute (mpt_set / mpt_root).

Used to generate (witness_nodes, root_hash, path_nibbles, new_value,
expected_new_root) test vectors and ziskemu `-i` probe inputs for the
`zisk_mpt_set` probe, and to cross-check the guest's RV64 implementation
byte-for-byte (the same discipline that validated mpt_walk and the node
encoders). RLP + keccak match Ethereum canonical encoding; verified here
against the guest's existing `single_leaf_trie_root` for the leaf case.

Scope of the FIRST milestone: VALUE-ONLY update of an EXISTING key (no
insert/delete, no structural change) — covers existing-account balance/
nonce updates and existing-slot updates, the bulk of state transitions.
The witness needs only the nodes ON THE PATH (root..leaf); a branch's
sibling slots are referenced by their unchanged refs inside the branch
RLP, so sibling bodies are not required.
"""
from __future__ import annotations
import struct, sys
from Crypto.Hash import keccak  # pycryptodome (available in execution-specs venv)


def k256(b: bytes) -> bytes:
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()


# ---- minimal RLP ----------------------------------------------------------
def rlp_len_prefix(length: int, base: int) -> bytes:
    if length < 56:
        return bytes([base + length])
    bl = length.to_bytes((length.bit_length() + 7) // 8, "big")
    return bytes([base + 55 + len(bl)]) + bl


def rlp_bytes(b: bytes) -> bytes:
    if len(b) == 1 and b[0] < 0x80:
        return b
    return rlp_len_prefix(len(b), 0x80) + b


def rlp_list(items: list[bytes]) -> bytes:
    payload = b"".join(items)
    return rlp_len_prefix(len(payload), 0xC0) + payload


# ---- HP (hex-prefix) encoding ---------------------------------------------
def hp_encode(nibbles: list[int], is_leaf: bool) -> bytes:
    flag = (2 if is_leaf else 0) + (1 if len(nibbles) % 2 else 0)
    out = bytearray()
    if len(nibbles) % 2 == 1:
        out.append(flag * 16 + nibbles[0]); nibbles = nibbles[1:]
    else:
        out.append(flag * 16)
    for i in range(0, len(nibbles), 2):
        out.append(nibbles[i] * 16 + nibbles[i + 1])
    return bytes(out)


# ---- node encoders --------------------------------------------------------
def leaf_node(path_nibbles: list[int], value: bytes) -> bytes:
    return rlp_list([rlp_bytes(hp_encode(path_nibbles, True)), rlp_bytes(value)])


def extension_node(path_nibbles: list[int], child_ref: bytes) -> bytes:
    # child_ref is an already-RLP-encoded item (0xa0||hash for hashed, or the
    # inline node RLP for <32B). It is concatenated verbatim into the list.
    return rlp_len_prefix(len(rlp_bytes(hp_encode(path_nibbles, False))) + len(child_ref), 0xC0) + \
           rlp_bytes(hp_encode(path_nibbles, False)) + child_ref


def branch_node(slots: list[bytes], value: bytes = b"") -> bytes:
    # slots: 16 already-RLP-encoded child refs (each b"\x80" if empty, else
    # the inline node RLP or 0xa0||hash); value is the 17th item.
    payload = b"".join(slots) + rlp_bytes(value)
    return rlp_len_prefix(len(payload), 0xC0) + payload


def node_ref(node_rlp: bytes) -> bytes:
    """The reference to a node as it appears inside its parent: the inline
    node RLP if <32 bytes, else 0xa0 || keccak256(node_rlp)."""
    if len(node_rlp) < 32:
        return node_rlp
    return b"\xa0" + k256(node_rlp)


def trie_root(root_node_rlp: bytes) -> bytes:
    """Root hash of a trie whose root node is root_node_rlp."""
    if len(root_node_rlp) < 32:
        return k256(root_node_rlp)  # tiny tries still hash the root
    return k256(root_node_rlp)


# ---- ziskemu probe input (mirrors mpt_walk's layout, + new_value) ---------
#   INPUT+8  : witness_len           INPUT+16 : path_len (nibbles)
#   INPUT+24 : new_value_len         INPUT+32 : root_hash (32B)
#   INPUT+64 : path_nibbles (1B each), then new_value, then witness section
def build_probe_input(root_hash, path_nibbles, new_value, witness_section) -> bytes:
    body = bytearray()
    body += struct.pack("<Q", len(witness_section))   # +8
    body += struct.pack("<Q", len(path_nibbles))      # +16
    body += struct.pack("<Q", len(new_value))         # +24
    body += root_hash                                 # +32 .. +64
    body += bytes(path_nibbles)                        # +64 ..
    body += new_value
    # 8-align before the witness section
    while len(body) % 8 != 0:
        body += b"\x00"
    body += witness_section
    # ziskemu maps the probe file directly to INPUT+8 (the probe reads its
    # first field at INPUT+8 == file[0:8]); no outer length prefix.
    body += b"\x00" * ((-len(body)) % 8)
    return bytes(body)


def ssz_section(elements: list[bytes]) -> bytes:
    """SSZ List[ByteList] wire form: u32 offset table then concatenated bodies
    (matches witness.state, what witness_lookup_by_hash scans)."""
    out = bytearray(); off = 4 * len(elements)
    for e in elements:
        out += struct.pack("<I", off); off += len(e)
    for e in elements:
        out += e
    return bytes(out)


# ---- vector shapes (value-only update of an existing key) -----------------
# On-path leaves in the branch/ext shapes use a >=32-byte value so their RLP
# hashes (node_ref => 0xa0||keccak): then EVERY on-path node is a distinct
# witness element with a clean section-relative byte offset, which the
# record-walk reports and the reference predicts without modelling
# inline-child positions. (The leaf shape's single leaf is found via
# root_hash regardless of size, so it stays short.)
A_OLD = b"a" * 32                  # forces la_old to hash
A_NEW = b"a-new-value-xyz"         # new value (record-walk ignores it)


def vec_leaf():
    """Trie = single leaf (root). key path = full 4 nibbles. depth 0."""
    path = [0x1, 0x2, 0x3, 0x4]
    old, new = b"old-value", b"new-value-1234"
    root_node = leaf_node(path, old)
    new_root_node = leaf_node(path, new)
    # levels: the non-terminal (branch/extension) nodes on the path, in
    # root->leaf order. (kind, nibble, nibbles_consumed). Empty for a leaf.
    return dict(name="leaf", witness=[root_node], root=trie_root(root_node),
                path=path, new_value=new, expected=trie_root(new_root_node),
                levels=[])


def vec_branch():
    """Trie = branch(root) with two leaf children at nibble 1 and 2. Update
    the child at nibble 1 (path 1,a,b). depth 1."""
    la_path, lb_path = [0xa, 0xb], [0xc, 0xd]
    b_val = b"b-val"
    la_old = leaf_node(la_path, A_OLD); lb = leaf_node(lb_path, b_val)
    slots = [b"\x80"] * 16
    slots[1] = node_ref(la_old); slots[2] = node_ref(lb)
    root_node = branch_node(slots)
    # update: child at nibble 1 -> new value
    la_new = leaf_node(la_path, A_NEW)
    slots2 = list(slots); slots2[1] = node_ref(la_new)
    new_root_node = branch_node(slots2)
    witness = [root_node, la_old]  # path nodes (lb not needed for value-only)
    return dict(name="branch", witness=witness, root=trie_root(root_node),
                path=[0x1] + la_path, new_value=A_NEW,
                expected=trie_root(new_root_node),
                levels=[("branch", 0x1, 1)])


def vec_ext_branch():
    """Trie = extension(root, prefix=[5,6]) -> branch -> two leaves. Update
    child at nibble 1 (path 5,6,1,a,b). depth 2."""
    ext_prefix = [0x5, 0x6]
    la_path, lb_path = [0xa, 0xb], [0xc, 0xd]
    b_val = b"b-val"
    la_old = leaf_node(la_path, A_OLD); lb = leaf_node(lb_path, b_val)
    slots = [b"\x80"] * 16
    slots[1] = node_ref(la_old); slots[2] = node_ref(lb)
    branch = branch_node(slots)
    root_node = extension_node(ext_prefix, node_ref(branch))
    # update
    la_new = leaf_node(la_path, A_NEW)
    slots2 = list(slots); slots2[1] = node_ref(la_new)
    branch2 = branch_node(slots2)
    new_root_node = extension_node(ext_prefix, node_ref(branch2))
    witness = [root_node, branch, la_old]
    return dict(name="ext_branch", witness=witness, root=trie_root(root_node),
                path=ext_prefix + [0x1] + la_path, new_value=A_NEW,
                expected=trie_root(new_root_node),
                levels=[("extension", 0, len(ext_prefix)),
                        ("branch", 0x1, 1)])


VECTORS = [vec_leaf, vec_branch, vec_ext_branch]


# ---- accumulating (2 sequential updates) vector (mpt_set_acc .4.3.1) -------
# Two value-only updates applied in sequence to a branch trie: update key A
# (nibble 1), then key B (nibble 2) starting from the NEW root. This forces
# the appendable node DB: update 2's walk starts at update 1's new root
# (only in the DB, not the witness) and descends into the unchanged sibling
# leaf (resolved from the witness). Both old leaves are >=32 bytes so they
# are hash-referenced (distinct witness elements), and the new root branch is
# itself >=32 so it is hash-keyed in the DB.
def build_acc_probe_input(root_hash, p1, v1, p2, v2, witness_section) -> bytes:
    """ziskemu `-i` body for zisk_mpt_set_acc (file maps to INPUT+8):
      +8 witness_len | +16 path1_len | +24 value1_len | +32 path2_len
      +40 value2_len | +48 root_hash(32B) | +80 path1 | value1 | path2
      | value2 | witness  -- each variable segment padded to 8 bytes."""
    body = bytearray()
    body += struct.pack("<Q", len(witness_section))   # +8
    body += struct.pack("<Q", len(p1))                # +16
    body += struct.pack("<Q", len(v1))                # +24
    body += struct.pack("<Q", len(p2))                # +32
    body += struct.pack("<Q", len(v2))                # +40
    body += root_hash                                 # +48 .. +80
    for seg in (bytes(p1), v1, bytes(p2), v2, witness_section):
        body += seg
        while len(body) % 8 != 0:
            body += b"\x00"
    return bytes(body)


def vec_acc():
    la_path, lb_path = [0xa, 0xb], [0xc, 0xd]
    a_old, b_old = b"a" * 32, b"b" * 32          # >=32 => hashed children
    v1, v2 = b"v1-new", b"v2-new-value-padded-to-thirty2!"
    la_old = leaf_node(la_path, a_old); lb_old = leaf_node(lb_path, b_old)
    slots = [b"\x80"] * 16
    slots[1] = node_ref(la_old); slots[2] = node_ref(lb_old)
    root_node = branch_node(slots)
    witness = [root_node, la_old, lb_old]
    # expected final trie after both updates
    la_new = leaf_node(la_path, v1); lb_new = leaf_node(lb_path, v2)
    fslots = list(slots)
    fslots[1] = node_ref(la_new); fslots[2] = node_ref(lb_new)
    final_root_node = branch_node(fslots)
    return dict(name="acc", witness=witness, root=trie_root(root_node),
                path1=[0x1] + la_path, value1=v1,
                path2=[0x2] + lb_path, value2=v2,
                expected=trie_root(final_root_node))


# ---- record-walk expectation (mpt_set .4.2.1) -----------------------------
def element_offsets(witness: list[bytes]) -> list[int]:
    """Byte offset of each element BODY within an ssz_section: the u32 offset
    table (4 bytes/element) followed by the concatenated bodies."""
    base = 4 * len(witness); offs = []; cur = base
    for e in witness:
        offs.append(cur); cur += len(e)
    return offs


def record_walk_expected(v: dict) -> list[tuple[str, int, int]]:
    """Expected probe OUTPUT fields for `zisk_mpt_set_record_walk` as
    (name, byte_offset_in_output, u64_value). Mirrors the asm descent: every
    on-path node is witness element i (path order); records 0..depth-1 are
    the branch/extension nodes, the terminal (leaf) is element `depth`.

    OUTPUT layout: status@0, meta(depth,consumed,leaf_offset,leaf_len)@8,
    records (offset,len,kind,nibble) 32 B each @128.
    """
    witness, levels = v["witness"], v["levels"]
    offs = element_offsets(witness)
    depth = len(levels)
    assert depth == len(witness) - 1, f"{v['name']}: depth/witness mismatch"
    consumed = sum(consumed_n for (_k, _nib, consumed_n) in levels)
    out = [
        ("status", 0, 0),
        ("depth", 8, depth),
        ("consumed", 16, consumed),
        ("leaf_offset", 24, offs[depth]),
        ("leaf_len", 32, len(witness[depth])),
    ]
    for i, (kind, nibble, _c) in enumerate(levels):
        base = 128 + 32 * i
        out += [
            (f"rec{i}_offset", base + 0, offs[i]),
            (f"rec{i}_len", base + 8, len(witness[i])),
            (f"rec{i}_kind", base + 16, 0 if kind == "branch" else 1),
            (f"rec{i}_nibble", base + 24, nibble),
        ]
    return out

if __name__ == "__main__":
    import os
    outdir = sys.argv[1] if len(sys.argv) > 1 else "gen-out/mpt-set"
    os.makedirs(outdir, exist_ok=True)
    for mk in VECTORS:
        v = mk()
        sec = ssz_section(v["witness"])
        inp = build_probe_input(v["root"], v["path"], v["new_value"], sec)
        with open(f"{outdir}/{v['name']}.input", "wb") as f:
            f.write(inp)
        with open(f"{outdir}/{v['name']}.expected", "w") as f:
            f.write(v["expected"].hex())
        # record-walk expectation: "<name> <output_byte_offset> <u64_value>"
        rw = record_walk_expected(v)
        with open(f"{outdir}/{v['name']}.rwexpected", "w") as f:
            for name, off, val in rw:
                f.write(f"{name} {off} {val}\n")
        depth = next(val for nm, _o, val in rw if nm == "depth")
        print(f"{v['name']:12} root={v['root'].hex()[:16]}.. "
              f"new_root={v['expected'].hex()[:16]}.. rw_depth={depth}")
    # accumulating 2-update vector (mpt_set_acc)
    a = vec_acc()
    sec = ssz_section(a["witness"])
    inp = build_acc_probe_input(a["root"], a["path1"], a["value1"],
                                a["path2"], a["value2"], sec)
    with open(f"{outdir}/acc.input", "wb") as f:
        f.write(inp)
    with open(f"{outdir}/acc.expected", "w") as f:
        f.write(a["expected"].hex())
    print(f"{'acc':12} root={a['root'].hex()[:16]}.. "
          f"final_root={a['expected'].hex()}")
