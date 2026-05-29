#!/usr/bin/env bash
# codegen-zisk-eip4788-beacon-root-lookup-check.sh
#
# Resolve the EIP-4788 parent-beacon-block-root for a given
# timestamp via the BEACON_ROOTS_ADDRESS system contract:
#   timestamp_idx = timestamp mod 8191
#   root_idx      = timestamp_idx + 8191
#   verify storage[timestamp_idx] == timestamp
#   return storage[root_idx]
#
# Output (40 bytes):
#   bytes  0.. 8 : status
#   bytes  8..40 : beacon root (u256 BE; zeros on absent/stale/error)
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then
    ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then
    ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else
    echo "ziskemu not found -- install via ziskup or set ZISKEMU=..." >&2
    exit 1
  fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit zisk_eip4788_beacon_root_lookup ELF"
lake exe codegen --program zisk_eip4788_beacon_root_lookup \
  --halt linux93 \
  -o gen-out/zisk_eip4788_beacon_root_lookup

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_ebrl_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_ebrl_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_ebrl_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp
from Crypto.Hash import keccak

def k256(b):
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()

def hp_encode(nibbles, is_leaf):
    flag = 2 if is_leaf else 0
    if len(nibbles) % 2 == 1:
        flag |= 1
        result = bytes([flag * 0x10 + nibbles[0]])
        nibbles = nibbles[1:]
    else:
        result = bytes([flag * 0x10])
    for i in range(0, len(nibbles), 2):
        result += bytes([nibbles[i] * 0x10 + nibbles[i+1]])
    return result

def leaf_node(path_nibbles, value):
    return rlp.encode([hp_encode(path_nibbles, True), value])

def bytes_to_nibbles(b):
    out = []
    for byte in b:
        out.append(byte >> 4)
        out.append(byte & 0xf)
    return out

def build_ssz_section(elements):
    n = len(elements)
    if n == 0:
        return b''
    section = b''
    offset = 4 * n
    for e in elements:
        section += struct.pack('<I', offset)
        offset += len(e)
    for e in elements:
        section += e
    return section

def encode_account(nonce, balance, storage_root, code_hash):
    return rlp.encode([nonce, balance, storage_root, code_hash])

def encode_header(state_root):
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, state_root, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    ]
    return rlp.encode(fields)

EMPTY_TRIE = bytes.fromhex('56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421')
EMPTY_CODE = bytes.fromhex('c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470')
BEACON_ADDR = bytes.fromhex('000F3df6D732807Ef1319fB7B8bB8522d0Beac02'.lower())
HISTORY_BUFFER_LENGTH = 8191

argv = sys.argv[1:]
mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]

def build_storage_trie(entries):
    # entries: list of (slot_idx_int, slot_value_int)
    leaves = []
    for (idx, val) in entries:
        idx_be = idx.to_bytes(32, 'big')
        path = bytes_to_nibbles(k256(idx_be))
        value_bytes = rlp.encode(val)
        leaves.append((path, value_bytes))
    # For a single-entry trie, this builds a leaf node.
    # For multi-entry, we'd need a real MPT builder (branch/extension).
    # The probe's K29 handles all of these correctly when given a real trie root.
    # For our tests we'll typically use a single-entry trie OR construct a
    # 2-leaf MPT manually if the two entries differ in just a few bits.
    # Easier: separate single-entry tries per test case, or run with a real MPT.
    raise SystemExit('use single_entry_trie or two_leaf_trie helpers')

def single_entry_trie(slot_idx_int, slot_value_int):
    idx_be = slot_idx_int.to_bytes(32, 'big')
    path = bytes_to_nibbles(k256(idx_be))
    value_bytes = rlp.encode(slot_value_int)
    leaf = leaf_node(path, value_bytes)
    root = k256(leaf)
    section = build_ssz_section([leaf])
    return root, section

def build_state_trie_one_account(addr, account_rlp):
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, account_rlp)
    return k256(leaf), build_ssz_section([leaf])

# Build a 2-leaf storage trie. The two leaves share some path prefix; we
# need an MPT with a branch and two leaves -- compute it from the two
# (key, value) entries.
def build_two_leaf_storage_trie(entries):
    # entries: [(slot_idx_int, slot_value_int), (slot_idx_int, slot_value_int)]
    leaf_inputs = []
    for (idx, val) in entries:
        idx_be = idx.to_bytes(32, 'big')
        path = bytes_to_nibbles(k256(idx_be))
        value_bytes = rlp.encode(val)
        leaf_inputs.append((path, value_bytes))
    # Find common prefix.
    path_a, val_a = leaf_inputs[0]
    path_b, val_b = leaf_inputs[1]
    common = 0
    while common < len(path_a) and common < len(path_b) and path_a[common] == path_b[common]:
        common += 1
    # The two paths diverge at position 'common'.
    # Build leaf_a as rlp([hp(path_a[common+1:], True), val_a])  -- skip the branch nibble.
    # Same for leaf_b.
    leaf_a = leaf_node(path_a[common + 1:], val_a)
    leaf_b = leaf_node(path_b[common + 1:], val_b)
    branch_a = path_a[common]
    branch_b = path_b[common]
    # Build branch node: 17 items, item[branch_a] = leaf_a (or its hash), etc.
    # For small leaves, branch items are inline RLP-encoded leaf bytes.
    # For large leaves (>= 32 bytes), branch items are keccak hashes.
    def branch_item(leaf_bytes):
        if len(leaf_bytes) < 32:
            # Embed the leaf inline.
            # But RLP semantics: branch[i] must be a byte string OR a recursive list.
            # Per EIP standards, embedded nodes are direct RLP.
            # rlp.encode places the leaf's rlp inline at the branch slot.
            # To embed: we put the leaf list directly as a branch slot (no extra wrap).
            return rlp.decode(leaf_bytes)
        else:
            return k256(leaf_bytes)
    children = [b'' for _ in range(16)]
    children[branch_a] = branch_item(leaf_a)
    children[branch_b] = branch_item(leaf_b)
    branch_rlp = rlp.encode(children + [b''])
    # The branch is the trie root if common == 0.
    # Otherwise we need an extension node wrapping the branch.
    nodes = [leaf_a, leaf_b, branch_rlp]  # the leaves only included as separate witnesses if branch_item used hashes
    if common == 0:
        root = k256(branch_rlp)
    else:
        ext = rlp.encode([hp_encode(path_a[:common], False), k256(branch_rlp) if len(branch_rlp) >= 32 else rlp.decode(branch_rlp)])
        root = k256(ext)
        nodes.append(ext)
    section = build_ssz_section(nodes)
    return root, section

if mode == 'stored_match':
    timestamp = int(parts[0])
    beacon_root_hex = parts[1]
    beacon_root = bytes.fromhex(beacon_root_hex)
    # storage[ts_idx] = timestamp (so it'll verify); storage[ts_idx + 8191] = beacon_root_as_u256
    ts_idx = timestamp % HISTORY_BUFFER_LENGTH
    root_idx = ts_idx + HISTORY_BUFFER_LENGTH
    beacon_root_int = int.from_bytes(beacon_root, 'big')
    storage_root, witness_storage = build_two_leaf_storage_trie([
        (ts_idx, timestamp),
        (root_idx, beacon_root_int),
    ])
    account = encode_account(1, 0, storage_root, EMPTY_CODE)
    state_root, witness_state = build_state_trie_one_account(BEACON_ADDR, account)
    header = encode_header(state_root)
    expected_status = 0
    expected_root = beacon_root
elif mode == 'stale_slot':
    # storage[ts_idx] holds a different timestamp -> slot is stale.
    requested_ts = int(parts[0])
    stored_ts = int(parts[1])
    beacon_root_hex = parts[2]
    beacon_root = bytes.fromhex(beacon_root_hex)
    ts_idx = stored_ts % HISTORY_BUFFER_LENGTH
    root_idx = ts_idx + HISTORY_BUFFER_LENGTH
    # The requested ts shares the same slot only if (requested % 8191) == (stored % 8191).
    if (requested_ts % HISTORY_BUFFER_LENGTH) != ts_idx:
        # Slot doesn't even alias -- ts_slot will be empty for requested, not a stale-slot test.
        # Make sure they alias: pick stored_ts such that they alias.
        raise SystemExit('stale_slot test needs requested_ts and stored_ts to alias to same slot mod 8191')
    beacon_root_int = int.from_bytes(beacon_root, 'big')
    storage_root, witness_storage = build_two_leaf_storage_trie([
        (ts_idx, stored_ts),
        (root_idx, beacon_root_int),
    ])
    account = encode_account(1, 0, storage_root, EMPTY_CODE)
    state_root, witness_state = build_state_trie_one_account(BEACON_ADDR, account)
    header = encode_header(state_root)
    timestamp = requested_ts
    expected_status = 0
    expected_root = b'\\x00' * 32  # stale slot -> 0
elif mode == 'no_beacon_contract':
    timestamp = int(parts[0])
    other_addr = b'\\xaa' * 20
    account = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE)
    state_root, witness_state = build_state_trie_one_account(other_addr, account)
    witness_storage = b''
    header = encode_header(state_root)
    expected_status = 0
    expected_root = b'\\x00' * 32
elif mode == 'garbage_header':
    timestamp = int(parts[0])
    witness_state = b''
    witness_storage = b''
    header = b'\\x00'
    expected_status = 4
    expected_root = b'\\x00' * 32
else:
    raise SystemExit('bad mode: ' + mode)

expected = struct.pack('<Q', expected_status) + expected_root

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(header))
        + struct.pack('<Q', len(witness_state))
        + struct.pack('<Q', len(witness_storage))
        + struct.pack('<Q', timestamp)
        + header
        + witness_state
        + witness_storage
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_eip4788_beacon_root_lookup.elf \
    -i "$in_file" -o "$out_file" -n 16000000 \
    >"$REPO_ROOT/gen-out/zisk_ebrl_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-30s OK   %d bytes match\n" "$name" "$exp_size"
    return 0
  else
    printf "  %-30s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

BEACON_HASH1="1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef"

FAILED=0
# Happy path: requested timestamp matches stored.
run_case "stored_match"            stored_match 1000 "$BEACON_HASH1" || FAILED=1
# Stale slot: same slot mod 8191 but different timestamp stored.
# 1000 % 8191 = 1000; pick stored_ts = 1000 + 8191 = 9191 (same slot).
run_case "stale_slot_aliased"      stale_slot 1000 9191 "$BEACON_HASH1" || FAILED=1
# No beacon contract.
run_case "no_beacon_contract"      no_beacon_contract 1000 || FAILED=1
# Garbage header.
run_case "garbage_header"          garbage_header 1000 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: eip4788_beacon_root_lookup end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
