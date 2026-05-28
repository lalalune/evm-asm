#!/usr/bin/env bash
# codegen-zisk-validate-state-root-against-witness-node-check.sh
#
# First step of stateless storage-proof verification: confirm
# that keccak256(witness state-trie root node bytes) matches
# the `state_root` field of the parent header.
#
# Composes K201 header_extract_state_root + zkvm_keccak256
# into a single composite, byte-compares the two 32-byte
# digests, returns:
#   0 -- match
#   1 -- mismatch
#   2 -- header parse failure / wrong state_root length
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

echo "==> emit zisk_validate_state_root_against_witness_node ELF"
lake exe codegen --program zisk_validate_state_root_against_witness_node \
  --halt linux93 \
  -o gen-out/zisk_validate_state_root_against_witness_node

REPO_ROOT="$(pwd)"

# run_case <name> <state_node_hex> <header_state_root_override_or_match> <exp_status>
#   header_state_root_override:
#     "match" => use keccak256(state_node) as the header's state_root
#     <64-char hex> => use that literal hex as the header's state_root
#     "garbage_header" => pass a 1-byte invalid header
run_case() {
  local name="$1" state_node_hex="$2" sr_override="$3" exp_status="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_vsraw_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_vsraw_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
from Crypto.Hash import keccak
state_node = bytes.fromhex('$state_node_hex')
sr_override = '$sr_override'
if sr_override == 'garbage_header':
    header_rlp = b'\\x00'
else:
    if sr_override == 'match':
        k = keccak.new(digest_bits=256)
        k.update(state_node)
        state_root = k.digest()
    else:
        state_root = bytes.fromhex(sr_override)
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, state_root, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    ]
    header_rlp = rlp.encode(fields)
H = len(header_rlp)
S = len(state_node)
with open(sys.argv[1], 'wb') as f:
    # [8 B header_len][8 B state_node_len][header_rlp][state_node]
    record = struct.pack('<Q', H) + struct.pack('<Q', S) + header_rlp + state_node
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_validate_state_root_against_witness_node.elf \
    -i "$in_file" -o "$out_file" -n 2000000 \
    >"$REPO_ROOT/gen-out/zisk_vsraw_${name}.emu.log" 2>&1 || true

  if [[ ! -s "$out_file" ]]; then
    printf "  %-26s FAIL (empty output -- ziskemu crashed)\n" "$name"
    return 1
  fi

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local status; status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$status_le'))[0])")"

  if [[ "$status" == "$exp_status" ]]; then
    printf "  %-26s OK   status=%s\n" "$name" "$status"
    return 0
  else
    printf "  %-26s FAIL status=%s expected=%s\n" "$name" "$status" "$exp_status"
    return 1
  fi
}

FAILED=0
# Empty list node = RLP [] = single byte 0xc0. keccak256(0xc0) =
# EMPTY_TRIE_ROOT 0x56e81f17... when header.state_root matches.
run_case "match_empty_node"      "c0" "match" 0 || FAILED=1
# 4-byte node; pass match.
run_case "match_short_node"      "deadbeef" "match" 0 || FAILED=1
# Mismatch: header has zeros, witness has c0.
run_case "mismatch_zero_root"    "c0" "0000000000000000000000000000000000000000000000000000000000000000" 1 || FAILED=1
# Mismatch: header has unrelated value.
run_case "mismatch_unrelated"    "deadbeef" "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" 1 || FAILED=1
# Parse failure: header is invalid RLP.
run_case "parse_fail"            "deadbeef" "garbage_header" 2 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: validate_state_root_against_witness_node matches/mismatches/parse-fails correctly"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
