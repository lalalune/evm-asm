#!/usr/bin/env bash
# codegen-zisk-validate-witness-state-contains-root-check.sh
#
# Second storage-proof step: given a parent header RLP and an
# SSZ `witness.state` list section, locate the node whose
# keccak256 matches the header's state_root field.
#
# Composes header_extract_state_root (K201) + witness_lookup_by_hash
# (K19) into a single composite. Returns:
#   0  hit (node found; OUTPUT+8/+16 hold its section offset/length)
#   1  miss (no node in section matches header.state_root)
#   2  header parse failure / state_root field not 32 B
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

echo "==> emit zisk_validate_witness_state_contains_root ELF"
lake exe codegen --program zisk_validate_witness_state_contains_root \
  --halt linux93 \
  -o gen-out/zisk_validate_witness_state_contains_root

REPO_ROOT="$(pwd)"

# run_case <name> <state_root_mode> <nodes_csv_hex> <exp_status> [exp_offset exp_length]
#   state_root_mode:
#     match:IDX -- header state_root = keccak256(nodes[IDX])
#     literal:HEX64 -- header state_root = the literal 32-byte hex
#     garbage_header -- 1-byte invalid header
#   nodes_csv_hex: comma-separated hex strings, one per witness.state entry.
#     Empty string -> 0 nodes (section_len = 0).
run_case() {
  local name="$1" sr_mode="$2" nodes_csv="$3" exp_status="$4"
  local exp_offset="${5:-0}" exp_length="${6:-0}"

  local in_file="$REPO_ROOT/gen-out/zisk_vwsc_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_vwsc_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
from Crypto.Hash import keccak
sr_mode = '$sr_mode'
csv = '$nodes_csv'
nodes = [bytes.fromhex(p) for p in csv.split(',') if p] if csv else []

# Build the SSZ List section: [N x u32 LE inner offsets][concat node bytes].
N = len(nodes)
section = b''
if N == 0:
    section = b''
else:
    offsets = b''
    body = b''
    cur = 4 * N
    for n in nodes:
        offsets += struct.pack('<I', cur)
        body += n
        cur += len(n)
    section = offsets + body
S = len(section)

# Build the header.
if sr_mode == 'garbage_header':
    header_rlp = b'\\x00'
else:
    if sr_mode.startswith('match:'):
        idx = int(sr_mode.split(':', 1)[1])
        k = keccak.new(digest_bits=256)
        k.update(nodes[idx])
        state_root = k.digest()
    elif sr_mode.startswith('literal:'):
        state_root = bytes.fromhex(sr_mode.split(':', 1)[1])
    else:
        raise SystemExit('bad sr_mode: ' + sr_mode)
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, state_root, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    ]
    header_rlp = rlp.encode(fields)
H = len(header_rlp)

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', H) + struct.pack('<Q', S) + header_rlp + section
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_validate_witness_state_contains_root.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_vwsc_${name}.emu.log" 2>&1 || true

  if [[ ! -s "$out_file" ]]; then
    printf "  %-30s FAIL (empty output -- ziskemu crashed)\n" "$name"
    return 1
  fi

  local s_hex off_hex len_hex
  s_hex="$(xxd -p -s 0 -l 8 "$out_file" | tr -d '\n')"
  off_hex="$(xxd -p -s 8 -l 8 "$out_file" | tr -d '\n')"
  len_hex="$(xxd -p -s 16 -l 8 "$out_file" | tr -d '\n')"
  local status offset length
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$s_hex'))[0])")"
  offset="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$off_hex'))[0])")"
  length="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$len_hex'))[0])")"

  if [[ "$status" != "$exp_status" ]]; then
    printf "  %-30s FAIL status=%s expected=%s\n" "$name" "$status" "$exp_status"
    return 1
  fi
  if [[ "$exp_status" == "0" ]]; then
    if [[ "$offset" != "$exp_offset" || "$length" != "$exp_length" ]]; then
      printf "  %-30s FAIL offset=%s/%s length=%s/%s\n" "$name" \
        "$offset" "$exp_offset" "$length" "$exp_length"
      return 1
    fi
    printf "  %-30s OK   hit (off=%s len=%s)\n" "$name" "$offset" "$length"
  else
    printf "  %-30s OK   status=%s\n" "$name" "$status"
  fi
}

FAILED=0
# One-node section, node = c0 (RLP []), header.state_root = keccak(c0).
# Section layout: [u32 off=4][c0]; matched offset within section = 4, length = 1.
run_case "match_one_node"            "match:0" "c0" 0 4 1 || FAILED=1
# Two-node section; match the second node.
# Layout: [u32 off=8][u32 off=9][c0][deadbeef]; offsets are absolute inside section.
# Element 0 occupies bytes [8..9) (1 byte); element 1 occupies [9..13) (4 bytes).
run_case "match_second_of_two"       "match:1" "c0,deadbeef" 0 9 4 || FAILED=1
# Three-node section; match the middle one.
run_case "match_middle_of_three"     "match:1" "deadbeef,1122334455,aabbccdd" 0 16 5 || FAILED=1
# Miss: state_root targets a hash not present in the witness section.
run_case "miss_unrelated_target"     "literal:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" "c0,deadbeef" 1 || FAILED=1
# Miss: empty witness section.
run_case "miss_empty_section"        "literal:0000000000000000000000000000000000000000000000000000000000000000" "" 1 || FAILED=1
# Parse fail: garbage header.
run_case "parse_fail"                "garbage_header" "c0" 2 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: validate_witness_state_contains_root locates / misses / parse-fails correctly"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
