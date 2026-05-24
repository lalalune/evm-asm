#!/usr/bin/env bash
# codegen-zisk-validate-block-hash-chain-match-check.sh -- PR-K195.
#
# Validate chain + check computed block_hash matches a caller claim.
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

echo "==> emit zisk_validate_block_hash_chain_match ELF"
lake exe codegen --program zisk_validate_block_hash_chain_match --halt linux93 \
  -o gen-out/zisk_validate_block_hash_chain_match

REPO_ROOT="$(pwd)"

# run_case <name> <spec_py> <break_claim_index_or_-1> <exp_status> <exp_valid> <exp_first_bad>
run_case() {
  local name="$1" spec="$2" break_idx="$3" exp_status="$4" exp_valid="$5" exp_bad="$6"

  local in_file="$REPO_ROOT/gen-out/zisk_validate_block_hash_chain_match_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_validate_block_hash_chain_match_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
try:
    from Crypto.Hash import keccak
    def keccak256(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    import sha3
    def keccak256(b): return sha3.keccak_256(b).digest()

def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')

def make_header(parent_hash, num, ts, gl):
    return rlp.encode([
        parent_hash, b'\\xb2'*32, b'\\xb3'*20, b'\\xb4'*32, b'\\xb5'*32,
        b'\\xb6'*32, b'\\x00'*256, b'', u_be(num), u_be(gl),
        b'\\x82\\x02\\x00', u_be(ts), b'', b'\\xb7'*32, b'\\x00'*8,
        b'\\x82\\x12\\x34',
    ])

spec = $spec
break_idx = $break_idx

headers = []
hashes = []
prev_hash = b'\\x00'*32
for n, ts, gl in spec:
    h = make_header(prev_hash, n, ts, gl)
    headers.append(h)
    hashes.append(keccak256(h))
    prev_hash = keccak256(h)

if break_idx >= 0:
    hashes[break_idx] = bytes([b ^ 0xff for b in hashes[break_idx]])

N = len(headers)
lengths = b''.join(struct.pack('<Q', len(h)) for h in headers)
claimed = b''.join(hashes)
flat = b''.join(headers)

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', N) + lengths + claimed + flat
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_validate_block_hash_chain_match.elf \
    -i "$in_file" -o "$out_file" -n 20000000 \
    >"$REPO_ROOT/gen-out/zisk_validate_block_hash_chain_match_${name}.emu.log" 2>&1 || true

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local valid_le;  valid_le="$( dd if="$out_file" bs=1 skip=8  count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local bad_le;    bad_le="$(   dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status valid bad
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$status_le'))[0])")"
  valid="$( python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$valid_le'))[0])")"
  bad="$(   python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$bad_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$valid" == "$exp_valid" && "$bad" == "$exp_bad" ]]; then
    printf "  %-30s OK   status=%s valid=%s bad=%s\n" "$name" "$status" "$valid" "$bad"
    return 0
  else
    printf "  %-30s FAIL status=%s/%s valid=%s/%s bad=%s/%s\n" \
      "$name" "$status" "$exp_status" "$valid" "$exp_valid" "$bad" "$exp_bad"
    return 1
  fi
}

FAILED=0
run_case "vacuous_empty" "[]" -1 0 1 0 || FAILED=1
run_case "single_hash_match" "[(100,1000,30000000)]" -1 0 1 0 || FAILED=1
run_case "single_hash_mismatch" "[(100,1000,30000000)]" 0 0 0 0 || FAILED=1
run_case "three_chain_all_match" "[
    (100,1000,30000000),
    (101,1001,30000000),
    (102,1002,30000000),
]" -1 0 1 0 || FAILED=1
# fail_hash_at_index_2: hash[2] is broken; failure caught during link i=1
# (where we hash headers[2] and compare). bad_index reports the LINK index
# at which we noticed the mismatch, not the broken-hash absolute index.
run_case "fail_hash_at_index_2" "[
    (100,1000,30000000),
    (101,1001,30000000),
    (102,1002,30000000),
]" 2 0 0 1 || FAILED=1
run_case "fail_chain_link_at_index_1" "[
    (100,1000,30000000),
    (101,1001,30000000),
    (103,1002,30000000),
]" -1 0 0 1 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: validate_block_hash_chain_match verifies both chain links and hash claims"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
