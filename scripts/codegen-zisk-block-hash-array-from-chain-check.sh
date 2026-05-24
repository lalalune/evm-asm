#!/usr/bin/env bash
# codegen-zisk-block-hash-array-from-chain-check.sh -- PR-K187.
#
# Validate a header chain and output the block_hash for each header.
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

echo "==> emit zisk_block_hash_array_from_chain ELF"
lake exe codegen --program zisk_block_hash_array_from_chain --halt linux93 \
  -o gen-out/zisk_block_hash_array_from_chain

REPO_ROOT="$(pwd)"

# run_case <name> <spec_py> <exp_status> <exp_valid> <exp_first_bad>
run_case() {
  local name="$1" spec="$2" exp_status="$3" exp_valid="$4" exp_bad="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_block_hash_array_from_chain_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_hash_array_from_chain_${name}.output"
  local exp_hashes_file="$REPO_ROOT/gen-out/zisk_block_hash_array_from_chain_${name}.expected_hashes.txt"

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
headers = []
expected_hashes = []
prev_hash = b'\\x00'*32
for n, ts, gl, override in spec:
    ph = override if override is not None else prev_hash
    h = make_header(ph, n, ts, gl)
    headers.append(h)
    expected_hashes.append(keccak256(h))
    prev_hash = keccak256(h)

N = len(headers)
lengths = b''.join(struct.pack('<Q', len(h)) for h in headers)
flat = b''.join(headers)

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', N) + lengths + flat
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    for h in expected_hashes:
        f.write(h.hex() + '\n')
" "$in_file" "$exp_hashes_file"

  "$ZISKEMU" -e gen-out/zisk_block_hash_array_from_chain.elf \
    -i "$in_file" -o "$out_file" -n 20000000 \
    >"$REPO_ROOT/gen-out/zisk_block_hash_array_from_chain_${name}.emu.log" 2>&1 || true

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local valid_le;  valid_le="$( dd if="$out_file" bs=1 skip=8  count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local bad_le;    bad_le="$(   dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status valid bad
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$status_le'))[0])")"
  valid="$( python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$valid_le'))[0])")"
  bad="$(   python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$bad_le'))[0])")"

  # Check the first <= N hashes against expected (limited by 256 B output cap).
  local hashes_ok=1
  if [[ "$exp_valid" == "1" ]]; then
    local i=0
    while IFS= read -r exp_hex; do
      [[ $i -ge 7 ]] && break  # output cap: 256B/32 = 8 hashes - 1 (header area)
      local offset=$((24 + i*32))
      local actual; actual="$(dd if="$out_file" bs=1 skip=$offset count=32 2>/dev/null | xxd -p | tr -d '\n')"
      if [[ "$actual" != "$exp_hex" ]]; then
        printf "  %-28s FAIL hash[%d] actual=%s exp=%s\n" "$name" "$i" "$actual" "$exp_hex"
        hashes_ok=0
        break
      fi
      i=$((i+1))
    done < "$exp_hashes_file"
  fi

  if [[ "$status" == "$exp_status" && "$valid" == "$exp_valid" && "$bad" == "$exp_bad" && "$hashes_ok" == 1 ]]; then
    printf "  %-28s OK   status=%s valid=%s bad=%s\n" "$name" "$status" "$valid" "$bad"
    return 0
  else
    printf "  %-28s FAIL status=%s/%s valid=%s/%s bad=%s/%s hashes_ok=%s\n" \
      "$name" "$status" "$exp_status" "$valid" "$exp_valid" "$bad" "$exp_bad" "$hashes_ok"
    return 1
  fi
}

FAILED=0
run_case "vacuous_empty" "[]" 0 1 0 || FAILED=1
run_case "vacuous_single" "[(100,1000,30000000,None)]" 0 1 0 || FAILED=1
run_case "three_chain_ok" "[
    (100,1000,30000000,None),
    (101,1001,30000000,None),
    (102,1002,30000000,None),
]" 0 1 0 || FAILED=1
run_case "fail_at_index_1" "[
    (100,1000,30000000,None),
    (101,1001,30000000,None),
    (103,1002,30000000,None),
]" 0 0 1 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_hash_array_from_chain validates chain and writes block_hashes"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
