#!/usr/bin/env bash
# codegen-zisk-chain-validate-full-check.sh -- PR-K222.
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

echo "==> emit zisk_chain_validate_full ELF"
lake exe codegen --program zisk_chain_validate_full --halt linux93 \
  -o gen-out/zisk_chain_validate_full

REPO_ROOT="$(pwd)"

# spec list: tuples (num, ts, gl, broken: 'none' | 'zeros' | 'parent_hash')
run_case() {
  local name="$1" spec="$2" exp_valid="$3" exp_bad="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_chain_validate_full_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_chain_validate_full_${name}.output"

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

EMPTY_OMMERS_HASH = bytes.fromhex('1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')

def make_header(parent_hash, num, ts, gl, broken):
    ommers = EMPTY_OMMERS_HASH if broken != 'zeros' else b'\\xff'*32
    return rlp.encode([
        parent_hash, ommers, b'\\xb3'*20, b'\\xb4'*32, b'\\xb5'*32,
        b'\\xb6'*32, b'\\x00'*256, b'', u_be(num), u_be(gl),
        b'\\x82\\x02\\x00', u_be(ts), b'', b'\\xb7'*32, b'\\x00'*8,
    ])

spec = $spec
headers = []
prev_hash = b'\\x00'*32
for i, (n, ts, gl, broken) in enumerate(spec):
    ph = bytes([b ^ 0xff for b in prev_hash]) if broken == 'parent_hash' else prev_hash
    h = make_header(ph, n, ts, gl, broken)
    headers.append(h)
    prev_hash = keccak256(h)

N = len(headers)
lengths = b''.join(struct.pack('<Q', len(h)) for h in headers)
flat = b''.join(headers)

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', N) + lengths + flat
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_chain_validate_full.elf \
    -i "$in_file" -o "$out_file" -n 20000000 \
    >"$REPO_ROOT/gen-out/zisk_chain_validate_full_${name}.emu.log" 2>&1 || true

  local valid_le; valid_le="$(dd if="$out_file" bs=1 skip=8  count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local bad_le;   bad_le="$(  dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local valid bad
  valid="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$valid_le'))[0])")"
  bad="$(  python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$bad_le'))[0])")"

  if [[ "$valid" == "$exp_valid" && "$bad" == "$exp_bad" ]]; then
    printf "  %-30s OK   valid=%s bad=%s\n" "$name" "$valid" "$bad"
    return 0
  else
    printf "  %-30s FAIL valid=%s/%s bad=%s/%s\n" "$name" "$valid" "$exp_valid" "$bad" "$exp_bad"
    return 1
  fi
}

FAILED=0
run_case "empty" "[]" 1 0 || FAILED=1
run_case "all_clean" "[
    (100, 1000, 30000000, 'none'),
    (101, 1001, 30000000, 'none'),
    (102, 1002, 30000000, 'none'),
]" 1 0 || FAILED=1
run_case "bad_zeros_at_index_1" "[
    (100, 1000, 30000000, 'none'),
    (101, 1001, 30000000, 'zeros'),
    (102, 1002, 30000000, 'none'),
]" 0 1 || FAILED=1
run_case "bad_link_at_index_1" "[
    (100, 1000, 30000000, 'none'),
    (101, 1001, 30000000, 'none'),
    (102, 1002, 30000000, 'parent_hash'),
]" 0 1 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chain_validate_full combines K221 + K175"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
