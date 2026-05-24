#!/usr/bin/env bash
# codegen-zisk-validate-empty-block-chain-check.sh -- PR-K184.
#
# Iterate validate_empty_block_with_parent over an N-element chain
# of (header, body) pairs.
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

echo "==> emit zisk_validate_empty_block_chain ELF"
lake exe codegen --program zisk_validate_empty_block_chain --halt linux93 \
  -o gen-out/zisk_validate_empty_block_chain

REPO_ROOT="$(pwd)"

EMPTY_TRIE_ROOT="56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
EMPTY_OMMERS_HASH="1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"

# run_case <name> <spec_py_expr> <exp_status> <exp_valid> <exp_first_bad>
run_case() {
  local name="$1" spec="$2" exp_status="$3" exp_valid="$4" exp_bad="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_validate_empty_block_chain_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_validate_empty_block_chain_${name}.output"

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

EMPTY_TRIE_ROOT = bytes.fromhex('$EMPTY_TRIE_ROOT')
EMPTY_OMMERS_HASH = bytes.fromhex('$EMPTY_OMMERS_HASH')
BAD = b'\\xff'*32

def make_header(parent_hash, num, ts, gl, tx_root=EMPTY_TRIE_ROOT):
    return rlp.encode([
        parent_hash, EMPTY_OMMERS_HASH, b'\\xb3'*20, b'\\xb4'*32, tx_root,
        EMPTY_TRIE_ROOT, b'\\x00'*256, b'', u_be(num), u_be(gl),
        b'\\x82\\x02\\x00', u_be(ts), b'', b'\\xb7'*32, b'\\x00'*8,
        b'\\x82\\x12\\x34', EMPTY_TRIE_ROOT,
    ])

def make_empty_body():
    return rlp.encode([[], [], []])

def make_body_with_tx():
    return rlp.encode([[b'\\xaa'*10], [], []])

# spec: list of (num, ts, gl, tx_root_override_or_None, body_kind: 'empty'|'with_tx')
# Chain: each header's parent_hash = keccak256(prev_rlp). Body[0] is ignored.
spec = $spec
headers = []
bodies = []
prev_hash = b'\\x00'*32
for n, ts, gl, override, body_kind in spec:
    tr = override if override is not None else EMPTY_TRIE_ROOT
    h = make_header(prev_hash, n, ts, gl, tx_root=tr)
    headers.append(h)
    bodies.append(make_body_with_tx() if body_kind == 'with_tx' else make_empty_body())
    prev_hash = keccak256(h)

N = len(headers)
header_lengths = b''.join(struct.pack('<Q', len(h)) for h in headers)
body_lengths   = b''.join(struct.pack('<Q', len(b)) for b in bodies)
flat_h = b''.join(headers)
flat_b = b''.join(bodies)

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', N) + header_lengths + body_lengths + flat_h + flat_b
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_validate_empty_block_chain.elf \
    -i "$in_file" -o "$out_file" -n 20000000 \
    >"$REPO_ROOT/gen-out/zisk_validate_empty_block_chain_${name}.emu.log" 2>&1 || true

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
run_case "vacuous_empty" "[]" 0 1 0 || FAILED=1
run_case "vacuous_single" "[(100,1000,30000000,None,'empty')]" 0 1 0 || FAILED=1
run_case "two_block_chain_ok" "[
    (100,1000,30000000,None,'empty'),
    (101,1001,30000000,None,'empty'),
]" 0 1 0 || FAILED=1
run_case "three_block_chain_ok" "[
    (100,1000,30000000,None,'empty'),
    (101,1001,30000000,None,'empty'),
    (102,1002,30000000,None,'empty'),
]" 0 1 0 || FAILED=1
run_case "fail_at_index_1_tx_root" "[
    (100,1000,30000000,None,'empty'),
    (101,1001,30000000,None,'empty'),
    (102,1002,30000000,bytes.fromhex('ff'*32),'empty'),
]" 0 0 1 || FAILED=1
run_case "fail_at_index_0_body" "[
    (100,1000,30000000,None,'empty'),
    (101,1001,30000000,None,'with_tx'),
]" 0 0 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: validate_empty_block_chain walks N-chain and reports first bad index"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
