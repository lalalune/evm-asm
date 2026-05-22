#!/usr/bin/env bash
# codegen-zisk-tx-decode-dispatch-check.sh -- PR-K87.
#
# Unified tx decoder routing to K36/K41/K42/K44/K45.
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

echo "==> emit zisk_tx_decode_dispatch ELF"
lake exe codegen --program zisk_tx_decode_dispatch --halt linux93 \
  -o gen-out/zisk_tx_decode_dispatch

REPO_ROOT="$(pwd)"

ALICE="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
R1="$(printf '11%.0s' $(seq 1 32))"
S1="$(printf '22%.0s' $(seq 1 32))"

# Build a tx envelope for each type.
build_legacy() {
  uv run --directory execution-specs --quiet python3 -c "
import sys, rlp
tx = [7, 1000000000, 21000, bytes.fromhex('$ALICE'), 10**18, b'', 27,
      int.from_bytes(bytes.fromhex('$R1'), 'big'),
      int.from_bytes(bytes.fromhex('$S1'), 'big')]
sys.stdout.buffer.write(rlp.encode(tx))
"
}

build_eip1559() {
  uv run --directory execution-specs --quiet python3 -c "
import sys, rlp
inner = [1, 7, 10**9, 2*10**9, 21000, bytes.fromhex('$ALICE'), 10**18, b'', [], 0,
         int.from_bytes(bytes.fromhex('$R1'), 'big'),
         int.from_bytes(bytes.fromhex('$S1'), 'big')]
sys.stdout.buffer.write(b'\\x02' + rlp.encode(inner))
"
}

build_eip2930() {
  uv run --directory execution-specs --quiet python3 -c "
import sys, rlp
inner = [1, 7, 10**9, 21000, bytes.fromhex('$ALICE'), 10**18, b'', [], 0,
         int.from_bytes(bytes.fromhex('$R1'), 'big'),
         int.from_bytes(bytes.fromhex('$S1'), 'big')]
sys.stdout.buffer.write(b'\\x01' + rlp.encode(inner))
"
}

build_eip4844() {
  uv run --directory execution-specs --quiet python3 -c "
import sys, rlp
H1 = bytes([0x01] + [0xaa]*31)
inner = [1, 7, 10**9, 2*10**9, 21000, bytes.fromhex('$ALICE'), 10**18, b'', [], 1, [H1], 0,
         int.from_bytes(bytes.fromhex('$R1'), 'big'),
         int.from_bytes(bytes.fromhex('$S1'), 'big')]
sys.stdout.buffer.write(b'\\x03' + rlp.encode(inner))
"
}

build_eip7702() {
  uv run --directory execution-specs --quiet python3 -c "
import sys, rlp
inner = [1, 7, 10**9, 2*10**9, 21000, bytes.fromhex('$ALICE'), 10**18, b'', [], [], 0,
         int.from_bytes(bytes.fromhex('$R1'), 'big'),
         int.from_bytes(bytes.fromhex('$S1'), 'big')]
sys.stdout.buffer.write(b'\\x04' + rlp.encode(inner))
"
}

# run_case <name> <build_fn> <expected_status_hex>
run_case() {
  local name="$1" builder="$2" expected_status="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_decode_dispatch_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_decode_dispatch_${name}.output"

  local env_file="$REPO_ROOT/gen-out/zisk_tx_decode_dispatch_${name}.env"
  $builder > "$env_file"
  python3 -c "
import struct, sys
with open(sys.argv[1], 'rb') as f:
    env = f.read()
out  = struct.pack('<Q', len(env))
out += env
pad = (-(8 + len(env))) % 8
if pad: out += b'\x00' * pad
sys.stdout.buffer.write(out)
" "$env_file" > "$in_file"

  "$ZISKEMU" -e gen-out/zisk_tx_decode_dispatch.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_tx_decode_dispatch_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local exp_le; exp_le="$(python3 -c "print(int('$expected_status', 16).to_bytes(8, 'little').hex())")"

  if [[ "$actual" == "$exp_le" ]]; then
    printf "  %-30s OK   status=0x%s\n" "$name" "$expected_status"
    return 0
  else
    printf "  %-30s FAIL  expected 0x%s got 0x%s\n" "$name" "$expected_status" "$actual"
    return 1
  fi
}

FAILED=0
run_case "legacy"      build_legacy   "0000"  || FAILED=1
run_case "eip2930"     build_eip2930  "0100"  || FAILED=1
run_case "eip1559"     build_eip1559  "0200"  || FAILED=1
run_case "eip4844"     build_eip4844  "0300"  || FAILED=1
run_case "eip7702"     build_eip7702  "0400"  || FAILED=1

# Unrecognized: byte 0 = 0x05 (not in 0x00..0x04 typed range, < 0xc0)
UNREC_FILE="$REPO_ROOT/gen-out/zisk_tx_decode_dispatch_unrec.env"
python3 -c "
import sys
sys.stdout.buffer.write(b'\\x05\\x00\\x00')
" > "$UNREC_FILE"
python3 -c "
import struct, sys
with open(sys.argv[1], 'rb') as f:
    env = f.read()
out  = struct.pack('<Q', len(env))
out += env
out += b'\x00' * 5
sys.stdout.buffer.write(out)
" "$UNREC_FILE" > "$REPO_ROOT/gen-out/zisk_tx_decode_dispatch_unrec.input"

"$ZISKEMU" -e gen-out/zisk_tx_decode_dispatch.elf \
  -i "$REPO_ROOT/gen-out/zisk_tx_decode_dispatch_unrec.input" \
  -o "$REPO_ROOT/gen-out/zisk_tx_decode_dispatch_unrec.output" -n 500000 \
  >"$REPO_ROOT/gen-out/zisk_tx_decode_dispatch_unrec.emu.log" 2>&1 || true

UR_STATUS="$(xxd -p -l 8 "$REPO_ROOT/gen-out/zisk_tx_decode_dispatch_unrec.output" | tr -d '\n')"
if [[ "$UR_STATUS" == "0100000000000000" ]]; then
  printf "  %-30s OK   status=0x0001 (unrec)\n" "unrec_type"
else
  printf "  %-30s FAIL  status=0x%s\n" "unrec_type" "$UR_STATUS"
  FAILED=1
fi

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_decode_dispatch routes all 5 tx types correctly"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
