#!/usr/bin/env bash
# codegen-zisk-validate-header-pair-check.sh -- PR-K174.
#
# Full pair validator: parent_hash link + number+1 + timestamp > +
# gas_limit ratio. Composes K173 + rlp_field_to_u64 + check_gas_limit.
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

echo "==> emit zisk_validate_header_pair ELF"
lake exe codegen --program zisk_validate_header_pair --halt linux93 \
  -o gen-out/zisk_validate_header_pair

REPO_ROOT="$(pwd)"

# run_case <name> <parent_num> <parent_ts> <parent_gl>
#                 <child_num>  <child_ts>  <child_gl>
#                 <wrong_phash 0/1>
#                 <exp_status> <exp_valid>
run_case() {
  local name="$1" pn="$2" pt="$3" pg="$4" cn="$5" ct="$6" cg="$7" wrong="$8" exp_status="$9" exp_valid="${10}"

  local in_file="$REPO_ROOT/gen-out/zisk_validate_header_pair_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_validate_header_pair_${name}.output"

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
    nb = n.bit_length()
    return n.to_bytes((nb + 7) // 8, 'big')

pn, pt, pg = $pn, $pt, $pg
cn, ct, cg = $cn, $ct, $cg
wrong_phash = $wrong == 1

parent_fields = [
    b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
    b'\\xa6'*32, b'\\x00'*256, b'', u_be(pn), u_be(pg),
    b'\\x82\\x02\\x00', u_be(pt), b'', b'\\xa7'*32, b'\\x00'*8,
    b'\\x82\\x12\\x34',
]
parent_rlp = rlp.encode(parent_fields)
correct_phash = keccak256(parent_rlp)

if wrong_phash:
    phash = bytes([b ^ 0xff for b in correct_phash])
else:
    phash = correct_phash

child_fields = [
    phash, b'\\xb2'*32, b'\\xb3'*20, b'\\xb4'*32, b'\\xb5'*32,
    b'\\xb6'*32, b'\\x00'*256, b'', u_be(cn), u_be(cg),
    b'\\x82\\x02\\x00', u_be(ct), b'', b'\\xb7'*32, b'\\x00'*8,
    b'\\x82\\x12\\x34',
]
child_rlp = rlp.encode(child_fields)

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(parent_rlp)) + \
             struct.pack('<Q', len(child_rlp)) + \
             parent_rlp + child_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_validate_header_pair.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_validate_header_pair_${name}.emu.log" 2>&1 || true

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local valid_le;  valid_le="$( dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status valid
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$status_le'))[0])")"
  valid="$( python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$valid_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$valid" == "$exp_valid" ]]; then
    printf "  %-36s OK   status=%s valid=%s\n" "$name" "$status" "$valid"
    return 0
  else
    printf "  %-36s FAIL status=%s (exp %s) valid=%s (exp %s)\n" \
      "$name" "$status" "$exp_status" "$valid" "$exp_valid"
    return 1
  fi
}

FAILED=0
# All 4 invariants hold.
run_case "match_all_invariants" \
   100  1000  30000000   101  1001  30000000   0   0 1 || FAILED=1
# Number off-by-one (child.number == parent.number + 2)
run_case "fail_number_skip" \
   100  1000  30000000   102  1001  30000000   0   0 0 || FAILED=1
# Timestamp not strictly increasing
run_case "fail_timestamp_equal" \
   100  1000  30000000   101  1000  30000000   0   0 0 || FAILED=1
# Gas-limit too far (> parent/1024)
run_case "fail_gas_limit_too_far" \
   100  1000  30000000   101  1001  60000000   0   0 0 || FAILED=1
# Wrong parent_hash spliced in
run_case "fail_wrong_parent_hash" \
   100  1000  30000000   101  1001  30000000   1   0 0 || FAILED=1
# Edge: gas_limit just inside the +1/1024 window (parent/1024 = 29296,
# delta = 29295 < 29296 is allowed).
run_case "edge_gas_limit_within_window" \
   100  1000  30000000   101  1001  30029295   0   0 1 || FAILED=1
# Edge: gas_limit at +1/1024 boundary (delta = 29296 = /1024 -> rejected
# by `>=` compare in check_gas_limit).
run_case "edge_gas_limit_at_boundary" \
   100  1000  30000000   101  1001  30029296   0   0 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: validate_header_pair enforces all 4 invariants jointly"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
