#!/usr/bin/env python3
"""
pack-bytecode.py — pack a bytecode (and optional calldata) into a
ziskemu `-i <file>` payload.

Used by M8.5's `scripts/codegen-opcodes-runtime-check.sh` to turn
the bytecode column of `lake exe codegen --list-test-cases` (which
mirrors `EvmAsm/Codegen/Tests/Cases.lean`'s `bytecode` field, e.g.
`"0x60, 0x02, 0x60, 0x0a, 0x04, 0x00"`) into a binary file the
runtime-bytecode dispatcher reads at `INPUT_ADDR + INPUT_DATA_OFFSET`.

M21 extension: optionally append a calldata segment, length-prefixed,
so the dispatcher's prologue can populate `env.callDataPtr` /
`env.callDataLen` and CALLDATALOAD / CALLDATACOPY can read real bytes.

M22 extension: optionally append a third segment carrying a list of
(storage-key, storage-value) pairs. The dispatcher prologue copies
them into a writable in-`.data` slot table; SLOAD / SSTORE read /
mutate the table via linear scan.

M28 extension: optionally append a fourth segment carrying the
BLOBBASEFEE value as one EVM stack word. The dispatcher prologue copies
it into `evm_env`; opcode 0x4a reads it from there. Defaults to zero.

Usage:
    pack-bytecode.py "0x60, 0x02, 0x60, 0x0a, 0x04, 0x00" output.bin
    pack-bytecode.py --calldata "0xdeadbeef" "0x36, 0x00" output.bin
    pack-bytecode.py --storage "(0x00, 0xdead)" "0x60, 0x00, 0x54, 0x00" output.bin
    pack-bytecode.py --blob-base-fee 0x1234 "0x4a, 0x00" output.bin
    echo "0x60, 0x00" | pack-bytecode.py - output.bin

Output layout:

    bytes 0..8         <8-byte LE u64 length of bytecode>
    bytes 8..          <bytecode bytes>
                       <zero pad to 8-byte boundary>
    next 8 bytes       <8-byte LE u64 length of calldata>
    following          <calldata bytes>
                       <zero pad to 8-byte boundary>
    next 8 bytes       <8-byte LE u64 slot_count>            (M22)
    following          <slot_count × 64-byte (key, value)>   (M22)
                       <zero pad to 8-byte boundary>
    next 32 bytes      <blob_base_fee as EVM stack word>      (M28)

ziskemu prepends 8 more bytes of its own metadata when loading,
landing the bytecode-length prefix at INPUT_ADDR+8 and the bytecode
at INPUT_ADDR+16 — which is where the runtime-bytecode dispatcher's
`li x10, 0x40000010` points. The calldata-length prefix lands at
the first 8-byte boundary past the bytecode bytes; the dispatcher
prologue computes those addresses at startup, then chains to the
slot-count prefix at the first 8-byte boundary past the calldata.

Backwards-compatible: pre-M21 callers that don't pass --calldata get
a zero-length calldata segment appended, which preserves the M17
"CALLDATA opcodes are no-op" behavior for existing test cases.
Pre-M22 callers that don't pass --storage get a zero-length storage
segment appended (SLOAD returns 0, SSTORE appends to an empty table).
Pre-M28 callers that don't pass --blob-base-fee get a zero word.
"""
import argparse
import re
import struct
import sys


def parse_csv(csv: str) -> bytes:
    """Parse a `0xNN, 0xMM, ...` string into raw bytes."""
    tokens = re.findall(r"0[xX][0-9a-fA-F]+", csv)
    if not tokens:
        raise ValueError(f"no `0xNN` tokens in input: {csv!r}")
    return bytes(int(t, 16) for t in tokens)


def parse_calldata(calldata_arg: str) -> bytes:
    """Parse a calldata arg as either CSV (`0x60, 0x42`) or hex blob
    (`0xdeadbeef` or `deadbeef`). Empty string returns empty bytes."""
    s = calldata_arg.strip()
    if not s:
        return b""
    # CSV form (has commas)?
    if "," in s:
        return parse_csv(s)
    # Hex-blob form, with optional 0x prefix
    if s.startswith(("0x", "0X")):
        s = s[2:]
    if len(s) % 2 != 0:
        raise ValueError(f"hex blob has odd length: {calldata_arg!r}")
    return bytes.fromhex(s)


def pad_to_8(buf: bytes) -> bytes:
    """Zero-pad a bytes buffer up to the next 8-byte boundary."""
    pad = (-len(buf)) % 8
    if pad:
        buf += b"\x00" * pad
    return buf


def parse_storage(storage_arg: str) -> list[tuple[bytes, bytes]]:
    """Parse a --storage arg into a list of (key, value) byte pairs,
    each in EVM-stack representation (4 little-endian u64 limbs, low
    limb first).

    Supported forms:
    - Empty: returns [].
    - Parenthesized pairs: "(0xKEY, 0xVAL) (0xKEY2, 0xVAL2)" where
      each KEY / VAL is a hex blob (with optional 0x prefix)
      interpreted as a u256 integer. The serialized bytes are the
      reverse of the natural 32-byte big-endian encoding — that is
      the layout PUSH32 + SSTORE would deposit on the EVM stack
      (see push32_basic in Tests/Cases.lean).
    """
    s = storage_arg.strip()
    if not s:
        return []
    pairs = re.findall(
        r"\(\s*(0[xX][0-9a-fA-F]+|[0-9a-fA-F]+)\s*,"
        r"\s*(0[xX][0-9a-fA-F]+|[0-9a-fA-F]+)\s*\)",
        s,
    )
    if not pairs:
        raise ValueError(f"no `(key, value)` pairs in --storage: {storage_arg!r}")
    out: list[tuple[bytes, bytes]] = []
    for raw_key, raw_val in pairs:
        out.append((_to_stack_bytes(raw_key), _to_stack_bytes(raw_val)))
    return out


def _to_stack_bytes(hex_blob: str) -> bytes:
    """Decode a hex blob (with optional 0x prefix) as a u256 integer
    and serialize as 32 bytes in EVM-stack representation: 4 LE u64
    limbs, low limb first. Equivalent to reversing the BE 32-byte
    encoding the user would naturally write."""
    s = hex_blob.strip()
    if s.startswith(("0x", "0X")):
        s = s[2:]
    if len(s) % 2 != 0:
        s = "0" + s  # nibble alignment
    raw_be = bytes.fromhex(s)
    if len(raw_be) > 32:
        raise ValueError(f"storage key/value > 32 bytes: {hex_blob!r}")
    raw_be = b"\x00" * (32 - len(raw_be)) + raw_be
    return raw_be[::-1]


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Pack a bytecode (and optional calldata) into a "
                    "ziskemu input file."
    )
    parser.add_argument(
        "bytecode",
        help="Comma-separated bytecode (e.g. '0x60, 0x02, 0x00'). "
             "Use '-' to read from stdin.",
    )
    parser.add_argument(
        "output",
        help="Path to write the packed binary. Use '-' for stdout.",
    )
    parser.add_argument(
        "--calldata",
        default="",
        help="Optional calldata, as either CSV ('0x60, 0x42') or a "
             "hex blob ('0xdeadbeef'). Defaults to empty (back-compat).",
    )
    parser.add_argument(
        "--storage",
        default="",
        help="Optional storage preload: parenthesized hex pairs like "
             "'(0x00, 0xdead) (0x01, 0xbeef)'. Each key / value is "
             "interpreted as a u256 integer and serialized in EVM-stack "
             "byte order. Defaults to empty (no preload).",
    )
    parser.add_argument(
        "--blob-base-fee",
        default="",
        help="Optional BLOBBASEFEE value as a u256 hex integer. Serialized "
             "in EVM-stack byte order. Defaults to zero.",
    )
    args = parser.parse_args()

    csv = sys.stdin.read() if args.bytecode == "-" else args.bytecode
    bytecode = parse_csv(csv)
    calldata = parse_calldata(args.calldata)
    storage_pairs = parse_storage(args.storage)
    blob_base_fee = _to_stack_bytes(args.blob_base_fee) if args.blob_base_fee.strip() else b"\x00" * 32

    # Bytecode segment: 8B LE length prefix + bytes, padded to 8-byte boundary
    # so the calldata-length cell that follows is aligned.
    packed = struct.pack("<Q", len(bytecode)) + bytecode
    packed = pad_to_8(packed)

    # Calldata segment: 8B LE length prefix + bytes, padded to 8-byte boundary
    # so the storage-count cell that follows is aligned.
    packed += struct.pack("<Q", len(calldata)) + calldata
    packed = pad_to_8(packed)

    # M22 storage segment: 8B LE slot count + slot_count × 64-byte
    # (key, value) pairs, padded to 8-byte boundary so the entire
    # input file size is a multiple of 8 (ziskemu requires this).
    packed += struct.pack("<Q", len(storage_pairs))
    for key, value in storage_pairs:
        packed += key + value
    packed = pad_to_8(packed)

    # M28 blob-context trailer: 32-byte BLOBBASEFEE word in stack
    # representation. It is naturally 8-byte aligned after the storage segment.
    packed += blob_base_fee

    if args.output == "-":
        sys.stdout.buffer.write(packed)
    else:
        with open(args.output, "wb") as f:
            f.write(packed)

    return 0


if __name__ == "__main__":
    sys.exit(main())
