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

Usage:
    pack-bytecode.py "0x60, 0x02, 0x60, 0x0a, 0x04, 0x00" output.bin
    pack-bytecode.py --calldata "0xdeadbeef" "0x36, 0x00" output.bin
    echo "0x60, 0x00" | pack-bytecode.py - output.bin

Output layout:

    bytes 0..8         <8-byte LE u64 length of bytecode>
    bytes 8..          <bytecode bytes>
                       <zero pad to 8-byte boundary>
    next 8 bytes       <8-byte LE u64 length of calldata>
    following          <calldata bytes>
                       <zero pad to 8-byte boundary>

ziskemu prepends 8 more bytes of its own metadata when loading,
landing the bytecode-length prefix at INPUT_ADDR+8 and the bytecode
at INPUT_ADDR+16 — which is where the runtime-bytecode dispatcher's
`li x10, 0x40000010` points. The calldata-length prefix lands at
the first 8-byte boundary past the bytecode bytes; the dispatcher
prologue computes that address at startup.

Backwards-compatible: pre-M21 callers that don't pass --calldata get
a zero-length calldata segment appended, which preserves the M17
"CALLDATA opcodes are no-op" behavior for existing test cases.
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
    args = parser.parse_args()

    csv = sys.stdin.read() if args.bytecode == "-" else args.bytecode
    bytecode = parse_csv(csv)
    calldata = parse_calldata(args.calldata)

    # Bytecode segment: 8B LE length prefix + bytes, padded to 8-byte boundary
    # so the calldata-length cell that follows is aligned.
    packed = struct.pack("<Q", len(bytecode)) + bytecode
    packed = pad_to_8(packed)

    # Calldata segment: 8B LE length prefix + bytes, padded to 8-byte boundary
    # so the entire input file size is a multiple of 8 (ziskemu requires this).
    packed += struct.pack("<Q", len(calldata)) + calldata
    packed = pad_to_8(packed)

    if args.output == "-":
        sys.stdout.buffer.write(packed)
    else:
        with open(args.output, "wb") as f:
            f.write(packed)

    return 0


if __name__ == "__main__":
    sys.exit(main())
