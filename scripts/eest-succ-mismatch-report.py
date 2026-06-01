#!/usr/bin/env python3
"""Report EEST successful_validation mismatches with executable-spec context.

Run after scripts/codegen-eest-stateless-check.sh has produced
gen-out/eest-run/manifest.tsv and per-case *.result.tsv files.

Recommended:
  uv run --directory execution-specs --quiet python3 \
    ../scripts/eest-succ-mismatch-report.py
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def add_execution_specs_to_path(root: Path) -> None:
    src = root / "execution-specs" / "src"
    if src.is_dir():
        sys.path.insert(0, str(src))


def unpack_zisk_input(path: Path) -> bytes:
    data = path.read_bytes()
    if len(data) < 8:
        raise ValueError("input shorter than zisk length prefix")
    n = int.from_bytes(data[:8], "little")
    blob = data[8 : 8 + n]
    if len(blob) != n:
        raise ValueError(f"input truncated: want {n} bytes, have {len(blob)}")
    return blob


def decode_context(input_path: Path) -> str:
    from ethereum.forks.amsterdam.stateless_guest import (  # type: ignore
        deserialize_stateless_input,
    )

    blob = unpack_zisk_input(input_path)
    stateless_input = deserialize_stateless_input(blob)
    payload = stateless_input.new_payload_request.execution_payload
    return "\t".join(
        [
            f"txs={len(payload.transactions)}",
            f"gas_limit={int(payload.gas_limit)}",
            f"gas_used={int(payload.gas_used)}",
            f"bal_bytes={len(payload.block_access_list)}",
            f"public_keys={len(stateless_input.public_keys)}",
            f"headers={len(stateless_input.witness.headers)}",
            f"state_nodes={len(stateless_input.witness.state)}",
            f"codes={len(stateless_input.witness.codes)}",
        ]
    )


def main() -> int:
    root = repo_root()
    add_execution_specs_to_path(root)

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--manifest",
        type=Path,
        default=root / "gen-out" / "eest-run" / "manifest.tsv",
    )
    parser.add_argument(
        "--results-dir",
        type=Path,
        default=None,
        help="directory containing *.result.tsv (default: manifest parent)",
    )
    parser.add_argument("--limit", type=int, default=0)
    args = parser.parse_args()

    manifest = args.manifest
    results_dir = args.results_dir or manifest.parent
    if not manifest.is_file():
        raise SystemExit(f"manifest not found: {manifest}")

    printed = 0
    print(
        "\t".join(
            [
                "label",
                "guest_succ",
                "expected_succ",
                "context",
                "fixture",
            ]
        )
    )
    with manifest.open() as f:
        for line in f:
            label, input_file, expected_hex, _succ_bit, _input_len, relpath = (
                line.rstrip("\n").split("\t", 5)
            )
            result = results_dir / f"{label}.result.tsv"
            if not result.is_file():
                continue
            status, actual = result.read_text().rstrip("\n").split("\t", 1)
            if status != "OK":
                continue
            expected = expected_hex[:210]
            guest_succ = actual[64:66]
            expected_succ = expected[64:66]
            if guest_succ == expected_succ:
                continue
            try:
                context = decode_context(Path(input_file))
            except Exception as exc:
                context = f"decode_error={type(exc).__name__}:{exc}"
            print(
                "\t".join(
                    [
                        label,
                        guest_succ,
                        expected_succ,
                        context,
                        relpath,
                    ]
                )
            )
            printed += 1
            if args.limit and printed >= args.limit:
                break
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
