# progress-history

Append-only per-commit snapshots of the kernel-checked progress
registry, emitted by `scripts/progress-snapshot.sh` from
`.github/workflows/progress-history.yml` (steering Phase 2, R-A5).

One JSON object per line in `history.jsonl` — see
`scripts/progress-snapshot.sh` for the field list. Read with
`scripts/progress-velocity.sh history.jsonl`.
