#!/usr/bin/env bash
# eest-fetch-fixtures.sh -- Download the EEST stateless ("zkevm") fixtures.
#
# The stateless guest is validated against the Ethereum Execution Spec
# Tests (EEST) "zkevm" fixture line, which targets the Amsterdam fork
# (the working name for Glamsterdam) and ships the SSZ-encoded
# `StatelessInput` guest program inputs the Lean `run_stateless_guest`
# consumes (2-byte schema-id prefix + `public_keys` filled as of
# `zkevm@v0.4.0`).
#
# This script downloads the `fixtures_zkevm.tar.gz` asset attached to
# the EEST release tag into a gitignored cache and extracts it.  The
# EEST repo itself is vendored as the `execution-spec-tests` submodule
# (pinned to the same tag) for provenance / source; the *fixtures* are
# consumed from the release tarball rather than re-filled locally.
#
# Usage:
#   scripts/eest-fetch-fixtures.sh [TAG]
#   TAG defaults to the EEST_FIXTURE_TAG env var, else "zkevm@v0.4.0".
#
# Output:
#   gen-out/eest-fixtures/<TAG>/fixtures_zkevm.tar.gz   (downloaded)
#   gen-out/eest-fixtures/<TAG>/fixtures/               (extracted tree)
#   gen-out/eest-fixtures/<TAG>/.asset-meta             (size for re-run checks)
#
# Idempotent: re-running with an already-downloaded asset of the
# expected size skips the download (pass --force to re-download).
#
# Exit:
#   0 -- fixtures present and extracted
#   1 -- download / extraction failed
set -euo pipefail

cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

REPO="${EEST_REPO:-ethereum/execution-spec-tests}"
TAG="${1:-${EEST_FIXTURE_TAG:-zkevm@v0.4.0}}"
ASSET="fixtures_zkevm.tar.gz"
FORCE=0
[[ "${2:-}" == "--force" || "${1:-}" == "--force" ]] && FORCE=1

CACHE_DIR="$REPO_ROOT/gen-out/eest-fixtures/$TAG"
TARBALL="$CACHE_DIR/$ASSET"
EXTRACT_DIR="$CACHE_DIR/fixtures"
META_FILE="$CACHE_DIR/.asset-meta"

mkdir -p "$CACHE_DIR"

echo "==> EEST stateless fixtures: $REPO @ $TAG ($ASSET)"

# Expected asset size (bytes) from the release metadata, if gh is available.
expected_size=""
if command -v gh >/dev/null 2>&1; then
  expected_size="$(gh release view "$TAG" --repo "$REPO" \
    --json assets \
    --jq ".assets[] | select(.name==\"$ASSET\") | .size" 2>/dev/null || true)"
fi

need_download=1
if [[ "$FORCE" -eq 0 && -f "$TARBALL" ]]; then
  actual_size="$(stat -c '%s' "$TARBALL" 2>/dev/null || echo 0)"
  if [[ -n "$expected_size" && "$actual_size" == "$expected_size" ]]; then
    echo "    cached tarball matches release size ($actual_size bytes) -- skipping download"
    need_download=0
  elif [[ -z "$expected_size" && "$actual_size" -gt 0 ]]; then
    echo "    cached tarball present ($actual_size bytes); gh unavailable to verify -- reusing"
    need_download=0
  fi
fi

if [[ "$need_download" -eq 1 ]]; then
  echo "==> downloading $ASSET"
  if command -v gh >/dev/null 2>&1; then
    gh release download "$TAG" --repo "$REPO" --pattern "$ASSET" \
      --output "$TARBALL" --clobber
  else
    # curl fallback -- URL-encode the '@' in the tag as %40.
    enc_tag="${TAG/@/%40}"
    url="https://github.com/$REPO/releases/download/$enc_tag/$ASSET"
    echo "    gh not found; curl $url"
    curl -fL --retry 3 -o "$TARBALL" "$url"
  fi
fi

dl_size="$(stat -c '%s' "$TARBALL" 2>/dev/null || echo 0)"
printf 'tag=%s\nasset=%s\nsize=%s\nexpected_size=%s\n' \
  "$TAG" "$ASSET" "$dl_size" "${expected_size:-unknown}" >"$META_FILE"
echo "    tarball: $TARBALL ($dl_size bytes)"

echo "==> extracting into $EXTRACT_DIR"
rm -rf "$EXTRACT_DIR"
mkdir -p "$EXTRACT_DIR"
tar -xzf "$TARBALL" -C "$EXTRACT_DIR"

n_json="$(find "$EXTRACT_DIR" -name '*.json' | wc -l | tr -d ' ')"
echo "==> done: $n_json json file(s) under $EXTRACT_DIR"
echo "    (set EEST_FIXTURES_DIR=$EXTRACT_DIR for the harness)"
