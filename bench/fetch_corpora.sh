#!/usr/bin/env bash
# Materialize the standard compression corpora used by the Track D dashboard
# into bench/corpora/<name>/, verified against recorded SHA-256 checksums.
#
#   bench/fetch_corpora.sh [canterbury]   # default: all known corpora
#
# Canterbury (~2.8 MB, 11 files) is committed to the repo, so CI needs no
# network; running this script is only needed to re-materialize or update it.
# Larger corpora (e.g. Silesia) are NOT committed and are fetched on demand
# into this gitignored cache — see bench/.gitignore. Sources (PLAN.md §D):
#   Canterbury: https://corpus.canterbury.ac.nz/
set -euo pipefail
cd "$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"

CORPORA_DIR="bench/corpora"

# Recorded SHA-256 of every Canterbury file (the standard cantrbry.tar.gz from
# corpus.canterbury.ac.nz). The fetch is verified file-by-file against these.
CANTERBURY_URL="https://corpus.canterbury.ac.nz/resources/cantrbry.tar.gz"
read -r -d '' CANTERBURY_SHA256 <<'EOF' || true
7467306ee0feed4971260f3c87421154a05be571d944e9cb021a5713700c38f0  alice29.txt
eaa3526fe53859f34ecdf255712f9ecf0b2c903451d4755b2edaa2e2599cb0fc  asyoulik.txt
e0cd21cef5b6c4069461e949be100080c3ce887de6f1dd8626c480528efaaf61  cp.html
85d73e354cc50cec76cb5a50537cf8dc035f8cbb8480f9e1cbe2f7d6c23393c7  fields.c
1b0805dfc0ae706b35aac2bb4e15f02485efd24dda5dbd29de7b2f84d1a88c15  grammar.lsp
9af47239ca29dfe20e633f80bbbb9a4cc9783d0803d7b2b5626f42e4c3790420  kennedy.xls
5314ba1dbb03f471df88bec6cd120a938ef60d0fd3511c5c1dce61bf7463245f  lcet10.txt
07e2e0b461af78c7c647cb53dab39de560198e16f799b4516eccf0fbd69f764c  plrabn12.txt
0ec3a75089bb52342813496b17e51377bc9eba3cb519a444d67025354841d650  ptt5
ee5733cd76ecc2f9d8ff156adc3c02a7a851051dcf43a2d56ff4ee4ff606bdb3  sum
c58aeb5d2d1e12751d47e7412b45784405fc30a5671b03d480fa05776e183619  xargs.1
EOF

fetch_canterbury() {
  local dest="$CORPORA_DIR/canterbury"
  echo "[canterbury] fetching $CANTERBURY_URL"
  local tmp
  tmp="$(mktemp -d)"
  curl -sSL --fail --max-time 120 -o "$tmp/cantrbry.tar.gz" "$CANTERBURY_URL"
  mkdir -p "$dest"
  tar xzf "$tmp/cantrbry.tar.gz" -C "$dest"
  rm -rf "$tmp"
  # Verify every file against the recorded checksum (fail closed on mismatch).
  ( cd "$dest" && printf '%s\n' "$CANTERBURY_SHA256" | sha256sum --check --quiet )
  echo "[canterbury] ok — 11 files in $dest verified against recorded SHA-256"
}

main() {
  mkdir -p "$CORPORA_DIR"
  local which="${1:-all}"
  case "$which" in
    canterbury|all) fetch_canterbury ;;
    *) echo "unknown corpus: $which (known: canterbury)" >&2; exit 2 ;;
  esac
}

main "$@"
