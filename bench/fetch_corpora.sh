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

# Silesia (~202 MB unzipped, 12 files) — the modern publishable standard, NOT
# committed (gitignored). Each file is a separate .zip on a pinned GitHub mirror
# (the primary host sun.aei.polsl.pl is unreliable); we fetch, unzip, and verify
# the unzipped bytes against the recorded SHA-256.
SILESIA_BASE="https://raw.githubusercontent.com/MiloszKrajewski/SilesiaCorpus/master"
read -r -d '' SILESIA_SHA256 <<'EOF' || true
b24c37886142e11d0ee687db6ab06f936207aa7f2ea1fd1d9a36763c7a507e6a  dickens
657fc3764b0c75ac9de9623125705831ebbfbe08fed248df73bc2dc66e2a963b  mozilla
68637ed52e3e4860174ed2dc0840ac77d5f1a60abbcb13770d5754e3774d53e6  mr
fc63a31770947b8c2062d3b19ca94c00485a232bb91b502021948fee983e1635  nci
e7ee013880d34dd5208283d0d3d91b07f442e067454276095ded14f322a656eb  ooffice
60f027179302ca3ad87c58ac90b6be72ec23588aaa7a3b7fe8ecc0f11def3fa3  osdb
0eac0114a3dfe6e2ee1f345a0f79d653cb26c3bc9f0ed79238af4933422b7578  reymont
93ba07bc44d8267789c1d911992f40b089ffa2140b4a160fac11ccae9a40e7b2  samba
c2d0ea2cc59d4c21b7fe43a71499342a00cbe530a1d5548770e91ecd6214adcc  sao
6a68f69b26daf09f9dd84f7470368553194a0b294fcfa80f1604efb11143a383  webster
7de9fce1405dc44ae5e6813ed21cd5751e761bd4265655a005d39b9685d1c9ad  x-ray
0e82e54e695c1938e4193448022543845b33020c8be6bf3bf3ead2224903e08c  xml
EOF

fetch_silesia() {
  local dest="$CORPORA_DIR/silesia"
  mkdir -p "$dest"
  echo "[silesia] fetching 12 files from $SILESIA_BASE"
  local f
  for f in dickens mozilla mr nci ooffice osdb reymont samba sao webster x-ray xml; do
    if [ ! -f "$dest/$f" ]; then
      curl -sSL --fail --max-time 300 -o "$dest/$f.zip" "$SILESIA_BASE/$f.zip"
      # unzip via python3 (avoids an `unzip` dependency)
      python3 -c "import zipfile,sys; zipfile.ZipFile(sys.argv[1]).extractall(sys.argv[2])" \
        "$dest/$f.zip" "$dest"
      rm -f "$dest/$f.zip"
    fi
  done
  ( cd "$dest" && printf '%s\n' "$SILESIA_SHA256" | sha256sum --check --quiet )
  echo "[silesia] ok — 12 files in $dest verified against recorded SHA-256"
}

main() {
  mkdir -p "$CORPORA_DIR"
  local which="${1:-all}"
  case "$which" in
    canterbury) fetch_canterbury ;;
    silesia)    fetch_silesia ;;
    all)        fetch_canterbury; fetch_silesia ;;
    *) echo "unknown corpus: $which (known: canterbury, silesia, all)" >&2; exit 2 ;;
  esac
}

main "$@"
