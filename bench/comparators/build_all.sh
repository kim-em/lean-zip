#!/usr/bin/env bash
# Build the external-language DEFLATE comparators for the Track D dashboard.
#
# Each comparator uses its own nix toolchain; a build failure warns and continues
# (the driver, run_external.py, then skips any comparator whose binary is absent),
# so the dashboard degrades gracefully when a toolchain or package is unavailable.
#
# Produces, when successful:
#   go/bench-go      js/node_modules/  zig/bench-zig      ocaml/bench-ocaml
set -uo pipefail
cd "$(dirname "$0")"

echo "[go] building (pure-Go compress/flate)…"
( cd go && nix-shell -p go --run "go build -o bench-go main.go" ) \
  && echo "[go] ok" || echo "[go] FAILED — skipping"

echo "[js] installing fflate (pure-JS)…"
( cd js && nix-shell -p nodejs --run "npm install --no-audit --no-fund --silent" ) \
  && echo "[js] ok" || echo "[js] FAILED — skipping"

# Zig 0.14.1 specifically: the 0.15 stdlib `flate.Compress` encoder is an
# unimplemented @panic("TODO"); 0.14.1 is the last release with a working one.
echo "[zig] building (pure-Zig std.compress.flate, zig 0.14.1)…"
( cd zig && nix-shell -p zig_0_14 --run "zig build-exe -O ReleaseFast bench.zig -femit-bin=bench-zig" ) \
  && echo "[zig] ok" || echo "[zig] FAILED — skipping"

echo "[ocaml] building (pure-OCaml mirage/decompress)…"
( cd ocaml && nix-shell -p ocaml dune_3 ocamlPackages.findlib ocamlPackages.decompress \
    --run "dune build && cp -f _build/default/bench.exe bench-ocaml" ) \
  && echo "[ocaml] ok" || echo "[ocaml] FAILED — skipping"

exit 0
