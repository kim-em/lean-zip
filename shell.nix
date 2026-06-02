{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  buildInputs = [
    pkgs.pkg-config
    pkgs.zlib
    # Track D Phase 0c — miniz_oxide comparator. cargo+rustc are required
    # to build rust/miniz_oxide_shim/. Without them, `lake build` still
    # succeeds but the comparator stubs raise IO.userError at runtime.
    pkgs.cargo
    pkgs.rustc
    # Track D dashboard — libdeflate/zopfli reference comparators (C libs,
    # linked directly via c/*_ffi.c) and the matplotlib plotter that renders
    # bench/results/*.json into the log-scale SVG graphs under bench/graphs/.
    pkgs.libdeflate
    pkgs.zopfli
    (pkgs.python3.withPackages (ps: [ ps.matplotlib ]))
  ];
}
