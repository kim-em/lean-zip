{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  buildInputs = [
    # The shipped library needs only zlib + pkg-config; a bare root
    # `lake build` / `lake exe test` uses nothing below this line.
    pkgs.pkg-config
    pkgs.zlib
    # Everything below serves the dev-only bench/ sub-package (Track D):
    # `bench/run.sh` invokes `lake -d bench …` and the plotter from this
    # same shell, so the comparator + plotting toolchain lives here.
    #
    # miniz_oxide comparator — cargo+rustc build bench/rust/miniz_oxide_shim/.
    # Without them, `cd bench && lake build` still succeeds but the miniz
    # stub raises IO.userError at runtime.
    pkgs.cargo
    pkgs.rustc
    # libdeflate/zopfli reference comparators (C libs, linked directly via
    # bench/c/*_ffi.c) and the matplotlib plotter that renders
    # bench/results/*.json into the log-scale SVG graphs under bench/graphs/.
    pkgs.libdeflate
    pkgs.zopfli
    (pkgs.python3.withPackages (ps: [ ps.matplotlib ]))
  ];
}
