{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  buildInputs = [
    # Only the dev-only conformance/ sub-package needs anything here; a
    # bare root `lake build` / `lake test` uses nothing below this line.
    pkgs.pkg-config
    pkgs.zlib
  ];
}
