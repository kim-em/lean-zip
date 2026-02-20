{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  buildInputs = [
    pkgs.pkg-config
    pkgs.zlib
    (pkgs.zstd.override { enableStatic = true; })
  ];
}
