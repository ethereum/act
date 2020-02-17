{nixpkgs ? import <nixpkgs> {}, compiler ? "ghc865"}:
nixpkgs.pkgs.haskell.packages.${compiler}.callPackage (import ./src/default_mod.nix) {}
