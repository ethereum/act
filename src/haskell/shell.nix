{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc865" }:
(import ./default.nix { inherit nixpkgs compiler; }).env
