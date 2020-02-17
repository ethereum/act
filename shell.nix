with import <nixpkgs> {}; with haskellPackages;
let
  drv = haskell.lib.addBuildTool (
    callPackage (import ./src/default.nix) {}
  ) [cabal-install cabal2nix BNFC];
in
  drv
