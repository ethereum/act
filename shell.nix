with import <nixpkgs> {}; with haskellPackages;
let
  drv = haskell.lib.addBuildTool (
    haskellPackages.callPackage (import src/default.nix) {}
  ) [cabal-install cabal2nix BNFC alex happy ghc];
in
  drv
