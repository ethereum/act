with import <nixpkgs> {};
let
drv = haskell.lib.addBuildTool (
    haskellPackages.callPackage (import ./default.nix) {}
  ) [cabal-install cabal2nix];

in
  drv
