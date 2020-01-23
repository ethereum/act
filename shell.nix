with import <nixpkgs> {}; with haskellPackages;
stdenv.mkDerivation {
  name = "act";
  buildInputs = [
    BNFC
    alex
    happy
    ghc
  ];
}
