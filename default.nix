{nixpkgs ? import <nixpkgs> {}, compiler ? "ghc865"}:
let
  dapptools = builtins.fetchGit {
    url = "https://github.com/dapphub/dapptools.git";
    rev = "064c25ada217f519a9d4e3cc750c33dbaa5083dc";
    ref = "symbolic";
  };
  pkgs-for-dapp = import <nixpkgs> {
    overlays = [
      (import (dapptools + /overlay.nix))
    ];
  };
  myHaskellPackages = nixpkgs.pkgs.haskell.packages.${compiler}.override {
    overrides = self: super: rec {
    sbv_8_4 = super.sbv_8_4.overrideAttrs (attrs: {
      meta.broken = false;
      postPatch = ''
      sed -i -e 's|"z3"|"${nixpkgs.pkgs.z3}/bin/z3"|' Data/SBV/Provers/Z3.hs'';
    });

    hevm = nixpkgs.pkgs.haskell.lib.dontHaddock((self.callPackage (import (dapptools + /src/hevm)) {
        # Haskell libs with the same names as C libs...
        # Depend on the C libs, not the Haskell libs.
        # These are system deps, not Cabal deps.
        inherit (nixpkgs.pkgs) secp256k1;
        ff = pkgs-for-dapp.libff;
        }
      ).overrideAttrs (attrs: {
      postInstall = ''
        wrapProgram $out/bin/hevm --suffix PATH \
          : "${nixpkgs.lib.makeBinPath (with nixpkgs.pkgs; [bash coreutils git])}"
      '';

      enableSeparateDataOutput = true;
      buildInputs = attrs.buildInputs ++ [nixpkgs.pkgs.solc nixpkgs.pkgs.z3];
      nativeBuildInputs = attrs.nativeBuildInputs ++ [nixpkgs.pkgs.makeWrapper];
      }));
};
};
in

myHaskellPackages.callPackage (import ./src/default.nix) {}
