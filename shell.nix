{compiler ? "ghc865"}:
let
  nixpkgs = import (builtins.fetchGit {
    url = "https://github.com/nixos/nixpkgs";
    ref = "release-19.09";
    rev = "54e89941c303687a6392a3264dbe1540fe3381d8";
  }) {};
  dapptools = builtins.fetchGit {
    url = "https://github.com/dapphub/dapptools.git";
    rev = "509a5741f03ea4d80a4901e1f6a6a9ac4b443ec0";
    ref = "symbolic";
  };
  pkgs-for-dapp = import <nixpkgs> {
    overlays = [
      (import (dapptools + /overlay.nix))
    ];
  };
  h = nixpkgs.pkgs.haskell.packages.${compiler}.override (old: {
    overrides = nixpkgs.pkgs.lib.composeExtensions (old.overrides or (_: _: {})) (
      import (dapptools + /haskell.nix) { lib = nixpkgs.pkgs.lib; pkgs = pkgs-for-dapp; }
    );
  });
in
nixpkgs.mkShell {
  buildInputs = [ (h.ghcWithPackages (p: [p.hevm p.sbv_8_4 p.aeson p.alex p.array p.base p.bytestring p.containers p.happy p.optparse-generic p.text p.vector])) ];
}
