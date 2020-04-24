{nixpkgs ? import <nixpkgs> {}, compiler ? "ghc865"}:
let  dapptools = builtins.fetchGit {
    url = "https://github.com/dapphub/dapptools.git";
    rev = "345b6ea42704c51af44c00bb18eb0becc768cf1f";
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
