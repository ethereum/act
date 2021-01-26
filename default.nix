let
  compiler = "ghc865";

  sources = import ./nix/sources.nix;
  haskellNix = import sources."haskell.nix" {};
  dapptools = import sources.dapptools {};

  overlays = haskellNix.overlays ++ dapptools.overlays ++ [ (self: super: { ff = self.libff; }) ];
  pkgs = import haskellNix.sources.nixpkgs-2009 (haskellNix.nixpkgsArgs // { inherit overlays; });

  myHaskellPackages = pkgs.haskell.packages.${compiler}.override {
    overrides = hself: hsuper: {
      hevm = dapptools.haskellPackages.hevm;
      sbv = dapptools.haskellPackages.sbv;
    };
  };
in
  pkgs.haskell-nix.project {
    hsPkgs = myHaskellPackages;
    src = pkgs.haskell-nix.haskellLib.cleanGit {
      name = "act";
      src = ./src;
    };
    compiler-nix-name = compiler;
    index-state = "2021-01-26T00:00:00Z";
    plan-sha256 = "03wy36lsf5bxrydi6mgndzyj3p2dzsyrli5xv4nkd5x7llk7zji9";
    modules = [{ packages.act.flags.ci = true; }];
  }

