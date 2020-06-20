{ compiler ? "ghc865" }:

let
  # git ls-remote https://github.com/NixOS/nixpkgs-channels.git nixos-19.09
  nixpkgs-commit = "289466dd6a11c65a7de4a954d6ebf66c1ad07652";
  pkgs = import (fetchTarball {
    url = "https://github.com/NixOS/nixpkgs-channels/tarball/${nixpkgs-commit}";
    sha256 = "0r5ja052s86fr54fm1zlhld3fwawz2w1d1gd6vbvpjrpjfyajibn";
  }) {};

  dapptools = import (fetchGit {
    url = https://github.com/dapphub/dapptools.git;
    ref = "symbolic";
  }) {};

  gitignore = pkgs.nix-gitignore.gitignoreSourcePure [ ./.gitignore ];

  myHaskellPackages = pkgs.haskell.packages.${compiler}.override {
    overrides = hself: hsuper: {
      hevm = dapptools.haskellPackages.hevm;
      sbv = dapptools.haskellPackages.sbv_8_6;
      act =
        hself.callCabal2nix
          "act"
          (gitignore ./src)
          {};
    };
  };

  shell = myHaskellPackages.shellFor {
    packages = p: [
      p.act
    ];
    buildInputs = with pkgs.haskellPackages; [
      myHaskellPackages.cabal-install
    ];
    withHoogle = true;
  };

  exe = pkgs.haskell.lib.justStaticExecutables (myHaskellPackages.act);
in
{
  inherit shell;
  inherit exe;
  inherit myHaskellPackages;
  act = myHaskellPackages.act;
}
