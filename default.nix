{ compiler ? "ghc865" }:

let
  sources = import ./nix/sources.nix;
  pkgs = import sources.nixpkgs {};
  dapptools = import sources.dapptools {};

  gitignore = pkgs.nix-gitignore.gitignoreSourcePure [ ./.gitignore ];

  myHaskellPackages = pkgs.haskell.packages.${compiler}.override {
    overrides = hself: hsuper: {
      hevm = dapptools.haskellPackages.hevm;
      sbv = dapptools.haskellPackages.sbv;
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
      cabal-install
      pkgs.jq
    ];
    withHoogle = true;
    shellHook = ''
      export PATH=${toString ./bin}:$PATH
    '';
  };

  exe = pkgs.haskell.lib.justStaticExecutables (myHaskellPackages.act);
in
{
  inherit shell;
  inherit exe;
  inherit myHaskellPackages;
  act = myHaskellPackages.act;
}
