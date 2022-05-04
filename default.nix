{ compiler ? "ghc8104" }:

let
  sources = import ./nix/sources.nix;
  pkgs = import sources.nixpkgs {};
  dapptools = import sources.dapptools {};

  gitignore = pkgs.nix-gitignore.gitignoreSourcePure [ ./.gitignore ];

  myHaskellPackages = pkgs.haskell.packages.${compiler}.override {
    overrides = hself: hsuper: {
      hevm = dapptools.sharedHaskellPackages.hevm;
      sbv = dapptools.sharedHaskellPackages.sbv;
      act = (hself.callCabal2nixWithOptions "act" (gitignore ./src) "-fci" {}).overrideAttrs (attrs : {
        buildInputs = attrs.buildInputs ++ [ pkgs.z3 pkgs.cvc4 ];
      });
    };
  };

  shell = myHaskellPackages.shellFor {
    packages = p: [
      p.act
    ];
    buildInputs = with pkgs.haskellPackages; [
      cabal-install
      haskell-language-server
      pkgs.jq
      pkgs.z3
      pkgs.cvc4
      pkgs.coq_8_10
      dapptools.solc
      pkgs.mdbook
      pkgs.mdbook-mermaid
    ];
    withHoogle = true;
    shellHook = ''
      export PATH=${toString ./bin}:$PATH
    '';
  };
in
{
  inherit shell;
  act = myHaskellPackages.act;
}
