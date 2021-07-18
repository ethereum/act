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
      act =
        pkgs.haskell.lib.dontCheck (hself.callCabal2nixWithOptions
          "act"
          (gitignore ./src)
          "-fci"
          {});
    };
  };

  shell = myHaskellPackages.shellFor {
    packages = p: [
      p.act
      p.hevm
    ];
    buildInputs = with pkgs.haskellPackages; [
      cabal-install
      haskell-language-server
      pkgs.jq
      pkgs.z3
      pkgs.cvc4
      pkgs.coq_8_10
      dapptools.solc
    ];
    withHoogle = true;
    shellHook = ''
      export PATH=${toString ./bin}:$PATH
    '';
  };
in
{
  inherit shell;
  exe = myHaskellPackages.act;
}
