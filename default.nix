{ compiler ? "ghc8104" }:

let
  sources = import ./nix/sources.nix;
  pkgs = import sources.nixpkgs {};
  dapptools = import sources.dapptools {};

  gitignore = pkgs.nix-gitignore.gitignoreSourcePure [ ./.gitignore ];

  haskell = pkgs.haskell.packages.${compiler}.override {
    overrides = self: super: {
      hevm = dapptools.sharedHaskellPackages.hevm;
      sbv = dapptools.sharedHaskellPackages.sbv;
      act =
        pkgs.haskell.lib.dontCheck (self.callCabal2nixWithOptions
          "act"
          (gitignore ./src)
          "-fci"
          {});
    };
  };

  shell = haskell.shellFor {
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
    ];
    withHoogle = true;
    shellHook = ''
      export PATH=${toString ./bin}:$PATH
    '';
  };
in
{
  inherit shell;
  exe = haskell.act;
}
