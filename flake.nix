{
  description = "act";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    hevm = {
      url = "github:ethereum/hevm/dynamic-flake-output";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { nixpkgs, flake-utils, hevm, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        gitignore = pkgs.nix-gitignore.gitignoreSourcePure [ ./.gitignore ];
        hspkgs = pkgs.haskellPackages.override {
          overrides = self: super: {
            hevm = hevm.packages.${system}.unwrapped;
          };
        };
        act = (hspkgs.callCabal2nixWithOptions "act" (gitignore ./.) "-fci" {})
          .overrideAttrs (attrs : {
            buildInputs = attrs.buildInputs ++ [ pkgs.z3 pkgs.cvc5 pkgs.solc ];
          });
      in rec {
        packages.act = act;
        packages.default = packages.act;

        apps.act = flake-utils.lib.mkApp { drv = packages.act; };
        apps.default = apps.act;

        devShell = let
          libraryPath = "${pkgs.lib.makeLibraryPath (with pkgs; [ libff secp256k1 gmp ])}";
        in hspkgs.shellFor {
          packages = _: [ act ];
          buildInputs = [
            hspkgs.cabal-install
            hspkgs.haskell-language-server
            pkgs.jq
            pkgs.z3
            pkgs.cvc5
            pkgs.coq
            pkgs.solc
            pkgs.mdbook
            pkgs.mdbook-mermaid
            pkgs.mdbook-katex
            pkgs.secp256k1
            pkgs.libff
          ];
          withHoogle = true;
          shellHook = ''
            export PATH=$(pwd)/bin:$PATH
            export DYLD_LIBRARY_PATH="${libraryPath}"
          '';
      };
    }
  );
}
