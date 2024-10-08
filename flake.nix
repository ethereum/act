{
  description = "act";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/f85a3c6af20f02135814867870deb419329e8297";
    hevmUpstream = {
      url = "github:ethereum/hevm";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, hevmUpstream, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        gitignore = pkgs.nix-gitignore.gitignoreSourcePure [ ./.gitignore ];
        myHaskellPackages = pkgs.haskellPackages.override {
          overrides = self: super: rec {
            hevm = hevmUpstream.packages.${system}.noTests;
          };
        };
        act = (myHaskellPackages.callCabal2nixWithOptions "act" (gitignore ./.) "-fci" {})
          .overrideAttrs (attrs : {
            buildInputs = attrs.buildInputs ++ [ pkgs.z3 pkgs.cvc5 pkgs.solc ];
          });
      in rec {
        packages.act = act;
        packages.default = packages.act;

        apps.act = flake-utils.lib.mkApp { drv = packages.act; };
        apps.default = apps.act;

        devShell = with pkgs;
          let libraryPath = "${lib.makeLibraryPath [ libff secp256k1 gmp ]}";
          in myHaskellPackages.shellFor {
          packages = _: [ act ];
          buildInputs = with pkgs.haskellPackages; [
            cabal-install
            haskell-language-server
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
