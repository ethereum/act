{
  description = "act";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs";
    hevmUpstream = {
      url = "github:ethereum/hevm/87a171da0437ac4902a723b78352a3e509c7dcc9";
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
        act = (myHaskellPackages.callCabal2nixWithOptions "act" (gitignore ./src) "-fci" {})
          .overrideAttrs (attrs : {
            buildInputs = attrs.buildInputs ++ [ pkgs.z3 pkgs.cvc4 ];
          });
      in rec {
        packages.act = act;
        packages.default = packages.act;

        apps.act = flake-utils.lib.mkApp { drv = packages.act; };
        apps.default = apps.act;

        devShell = myHaskellPackages.shellFor {
          packages = _: [ act ];
          buildInputs = with pkgs.haskellPackages; [
            cabal-install
            haskell-language-server
            pkgs.jq
            pkgs.z3
            pkgs.cvc4
            pkgs.coq
            pkgs.solc
            pkgs.mdbook
            pkgs.mdbook-mermaid
            pkgs.mdbook-katex
          ];
          withHoogle = true;
          shellHook = ''
            export PATH=$(pwd)/bin:$PATH
          '';
        };
      }
  );
}
