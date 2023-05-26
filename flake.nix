{
  description = "act";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs";
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        gitignore = pkgs.nix-gitignore.gitignoreSourcePure [ ./.gitignore ];
        act = (pkgs.haskellPackages.callCabal2nixWithOptions "act" (gitignore ./src) "-fci" {})
          .overrideAttrs (attrs : {
            buildInputs = attrs.buildInputs ++ [ pkgs.z3 pkgs.cvc4 ];
          });
      in rec {
        packages.act = act;
        packages.default = packages.act;

        apps.act = flake-utils.lib.mkApp { drv = packages.act; };
        apps.default = apps.act;

        devShell = pkgs.haskellPackages.shellFor {
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
          ];
          withHoogle = true;
          shellHook = ''
            export PATH=$(pwd)/bin:$PATH
          '';
        };
      }
  );
}
