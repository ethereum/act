let
  pkgs = import ./default.nix;

  sources = import ./nix/sources.nix;
  haskellNix = import sources."haskell.nix" {};
  dapptools = import sources.dapptools {};

  overlays = haskellNix.overlays ++ dapptools.overlays ++ [ (self: super: { ff = self.libff; }) ];
  nixpkgs = import haskellNix.sources.nixpkgs-2009 (haskellNix.nixpkgsArgs // { inherit overlays; });
in
  pkgs.shellFor {
    packages = ps: [ ps.act ];
    buildInputs = [ nixpkgs.secp256k1 ];
    tools = {
      haskell-language-server = "latest";
      cabal-install = "latest";
      happy = "latest";
      alex = "latest";
    };
    withHoogle = true;
  }

