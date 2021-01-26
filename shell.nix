let
  pkgs = import ./default.nix;
in
  pkgs.shellFor {
    packages = ps: [ ps.act ];
    tools = {
      haskell-language-server = "latest";
      cabal-install = "latest";
      happy = "latest";
      alex = "latest";
    };
    withHoogle = true;
  }

