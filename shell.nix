{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  name = "act";
  buildInputs = (with pkgs; [
    coq_8_9
  ]) ++ (with pkgs.haskellPackages; [
    alex
    BNFC
    happy
  ]);
}
