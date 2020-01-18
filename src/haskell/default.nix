{ mkDerivation, aeson, base, stdenv }:
mkDerivation {
  pname = "act";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [ aeson base ];
  license = "unknown";
  hydraPlatforms = stdenv.lib.platforms.none;
}
