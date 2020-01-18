{ mkDerivation, aeson, array, base, bytestring, stdenv, text }:
mkDerivation {
  pname = "act";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [ aeson array base bytestring text ];
  license = "unknown";
  hydraPlatforms = stdenv.lib.platforms.none;
}
