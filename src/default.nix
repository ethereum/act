{ mkDerivation, aeson, array, base, bytestring, stdenv, text
, vector
}:
mkDerivation {
  pname = "act";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [
    aeson array base bytestring text vector
  ];
  license = "unknown";
  hydraPlatforms = stdenv.lib.platforms.none;
}
