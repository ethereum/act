{ mkDerivation, aeson, alex, array, base, BNFC, bytestring, happy
, optparse-generic , stdenv, text, vector
}:
mkDerivation {
  pname = "act";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [
    aeson array base bytestring optparse-generic text vector
  ];
  preBuild = "make parser";
  executableToolDepends = [ alex BNFC happy ];
  license = "unknown";
  hydraPlatforms = stdenv.lib.platforms.none;
}
