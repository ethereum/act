{ mkDerivation, aeson, alex, array, base, BNFC, bytestring, containers, happy
, optparse-generic , stdenv, sbv_8_4, text, vector, hevm
}:
mkDerivation {
  pname = "act";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [
    aeson array base bytestring containers hevm optparse-generic sbv_8_4 text vector
  ];
  preBuild = "make parser";
  executableToolDepends = [ alex BNFC happy ];
  license = "unknown";
  hydraPlatforms = stdenv.lib.platforms.none;
}
