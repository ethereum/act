{ mkDerivation, aeson, alex, array, base, bytestring, containers, happy
, optparse-generic, stdenv, sbv_8_4, text, vector, mtl, hevm
}:
mkDerivation {
  pname = "act";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [
    aeson array base bytestring containers hevm optparse-generic sbv_8_4 text vector mtl
  ];
  preBuild = "make";
  executableToolDepends = [ alex happy ];
  license = "unknown";
  hydraPlatforms = stdenv.lib.platforms.none;
}
