{ nixpkgs ? (fetchTarball "https://github.com/NixOS/nixpkgs/archive/81cef6b70fb5d5cdba5a0fef3f714c2dadaf0d6d.tar.gz") }:
with (import nixpkgs {});
agdaPackages.mkDerivation {
  version = "0.1";
  pname = "generic-lr";
  src = ./.;
  everythingFile = "src/Everything.agda";
  buildInputs = [
    agdaPackages.standard-library
  ];
  meta = with lib; {
    description = "AACMM's generic-syntax, but with QTT-style annotations";
    homepage = "https://github.com/laMudri/generic-lr/";
    license = licenses.gpl3;
  };
}
