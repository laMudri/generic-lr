{ stdenv, texlive }:
let
  tex-env = texlive.combine {
    inherit (texlive) scheme-small latexmk beamer stmaryrd mathpartir rsfs
                      cmll xcolor paralist makecell tikz-cd ncctools biblatex
                      biber;
  };
in stdenv.mkDerivation {
  name = "vest";
  src = ./.;
  buildInputs = [ tex-env ];
  buildPhase = ''
    latexmk generic-lr.tex
  '';
  installPhase = "";
}
