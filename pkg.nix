{ stdenv, lib, texlive, agda }:
let
  tex-env = texlive.combine {
    inherit (texlive) scheme-small latexmk chktex stmaryrd mathpartir rsfs
                      cmll xcolor paralist makecell tikz-cd ncctools biblatex
                      xifthen ifmtarg polytable etoolbox environ xkeyval
                      lazylist trimspaces newunicodechar
                      catchfilebetweentags catchfile;
  };
  agda-env = agda.withPackages (p: with p; [ standard-library ]);
in stdenv.mkDerivation {
  name = "generic-lr";
  src = lib.sourceFilesBySuffices ./tex [ ".nix" ".tex" ]
      + lib.sourceFilesBySuffices ./src [ ".agda" ".lagda.tex" ];
  buildInputs = [ tex-env agda-env ];
  buildPhase = ''
    make
  '';
  installPhase = "";
}
