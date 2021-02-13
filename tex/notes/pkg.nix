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
  name = "notes";
  src = lib.sourceFilesBySuffices ./. [ ".nix" ".tex" ];
  # [ ./pkg.nix ./default.nix ./shell.nix ];
  buildInputs = [ tex-env agda-env ];
  buildPhase = ''
    latexmk notes.tex
  '';
  installPhase = "";
}
