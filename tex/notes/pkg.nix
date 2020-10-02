{ stdenv, lib, texlive }:
let
  tex-env = texlive.combine {
    inherit (texlive) scheme-small latexmk chktex stmaryrd mathpartir rsfs
                      cmll xcolor paralist makecell tikz-cd ncctools biblatex;
  };
in stdenv.mkDerivation {
  name = "notes";
  src = lib.sourceFilesBySuffices ./. [ ".nix" ".tex" ];
  # [ ./pkg.nix ./default.nix ./shell.nix ];
  buildInputs = [ tex-env ];
  buildPhase = ''
    latexmk notes.tex
  '';
  installPhase = "";
}
