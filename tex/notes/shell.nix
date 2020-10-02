{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  inputsFrom = [ (pkgs.callPackage ./pkg.nix { }) ];
}
