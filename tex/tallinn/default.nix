{ nixpkgs ? import <nixpkgs> {} }:
nixpkgs.pkgs.callPackage ./pkg.nix { }
