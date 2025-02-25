# https://phijor.me/tutorials/agda-development-nix-flakes/

{
  description = "An Agda Library set up with Nix Flakes";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = {
    self,
    nixpkgs,
    flake-utils,
    ...
  }: let
    inherit (flake-utils.lib) simpleFlake defaultSystems;

    name = "plfa";

    overlay = final: prev: {
      ${name} = {
        defaultPackage = final.callPackage ./plfa.nix {};
      };
    };
  in
    simpleFlake {
      inherit self nixpkgs name overlay;
      systems = defaultSystems;

      shell = {pkgs}:
        pkgs.mkShell {
          inputsFrom = [pkgs.${name}.defaultPackage];
        };
    };
}

