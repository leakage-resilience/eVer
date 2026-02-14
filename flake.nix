{
  description = "A Nix-based development environment for eVer";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfree = true;
        };

        ocamlPkgs = pkgs.ocamlPackages;

        mySage = pkgs.sage.override {
          extraPythonPackages = ps: with ps; [
            jupyterlab
            nbconvert
            pytest
            diskcache
            tqdm
            pandas
            snakeviz
            networkx
          ];
        };
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            # Sage + Python tooling
            mySage
            # pkgs.python3 - this is not working since sage and python would conflict

            # OCaml toolchain
            pkgs.ocaml
            pkgs.opam
            pkgs.dune_3

            # Jasmin
            pkgs.jasmin-compiler

            # OCaml libraries / tools
            ocamlPkgs.findlib
            ocamlPkgs.ocamlbuild
            ocamlPkgs.menhir
            ocamlPkgs.zarith
            ocamlPkgs.merlin
            ocamlPkgs.ocamlgraph
            ocamlPkgs.batteries
            ocamlPkgs.ppx_deriving
            ocamlPkgs.ppx_import
            ocamlPkgs.re
          ];
        };
      }
    );
}
