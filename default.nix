{ pkgs ? import <nixpkgs> {}
, coq ? import (fetchTarball "https://github.com/coq/coq/tarball/master") {}
, shell ? false }:

with coq.coqPackages;

pkgs.stdenv.mkDerivation {

  name = "bignums";

  buildInputs = with coq.ocamlPackages; [ ocaml findlib ]
    ++ pkgs.lib.optionals shell [ merlin ocp-indent ocp-index ];

  propagatedBuildInputs = [
    coq
  ];

  src = if shell then null else ./.;

  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";
}
