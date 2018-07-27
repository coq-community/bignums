{ pkgs ? import <nixpkgs> {},
  coq ? import (fetchTarball "https://github.com/coq/coq/tarball/v8.8") {} }:

pkgs.stdenv.mkDerivation rec {
  name = "bignums";
  src = ./.;
  buildInputs = with coq.ocamlPackages; [ coq ocaml findlib camlp5_strict ];
  installFlags = "COQLIB=$(out)/lib/coq/";
}
