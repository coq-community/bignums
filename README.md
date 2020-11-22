# Bignums

[![CI](https://github.com/coq/bignums/workflows/CI/badge.svg?branch=master)](https://github.com/coq/bignums/actions?query=workflow%3ACI)

Provides BigN, BigZ, BigQ that used to be part of Coq standard library

## Meta

- Author(s):
  - Laurent Théry
  - Benjamin Grégoire
  - Arnaud Spiwack
  - Evgeny Makarov
  - Pierre Letouzey
- License: [GNU Lesser General Public License v2.1](LICENSE)
- Compatible Coq versions: master (use the corresponding branch or release for other Coq versions)
- Compatible OCaml versions: all versions supported by Coq
- Additional Coq dependencies: none

## Building and installation instructions

The easiest way to install the latest released version of Bignums
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-bignums
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq/bignums
cd bignums
make   # or make -j <number-of-cores-on-your-machine>
make install
```

After installation, the included modules are available under
the `Bignums` namespace.
