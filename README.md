<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Bignums

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[docker-action-shield]: https://github.com/coq-community/bignums/workflows/Docker%20CI/badge.svg?branch=v8.15
[docker-action-link]: https://github.com/coq-community/bignums/actions?query=workflow:"Docker%20CI"

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



This Coq library provides BigN, BigZ, and BigQ that used to
be part of the standard library.


## Meta

- Author(s):
  - Laurent Théry
  - Benjamin Grégoire
  - Arnaud Spiwack
  - Evgeny Makarov
  - Pierre Letouzey
- Coq-community maintainer(s):
  - Pierre Roux ([**@proux01**](https://github.com/proux01))
  - Érik Martin-Dorel ([**@erikmd**](https://github.com/erikmd))
- License: [GNU Lesser General Public License v2.1](LICENSE)
- Compatible Coq versions: The v8.15 branch tracks version 8.15 of Coq, see releases for compatibility with released versions of Coq
- Compatible OCaml versions: all versions supported by Coq
- Additional dependencies: none
- Coq namespace: `Bignums`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of Bignums
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-bignums
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/bignums.git
cd bignums
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



