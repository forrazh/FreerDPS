<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Freer Equational Reasoning for Distributed and Probabilistic Systems

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/FreerDPS/FreerDPS/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/FreerDPS/FreerDPS/actions/workflows/docker-action.yml




This work started as a rewrite/extension of [FreeSpec Core](https://github.com/lthms/FreeSpec) using [monae](https://github.com/affeldt-aist/monae) / ssreflect.

This work has been accepted for presentation to [COMPAS26](https://2026.compas-conference.fr/) (no paper available online).

## Meta

- Author(s):
  - Hugo Forraz (initial)
- License: [MIT License](LICENSE)
- Additional dependencies:
  - [MathComp](https://math-comp.github.io)
  - [MathComp Analysis](https://github.com/math-comp/analysis)
  - [MathComp Algebra Tactics](https://github.com/math-comp/algebra-tactics)
  - Monae
- Related publication(s):
  - []()

## Building and installation instructions

The easiest way to install the latest released version of Freer Equational Reasoning for Distributed and Probabilistic Systems
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install coq-FreerDPS
```

To instead build and install manually, you need to make sure that all the
libraries this development depends on are installed.  The easiest way to do that
is still to rely on opam:

``` shell
git clone https://github.com/FreerDPS/FreerDPS.git
cd FreerDPS
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
make   # or make -j <number-of-cores-on-your-machine>
make install
```
