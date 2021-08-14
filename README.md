# Oblivious Algebraic Data Type

[![Build status][action-badge]][action-link]
[![coqdoc][doc-badge]][doc-link]

[action-badge]: https://github.com/ccyip/oadt/actions/workflows/build.yml/badge.svg?branch=tape
[action-link]: https://github.com/ccyip/oadt/actions

[doc-badge]: https://img.shields.io/badge/docs-coqdoc-blue.svg
[doc-link]: https://ccyip.github.io/oadt

This is the Coq formalization of the core calculus for oblivious algebraic data
types.

[The coqdoc documentation](https://ccyip.github.io/oadt)

## Requirements

- [coq](https://coq.inria.fr) (8.12-8.13)
- [coq-stdpp](https://gitlab.mpi-sws.org/iris/stdpp) (>= 1.5.0)
- [coq-smpl](https://github.com/uds-psl/smpl) (>= 8.12.0.1)
- [coq-hammer-tactics](https://coqhammer.github.io) (>= 1.3.1+8.12)

See [`coq-oadt.opam`](./coq-oadt.opam) for more details.

The easiest way to install the dependencies and build the project is via
[OPAM](https://opam.ocaml.org/doc/Install.html).

``` sh
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-oadt --deps-only
```

## Building

Run `make` in the top-level directory.
