# Oblivious Algebraic Data Type (adapted to Taype)

This is the Coq formalization of the core calculus of Taype, a variant of
oblivious algebraic data types. It adds serveral features: oblivious product,
label promotion, explicit and uniform label checking.

## Requirements

- [coq](https://coq.inria.fr) (8.16)
- [coq-stdpp](https://gitlab.mpi-sws.org/iris/stdpp) (>= 1.8)
- [coq-smpl](https://github.com/uds-psl/smpl) (>= 8.16)
- [coq-hammer-tactics](https://coqhammer.github.io) (>= 1.3.2)
- [coq-idt](https://github.com/ccyip/coq-idt) (>= 1.1)

See [`coq-oadt.opam`](./coq-oadt.opam) for more details.

The easiest way to install the dependencies and build the project is via
[OPAM](https://opam.ocaml.org/doc/Install.html).

``` sh
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
cd path/to/oadt
opam install . --deps-only
```

## Building

Run `make` in the top-level directory.

## References

- Qianchuan Ye and Benjamin Delaware. 2022. Oblivious Algebraic Data Types. Proc. ACM Program. Lang. 6, POPL, Article 51 (January 2022), 29 pages. https://doi.org/10.1145/3498713
- Qianchuan Ye and Benjamin Delaware. 2021. Oblivious Algebraic Data Types: POPL22 Artifact. Zenodo. https://doi.org/10.5281/zenodo.5652106
