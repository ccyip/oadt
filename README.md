# Oblivious Algebraic Data Types (adapted to Taypsi)

This is the Coq formalization of the core calculus of Taypsi, an extension of
oblivious algebraic data types with Ψ-types. For simplicity, this calculus
differs slightly from the one presented in the Taypsi paper. First, similar to
Ye and Delaware 2022 (POPL), the mechanization includes `fold` and `unfold`
operators for recursive ADTs, instead of the ML-style ADTs. The equivalence
between these two styles is well-known. Second, similar to Ye and Delaware 2023
(PLDI), the mechanization distinguishes between oblivious product (whose
components must be oblivious) and normal product (whose components can be any
types), while the product type in the Taypsi paper can connect any types
(including oblivious types) for presentation purposes. The style in the Taypsi
paper is closer to the mechanization of Ye and Delaware 2022 (POPL).

## Requirements

- [coq](https://coq.inria.fr) (8.16)
- [coq-stdpp](https://gitlab.mpi-sws.org/iris/stdpp) (1.9)
- [coq-smpl](https://github.com/uds-psl/smpl) (>= 8.16)
- [coq-hammer-tactics](https://coqhammer.github.io) (>= 1.3.2)
- [coq-idt](https://github.com/ccyip/coq-idt) (>= 1.1)

See [`coq-taypsi.opam`](./coq-taypsi.opam) for more details.

The easiest way to install the dependencies and build the project is via
[OPAM](https://opam.ocaml.org/doc/Install.html).

``` sh
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
cd path/to/taypsi-theories
opam install . --deps-only
```

## Building

Run `make` in the top-level directory.

## References

- Qianchuan Ye and Benjamin Delaware. 2022. Oblivious Algebraic Data Types.
  Proc. ACM Program. Lang. 6, POPL, Article 51 (January 2022), 29 pages.
  https://doi.org/10.1145/3498713
- Qianchuan Ye and Benjamin Delaware. 2021. Oblivious Algebraic Data Types:
  POPL22 Artifact. Zenodo. https://doi.org/10.5281/zenodo.5652106
- Qianchuan Ye and Benjamin Delaware. 2023. Taype: A Policy-Agnostic Language
  for Oblivious Computation. Proc. ACM Program. Lang. 7, PLDI, Article 147 (June
  2023), 25 pages. https://doi.org/10.1145/3591261
- Qianchuan Ye and Benjamin Delaware. 2023. Taype: A Policy-Agnostic Language
  for Oblivious Computation: PLDI23 Artifact. Zenodo.
  https://doi.org/10.5281/zenodo.7806981