# Oblivious Algebraic Data Type

## Requirements

- [coq](https://coq.inria.fr) (8.12.2)
- [coq-stdpp](https://gitlab.mpi-sws.org/iris/stdpp) (1.5.0)
- [coq-hammer-tactics](https://coqhammer.github.io) (development version)

All dependencies can be easily installed via opam, except for
coq-hammer-tactics, which needs manual installation via the following commands.

``` sh
git clone -b coq8.12 git@github.com:lukaszcz/coqhammer.git
cd coqhammer
make
make install
```
