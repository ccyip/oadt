# POPL22 artifact of Oblivious Algebraic Data Types

## Introduction

This artifact holds the Coq formalization of Oblivious Algebraic Data Types, a
language for writing secure computation with recursive data types whose
structures are protected. More specifically, it formalizes the two core calculi
from the paper, λOADT and λOADT✚, and proves their soundness and obliviousness.

The source code can be found on [our Github
repository](https://github.com/ccyip/oadt). We use different branches to manage
the two calucli: λOADT is on the branch
[pure](https://github.com/ccyip/oadt/tree/pure), and λOADT✚ is on the branch
[tape](https://github.com/ccyip/oadt/tree/tape). The generated CoqDoc can be
found [here](https://ccyip.github.io/oadt/).

The final versions of the formalization and a virtual machine image are also
available on [Zenodo](https://zenodo.org/record/5652106):
- λOADT: [oadt-pure-popl22.zip](https://zenodo.org/record/5652106/files/oadt-pure-popl22.zip?download=1).
  This is a snapshot of tag [pure-popl22](https://github.com/ccyip/oadt/releases/tag/pure-popl22)
  (commit [b34546f](https://github.com/ccyip/oadt/commit/b34546f2f4a1930055e8f11175909519a20ece30)).
- λOADT✚: [oadt-tape-popl22.zip](https://zenodo.org/record/5652106/files/oadt-tape-popl22.zip?download=1).
  This is a snapshot of tag [tape-popl22](https://github.com/ccyip/oadt/releases/tag/tape-popl22)
  (commit [32d8fc4](https://github.com/ccyip/oadt/commit/32d8fc4927f0f5781e3cf5b5e87748c9a587815d)).
- The virtual machine image: [oadt-popl22.ova](https://zenodo.org/record/5652106/files/oadt-popl22.ova?download=1).
  See instructions below.

The next section (Review Instructions) contains instructions on how to review
our Coq development and check the mechanized proofs.

Section (Build Instructions) shows how to install the dependencies and build the
project.

Section (Dependencies) explains the libraries and methodologies this artifact
depends on and how we use them.

Section (File Structures) outlines how we organize the formalization by
explaining the purpose of each file.

Section (Paper-to-artifact Correspondence) connects the definitions and theorems
in the paper to the formalization in the artifact.

Section (Differences Between Paper and Artifact) discusses the minor
discrepancies between our Coq formalization and the paper due to presentation
reasons.

Section (Review the Build Logs) explains how to review the compilation output.

## Review Instructions

### Review online
This artifact can be reviewed fully online.
- The source code for λOADT can be reviewed on the [pure
  branch](https://github.com/ccyip/oadt/tree/pure) of our repository, and λOADT✚
  on the [tape branch](https://github.com/ccyip/oadt/tree/tape).
- We recommend reading the generated Coq documentation instead. This way it is
  easier to navigate between different definitions and read our comments. The
  document of λOADT is [here](https://ccyip.github.io/oadt/pure/toc.html), and
  that of λOADT✚ is [here](https://ccyip.github.io/oadt/tape/toc.html).
- We use Github Actions to automatically compile the project against different
  Coq versions. Therefore, one can easily confirm that Coq indeed accepts our
  proofs by heading to the [action page](https://github.com/ccyip/oadt/actions)
  of the right branch, selecting the latest "workflow", and checking the build
  logs. More specifically, the action page of λOADT can be found
  [here](https://github.com/ccyip/oadt/actions?query=branch%3Apure), and that of
  λOADT✚ can be found
  [here](https://github.com/ccyip/oadt/actions?query=branch%3Atape). We explain
  how to review these build logs in section (Review the Build Logs).
- Github will delete the build logs after a period of time. In that case, you can
  review with the virtual machine or by building the project manually.

### Virtual Machine
We also provide a virtual machine (based on Debian 11 with Gnome desktop),
available on [Zenodo](https://zenodo.org/record/5652106), so one can inspect our
proofs interactively, with environment already set up. The virtual machine was
tested in Oracle VirtualBox (6.1). To get started,
1. Download the `oadt-popl22.ova` file from [Zenodo](https://zenodo.org/record/5652106).
2. Open VirtualBox and select menu `File` then `Import Appliance`.
3. Choose the downloaded `ova` file to import.
4. Adjust settings such as CPU cores and RAM. Note that compiling our Coq code
   requires more than 1.2 GB of RAM, not including RAM used by system and other
   applications, so we suggest allocate 4 GB of RAM.
5. Import it and boot up the system.

You may need the login information to run `sudo` command:
- User name: oadt
- Password: oadt

After launching the terminal (from the dock to the left, accessed by clicking
the top-left corner or pressing the `Super`/`Win`/`Cmd` key), you can experiment
with our Coq development interactively:
```
# Check out λOADT
cd ~/oadt-pure

# Or check out λOADT✚
cd ~/oadt-tape

# Use CoqIDE
coqide theories/lang_oadt/metatheories.v

# Use Emacs
emacs theories/lang_oadt/metatheories.v

# Use VSCode
code theories/lang_oadt/metatheories.v

```

Emacs and VSCode are also accessible from the dock. The code is pre-compiled. To
build the project again, run `make clean` first.

A few tips:
- We recommend taking a snapshot after booting up the virtual machine. If
  anything happens, one can easily revert back to the inital state.
- You may want to set the screen resolution first. Click the top-right corner
  and select `Settings`. Resolution options can be found under the `Display`
  tab.


### Build manually
Alternatively, you can build our project on your own machine following the next
section.

## Build Instructions

[Opam](https://opam.ocaml.org/) is needed to compile our Coq code. See opam's
[documentation](https://opam.ocaml.org/doc/Install.html) for install and setup
instructions.

Once opam is set up, run the following commands:
```sh
# Create a fresh opam environment
opam switch create oadt-popl22 4.11.1+flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam update

# Assume we are building it at home directory
cd ~

# Build λOADT
git clone -b pure https://github.com/ccyip/oadt.git oadt-pure
cd oadt-pure
opam install . --deps-only
make

cd ~

# Build λOADT✚
git clone -b tape https://github.com/ccyip/oadt.git oadt-tape
cd oadt-tape
opam install . --deps-only
make DEMO=1
```

If Ocaml 4.11.1 is not available on your system (e.g. certain macs), you may install
4.12.0 instead.
```sh
opam switch create oadt-popl22 --package=ocaml-variants.4.12.0+options,ocaml-option-flambda
```

## Dependencies

Our formalization is tested against Coq 8.12 to Coq 8.13. We also rely on the
following wonderful libraries:
- [coq-stdpp](https://gitlab.mpi-sws.org/iris/stdpp) (1.5.0): we use many common
definitions, type classes, lemmas and tactics from the stdpp library to avoid
reinventing the wheels, such as finite set and finite map.
- [coq-smpl](https://github.com/uds-psl/smpl) (8.12.0.1 or 8.13): we use smpl
library to chain our ad-hoc saturation-style forward-reasoning tactics for
discharging obligations about free variables.
- [coq-hammer-tactics](https://coqhammer.github.io) (1.3.2+8.12 or 1.3.2+8.13):
we use many tactics from the hammer library to ease the automation in our proof
scripts.

Our formalization takes inspiration and ideas from the following work, though
does not directly depend on them:
- [Software Foundations](https://softwarefoundations.cis.upenn.edu/): a lot of
  our formalization is inspired by the style used in Software Foundations.
- [The Locally Nameless
  Representation](https://link.springer.com/article/10.1007%2Fs10817-011-9225-2):
  we use locally nameless representation for variable bindings. Some related
  proofs and tactics are inspired by
  [formalmetacoq](https://github.com/charguer/formalmetacoq/) by the same
  author.
- [Iron Lambda](https://github.com/discus-lang/iron): the style we use to define
  evaluation context is inspired by Iron Lambda.

## File Structures

We list the files in the `theories` directory and explain the purpose of each
file.

The following files appear in λOADT✚ and λOADT.
- base.v: common definitions, lemmas and notations.
- tactics.v: common tactics.
- ln.v: definitions and tactics about locally nameless representation.
- semilattice.v: formalize the semi-lattice structure used for kinding.
- prelude.v: include all of above.
- lang_oadt/base.v: common setup for the formalization.
- lang_oadt/syntax.v: definitions and notations of the syntax, including other
  definitions such as indistinguishability.
- lang_oadt/semantics.v: definitions and notations of the dynamic semantics.
- lang_oadt/typing.v: definitions and notations of typing, kinding and parallel
  reduction.
- lang_oadt/infrastructure.v: common tactics and lemmas, and various definitions
  and lemmas about locally nameless representation and free variables.
- lang_oadt/equivalence.v: properties of parallel reduction and term
  equivalence, such as notably the confluence theorem for parallel reduction.
- lang_oadt/admissible.v: renaming lemmas and a few admissible typing and
  kinding rules.
- lang_oadt/inversion.v: inversion lemmas for typing and kinding.
- lang_oadt/values.v: properties of various value definitions.
- lang_oadt/preservation.v: proofs of the preservation theorem.
- lang_oadt/progress.v: proofs of the progress theorem.
- lang_oadt/obliviousness.v: proofs of the obliviousness theorem.
- lang_oadt/metatheories.v: corollaries of soundness and obliviousness.

These files only appear in λOADT✚.
- lang_oadt/dec.v: a few decision procedures and a naive implementation of the
  step relation. It is used for the demos.
- demo/demo_prelude.v: auxiliary definitions, lemmas and tactics for the demos.
- demo/int.v: extending the core calculus with primitive bounded integers. We
  did not prove the metatheories about this extension. Only the lemmas needed for the demos
  are proved.
- demo/int_prelude.v: the same as `demo_prelude.v`, but for the integer
  extensions.
- demo/demo1.v: encodes the running example in the paper: oblivious tree with
  the maximum depth and the upper bound of its spine as public views. The lookup
  function and the insert function are encoded.
- demo/demo2.v: encodes an oblivious list.
- demo/demo3.v: encodes an oblivious tree with the number of its vertices as the
  public view.
- demo/demo4.v: encodes a higher-order function for oblivious trees.

## Paper-to-artifact Correspondence

- Definitions and theorems of λOADT in Section 3 (λOADT, formally): (in the pure branch)

| Definition/Theorems | Paper | File | Name (link to CoqDoc) |
|---------------------|-------|------|-----------------------|
| Expression syntax | Fig. 9 | [theories/lang_oadt/syntax.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/syntax.v) | [expr](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.syntax.html#expr) |
| Global definitions | Fig. 9 | [theories/lang_oadt/syntax.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/syntax.v) | [gdef](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.syntax.html#gdef) |
| Oblivious type values | Fig. 9 | [theories/lang_oadt/syntax.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/syntax.v) | [otval](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.syntax.html#otval) |
| Oblivious values | Fig. 9 | [theories/lang_oadt/syntax.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/syntax.v) | [oval](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.syntax.html#oval) |
| Values | Fig. 9 | [theories/lang_oadt/syntax.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/syntax.v) | [val](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.syntax.html#val) |
| Small-step relation | Fig. 10 | [theories/lang_oadt/semantics.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/semantics.v) | [step](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.semantics.html#step) |
| Evaluation context | Fig. 10 | [theories/lang_oadt/semantics.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/semantics.v) | [ectx](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.semantics.html#ectx) |
| Auxiliary oblivious value typing relation | Fig. 10 | [theories/lang_oadt/semantics.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/semantics.v) | [ovalty](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.semantics.html#ovalty) |
| Kinds | At the begining of Section 3.3 | [theories/lang_oadt/typing.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/typing.v) | [kind](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.typing.html#kind) |
| Kinding rules | Fig. 12 | [theories/lang_oadt/typing.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/typing.v) | [kinding](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.typing.html#kinding) |
| Typing rules | Fig. 13 | [theories/lang_oadt/typing.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/typing.v) | [typing](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.typing.html#typing) |
| Parallel reduction rules | Fig. 14 | [theories/lang_oadt/typing.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/typing.v) | [pared](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.typing.html#pared) |
| Global definition typing | Fig. 15 | [theories/lang_oadt/typing.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/typing.v) | [gdef_typing](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.typing.html#gdef_typing) |
| Theorem 3.1 (Progress) | Section 3.4 | [theories/lang_oadt/progress.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/progress.v) | [progress](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.progress.html#progress), [kinding_progress](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.progress.html#kinding_progress) |
| Theorem 3.2 (Preservation) | Section 3.4 | [theories/lang_oadt/preservation.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/preservation.v) | [preservation](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.preservation.html#preservation), [kinding_presevation](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.preservation.html#kinding_preservation) |
| Lemma 3.3 (Preservation for parallel reduction) | Section 3.4 | [theories/lang_oadt/preservation.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/preservation.v) | [pared_preservation](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.preservation.html#pared_preservation) |
| Lemma 3.4 (Regularity) | Section 3.4 | [theories/lang_oadt/preservation.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/preservation.v) | [regularity](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.preservation.html#regularity) |
| Lemma 3.5 (Confluence of parallel reduction) | Section 3.4 | [theories/lang_oadt/equivalence.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/equivalence.v) | [pared_confluent](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.equivalence.html#pared_confluent) |
| Definition 3.6 (indistinguishability) | Section 3.4 | [theories/lang_oadt/syntax.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/syntax.v) | [indistinguishable](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.syntax.html#indistinguishable) |
| Theorem 3.7 (Obliviousness) | Section 3.4 | [theories/lang_oadt/metatheories.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/metatheories.v) | [obliviousness](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.metatheories.html#obliviousness) |
| Lemma 3.8 | Section 3.4 | [theories/lang_oadt/obliviousness.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/obliviousness.v) | [indistinguishable_obliv_val](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.obliviousness.html#indistinguishable_obliv_val) |
| Lemma 3.9 | Section 3.4 | [theories/lang_oadt/obliviousness.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/obliviousness.v) | [indistinguishable_val_obliv_type_equiv](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.obliviousness.html#indistinguishable_val_obliv_type_equiv) |
| Lemma 3.10 | Section 3.4 | [theories/lang_oadt/obliviousness.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/obliviousness.v) | [pared_equiv_obliv_preservation](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.obliviousness.html#pared_equiv_obliv_preservation) |
| Corollary 3.11 | Section 3.4 | [theories/lang_oadt/metatheories.v](https://github.com/ccyip/oadt/blob/pure/theories/lang_oadt/metatheories.v) | [obliviousness_open_obliv_val](https://ccyip.github.io/oadt/pure/oadt.lang_oadt.metatheories.html#obliviousness_open_obliv_val) |

- Definitions and theorems of λOADT✚ in Section 4 (λOADT✚, formally): (in the tape branch)

| Definition/Theorems | Paper | File | Name (link to CoqDoc) |
|---------------------|-------|------|-----------------------|
| Expression syntax | Fig. 16 | [theories/lang_oadt/syntax.v](https://github.com/ccyip/oadt/blob/tape/theories/lang_oadt/syntax.v) | [expr](https://ccyip.github.io/oadt/tape/oadt.lang_oadt.syntax.html#expr) |
| Global definitions | Fig. 16 | [theories/lang_oadt/syntax.v](https://github.com/ccyip/oadt/blob/tape/theories/lang_oadt/syntax.v) | [gdef](https://ccyip.github.io/oadt/tape/oadt.lang_oadt.syntax.html#gdef) |
| Leakage label | Fig. 16 | [theories/lang_oadt/syntax.v](https://github.com/ccyip/oadt/blob/tape/theories/lang_oadt/syntax.v) | [llabel](https://ccyip.github.io/oadt/tape/oadt.lang_oadt.syntax.html#llabel) |
| Small-step relation | Fig. 17 | [theories/lang_oadt/semantics.v](https://github.com/ccyip/oadt/blob/tape/theories/lang_oadt/semantics.v) | [step](https://ccyip.github.io/oadt/tape/oadt.lang_oadt.semantics.html#step) |
| Weak values | Fig. 17 | [theories/lang_oadt/semantics.v](https://github.com/ccyip/oadt/blob/tape/theories/lang_oadt/semantics.v) | [wval](https://ccyip.github.io/oadt/tape/oadt.lang_oadt.semantics.html#wval) |
| Evaluation context | Fig. 17 | [theories/lang_oadt/semantics.v](https://github.com/ccyip/oadt/blob/tape/theories/lang_oadt/semantics.v) | [ectx](https://ccyip.github.io/oadt/tape/oadt.lang_oadt.semantics.html#ectx) |
| Leaky context | Fig. 17 | [theories/lang_oadt/semantics.v](https://github.com/ccyip/oadt/blob/tape/theories/lang_oadt/semantics.v) | [lectx](https://ccyip.github.io/oadt/tape/oadt.lang_oadt.semantics.html#lectx) |
| Typing rules | Fig. 18 | [theories/lang_oadt/typing.v](https://github.com/ccyip/oadt/blob/tape/theories/lang_oadt/typing.v) | [typing](https://ccyip.github.io/oadt/tape/oadt.lang_oadt.typing.html#typing) |
| Kinding rules | Fig. 19 | [theories/lang_oadt/typing.v](https://github.com/ccyip/oadt/blob/tape/theories/lang_oadt/typing.v) | [kinding](https://ccyip.github.io/oadt/tape/oadt.lang_oadt.typing.html#kinding) |
| Parallel reduction rules | Fig. 20 | [theories/lang_oadt/typing.v](https://github.com/ccyip/oadt/blob/tape/theories/lang_oadt/typing.v) | [pared](https://ccyip.github.io/oadt/tape/oadt.lang_oadt.typing.html#pared) |
| Theorem 4.1 (Progress) | Section 4.4 | [theories/lang_oadt/progress.v](https://github.com/ccyip/oadt/blob/tape/theories/lang_oadt/progress.v) | [progress](https://ccyip.github.io/oadt/tape/oadt.lang_oadt.progress.html#progress), [kinding_progress](https://ccyip.github.io/oadt/tape/oadt.lang_oadt.progress.html#kinding_progress) |
| Lemma 4.2 | Section 4.4 | [theories/lang_oadt/progress.v](https://github.com/ccyip/oadt/blob/tape/theories/lang_oadt/progress.v) | [progress_weak](https://ccyip.github.io/oadt/tape/oadt.lang_oadt.progress.html#progress_weak) |
| Updated version of Lemma 3.10 | Section 4.4 | [theories/lang_oadt/progress.v](https://github.com/ccyip/oadt/blob/tape/theories/lang_oadt/progress.v) | [pared_equiv_obliv_preservation](https://ccyip.github.io/oadt/tape/oadt.lang_oadt.progress.html#pared_equiv_obliv_preservation) |
| Theorem 4.3 (Preservation) | Section 4.4 | [theories/lang_oadt/preservation.v](https://github.com/ccyip/oadt/blob/tape/theories/lang_oadt/preservation.v) | [preservation](https://ccyip.github.io/oadt/tape/oadt.lang_oadt.preservation.html#preservation), [kinding_preservation](https://ccyip.github.io/oadt/tape/oadt.lang_oadt.preservation.html#kinding_preservation) |
| Theorem 4.4 (Obliviousness) | Section 4.4 | [theories/lang_oadt/metatheories.v](https://github.com/ccyip/oadt/blob/tape/theories/lang_oadt/metatheories.v) | [obliviousness](https://ccyip.github.io/oadt/tape/oadt.lang_oadt.metatheories.html#obliviousness) |

- Extending λOADT✚ with primitive integers, in Section 4.5 (Extending λOADT✚)

| Definition | Paper | File | Name (link to CoqDoc) |
|------------|-------|------|-----------------------|
| Expression syntax | Fig. 21 | [theories/demo/int.v](https://github.com/ccyip/oadt/blob/tape/theories/demo/int.v) | [expr](https://ccyip.github.io/oadt/tape/oadt.demo.int.html#expr) |
| Typing rules | Fig. 21 | [theories/demo/int.v](https://github.com/ccyip/oadt/blob/tape/theories/demo/int.v) | [typing](https://ccyip.github.io/oadt/tape/oadt.demo.int.html#typing) |
| Small-step relation | Fig. 21 | [theories/demo/int.v](https://github.com/ccyip/oadt/blob/tape/theories/demo/int.v) | [step](https://ccyip.github.io/oadt/tape/oadt.demo.int.html#step) |

- Examples in Section 2 (Overview) and Section 4.6 (λOADT✚ in action)

| Example | Paper | File | CoqDoc |
|---------|-------|------|--------|
| Oblivious trees | Fig. 3 | [theories/demo/demo1.v](https://github.com/ccyip/oadt/blob/tape/theories/demo/demo1.v) | [demo1](https://ccyip.github.io/oadt/tape/oadt.demo.demo1.html) |
| Section, retraction and oblivious lookup function | Fig. 3 | [theories/demo/demo1.v](https://github.com/ccyip/oadt/blob/tape/theories/demo/demo1.v) | [demo1](https://ccyip.github.io/oadt/tape/oadt.demo.demo1.html) |
| Oblivious list with the upper bound of its length | Section 4.6 | [theories/demo/demo2.v](https://github.com/ccyip/oadt/blob/tape/theories/demo/demo2.v) | [demo2](https://ccyip.github.io/oadt/tape/oadt.demo.demo2.html) |
| Oblivious tree with the upper bound of its depth | Section 4.6 | [theories/demo/demo1.v](https://github.com/ccyip/oadt/blob/tape/theories/demo/demo1.v) | [demo1](https://ccyip.github.io/oadt/tape/oadt.demo.demo1.html) |
| Oblivious tree with the upper bound of its spine | Section 4.6 | [theories/demo/demo1.v](https://github.com/ccyip/oadt/blob/tape/theories/demo/demo1.v) | [demo1](https://ccyip.github.io/oadt/tape/oadt.demo.demo1.html) |
| Oblivious tree with the upper bound of the number of its vertices | Section 4.6 | [theories/demo/demo3.v](https://github.com/ccyip/oadt/blob/tape/theories/demo/demo3.v) | [demo3](https://ccyip.github.io/oadt/tape/oadt.demo.demo3.html) |
| Example of the map function | Section 4.6 | [theories/demo/demo4.v](https://github.com/ccyip/oadt/blob/tape/theories/demo/demo4.v) | [demo4](https://ccyip.github.io/oadt/tape/oadt.demo.demo4.html) |

## Differences Between Paper and Artifact

- In the formalization, we use locally nameless representation for variable
  bindings, while in paper we use a more casual named representation. Because of
  that, our examples (in `theories/demo`) are encoded directly using de Bruijn
  indices.
- The expression syntax has free variables (as part of locally nameless
  representation) and also global variables in the formalization, referring to
  the global functions, ADTs and OADTs.
- In the paper, the type component of boxed injection is an oblivious type value
  and the payload component of it is an oblivious values. In contrast, both
  components are simply expressions in the formalization. We then use a
  well-formedness condition to ensure those components are in the correct
  classes.
- In the formalization, we do not define oblivious type values, oblivious
  values, values and weak values as syntax. Instead, they are defined as
  predicates on expressions.
- Let binding is also formalized, but omitted in the paper.
- As mentioned in the paper, some side conditions about kindings are omitted in
  the typing rules for brevity. These omitted side conditions can be found in
  the Coq formalization.

### Notation differences

We try to keep the notations used in Coq as consistent with the paper as
possible, but there are still some differences. The major differences are:
- In the paper, the oblivious constructs are decorated with `\hat`s to distinguish
  from the public counterparts, while in the formalization, they are prefixed by `~`,
  e.g., `~case` for oblivious sum elimination.
- We also use `\hat` to decorate oblivious variables and oblivious values in the paper.
  But in the formalization there is no visual "hint" for that. For example, `v` is used
  for both values and oblivious values. It should be obvious from the context though.
- Other minor differences should be self-explanatory.


## Review the Build Logs

The goal of reviewing the output of compilation is to confirm that Coq accepts
our proofs, and the examples return correct results.

When reviewing online, one can find the compilation output by heading to the
Github Action page (See Section (Review Instructions)). Then
1. Select the latest workflow.
2. Select a job, e.g., build (8.13, 4.11-flambda).
3. Expand the toggle `Run coq-community/docker-coq-action@v1`, and then the
   toggle `Build project`.
   
When reviewing with the provided virtual machine, run `make clean` first and then run
`make` (in the pure branch) or `make DEMO=1` (in the tape branch).


What to look for:
- The compilation succeeds.
- We add `Print Assumptions soundness` (the type safety theorem, a corollary
  from preservation and progress) and `Print Assumptions obliviousness` at the
  end of file `theories/lang_oadt/metatheories.v` to print out any axioms used
  in these proofs. After compiling this file, it should output two `Closed under
  the global context`, showing that our proofs are axiom-free.
- In the tape branch, `demo1.v` and `demo4.v` will print out the results of
  running the sample programs, to test the small-step semantics. Check that
  these results make sense.
