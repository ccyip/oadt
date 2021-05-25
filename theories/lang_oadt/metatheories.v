From oadt Require Import prelude.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.obliviousness.

(** * Metatheories *)
(** The high level metatheories. *)

Module metatheories (atom_sig : AtomSig).

Module Export obliviousness := obliviousness atom_sig.
Import syntax.notations.
Import semantics.notations.
Import typing.notations.

Implicit Types (x X y Y : atom) (L : aset).
Implicit Types (b : bool).


(** ** Soundness *)

Definition stuck (Σ : gctx) (e : expr) : Prop :=
  nf (@step Σ) e /\ ¬val e.

Corollary soundness Ds e Σ τ e' :
  program_typing Ds e Σ τ ->
  Σ ⊨ e -->* e' ->
  ¬(stuck Σ e').
Proof.
  intros [Hd Ht]. apply gdefs_typing_wf in Hd.
  induction 1;
    qauto use: progress, preservation unfold: stuck, nf.
Qed.

(** ** Obliviousness *)
(* TODO: the obliviousness corollary for trace. *)

End metatheories.
