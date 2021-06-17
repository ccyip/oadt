From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.
From oadt Require Import lang_oadt.infrastructure.
From oadt Require Import lang_oadt.properties.
From oadt Require Import lang_oadt.progress.
From oadt Require Import lang_oadt.preservation.
From oadt Require Import lang_oadt.obliviousness.

(** * Metatheories *)
(** The high level metatheories. *)

Import syntax.notations.
Import semantics.notations.
Import typing.notations.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

Lemma gdefs_typing_wf Σ :
  gctx_typing Σ ->
  gctx_wf Σ.
Proof.
  intros.
  eapply map_Forall_impl; eauto.
  simpl.
  intros ??. inversion 1; eauto.
Qed.

(** ** Soundness *)

Definition stuck (Σ : gctx) (e : expr) : Prop :=
  nf (@step Σ) e /\ ¬val e.

(* If a program is well-typed, it will never get stuck. *)
Corollary soundness e Σ τ e' :
  Σ; e ▷ τ ->
  Σ ⊨ e -->* e' ->
  ¬(stuck Σ e').
Proof.
  intros [Hd Ht]. apply gdefs_typing_wf in Hd.
  induction 1;
    qauto use: progress, preservation unfold: stuck, nf.
Qed.

(** ** Obliviousness *)
(* TODO: the obliviousness corollary for trace. *)
