From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.
From oadt Require Import lang_oadt.infrastructure.
From oadt Require Import lang_oadt.values.
From oadt Require Import lang_oadt.progress.
From oadt Require Import lang_oadt.preservation.
From oadt Require Import lang_oadt.obliviousness.

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

(** * Soundness *)

Definition stuck (Σ : gctx) (e : expr) : Prop :=
  nf (@step Σ) e /\ ¬val e.

(** If a program is well-typed, it will never get stuck. *)
Corollary soundness e Σ τ e' :
  Σ; e ▷ τ ->
  Σ ⊨ e -->* e' ->
  ¬(stuck Σ e').
Proof.
  intros [Hd Ht]. apply gdefs_typing_wf in Hd.
  induction 1;
    qauto use: progress, preservation unfold: stuck, nf.
Qed.

(** * Obliviousness *)

(** This corresponds to Theorem 3.7 (Obliviousness) in the paper. *)
(** Essentially a noninterference theorem. Indistinguishable well-typed
expressions always take the same number of steps, and each expressions they step
to remain indistinguishable. This ensures that an attacker can not tell [e1] and
[e2] apart, even given the entire execution traces of them. *)
Theorem obliviousness Σ e1 e1' e2 τ1 τ2 n :
  Σ; e1 ▷ τ1 ->
  Σ; e2 ▷ τ2 ->
  Σ ⊨ e1 -->{n} e1' ->
  e1 ≈ e2 ->
  (exists e2', Σ ⊨ e2 -->{n} e2') /\
  (forall e2', Σ ⊨ e2 -->{n} e2' -> e1' ≈ e2').
Proof.
  intros [Hd Ht1] [_ Ht1']. apply gdefs_typing_wf in Hd.
  intros H. revert dependent e2.
  induction H; intros.
  - hauto ctrs: nsteps inv: nsteps.
  - edestruct obliviousness_step as [[??] ?]; eauto.
    split; intros.
    + hauto ctrs: nsteps use: preservation.
    + select (_ ⊨ _ -->{_} _) (fun H => sinvert H).
      qauto use: preservation.
Qed.

(** This is a corollary for open programs. An open (partial) program can be
instantiated with indistinguishable expressions, and the resulting programs
produce indistinguishable traces. As a consequence, a type-checked function does
not leak when it is applied to concrete arguments. *)
Corollary obliviousness_open Σ x τ' e e1 τ s1 s2 n :
  gctx_typing Σ ->
  Σ; ({[x:=τ']}) ⊢ e : τ ->
  x ∉ fv τ' ->
  Σ; ∅ ⊢ s1 : τ' ->
  Σ; ∅ ⊢ s2 : τ' ->
  s1 ≈ s2 ->
  Σ ⊨ <{ {x↦s1}e }> -->{n} e1 ->
  (exists e2, Σ ⊨ <{ {x↦s2}e }> -->{n} e2) /\
  (forall e2, Σ ⊨ <{ {x↦s2}e }> -->{n} e2 -> e1 ≈ e2).
Proof.
  intros.
  eapply obliviousness; eauto.

  1-2: split; eauto;
  eapply subst_preservation;
  eauto using gdefs_typing_wf; fast_set_solver!!.

  apply indistinguishable_subst; try reflexivity; eauto.
Qed.

(** This corresponds to Corollary 3.11 in the paper. *)
(** Two expressions that only differ in an oblivious value in it produce
indistinguishable traces, meaning that an attacker can not infer the oblivious
value by analyzing the execution trace. *)
Corollary obliviousness_open_obliv_val Σ x τ' e e1 τ v1 v2 n :
  gctx_typing Σ ->
  Σ; ({[x:=τ']}) ⊢ e : τ ->
  x ∉ fv τ' ->
  Σ; ∅ ⊢ v1 : τ' ->
  Σ; ∅ ⊢ v2 : τ' ->
  Σ; ∅ ⊢ τ' :: *@O ->
  val v1 -> val v2 ->
  Σ ⊨ <{ {x↦v1}e }> -->{n} e1 ->
  (exists e2, Σ ⊨ <{ {x↦v2}e }> -->{n} e2) /\
  (forall e2, Σ ⊨ <{ {x↦v2}e }> -->{n} e2 -> e1 ≈ e2).
Proof.
  eauto using obliviousness_open, indistinguishable_obliv_val, gdefs_typing_wf.
Qed.

Print Assumptions soundness.
Print Assumptions obliviousness.
