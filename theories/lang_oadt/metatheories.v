From oadt.lang_oadt Require Import
     base syntax semantics typing indistinguishable infrastructure
     values preservation progress obliviousness.
Import syntax.notations semantics.notations typing.notations
       equivalence.notations indistinguishable.notations.

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
  nf (step Σ) e /\ ¬val e.

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

(** [e1] and [e2] are trace-indistinguishable if the traces they produce are
pointwise indistinguishable, i.e. they always take the same number of steps, and
each expressions they step to remain indistinguishable. This ensures that an
attacker can not tell [e1] and [e2] apart, even given the entire execution
traces of them. *)
Definition trace_indistinguishable Σ e1 e2 : Prop :=
  forall n e1',
    Σ ⊨ e1 -->{n} e1' ->
    (exists e2', Σ ⊨ e2 -->{n} e2') /\
    (forall e2', Σ ⊨ e2 -->{n} e2' -> e1' ≈ e2').

(** Essentially a noninterference theorem. Indistinguishable well-typed
expressions produce indistinguishable traces. *)
Theorem obliviousness Σ e1 e2 τ1 τ2 :
  Σ; e1 ▷ τ1 ->
  Σ; e2 ▷ τ2 ->
  e1 ≈ e2 ->
  trace_indistinguishable Σ e1 e2.
Proof.
  unfold trace_indistinguishable.
  intros [Hd Ht1] [_ Ht1']. apply gdefs_typing_wf in Hd.
  intros ??? H. generalize dependent e2.
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
Corollary obliviousness_open Σ x τ' e τ s1 s2 :
  gctx_typing Σ ->
  Σ; ({[x:=τ']}) ⊢ e : τ ->
  x ∉ fv τ' ->
  Σ; ∅ ⊢ s1 : τ' ->
  Σ; ∅ ⊢ s2 : τ' ->
  s1 ≈ s2 ->
  trace_indistinguishable Σ <{ {x↦s1}e }> <{ {x↦s2}e }>.
Proof.
  intros.
  eapply obliviousness; eauto.

  1-2: split; eauto;
  eapply subst_preservation;
  eauto using gdefs_typing_wf;
  unfold tctx_fv; rewrite map_fold_empty; fast_set_solver!!.

  apply indistinguishable_subst; try reflexivity; eauto.
Qed.

(** This is another corollary. Two expressions that only differ in an oblivious
value in it produce indistinguishable traces, meaning that an attacker can not
infer the oblivious value by analyzing the execution trace. *)
Corollary obliviousness_open_obliv_val Σ x τ' e τ v1 v2 :
  gctx_typing Σ ->
  Σ; ({[x:=τ']}) ⊢ e : τ ->
  x ∉ fv τ' ->
  Σ; ∅ ⊢ v1 : τ' ->
  Σ; ∅ ⊢ v2 : τ' ->
  Σ; ∅ ⊢ τ' :: *@O ->
  val v1 -> val v2 ->
  trace_indistinguishable Σ <{ {x↦v1}e }> <{ {x↦v2}e }>.
Proof.
  eauto using obliviousness_open, indistinguishable_obliv_val, gdefs_typing_wf.
Qed.
