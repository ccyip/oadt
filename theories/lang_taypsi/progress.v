From taypsi.lang_taypsi Require Import
     base syntax semantics typing infrastructure
     equivalence admissible inversion values preservation.
Import syntax.notations semantics.notations typing.notations equivalence.notations.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

#[local]
Coercion EFVar : atom >-> expr.

Section fix_gctx.

Context (Σ : gctx).
Context (Hwf : gctx_wf Σ).

#[local]
Set Default Proof Using "Hwf".

(** * Lemmas about obliviousness *)

Lemma pared_obliv_preservation_inv Γ τ τ' κ :
  τ ⇛ τ' ->
  Γ ⊢ τ :: κ ->
  Γ ⊢ τ' :: *@O ->
  Γ ⊢ τ :: *@O.
Proof.
  induction 1; intros; try case_label;
    kind_inv;
    simpl_cofin?;
    simplify_eq;
    try solve [ kinding_intro; eauto; set_shelve ];
    try easy.

  Unshelve.
  all : fast_set_solver!!.
Qed.

Lemma pared_equiv_obliv_preservation Γ τ τ' κ :
  τ ≡ τ' ->
  Γ ⊢ τ :: *@O ->
  Γ ⊢ τ' :: κ ->
  Γ ⊢ τ' :: *@O.
Proof.
  induction 1; intros;
    eauto using pared_obliv_preservation_inv, pared_kinding_preservation.
Qed.

Lemma val_oval Γ v τ :
  Γ ⊢ v : τ ->
  Γ ⊢ τ :: *@O ->
  val v ->
  oval v.
Proof.
  induction 1; intros; try val_inv; try oval_inv;
    kind_inv; simplify_eq;
      try hauto lq: on ctrs: oval; try easy.

  (* TConv *)
  apply_regularity.
  auto_apply; eauto.
  eapply pared_equiv_obliv_preservation; eauto.
  equiv_naive_solver.
Qed.

(** * Canonical forms *)
Ltac canonical_form_solver :=
  inversion 1; intros; subst; eauto;
  try select (oval _) (fun H => sinvert H);
  type_inv;
  kind_inv;
  try simpl_whnf_equiv;
  simplify_eq;
  eauto 10.

Lemma canonical_form_unit Γ e :
  val e ->
  Γ ⊢ e : 𝟙 ->
  e = <{ () }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_abs Γ e τ2 τ1 :
  val e ->
  Γ ⊢ e : Π:τ2, τ1 ->
  exists e' τ, e = <{ \:τ => e' }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_bool Γ e :
  val e ->
  Γ ⊢ e : 𝔹 ->
  exists b, e = <{ b }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_obool Γ e :
  val e ->
  Γ ⊢ e : ~𝔹 ->
  exists b, e = <{ [b] }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_prod Γ e τ1 τ2 :
  val e ->
  Γ ⊢ e : τ1 * τ2 ->
  exists v1 v2, val v1 /\ val v2 /\ e = <{ (v1, v2) }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_oprod Γ e τ1 τ2 :
  val e ->
  Γ ⊢ e : τ1 ~* τ2 ->
  exists v1 v2, oval v1 /\ oval v2 /\ e = <{ ~(v1, v2) }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_psi Γ e X :
  val e ->
  Γ ⊢ e : Ψ X ->
  exists v1 v2, val v1 /\ oval v2 /\ e = <{ #(v1, v2) }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_sum Γ e τ1 τ2 :
  val e ->
  Γ ⊢ e : τ1 + τ2 ->
  exists b v τ, val v /\ e = <{ inj@b<τ> v }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_osum Γ e τ1 τ2 :
  val e ->
  Γ ⊢ e : τ1 ~+ τ2 ->
  exists b v ω1 ω2, oval v /\ otval ω1 /\ otval ω2 /\
               e = <{ [inj@b<ω1 ~+ ω2> v] }>.
Proof.
  canonical_form_solver.

  (* The cases when [e] is boxed injection. *)
  otval_inv.
  repeat esplit; auto.
Qed.

(** Though it seems we should have a condition of [X] being an (public) ADT, this
condition is not needed since it is implied by the typing judgment. *)
Lemma canonical_form_fold Γ e X :
  val e ->
  Γ ⊢ e : gvar X ->
  exists v X', val v /\ e = <{ fold<X'> v }>.
Proof.
  inversion 1; canonical_form_solver.
Qed.

End fix_gctx.

Ltac apply_canonical_form_lem τ :=
  lazymatch τ with
  | <{ 𝟙 }> => canonical_form_unit
  | <{ 𝔹 }> => canonical_form_bool
  | <{ ~𝔹 }> => canonical_form_obool
  | <{ _ * _ }> => canonical_form_prod
  | <{ _ ~* _ }> => canonical_form_oprod
  | <{ Ψ _ }> => canonical_form_psi
  | <{ _ + _ }> => canonical_form_sum
  | <{ _ ~+ _ }> => canonical_form_osum
  | <{ Π:_, _ }> => canonical_form_abs
  | <{ gvar _ }> => canonical_form_fold
  end.

Ltac apply_canonical_form :=
  match goal with
  | H : val ?e, H' : _; _ ⊢ ?e : ?τ |- _ =>
    let lem := apply_canonical_form_lem τ in
    eapply lem in H; [ | solve [ eauto ] | solve [ eauto ] ]; try simp_hyp H
  end; subst.

Section fix_gctx.

Context (Σ : gctx).
Context (Hwf : gctx_wf Σ).

#[local]
Set Default Proof Using "Hwf".

(** * Progress *)

Ltac ctx_solver :=
  match goal with
  | |- exists _, _ ⊨ _ -->! _ =>
    eexists; solve_ectx
  end.

(** The combined progress theorems for expressions and types. *)
Theorem progress_ :
  (forall Γ e τ,
      Γ ⊢ e : τ ->
      Γ = ∅ ->
      val e \/ exists e', e -->! e') /\
  (forall Γ τ κ,
     Γ ⊢ τ :: κ ->
     Γ = ∅ ->
     κ = <{ *@O }> ->
     otval τ \/ exists τ', τ -->! τ').
Proof.
  eapply typing_kinding_mutind; intros; subst;
    (* If a type is not used in the conclusion, the mutual inductive hypothesis
    for it is useless. Remove this hypothesis to avoid slowdown the
    automation. *)
    try match goal with
        | H : context [otval ?τ \/ _] |- val ?e \/ _ =>
          assert_fails contains e τ; clear H
        end;
    simp_hyps; try case_label; simplify_map_eq; eauto;
    (* Solve the trivial evaluation context step. *)
    repeat
      match reverse goal with
      | H : otval _ \/ exists _, _ |- _ =>
          destruct H as [| [] ]; [ | solve [ right; ctx_solver ] ]
      end;
    repeat
      match reverse goal with
      | H : val _ \/ exists _, _ |- _ =>
          destruct H as [| [] ]; [ | solve [ right; ctx_solver ] ]
      end;
    try apply_canonical_form;
    try solve [ right; eauto using step, val; ctx_solver
              | left; eauto using val, oval, otval ].

  (* Oblivious injection. It steps to boxed injection. *)
  right. otval_inv.
  repeat econstructor; eauto.
  case_split; eauto using otval_well_kinded, val_oval.

  (* Oblivious case. *)
  right.
  select! (otval _) (fun H => use (ovalty_inhabited _ H)).
  eauto using step.

  (* Oblivious pair. *)
  left. eauto 10 using val, oval, val_oval.

  (* Psi pair. *)
  left. eauto using val, val_oval, kinding.

  (* Boxed injection. *)
  left. qauto use: ovalty_elim ctrs: val.

  (* Public product and sum. These case are impossible. *)
  1-2: enough (<{ *@P }> ⊑ <{ *@O }>) by easy; scongruence use: join_ub_r.

  (* Kinding subsumption *)
  select kind (fun κ => destruct κ); sintuition use: any_kind_otval.
Qed.

Theorem progress τ e :
  ∅ ⊢ e : τ ->
  val e \/ exists e', e -->! e'.
Proof.
  hauto use: progress_.
Qed.

Theorem kinding_progress τ :
  ∅ ⊢ τ :: *@O ->
  otval τ \/ exists τ', τ -->! τ'.
Proof.
  hauto use: progress_.
Qed.

End fix_gctx.
