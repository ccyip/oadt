From oadt.lang_oadt Require Import
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

Lemma wval_woval Γ v l τ :
  Γ ⊢ v :{l} τ ->
  Γ ⊢ τ :: *@O ->
  wval v ->
  woval v.
Proof.
  induction 1; intros; try wval_inv; try oval_inv;
    kind_inv; simplify_eq;
      try hauto lq: on ctrs: woval, oval; try easy.

  (* TConv *)
  apply_regularity.
  auto_apply; eauto.
  eapply pared_equiv_obliv_preservation; eauto.
  equiv_naive_solver.
Qed.

Lemma val_oval Γ v l τ :
  Γ ⊢ v :{l} τ ->
  Γ ⊢ τ :: *@O ->
  val v ->
  oval v.
Proof.
  intros Ht Hk Hv.
  pose proof Hv.
  apply val_wval in Hv.
  eapply wval_woval in Hv; eauto.
  sinvert Hv; eauto. val_inv. oval_inv.
Qed.

(** * Canonical forms *)
Ltac canonical_form_solver :=
  inversion 1; intros; subst;
  try select (oval _) (fun H => sinvert H);
  eauto;
  type_inv;
  kind_inv;
  try simpl_whnf_equiv;
  simplify_eq;
  eauto 10.

Lemma canonical_form_unit Γ l e :
  val e ->
  Γ ⊢ e :{l} 𝟙 ->
  e = <{ () }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_abs Γ l1 l2 e τ2 τ1 :
  val e ->
  Γ ⊢ e :{l1} Π:{l2}τ2, τ1 ->
  exists e' τ, e = <{ \:{l2}τ => e' }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_bool Γ l e :
  val e ->
  Γ ⊢ e :{l} 𝔹 ->
  exists b, e = <{ b }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_obool Γ l e :
  val e ->
  Γ ⊢ e :{l} ~𝔹 ->
  exists b, e = <{ [b] }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_prod Γ l e τ1 τ2 :
  val e ->
  Γ ⊢ e :{l} τ1 * τ2 ->
  exists v1 v2, val v1 /\ val v2 /\ e = <{ (v1, v2) }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_oprod Γ l e τ1 τ2 :
  val e ->
  Γ ⊢ e :{l} τ1 ~* τ2 ->
  exists v1 v2, oval v1 /\ oval v2 /\ e = <{ ~(v1, v2) }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_sum Γ l e τ1 τ2 :
  val e ->
  Γ ⊢ e :{l} τ1 + τ2 ->
  exists b v τ, val v /\ e = <{ inj@b<τ> v }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_osum Γ l e τ1 τ2 :
  val e ->
  Γ ⊢ e :{l} τ1 ~+ τ2 ->
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
Lemma canonical_form_fold Γ l e X :
  val e ->
  Γ ⊢ e :{l} gvar X ->
  exists v X', val v /\ e = <{ fold<X'> v }>.
Proof.
  inversion 1; canonical_form_solver.
Qed.

(** * Canonical forms for weak values *)

Lemma canonical_form_weak_unit Γ l e :
  wval e ->
  Γ ⊢ e :{l} 𝟙 ->
  e = <{ () }> \/
  (exists b v1 v2, wval v1 /\ wval v2 /\ e = <{ ~if [b] then v1 else v2 }>).
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_weak_abs Γ l1 l2 e τ2 τ1 :
  wval e ->
  Γ ⊢ e :{l1} Π:{l2}τ2, τ1 ->
  (exists e' τ, e = <{ \:{l2}τ => e' }>) \/
  (exists b v1 v2, wval v1 /\ wval v2 /\ e = <{ ~if [b] then v1 else v2 }>).
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_weak_bool Γ l e :
  wval e ->
  Γ ⊢ e :{l} 𝔹 ->
  (exists b, e = <{ b }>) \/
  (exists b v1 v2, wval v1 /\ wval v2 /\ e = <{ ~if [b] then v1 else v2 }>).
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_weak_prod Γ l e τ1 τ2 :
  wval e ->
  Γ ⊢ e :{l} τ1 * τ2 ->
  (exists v1 v2, wval v1 /\ wval v2 /\ e = <{ (v1, v2) }>) \/
  (exists b v1 v2, wval v1 /\ wval v2 /\ e = <{ ~if [b] then v1 else v2 }>).
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_weak_sum Γ l e τ1 τ2 :
  wval e ->
  Γ ⊢ e :{l} τ1 + τ2 ->
  (exists b v τ, wval v /\ e = <{ inj@b<τ> v }>) \/
  (exists b v1 v2, wval v1 /\ wval v2 /\ e = <{ ~if [b] then v1 else v2 }>).
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_weak_fold Γ l e X :
  wval e ->
  Γ ⊢ e :{l} gvar X ->
  (exists v X', wval v /\ e = <{ fold<X'> v }>) \/
  (exists b v1 v2, wval v1 /\ wval v2 /\ e = <{ ~if [b] then v1 else v2 }>).
Proof.
  inversion 1; canonical_form_solver.
Qed.

End fix_gctx.

Ltac apply_canonical_form_lem τ :=
  lazymatch τ with
  | <{ 𝟙 }> => canonical_form_unit
  | <{ ~𝔹 }> => canonical_form_obool
  | <{ _ ~* _ }> => canonical_form_oprod
  | <{ _ ~+ _ }> => canonical_form_osum
  end.

Ltac apply_canonical_form :=
  match goal with
  | H : val ?e, H' : _; _ ⊢ ?e :{_} ?τ |- _ =>
    let lem := apply_canonical_form_lem τ in
    eapply lem in H; [ | solve [ eauto ] | solve [ eauto ] ]; try simp_hyp H
  end; subst.

Ltac apply_canonical_form_weak_lem τ :=
  lazymatch τ with
  | <{ Π:{_}_, _ }> => canonical_form_weak_abs
  | <{ 𝔹 }> => canonical_form_weak_bool
  | <{ _ + _ }> => canonical_form_weak_sum
  | <{ _ * _ }> => canonical_form_weak_prod
  | <{ gvar _ }> => canonical_form_weak_fold
  end.

Ltac apply_canonical_form_weak :=
  match goal with
  | Hw : wval ?e, Ht : _; _ ⊢ ?e :{⊥} ?τ |- _ =>
      eapply wval_val in Hw; [ | solve [ eauto ] ];
      apply_canonical_form
  | Hw : wval ?e, Ht : _; _ ⊢ ?e :{_} ?τ |- _ =>
      let lem := apply_canonical_form_weak_lem τ in
      eapply lem in Hw; [ | solve [ eauto ] | solve [ eauto ] ];
      destruct Hw; try simp_hyp Hw; subst
  end.


Section fix_gctx.

Context (Σ : gctx).
Context (Hwf : gctx_wf Σ).

#[local]
Set Default Proof Using "Hwf".

(** * Progress *)

Ltac ctx_solver :=
  match goal with
  | |- exists _, _ ⊨ _ -->! _ =>
    eexists; solve_ctx
  end.

(** The combined progress theorems for expressions and types. *)
Theorem progress_ :
  (forall Γ e l τ,
      Γ ⊢ e :{l} τ ->
      Γ = ∅ ->
      wval e \/ exists e', e -->! e') /\
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
      | H : wval _ \/ exists _, _ |- _ =>
          destruct H as [| [] ]; [ | solve [ right; ctx_solver ] ]
      end;
    try apply_canonical_form_weak;
    try solve [ right; eauto using step, wval; ctx_solver
              | left; eauto using wval, oval, otval ].

  (* Oblivious injection. It steps to boxed injection. *)
  right. otval_inv.
  repeat econstructor; eauto.
  case_split; eauto using otval_well_kinded, val_oval, wval_val.

  (* Oblivious case. *)
  right.
  select! (otval _) (fun H => use (ovalty_inhabited _ H)).
  eauto using step.

  (* Oblivious pair. *)
  left. eauto 10 using wval, oval, val_oval, wval_val.

  (* Tape. *)
  right.
  hauto use: wval_woval ctrs: step inv: woval.

  (* Boxed injection. *)
  left. qauto use: ovalty_elim ctrs: wval.

  (* Public product and sum. These case are impossible. *)
  1-2:  enough (<{ *@P }> ⊑ <{ *@O }>) by easy; scongruence use: join_ub_r.

  (* Kinding subsumption *)
  select kind (fun κ => destruct κ); sintuition use: any_kind_otval.
Qed.

Theorem progress_weak l τ e :
  ∅ ⊢ e :{l} τ ->
  wval e \/ exists e', e -->! e'.
Proof.
  hauto use: progress_.
Qed.

Theorem progress τ e :
  ∅ ⊢ e :{⊥} τ ->
  val e \/ exists e', e -->! e'.
Proof.
  hauto use: progress_, wval_val.
Qed.

Theorem kinding_progress τ :
  ∅ ⊢ τ :: *@O ->
  otval τ \/ exists τ', τ -->! τ'.
Proof.
  hauto use: progress_.
Qed.

End fix_gctx.
