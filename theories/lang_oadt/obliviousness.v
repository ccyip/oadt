From oadt Require Import prelude.
From oadt Require Import lang_oadt.preservation.

(** * Obliviousness *)
(** The obliviousness metatheorem. Essentially a noninterference property. *)

Module M (atom_sig : AtomSig).

Include preservation.M atom_sig.
Import syntax_notations.
Import semantics_notations.
Import typing_notations.

Implicit Types (x X y Y : atom) (L : aset).
Implicit Types (b : bool).

#[local]
Coercion EFVar : atom >-> expr.


(** Indistinguishability is equivalence. *)
Instance indistinguishable_is_equiv : Equivalence indistinguishable.
Proof.
  split.
  - intros e. induction e; eauto with indistinguishable.
  - intros ??; induction 1; eauto with indistinguishable.
  - intros e1 e2 e3. intros H. revert e3.
    induction H; intros e3; inversion 1; subst; eauto with indistinguishable.
Qed.

Lemma indistinguishable_open e e' s s' :
  e ≈ e' ->
  s ≈ s' ->
  <{ e^s }> ≈ <{ e'^s' }>.
Proof.
  unfold open. intros H. generalize 0.
  induction H; intros; simpl in *;
    try case_decide; eauto with indistinguishable.
Qed.

Lemma indistinguishable_oval v v' ω :
  oval v ω ->
  oval v' ω ->
  v ≈ v'.
Proof.
  intros H. revert v'.
  induction H; intros v'; inversion 1; subst;
    eauto with indistinguishable.
Qed.

Lemma indistinguishable_oval_inv v v' ω ω' :
  v ≈ v' ->
  oval v ω ->
  oval v' ω' ->
  ω = ω'.
Proof.
  intros H. revert ω ω'.
  induction H; intros ??; inversion 1; subst; inversion 1; subst;
    qauto l: on inv: oval.
Qed.

Lemma indistinguishable_otval ω ω' :
  ω ≈ ω' ->
  otval ω ->
  otval ω'.
Proof.
  induction 1; intros;
    qauto l: on inv: otval ctrs: otval.
Qed.

Lemma indistinguishable_otval_inv ω ω' :
  ω ≈ ω' ->
  otval ω ->
  otval ω' ->
  ω = ω'.
Proof.
  induction 1; intros;
    qauto l: on inv: otval.
Qed.

Lemma indistinguishable_val_ v v' :
  v ≈ v' ->
  val v ->
  expr_wf v' ->
  val v'.
Proof.
  induction 1; intros; try qauto l: on ctrs: val inv: val, expr_wf.
  (* The boxed injection case. *)
  qauto l: on ctrs: val inv: val, expr_wf use: oval_elim.
Qed.

Lemma indistinguishable_val v v' Σ Γ τ :
  v ≈ v' ->
  val v ->
  Σ; Γ ⊢ v' : τ ->
  val v'.
Proof.
  qauto use: indistinguishable_val_, typing_expr_wf.
Qed.

Lemma indistinguishable_val_is_nf Σ v v' :
  val v ->
  v ≈ v' ->
  nf (@step Σ) v'.
Proof.
  intros H. revert v'.
  induction H; intros ?? [];
    select (_ ≈ _) (fun H => sinvert H);
    select (_ ⊨ _ -->! _) (fun H => sinvert H);
    try select (ectx _) (fun H => sinvert H);
    simplify_eq; eauto; sfirstorder.
Qed.

Lemma indistinguishable_otval_is_nf Σ ω ω' :
  otval ω ->
  ω ≈ ω' ->
  nf (@step Σ) ω'.
Proof.
  intros H. revert ω'.
  induction H; intros ?? [];
    select (_ ≈ _) (fun H => sinvert H);
    select (_ ⊨ _ -->! _) (fun H => sinvert H);
    try select (ectx _) (fun H => sinvert H);
    simplify_eq; eauto; sfirstorder.
Qed.

Lemma indistinguishable_val_step Σ v v' e :
  val v ->
  v ≈ v' ->
  Σ ⊨ v' -->! e ->
  False.
Proof.
  sfirstorder use: indistinguishable_val_is_nf.
Qed.

Lemma indistinguishable_otval_step Σ ω ω' e :
  otval ω ->
  ω ≈ ω' ->
  Σ ⊨ ω' -->! e ->
  False.
Proof.
  sfirstorder use: indistinguishable_otval_is_nf.
Qed.

(** The next few lemmas can be proved independently, but they can simply reduce
to the indistinguishable counterparts. *)
Lemma val_is_nf Σ v :
  val v ->
  nf (@step Σ) v.
Proof.
  qauto use: indistinguishable_val_is_nf solve: reflexivity.
Qed.

Lemma otval_is_nf Σ ω :
  otval ω ->
  nf (@step Σ) ω.
Proof.
  qauto use: indistinguishable_otval_is_nf solve: reflexivity.
Qed.

Lemma val_step Σ v e :
  Σ ⊨ v -->! e ->
  val v ->
  False.
Proof.
  sfirstorder use: val_is_nf.
Qed.

Lemma otval_step Σ ω e :
  Σ ⊨ ω -->! e ->
  otval ω ->
  False.
Proof.
  sfirstorder use: otval_is_nf.
Qed.


Ltac apply_canonical_form_ H τ :=
  lazymatch τ with
  | <{ 𝟙 }> => eapply canonical_form_unit in H
  | <{ ~𝔹 }> => eapply canonical_form_obool in H
  | <{ _ * _ }> => eapply canonical_form_prod in H
  | <{ _ ~+ _ }> => eapply canonical_form_osum in H
  end.

(* This tactic is destructive. *)
Tactic Notation "apply_canonical_form" "by" tactic3(tac) :=
  match goal with
  | H : val ?e, H' : _; _ ⊢ ?e : ?τ |- _ =>
    first [ apply_canonical_form_ H τ
          | match goal with
            | H' : _ ⊢ τ ≡ ?τ' |- _ => apply_canonical_form_ H τ'
            | H' : _ ⊢ ?τ' ≡ τ |- _ => apply_canonical_form_ H τ'
            end ];
      [ try simp_hyp H
      | tac ]
  end; subst.

Tactic Notation "apply_canonical_form" :=
  apply_canonical_form by (first [ solve [eauto]
                                 | eapply TConv;
                                   [ solve [eauto]
                                   | eauto with kinding
                                   | equiv_naive_solver ] ]).

Ltac apply_obliv_type_preserve :=
  simpl_cofin?;
  try select! (_; _ ⊢ _ : _)
      (fun H => dup_hyp H (fun H => eapply regularity in H;
                                [ simp_hyp H | eauto ]));
  apply_type_inv;
  repeat
    match goal with
    | H : _ ⊢ ?τ ≡ _, H' : _; _ ⊢ ?τ :: _ |- _ =>
      eapply expr_equiv_obliv_type_preserve in H;
      [| eassumption | apply H' | eauto; kinding_intro; eauto; fast_set_solver!! ]
    end;
  repeat
    match goal with
    | Hwf : gctx_wf _, H : _ !! _ = Some (DADT _) |- _ =>
      apply Hwf in H; try simp_hyp H
    end;
  apply_kind_inv.

Lemma indistinguishable_obliv_val Σ Γ v1 v2 τ :
  gctx_wf Σ ->
  val v1 ->
  val v2 ->
  Σ; Γ ⊢ v1 : τ ->
  Σ; Γ ⊢ v2 : τ ->
  Σ; Γ ⊢ τ :: *@O ->
  v1 ≈ v2.
Proof.
  intros Hwf H. revert Γ v2 τ.
  induction H; intros;
    apply_type_inv;
    try solve [apply_obliv_type_preserve; easy];
    try apply_canonical_form;
    eauto with indistinguishable.

  (* Pair *)
  - select (_ ⊢ _ ≡ _) (fun H => dup_hyp H (fun H => revert H)).
    apply_obliv_type_preserve.
    intros.
    apply_canonical_form by (eapply TConv; eauto;
                             kinding_intro; eauto).
    apply_type_inv.
    match goal with
    | H1 : _ ⊢ ?τ ≡ _, H2 : _ ⊢ ?τ ≡ _ |- _ =>
      rewrite H1 in H2
    end.
    simpl_whnf_equiv.
    constructor; auto_eapply; eauto; econstructor; eauto; equiv_naive_solver.

  (* Boxed injection *)
  - apply_canonical_form by (eapply TConv; eauto;
                             qauto use: otval_well_kinded).
    apply_type_inv.
    match goal with
    | H1 : _ ⊢ ?τ ≡ _, H2 : _ ⊢ ?τ ≡ _ |- _ =>
      rewrite H1 in H2
    end.
    match goal with
    | |- <{ [inj@_< ?ω1 > _] }> ≈ <{ [inj@_< ?ω2 > _] }> =>
      replace ω2 with ω1 by (eauto using otval_uniq with otval)
    end.
    eauto with indistinguishable.
Qed.

Lemma indistinguishable_val_obliv_type_equiv Σ Γ v v' τ τ' :
  gctx_wf Σ ->
  val v ->
  v ≈ v' ->
  Σ; Γ ⊢ v : τ ->
  Σ; Γ ⊢ v' : τ' ->
  Σ; Γ ⊢ τ :: *@O ->
  Σ ⊢ τ ≡ τ'.
Proof.
  intros Hwf H. revert Γ v' τ τ'.
  induction H; intros; subst;
    select (_ ≈ _) (fun H => sinvert H);
    apply_type_inv;
    try solve [apply_obliv_type_preserve; easy];
    try equiv_naive_solver.

  (* Product *)
  - repeat
      match goal with
      | H : _ ⊢ ?τ ≡ _ |- _ ⊢ ?τ ≡ _ => rewrite H
      | H : _ ⊢ ?τ ≡ _ |- _ ⊢ _ ≡ ?τ => rewrite H
      end.
    apply_obliv_type_preserve.
    apply expr_equiv_iff_whnf_equiv; [ solve [eauto with whnf]
                                     | solve [eauto with whnf]
                                     | econstructor; eauto ];
    (* Apply the right induction hypothesis. *)
    match goal with
    | H : context [?v ≈ _ -> _], H' : _; _ ⊢ ?v : ?τ |- _ ⊢ ?τ ≡ _ =>
      eapply H
    end;
    try (goal_is (_ ≈ _); eauto); eauto;
      eauto with kinding.

  (* Oblivious sum *)
  - subst.
    select (<{ _ ~+ _ }> = <{ _ ~+ _ }>) (fun H => sinvert H).
    equiv_naive_solver.
Qed.

(* This lemma can be strengthened so that we drop the typing assumption for
[v']. In order for that, we have to prove [v'] can be typed which should be
provable. But this version is good enough for the main theorem. *)
Lemma indistinguishable_val_type Σ Γ v v' τ τ' :
  gctx_wf Σ ->
  val v ->
  v ≈ v' ->
  Σ; Γ ⊢ v : τ ->
  Σ; Γ ⊢ v' : τ' ->
  Σ; Γ ⊢ τ :: *@O ->
  Σ; Γ ⊢ v' : τ.
Proof.
  intros.
  eapply TConv; eauto.
  symmetry.
  eapply indistinguishable_val_obliv_type_equiv; eauto.
Qed.

Ltac val_step_absurd :=
  match goal with
  | H : _ ⊨ _ -->! _ |- _ =>
    exfalso; eapply otval_step;
    [ apply H
    | solve [ eauto
            | eapply indistinguishable_otval;
              [ solve [ eassumption | symmetry; eassumption ]
              | eauto with otval ] ] ]
  | H : _ ⊨ _ -->! _ |- _ =>
    exfalso; eapply val_step;
    [ apply H
    | solve [ eauto
            | eapply indistinguishable_val;
              [ solve [ eassumption | symmetry; eassumption ]
              | eauto with val
              | eauto ] ] ]
  end.

Theorem indistinguishable_step Σ e1 e1' e2 τ τ' :
  gctx_wf Σ ->
  Σ ⊨ e1 -->! e2 ->
  e1 ≈ e1' ->
  Σ; ∅ ⊢ e1 : τ ->
  Σ; ∅ ⊢ e1' : τ' ->
  exists e2', Σ ⊨ e1' -->! e2'.
Proof.
  intros.
  qauto use: progress solve: val_step_absurd.
Qed.

Tactic Notation "apply_kind_inv" hyp(H) "by" tactic3(tac) :=
  lazymatch type of H with
  | _; _ ⊢ Π:_, _ :: _ => tac kind_inv_pi
  | _; _ ⊢ 𝔹 :: _ => tac kind_inv_bool
  | _; _ ⊢ _ _ :: _ => tac kind_inv_app
  | _; _ ⊢ let _ in _ :: _ => tac kind_inv_let
  | _; _ ⊢ _ * _ :: _ => tac kind_inv_prod
  | _; _ ⊢ _ + _ :: _ => tac kind_inv_sum
  | _; _ ⊢ _ ~+ _ :: _ => tac kind_inv_osum
  | _; _ ⊢ gvar _ :: _ => tac kind_inv_gvar
  | _; _ ⊢ ~if _ then _ else _ :: _ => apply kind_inv_mux in H; elim H
  | _; _ ⊢ if _ then _ else _ :: _ => tac kind_inv_ite
  | _; _ ⊢ ~case _ of _ | _ :: _ => apply kind_inv_ocase in H; elim H
  | _; _ ⊢ case{_} _ of _ | _ :: _ => tac kind_inv_case
  | _; _ ⊢ s𝔹 _ :: _ => apply kind_inv_sec in H; elim H
  | _; _ ⊢ (_, _) :: _ => apply kind_inv_pair in H; elim H
  | _; _ ⊢ π@_ _ :: _ => apply kind_inv_proj in H; elim H
  | _; _ ⊢ inj{_}@_<_> _ :: _ => apply kind_inv_inj in H; elim H
  | _; _ ⊢ fold<_> _ :: _ => apply kind_inv_fold in H; elim H
  | _; _ ⊢ unfold<_> _ :: _ => apply kind_inv_unfold in H; elim H
  end.

Tactic Notation "apply_kind_inv" hyp(H) :=
  apply_kind_inv H by (fun lem => apply lem in H; try simp_hyp H).

Tactic Notation "apply_kind_inv" :=
  do_hyps (fun H => try apply_kind_inv H).

Theorem indistinguishable_deterministic Σ e1 e1' e2 e2' :
  gctx_wf Σ ->
  Σ ⊨ e1 -->! e2 ->
  Σ ⊨ e1' -->! e2' ->
  e1 ≈ e1' ->
  ((exists τ τ', Σ; ∅ ⊢ e1 : τ /\ Σ; ∅ ⊢ e1' : τ') \/
   (exists κ κ', Σ; ∅ ⊢ e1 :: κ /\ Σ; ∅ ⊢ e1' :: κ')) ->
  e2 ≈ e2'.
Proof.
  intros Hwf H. revert e1' e2'.
  induction H; intros;
    try select (ectx _) (fun H => sinvert H); simplify_eq;
      repeat
        (match goal with
         | H : ?e ≈ _ |- _ => head_constructor e; sinvert H
         | H : _ ≈ ?e |- _ => head_constructor e; sinvert H
         end;
         try (select (_ \/ _) (fun H => destruct H as [ [?[?[??]]] | [?[?[??]]] ]));
         apply_type_inv; apply_kind_inv;
         try match goal with
             | H : _ ⊨ ?e -->! _ |- _ =>
               head_constructor e; sinvert H
             end;
         try select (ectx _) (fun H => sinvert H); simplify_eq;
         try solve
             (* Discharge the impossible cases *)
             [ val_step_absurd
             (* Solve the trivial cases *)
             | eauto using indistinguishable_open
             (* Solve the inductive cases. *)
             | econstructor; eauto; auto_eapply; eauto 10 with kinding ]);
      (* Solve other less trivial cases *)
      try qauto rew: off use: indistinguishable_open solve: reflexivity.

  (* Step from oblivious case to mux *)
  - repeat
      match goal with
      | H : oval ?v _ |- _ => head_constructor v; sinvert H
      end.
    econstructor; eauto with indistinguishable;
      case_splitting;
      eauto using indistinguishable_open, indistinguishable_oval.

  (* Step from oblivious injection to boxed injection *)
  - match goal with
    | |- <{ [inj@_< ?ω1 > _] }> ≈ <{ [inj@_< ?ω2 > _] }> =>
      replace ω2 with ω1
        by (eauto using indistinguishable_otval_inv with indistinguishable)
    end.
    eauto with indistinguishable.

  (* Step from mux *)
  - case_splitting;
      eauto using indistinguishable_obliv_val, indistinguishable_val_type.
Qed.

(** The one-step obliviousness theorem, which is essentially a noninterference
theorem. Two indistinguishable well-typed expressions always step to
indistinguishable new expressions, or they both can not take any more step. It
is important that if one of them takes step, another one also takes step.
Otherwise the adversaries can distinguish them by this mismatched behavior. *)
Corollary obliviousness_step Σ e1 e1' e2 τ τ' :
  gctx_wf Σ ->
  Σ ⊨ e1 -->! e2 ->
  e1 ≈ e1' ->
  Σ; ∅ ⊢ e1 : τ ->
  Σ; ∅ ⊢ e1' : τ' ->
  (exists e2', Σ ⊨ e1' -->! e2') /\
  (forall e2', Σ ⊨ e1' -->! e2' -> e2 ≈ e2').
Proof.
  qauto use: indistinguishable_step, indistinguishable_deterministic.
Qed.

End M.
