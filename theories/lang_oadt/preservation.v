From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.
From oadt Require Import lang_oadt.infrastructure.
From oadt Require Import lang_oadt.values.
From oadt Require Import lang_oadt.admissible.
From oadt Require Import lang_oadt.inversion.
From oadt Require Import lang_oadt.equivalence.

Import syntax.notations.
Import semantics.notations.
Import typing.notations.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

#[local]
Coercion EFVar : atom >-> expr.


(** * Weakening lemmas  *)
Lemma pared_weakening Σ e e' :
  Σ ⊢ e ==>! e' ->
  forall Σ', Σ ⊆ Σ' ->
        Σ' ⊢ e ==>! e'.
Proof.
  induction 1; intros; eauto using pared, lookup_weaken.
Qed.

Lemma pared_equiv_weakening Σ e e' :
  Σ ⊢ e ≡ e' ->
  forall Σ', Σ ⊆ Σ' ->
        Σ' ⊢ e ≡ e'.
Proof.
  induction 1; intros; eauto using pared_equiv, pared_weakening.
Qed.

Lemma weakening_ Σ :
  (forall Γ e τ,
    Σ; Γ ⊢ e : τ ->
    forall Σ' Γ',
      Σ ⊆ Σ' ->
      Γ ⊆ Γ' ->
      Σ'; Γ' ⊢ e : τ) /\
  (forall Γ τ κ,
    Σ; Γ ⊢ τ :: κ ->
    forall Σ' Γ',
      Σ ⊆ Σ' ->
      Γ ⊆ Γ' ->
      Σ'; Γ' ⊢ τ :: κ).
Proof.
  apply typing_kinding_mutind; intros; subst;
    try qauto l: on ctrs: typing, kinding;
    try qauto l: on use: lookup_weaken ctrs: typing, kinding;
    try qauto l: on use: insert_mono ctrs: typing, kinding;
    (* For the [case]/[~case] cases and the [TConv] case. *)
    econstructor; eauto using insert_mono, pared_equiv_weakening.
Qed.

Lemma weakening Σ Γ Σ' Γ' e τ :
  Σ; Γ ⊢ e : τ ->
  Σ ⊆ Σ' ->
  Γ ⊆ Γ' ->
  Σ'; Γ' ⊢ e : τ.
Proof.
  hauto use: weakening_.
Qed.

Lemma kinding_weakening Σ Γ Σ' Γ' τ κ :
  Σ; Γ ⊢ τ :: κ ->
  Σ ⊆ Σ' ->
  Γ ⊆ Γ' ->
  Σ'; Γ' ⊢ τ :: κ.
Proof.
  hauto use: weakening_.
Qed.

Lemma weakening_empty Σ Γ e τ :
  Σ; ∅ ⊢ e : τ ->
  Σ; Γ ⊢ e : τ.
Proof.
  eauto using weakening, map_empty_subseteq.
Qed.

Lemma kinding_weakening_empty Σ Γ τ κ :
  Σ; ∅ ⊢ τ :: κ ->
  Σ; Γ ⊢ τ :: κ.
Proof.
  eauto using kinding_weakening, map_empty_subseteq.
Qed.

Lemma weakening_insert Σ Γ e τ τ' x :
  Σ; Γ ⊢ e : τ ->
  x ∉ dom aset Γ ->
  Σ; (<[x:=τ']>Γ) ⊢ e : τ.
Proof.
  eauto using weakening, insert_fresh_subseteq.
Qed.

Lemma kinding_weakening_insert Σ Γ τ τ' κ x :
  Σ; Γ ⊢ τ :: κ ->
  x ∉ dom aset Γ ->
  Σ; (<[x:=τ']>Γ) ⊢ τ :: κ.
Proof.
  eauto using kinding_weakening, insert_fresh_subseteq.
Qed.

(** * Substitution lemmas *)

Lemma subst_tctx_typing_kinding_ Σ x s :
  gctx_wf Σ ->
  (forall Γ e τ,
      Σ; Γ ⊢ e : τ ->
      x ∉ fv τ ∪ dom aset Γ ->
      Σ; ({x↦s} <$> Γ) ⊢ e : τ) /\
  (forall Γ τ κ,
      Σ; Γ ⊢ τ :: κ ->
      x ∉ dom aset Γ ->
      Σ; ({x↦s} <$> Γ) ⊢ τ :: κ).
Proof.
  intros Hwf.
  apply typing_kinding_mutind; intros; subst; simpl in *;
    econstructor; eauto;
      simpl_cofin?;
      (* Try to apply induction hypotheses. *)
      lazymatch goal with
      | |- _; ?Γ ⊢ ?e : _ =>
        auto_apply || lazymatch goal with
                      | H : _ -> _; ?Γ' ⊢ e : _ |- _ =>
                        replace Γ with Γ'; [auto_apply |]
                      end
      | |- _; ?Γ ⊢ ?τ :: _ =>
        auto_apply || lazymatch goal with
                      | H : _ -> _; ?Γ' ⊢ τ :: _ |- _ =>
                        replace Γ with Γ'; [auto_apply |]
                      end
      | _ => idtac
      end; eauto;
        (* Solve other side conditions *)
        repeat lazymatch goal with
               | |- _ ∉ _ =>
                 shelve
               | |- _ <> _ =>
                 shelve
               | |- {_↦_} <$> (<[_:=_]>_) = <[_:=_]>({_↦_} <$> _) =>
                 rewrite fmap_insert; try reflexivity; repeat f_equal
               | |- _ !! _ = Some _ =>
                 simplify_map_eq
               | |- Some _ = Some _ =>
                 try reflexivity; repeat f_equal
               | |- {_↦_} _ = _ =>
                 rewrite subst_fresh
               end;
        eauto.

  Unshelve.

  all : try fast_set_solver!!; simpl_fv; fast_set_solver!!.
Qed.

Lemma subst_tctx_typing Σ Γ e τ x s :
  gctx_wf Σ ->
  Σ; Γ ⊢ e : τ ->
  x ∉ fv τ ∪ dom aset Γ ->
  Σ; ({x↦s} <$> Γ) ⊢ e : τ.
Proof.
  qauto use: subst_tctx_typing_kinding_.
Qed.

(* Note that [lc s] is not needed, and it is here only for convenience. I will
drop it in the actual lemma. *)
Lemma subst_preservation_ Σ x s τ' :
  gctx_wf Σ ->
  lc s ->
  (forall Γ' e τ,
      Σ; Γ' ⊢ e : τ ->
      forall Γ,
        Γ' = <[x:=τ']>Γ ->
        x ∉ fv τ' ∪ dom aset Γ ->
        Σ; Γ ⊢ s : τ' ->
        Σ; ({x↦s} <$> Γ) ⊢ {x↦s}e : {x↦s}τ) /\
  (forall Γ' τ κ,
      Σ; Γ' ⊢ τ :: κ ->
      forall Γ,
        Γ' = <[x:=τ']>Γ ->
        x ∉ fv τ' ∪ dom aset Γ ->
        Σ; Γ ⊢ s : τ' ->
        Σ; ({x↦s} <$> Γ) ⊢ {x↦s}τ :: κ).
Proof.
  intros Hwf Hlc.
  apply typing_kinding_mutind; intros; subst; simpl in *;
    (* First we normalize the typing and kinding judgments so they are ready
    for applying typing and kinding rules to. *)
    rewrite ?subst_open_distr by assumption;
    rewrite ?subst_ite_distr;
    try lazymatch goal with
        | |- _; _ ⊢ [inj@_< ?ω > _] : {_↦_}?ω =>
          rewrite subst_fresh by shelve
        | |- context [decide (_ = _)] =>
          (* The case of [fvar x] is the trickier one. Let's handle it later. *)
          case_decide; subst; [shelve |]
        end;
      (* Apply typing and kinding rules. *)
      econstructor;
      simpl_cofin?;
      (* We define this subroutine [go] for applying induction hypotheses. *)
      let go Γ :=
          (* We massage the typing and kinding judgments so that we can apply
          induction hypotheses to them. *)
          rewrite <- ?subst_ite_distr;
            rewrite <- ?subst_open_distr by assumption;
            rewrite <- ?subst_open_comm by (try assumption; shelve);
            try lazymatch Γ with
                | <[_:=_]>({_↦_} <$> _) =>
                  rewrite <- fmap_insert
                end;
            (* Apply one of the induction hypotheses. *)
            first [ auto_apply
                  (* In [if] and [case] cases, prove the type matching the
                  induction hypothesis later. *)
                  | relax_typing_type; [ auto_apply | ] ] in
      (* Make sure we complete handling the typing and kinding judgments first.
      Otherwise some existential variables may have undesirable
      instantiation. *)
      lazymatch goal with
      | |- _; ?Γ ⊢ _ : _ => go Γ
      | |- _; ?Γ ⊢ _ :: _ => go Γ
      | _ => idtac
      end;
        (* Try to solve other side conditions. *)
        eauto;
        repeat lazymatch goal with
               | |- _ ∉ _ =>
                 shelve
               | |- _ <> _ =>
                 shelve
               | |- <[_:=_]>(<[_:=_]>_) = <[_:=_]>(<[_:=_]>_) =>
                 apply insert_commute
               | |- _ ⊢ _ ≡ _ =>
                 apply pared_equiv_subst2
               | |- (_ <$> _) !! _ = Some _ =>
                 simplify_map_eq
               | |- _; (<[_:=_]>_) ⊢ _ : _ =>
                 apply weakening_insert
               | |- Some _ = Some _ =>
                 try reflexivity; repeat f_equal
               | |- _ = {_↦_} _ =>
                 rewrite subst_fresh
               | H : ?Σ !! ?x = Some _ |- ?Σ !! ?x = Some _ =>
                 rewrite H
               end;
        eauto.

  (* Prove the types of [if] and [case] match the induction hypotheses. *)
  all : rewrite subst_open_distr by eassumption; simpl; eauto;
    rewrite decide_False by shelve; eauto.

  Unshelve.

  (* Case [fvar x] *)
  simplify_map_eq.
  rewrite subst_fresh.
  apply subst_tctx_typing; eauto.

  (* Solve other side conditions of free variables. *)
  all : try fast_set_solver!!; simpl_fv; fast_set_solver*!!.
Qed.

(** The actual substitution lemma *)
Lemma subst_preservation Σ x s τ' Γ e τ :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ e : τ ->
  Σ; Γ ⊢ s : τ' ->
  x ∉ fv τ' ∪ dom aset Γ ∪ tctx_fv Γ ->
  Σ; Γ ⊢ {x↦s}e : {x↦s}τ.
Proof.
  intros.
  rewrite <- (subst_tctx_fresh Γ x s) by fast_set_solver!!.
  eapply subst_preservation_; eauto using typing_lc.
  fast_set_solver!!.
Qed.

Lemma kinding_subst_preservation Σ x s τ' Γ τ κ :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ τ :: κ ->
  Σ; Γ ⊢ s : τ' ->
  x ∉ fv τ' ∪ dom aset Γ ∪ tctx_fv Γ ->
  Σ; Γ ⊢ {x↦s}τ :: κ.
Proof.
  intros.
  rewrite <- (subst_tctx_fresh Γ x s) by fast_set_solver!!.
  eapply subst_preservation_; eauto using typing_lc.
  fast_set_solver!!.
Qed.

Lemma open_preservation_alt Σ x s τ' Γ e τ :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ e^x : τ ->
  Σ; Γ ⊢ s : τ' ->
  x ∉ fv τ' ∪ fv e ∪ dom aset Γ ∪ tctx_fv Γ ->
  Σ; Γ ⊢ e^s : {x↦s}τ.
Proof.
  intros.
  rewrite (subst_intro e s x) by fast_set_solver!!.
  eapply subst_preservation; eauto.
  fast_set_solver!!.
Qed.

Lemma open_preservation Σ x s τ' Γ e τ :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ e^x : τ^x ->
  Σ; Γ ⊢ s : τ' ->
  x ∉ fv τ' ∪ fv e ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ->
  Σ; Γ ⊢ e^s : τ^s.
Proof.
  intros.
  rewrite (subst_intro e s x) by fast_set_solver!!.
  rewrite (subst_intro τ s x) by fast_set_solver!!.
  eapply subst_preservation; eauto.
  fast_set_solver!!.
Qed.

Lemma kinding_open_preservation Σ x s τ' Γ τ κ :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ τ^x :: κ ->
  Σ; Γ ⊢ s : τ' ->
  x ∉ fv τ' ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ->
  Σ; Γ ⊢ τ^s :: κ.
Proof.
  intros.
  rewrite (subst_intro τ s x) by fast_set_solver!!.
  eapply kinding_subst_preservation; eauto.
  fast_set_solver!!.
Qed.

Lemma open_preservation_lc Σ x s τ' Γ e τ :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ e^x : τ ->
  Σ; Γ ⊢ s : τ' ->
  x ∉ fv τ' ∪ fv e ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ->
  Σ; Γ ⊢ e^s : τ.
Proof.
  intros Hwf H. intros.
  erewrite <- (open_lc_intro τ s) by eauto using typing_type_lc.
  erewrite <- (open_lc_intro τ x) in H by eauto using typing_type_lc.
  eapply open_preservation; eauto.
Qed.

(** * Other lemmas *)

(** Types of well-typed expressions are well-kinded *)
Lemma regularity Σ Γ e τ :
  gctx_wf Σ ->
  Σ; Γ ⊢ e : τ ->
  exists κ, Σ; Γ ⊢ τ :: κ.
Proof.
  intros Hwf.
  induction 1; simp_hyps; eauto using kinding;
    try (apply_gctx_wf; eauto using kinding_weakening_empty);
    apply_kind_inv; simpl_cofin?; simp_hyps;
    try first [ eexists; typing_kinding_intro; eauto; fast_set_solver!!
              (* Types may be opened. *)
              | eexists; qauto use: kinding_open_preservation
                               solve: fast_set_solver!! ].

  (* Boxed injection case *)
  sfirstorder use: otval_well_kinded, ovalty_elim.
Qed.

Ltac apply_regularity :=
  select! (_; _ ⊢ _ : _)
        (fun H => dup_hyp H (fun H => eapply regularity in H;
                                  [ simp_hyp H | eauto ])).

(** Oblivious type can not be typed. *)
Lemma obliv_type_not_typed Σ X τ e Γ τ' :
  gctx_wf Σ ->
  Σ !! X = Some (DOADT τ e) ->
  Σ; Γ ⊢ gvar X : τ' ->
  False.
Proof.
  intros.
  apply_type_inv.
  scongruence.
Qed.

(** We can substitute with an equivalent type in the typing contexts. *)
Lemma subst_equiv_ Σ x τ1 τ2 :
  gctx_wf Σ ->
  Σ ⊢ τ1 ≡ τ2 ->
  (forall Γ' e τ,
      Σ; Γ' ⊢ e : τ ->
      forall Γ κ',
        Γ' = <[x:=τ1]>Γ ->
        x ∉ dom aset Γ ->
        Σ; Γ ⊢ τ2 :: κ' ->
        Σ; (<[x:=τ2]>Γ) ⊢ e : τ) /\
  (forall Γ' τ κ,
      Σ; Γ' ⊢ τ :: κ ->
      forall Γ κ',
        Γ' = <[x:=τ1]>Γ ->
        x ∉ dom aset Γ ->
        Σ; Γ ⊢ τ2 :: κ' ->
        Σ; (<[x:=τ2]>Γ) ⊢ τ :: κ).
Proof.
  intros Hwf Heq.
  apply typing_kinding_mutind; intros; subst;
    (* [TFVar] is the key base case. Prove it later *)
    try lazymatch goal with
        | |- _; _ ⊢ fvar _ : _ =>
          shelve
        end;
    try solve [ econstructor; eauto ];
    simpl_cofin?;
    repeat
      match goal with
      | H : forall _ _, _ -> _ -> _ -> _ |- _ =>
        efeed specialize H;
          [ try reflexivity; rewrite insert_commute by fast_set_solver!!; reflexivity
          | fast_set_solver!!
          | eauto using kinding_weakening_insert
          | .. ];
          try rewrite insert_commute in H by fast_set_solver!!
      end;
    try apply_regularity;
    try eapply TConv;
      repeat
        (eauto;
         lazymatch goal with
         | |- _; _ ⊢ _ : _ =>
           typing_intro
         | |- _; _ ⊢ _^_ :: _ =>
           eapply kinding_open_preservation
         | |- _; _ ⊢ _ :: _ =>
           kinding_intro
         | |- _ ⊢ _ ≡ _ =>
           equiv_naive_solver
         | |- _ ∉ _ =>
           shelve
         end).

  Unshelve.

  (* [TFVar] *)
  match goal with
  | |- _; _ ⊢ fvar ?x' : _ => destruct (decide (x' = x))
  end; subst;
    try solve [ econstructor; simplify_map_eq; eauto ].
  simplify_map_eq.
  eapply TConv; eauto.
  typing_intro; simplify_map_eq; eauto.
  eauto using kinding_weakening_insert.
  equiv_naive_solver.

  all : try fast_set_solver!!; simpl_fv; fast_set_solver!!.
Qed.

Lemma subst_equiv Σ Γ e τ κ' x τ1 τ2 :
  gctx_wf Σ ->
  Σ; (<[x:=τ1]>Γ) ⊢ e : τ ->
  Σ; Γ ⊢ τ2 :: κ' ->
  Σ ⊢ τ1 ≡ τ2 ->
  x ∉ dom aset Γ ->
  Σ; (<[x:=τ2]>Γ) ⊢ e : τ.
Proof.
  hauto use: subst_equiv_.
Qed.

Lemma kinding_subst_equiv Σ Γ τ κ κ' x τ1 τ2 :
  gctx_wf Σ ->
  Σ; (<[x:=τ1]>Γ) ⊢ τ :: κ ->
  Σ; Γ ⊢ τ2 :: κ' ->
  Σ ⊢ τ1 ≡ τ2 ->
  x ∉ dom aset Γ ->
  Σ; (<[x:=τ2]>Γ) ⊢ τ :: κ.
Proof.
  hauto use: subst_equiv_.
Qed.

(** * Preservation *)

(** The combined preservation theorems for parallel reduction. *)
Lemma pared_preservation_ Σ :
  gctx_wf Σ ->
  (forall Γ e τ,
      Σ; Γ ⊢ e : τ ->
      forall e', Σ ⊢ e ==>! e' ->
            Σ; Γ ⊢ e' : τ) /\
  (forall Γ τ κ,
      Σ; Γ ⊢ τ :: κ ->
      forall τ', Σ ⊢ τ ==>! τ' ->
            Σ; Γ ⊢ τ' :: κ).
Proof.
  intros Hwf.
  apply typing_kinding_mutind; intros; subst;
    (* Inversion on parallel reduction. *)
    repeat apply_pared_inv;
    simplify_eq;
    try apply_gctx_wf;
    simpl_cofin?;
    (* Solve some trivial cases. *)
    try solve [ lazymatch goal with
                | H : _ !! ?X = Some (DOADT _ _), H' : _; _ ⊢ gvar ?X : _ |- _ =>
                  (* It is not possible to type oblivious type *)
                  exfalso; eauto using obliv_type_not_typed
                | H : _ !! _ = Some (DFun _ _) |- _ =>
                  eauto using weakening_empty
                end
              | try case_ite_expr;
                simp_hyps;
                repeat
                  (eauto;
                   lazymatch goal with
                   | |- _; _ ⊢ _ : ?τ =>
                     first [ is_evar τ | econstructor ]
                   | |- _; _ ⊢ _ :: ?κ =>
                     first [ is_evar κ | econstructor ]
                   end)];
    (* Now turn to the more interesting cases. *)
    (* Derive some equivalence for later convenience. *)
    try select! (_ ⊢ _ ==>! _)
        (fun H => dup_hyp H (fun H => apply pared_equiv_pared in H));
    (* Derive well-kindedness from typing. *)
    try apply_regularity;
    (* Apply inversion lemmas for typing and kinding. *)
    apply_kind_inv;
    apply_type_inv;
    (* Instantiate induction hypotheses. *)
    repeat
      match goal with
      | H : forall _, _ ⊢ _ ==>! _ -> _ |- _ =>
        efeed specialize H; [
          solve [ repeat
                    (eauto;
                     lazymatch goal with
                     | |- _ ⊢ ?e ==>! _ =>
                       first [ head_constructor e; pared_intro
                             | eapply pared_open1
                             | lcrefl ]
                     | |- lc _ => eauto using kinding_lc
                     | |- _ ∉ _ => shelve
                     end) ]
         |];
        try apply_type_inv H;
        try apply_kind_inv H
      end;
    (* Derive equivalence for the sub-expressions. *)
    try simpl_whnf_equiv;
    (* We may have cofinite quantifiers that are generated by the inversion
    lemmas. *)
    simpl_cofin?;
    simplify_eq;
    (* Main solver. *)
    repeat
      (try case_ite_expr;
       eauto;
       match goal with
       (* Replace the types in context with an equivalent ones. *)
       | |- _; (<[_:=_]>_) ⊢ _ : _ =>
         eapply subst_equiv
       | |- _; (<[_:=_]>_) ⊢ _ :: _ =>
         eapply kinding_subst_equiv
       (* Apply substitution/open lemmas. *)
       | H : _; _ ⊢ ?e^(fvar _) : ?τ |- _; _ ⊢ ?e^_ : ?τ =>
         eapply open_preservation_lc
       | H : _; _ ⊢ ?e^(fvar _) : _^(fvar _) |- _; _ ⊢ ?e^_ : _ =>
         eapply open_preservation
       (* This is for the dependent case expression. *)
       | H : _; _ ⊢ ?e^(fvar _) : _^_ |- _; _ ⊢ ?e^_ : _ =>
         eapply open_preservation_alt
       | H : _; (<[_:=_]>?Γ) ⊢ ?e^(fvar _) :: _ |- _; ?Γ ⊢ ?e^_ :: _ =>
         eapply kinding_open_preservation
       (* Apply typing rules. *)
       | |- _; _ ⊢ _ : _ =>
         typing_intro
       | |- _; _ ⊢ _ : ?τ =>
         assert_fails is_evar τ; eapply TConv
       (* Apply kinding rules. *)
       | |- _; _ ⊢ _ :: _ =>
         kinding_intro
       (* Solve equivalence. *)
       | |- _ ⊢ _ ≡ _ =>
         try case_split; equiv_naive_solver
       | |- _ ⊢ _ ≡ _ =>
         apply_pared_equiv_congr
       | |- _ ⊢ _^_ ≡ _^_ =>
         eapply pared_equiv_open1; simpl_cofin?
       | |- _ ⊢ _^_ ≡ _^_ =>
         eapply pared_equiv_open
       (* Solve other side conditions. *)
       | |- lc _ =>
         eauto using lc, open_respect_lc, typing_type_lc, typing_lc, kinding_lc
       | |- _ ∉ _ => shelve
       end).

  (* The case when oblivious injection steps to boxed injection. *)
  hauto lq: on ctrs: ovalty inv: otval use: ovalty_intro.

  (* These equivalence are generated by the case when the case discriminee takes
  a step. *)

  1-2:
  rewrite subst_open_distr by eauto using typing_lc; simpl;
    rewrite decide_True by auto;
    rewrite !subst_fresh by shelve;
    let xauto := eauto using lc, open_respect_lc, typing_lc, kinding_lc
    in eapply pared_equiv_open1; simpl_cofin?; xauto;
       apply_pared_equiv_congr; xauto;
       equiv_naive_solver.

  (* These 4 cases are generated by the case when oblivious case analysis steps
  to oblivious condition. *)
  1-4 :
    repeat
      match goal with
      | H : ovalty ?e _ |- _ =>
        head_constructor e; sinvert H
      end;
    select! (ovalty _ _) (fun H => apply ovalty_elim in H; simp_hyp H);
    eapply TConv;
    [ eauto using weakening, map_empty_subseteq
    | eauto
    | equiv_naive_solver ].

  (* The case when we apply oblivious type to its argument: [SAppOADT] *)
  eapply kinding_open_preservation; eauto; try set_shelve.
  eapply kinding_weakening; eauto.
  rewrite insert_union_singleton_l.
  apply map_union_subseteq_l.

  Unshelve.

  all : fast_set_solver!!.
Qed.

Lemma pared_preservation Σ Γ e e' τ :
  gctx_wf Σ ->
  Σ; Γ ⊢ e : τ ->
  Σ ⊢ e ==>! e' ->
  Σ; Γ ⊢ e' : τ.
Proof.
  hauto use: pared_preservation_.
Qed.

Lemma pared_kinding_preservation Σ Γ τ τ' κ :
  gctx_wf Σ ->
  Σ; Γ ⊢ τ :: κ ->
  Σ ⊢ τ ==>! τ' ->
  Σ; Γ ⊢ τ' :: κ.
Proof.
  hauto use: pared_preservation_.
Qed.

(** The preservation theorem for [step]. *)
Theorem preservation Σ Γ e e' τ :
  gctx_wf Σ ->
  Σ; Γ ⊢ e : τ ->
  Σ ⊨ e -->! e' ->
  Σ; Γ ⊢ e' : τ.
Proof.
  hauto use: pared_preservation, pared_step, typing_lc.
Qed.

Theorem kinding_preservation Σ Γ τ τ' κ :
  gctx_wf Σ ->
  Σ; Γ ⊢ τ :: κ ->
  Σ ⊨ τ -->! τ' ->
  Σ; Γ ⊢ τ' :: κ.
Proof.
  hauto use: pared_kinding_preservation, pared_step, kinding_lc.
Qed.
