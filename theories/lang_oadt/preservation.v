From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.
From oadt Require Import lang_oadt.infrastructure.
From oadt Require Import lang_oadt.properties.
From oadt Require Import lang_oadt.admissible.

(** * Preservation *)
(** The preservation metatheorem. *)

Import syntax.notations.
Import semantics.notations.
Import typing.notations.

Implicit Types (x X y Y : atom) (L : aset).
Implicit Types (b : bool).

#[local]
Coercion EFVar : atom >-> expr.

(** ** Weakening lemmas  *)
Lemma weakening_ Σ :
  (forall Φ Γ e τ,
    Σ; Φ; Γ ⊢ e : τ ->
    forall Σ' Φ' Γ',
      Σ ⊆ Σ' ->
      Φ ⊆ Φ' ->
      Γ ⊆ Γ' ->
      Σ'; Φ'; Γ' ⊢ e : τ) /\
  (forall Φ Γ τ κ,
    Σ; Φ; Γ ⊢ τ :: κ ->
    forall Σ' Φ' Γ',
      Σ ⊆ Σ' ->
      Φ ⊆ Φ' ->
      Γ ⊆ Γ' ->
      Σ'; Φ'; Γ' ⊢ τ :: κ).
Proof.
  apply typing_kinding_mutind; intros; subst;
    try solve [econstructor; eauto using insert_mono, expr_equiv_weakening];
    try qauto l: on use: lookup_weaken ctrs: typing, kinding.

  (* [if] and [case] case *)
  all: econstructor; eauto; simpl_cofin?;
    auto_apply; eauto using insert_mono; fast_set_solver!!.
Qed.

Lemma weakening Σ Φ Γ Σ' Φ' Γ' e τ :
  Σ; Φ; Γ ⊢ e : τ ->
  Σ ⊆ Σ' ->
  Φ ⊆ Φ' ->
  Γ ⊆ Γ' ->
  Σ'; Φ'; Γ' ⊢ e : τ.
Proof.
  hauto use: weakening_.
Qed.

Lemma kinding_weakening Σ Φ Γ Σ' Φ' Γ' τ κ :
  Σ; Φ; Γ ⊢ τ :: κ ->
  Σ ⊆ Σ' ->
  Φ ⊆ Φ' ->
  Γ ⊆ Γ' ->
  Σ'; Φ'; Γ' ⊢ τ :: κ.
Proof.
  hauto use: weakening_.
Qed.

Lemma weakening_empty Σ Φ Γ e τ :
  Σ; ∅; ∅ ⊢ e : τ ->
  Σ; Φ; Γ ⊢ e : τ.
Proof.
  eauto using weakening, map_empty_subseteq with set_solver.
Qed.

Lemma kinding_weakening_empty Σ Φ Γ τ κ :
  Σ; ∅; ∅ ⊢ τ :: κ ->
  Σ; Φ; Γ ⊢ τ :: κ.
Proof.
  eauto using kinding_weakening, map_empty_subseteq with set_solver.
Qed.

Lemma weakening_insert Σ Φ Γ e τ τ' x :
  Σ; Φ; Γ ⊢ e : τ ->
  x ∉ dom aset Γ ->
  Σ; Φ; (<[x:=τ']>Γ) ⊢ e : τ.
Proof.
  eauto using weakening, insert_fresh_subseteq.
Qed.

Lemma kinding_weakening_insert Σ Φ Γ τ τ' κ x :
  Σ; Φ; Γ ⊢ τ :: κ ->
  x ∉ dom aset Γ ->
  Σ; Φ; (<[x:=τ']>Γ) ⊢ τ :: κ.
Proof.
  eauto using kinding_weakening, insert_fresh_subseteq.
Qed.

Lemma weakening_actx_insert Σ Φ Γ e e1 e2 τ :
  Σ; Φ; Γ ⊢ e : τ ->
  Σ; ({{e1 ≡ e2}}Φ); Γ ⊢ e : τ.
Proof.
  intros. eapply weakening; eauto.
  fast_set_solver!!.
Qed.

(** ** Well-formedness of [gctx] *)

Lemma gdef_typing_wf D Σ' Σ :
  Σ' =[ D ]=> Σ ->
  gctx_wf Σ' ->
  gctx_wf Σ.
Proof.
  inversion 1; subst; intros Hd X' D Hm.
  all:
    destruct (decide (X' = X)); subst; simpl_map;
    [ inversion Hm; subst
    | apply Hd in Hm; case_split; simp_hyps ];
    eauto 10 using weakening, kinding_weakening, insert_subseteq.
Qed.

Lemma gdefs_typing_wf_ Ds Σ' Σ :
  Σ' ={ Ds }=> Σ ->
  gctx_wf Σ' ->
  gctx_wf Σ.
Proof.
  induction 1; eauto using gdef_typing_wf.
Qed.

Lemma gdefs_typing_wf Ds Σ :
  ∅ ={ Ds }=> Σ ->
  gctx_wf Σ.
Proof.
  intros. eapply gdefs_typing_wf_; eauto.
  unfold gctx_wf, map_Forall.
  intros. simplify_map_eq.
Qed.

(** ** Substitution lemma *)

Lemma subst_tctx_typing_kinding_ Σ x s :
  gctx_wf Σ ->
  (forall Φ Γ e τ,
      Σ; Φ; Γ ⊢ e : τ ->
      x ∉ fv τ ∪ dom aset Γ ->
      Σ; Φ; ({x↦s} <$> Γ) ⊢ e : τ) /\
  (forall Φ Γ τ κ,
      Σ; Φ; Γ ⊢ τ :: κ ->
      x ∉ dom aset Γ ->
      Σ; Φ; ({x↦s} <$> Γ) ⊢ τ :: κ).
Proof.
  intros Hwf.
  apply typing_kinding_mutind; intros; subst; simpl in *;
    econstructor; eauto;
      simpl_cofin?;
      (* Try to apply induction hypotheses. *)
      lazymatch goal with
      | |- _; _; ?Γ ⊢ ?e : ?τ =>
        auto_apply || lazymatch goal with
                      | H : _ -> _; _; ?Γ' ⊢ e : τ |- _ =>
                        replace Γ with Γ'; [auto_apply |]
                      end
      | |- _; _; ?Γ ⊢ ?τ :: _ =>
        auto_apply || lazymatch goal with
                      | H : _ -> _; _; ?Γ' ⊢ τ :: _ |- _ =>
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

Lemma subst_tctx_typing Σ Φ Γ e τ x s :
  gctx_wf Σ ->
  Σ; Φ; Γ ⊢ e : τ ->
  x ∉ fv τ ∪ dom aset Γ ->
  Σ; Φ; ({x↦s} <$> Γ) ⊢ e : τ.
Proof.
  qauto use: subst_tctx_typing_kinding_.
Qed.

(* The condition [lc s] might not be necessary. *)
Lemma subst_actx_typing_kinding_ Σ x s :
  gctx_wf Σ ->
  lc s ->
  (forall Φ Γ e τ,
      Σ; Φ; Γ ⊢ e : τ ->
      x ∉ fv τ ∪ dom aset Γ ->
      Σ; (actx_map ({x↦s}) Φ); Γ ⊢ e : τ) /\
  (forall Φ Γ τ κ,
      Σ; Φ; Γ ⊢ τ :: κ ->
      x ∉ dom aset Γ ->
      Σ; (actx_map ({x↦s}) Φ); Γ ⊢ τ :: κ).
Proof.
  intros Hwf Hlc.
  apply typing_kinding_mutind; intros; subst; simpl in *;
    econstructor; eauto;
      simpl_cofin?;
      (* Try to apply induction hypotheses. *)
      lazymatch goal with
      | H : _ -> _; _; _ ⊢ ?e : _ |- _; _; _ ⊢ ?e : _ =>
        first [ apply H | relax_actx by shelve; apply H ]
      | |- _; _; _ ⊢ _ :: _ =>
        auto_apply
      | _ => idtac
      end; eauto;
        (* Do set solving later *)
        try lazymatch goal with
            | |- _ ∉ _ => shelve
            | |- _ <> _ => shelve
            end.

  (* [TConv] *)
  apply_eq expr_equiv_subst1; eauto;
    rewrite subst_fresh by shelve; reflexivity.

  Unshelve.

  (* Equivalence of assumptions context *)
  all : try lazymatch goal with
            | |- _ ≡ _ => idtac
            | |- _ => shelve
            end.

  all : rewrite actx_map_insert; rewrite !subst_fresh by shelve; reflexivity.

  Unshelve.

  (* Set solving *)
  all : try fast_set_solver!!; simpl_fv; fast_set_solver!!.
Qed.

Lemma subst_actx_typing Σ Φ Γ e τ x s :
  gctx_wf Σ ->
  lc s ->
  Σ; Φ; Γ ⊢ e : τ ->
  x ∉ fv τ ∪ dom aset Γ ->
  Σ; (actx_map ({x↦s}) Φ); Γ ⊢ e : τ.
Proof.
  qauto use: subst_actx_typing_kinding_.
Qed.

(* Note that [lc s] is not needed, and it is here only for convenience. I will
drop it in the actual lemma. *)
Lemma subst_preservation_ Σ x s τ' :
  gctx_wf Σ ->
  lc s ->
  (forall Φ Γ' e τ,
      Σ; Φ; Γ' ⊢ e : τ ->
      forall Γ,
        Γ' = <[x:=τ']>Γ ->
        x ∉ fv τ' ∪ dom aset Γ ->
        Σ; Φ; Γ ⊢ s : τ' ->
        Σ; (actx_map ({x↦s}) Φ); ({x↦s} <$> Γ) ⊢ {x↦s}e : {x↦s}τ) /\
  (forall Φ Γ' τ κ,
      Σ; Φ; Γ' ⊢ τ :: κ ->
      forall Γ,
        Γ' = <[x:=τ']>Γ ->
        x ∉ fv τ' ∪ dom aset Γ ->
        Σ; Φ; Γ ⊢ s : τ' ->
        Σ; (actx_map ({x↦s}) Φ); ({x↦s} <$> Γ) ⊢ {x↦s}τ :: κ).
Proof.
  intros Hwf Hlc.
  apply typing_kinding_mutind; intros; subst; simpl in *;
    (* First we normalize the typing and kinding judgments so they are ready
    for applying typing and kinding rules to. *)
    rewrite ?subst_open_distr by assumption;
    rewrite ?subst_ite_distr;
    try lazymatch goal with
        | |- _; _; _ ⊢ [inj@_< ?ω > _] : {_↦_}?ω =>
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
            rewrite <- ?subst_open_comm by (try assumption; shelve);
            try lazymatch Γ with
                | <[_:=_]>({_↦_} <$> _) =>
                  rewrite <- fmap_insert
                end;
            try relax_actx by shelve;
            (* Apply one of the induction hypotheses. *)
            auto_eapply in
      (* Make sure we complete handling the typing and kinding judgments first.
      Otherwise some existential variables may have undesirable
      instantiation. *)
      lazymatch goal with
      | |- _; _; ?Γ ⊢ _ : _ => go Γ
      | |- _; _; ?Γ ⊢ _ :: _ => go Γ
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
               | |- _; _ ⊢ _ ≡ _ =>
                 apply expr_equiv_subst1
               | |- (_ <$> _) !! _ = Some _ =>
                 simplify_map_eq
               | |- _; _; (<[_:=_]>_) ⊢ _ : _ =>
                 apply weakening_insert
               | |- _; ({{_ ≡ _}}_); _ ⊢ _ : _ =>
                 eapply weakening_actx_insert
               | |- Some _ = Some _ =>
                 try reflexivity; repeat f_equal
               | |- _ = {_↦_} _ =>
                 rewrite subst_fresh
               | H : ?Σ !! ?x = Some _ |- ?Σ !! ?x = Some _ =>
                 rewrite H
               end;
        eauto.

  Unshelve.

  (* Case [fvar x] *)
  simplify_map_eq.
  simpl_fv.
  rewrite subst_fresh by shelve.
  apply subst_tctx_typing; eauto.
  apply subst_actx_typing; eauto.

  (* Equivalence of assumptions context *)
  all : try lazymatch goal with
            | |- _ ≡ _ => idtac
            | |- _ => shelve
            end.

  all : rewrite actx_map_insert; try reflexivity;
    repeat f_equiv; simpl; case_decide; try reflexivity;
      exfalso; fast_set_solver.

  Unshelve.

  (* Set solving *)
  all : try fast_set_solver!!; simpl_fv; fast_set_solver*!!.
Qed.

(** The actual substitution lemma *)
Lemma subst_preservation Σ Φ x s τ' Γ e τ :
  gctx_wf Σ ->
  Σ; Φ; (<[x:=τ']>Γ) ⊢ e : τ ->
  Σ; Φ; Γ ⊢ s : τ' ->
  x ∉ fv τ' ∪ dom aset Γ ∪ tctx_fv Γ ∪ actx_fv Φ ->
  Σ; Φ; Γ ⊢ {x↦s}e : {x↦s}τ.
Proof.
  intros.
  rewrite <- (subst_tctx_fresh Γ x s) by fast_set_solver!!.
  rewrite <- (subst_actx_fresh Φ x s) by fast_set_solver!!.
  eapply subst_preservation_; eauto using typing_lc.
  fast_set_solver!!.
Qed.

Lemma kinding_subst_preservation Σ Φ x s τ' Γ τ κ :
  gctx_wf Σ ->
  Σ; Φ; (<[x:=τ']>Γ) ⊢ τ :: κ ->
  Σ; Φ; Γ ⊢ s : τ' ->
  x ∉ fv τ' ∪ dom aset Γ ∪ tctx_fv Γ ∪ actx_fv Φ ->
  Σ; Φ; Γ ⊢ {x↦s}τ :: κ.
Proof.
  intros.
  rewrite <- (subst_tctx_fresh Γ x s) by fast_set_solver!!.
  rewrite <- (subst_actx_fresh Φ x s) by fast_set_solver!!.
  eapply subst_preservation_; eauto using typing_lc.
  fast_set_solver!!.
Qed.

Lemma subst_preservation_alt Σ Φ x s τ' Γ e e1 e2 τ :
  gctx_wf Σ ->
  Σ; ({{e1 ≡ e2}}Φ); (<[x:=τ']>Γ) ⊢ e : τ ->
  Σ; Φ; Γ ⊢ s : τ' ->
  x ∉ fv τ' ∪ dom aset Γ ∪ tctx_fv Γ ∪ actx_fv Φ ->
  Σ; ({{({x↦s}e1) ≡ ({x↦s}e2)}}Φ); Γ ⊢ {x↦s}e : {x↦s}τ.
Proof.
  intros.
  rewrite <- (subst_tctx_fresh Γ x s) by fast_set_solver!!.
  relax_actx by shelve.
  eapply subst_preservation_; eauto using typing_lc, weakening_actx_insert.
  fast_set_solver!!.

  Unshelve.
  rewrite actx_map_insert. f_equiv.
  rewrite subst_actx_fresh by fast_set_solver!!. reflexivity.
Qed.

Lemma open_preservation Σ Φ x s τ' Γ e τ :
  gctx_wf Σ ->
  Σ; Φ; (<[x:=τ']>Γ) ⊢ e^x : τ^x ->
  Σ; Φ; Γ ⊢ s : τ' ->
  x ∉ fv τ' ∪ fv e ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ∪ actx_fv Φ ->
  Σ; Φ; Γ ⊢ e^s : τ^s.
Proof.
  intros.
  rewrite (subst_intro e s x) by fast_set_solver!!.
  rewrite (subst_intro τ s x) by fast_set_solver!!.
  eapply subst_preservation; eauto.
  fast_set_solver!!.
Qed.

Lemma kinding_open_preservation Σ Φ x s τ' Γ τ κ :
  gctx_wf Σ ->
  Σ; Φ; (<[x:=τ']>Γ) ⊢ τ^x :: κ ->
  Σ; Φ; Γ ⊢ s : τ' ->
  x ∉ fv τ' ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ∪ actx_fv Φ ->
  Σ; Φ; Γ ⊢ τ^s :: κ.
Proof.
  intros.
  rewrite (subst_intro τ s x) by fast_set_solver!!.
  eapply kinding_subst_preservation; eauto.
  fast_set_solver!!.
Qed.

Lemma open_preservation_lc Σ Φ x s τ' Γ e τ :
  gctx_wf Σ ->
  Σ; Φ; (<[x:=τ']>Γ) ⊢ e^x : τ ->
  Σ; Φ; Γ ⊢ s : τ' ->
  x ∉ fv τ' ∪ fv e ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ∪ actx_fv Φ ->
  Σ; Φ; Γ ⊢ e^s : τ.
Proof.
  intros Hwf H. intros.
  erewrite <- (open_lc_intro τ s) by eauto using typing_type_lc.
  erewrite <- (open_lc_intro τ x) in H by eauto using typing_type_lc.
  eapply open_preservation; eauto.
Qed.

Lemma open_preservation_alt Σ Φ x s τ' Γ e e1 e2 τ :
  gctx_wf Σ ->
  Σ; ({{e1 ≡ e2}}Φ); (<[x:=τ']>Γ) ⊢ e^x : τ^x ->
  Σ; Φ; Γ ⊢ s : τ' ->
  x ∉ fv τ' ∪ fv e ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ∪ actx_fv Φ ->
  Σ; ({{({x↦s}e1) ≡ ({x↦s}e2)}}Φ); Γ ⊢ e^s : τ^s.
Proof.
  intros.
  rewrite (subst_intro e s x) by fast_set_solver!!.
  rewrite (subst_intro τ s x) by fast_set_solver!!.
  eapply subst_preservation_alt; eauto.
  fast_set_solver!!.
Qed.

Lemma open_preservation_lc_alt Σ Φ x s τ' Γ e e1 e2 τ :
  gctx_wf Σ ->
  Σ; ({{e1 ≡ e2}}Φ); (<[x:=τ']>Γ) ⊢ e^x : τ ->
  Σ; Φ; Γ ⊢ s : τ' ->
  x ∉ fv τ' ∪ fv e ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ∪ actx_fv Φ ->
  Σ; ({{({x↦s}e1) ≡ ({x↦s}e2)}}Φ); Γ ⊢ e^s : τ.
Proof.
  intros Hwf H. intros.
  erewrite <- (open_lc_intro τ s) by eauto using typing_type_lc.
  erewrite <- (open_lc_intro τ x) in H by eauto using typing_type_lc.
  eapply open_preservation_alt; eauto.
Qed.

(** Types of well-typed expressions are well-kinded *)
Lemma regularity Σ Φ Γ e τ :
  gctx_wf Σ ->
  Σ; Φ; Γ ⊢ e : τ ->
  exists κ, Σ; Φ; Γ ⊢ τ :: κ.
Proof.
  intros Hwf.
  induction 1; simp_hyps; eauto with kinding;
    try match goal with
        | H : _ !! _ = _ |- _ =>
          apply Hwf in H; simp_hyps; eauto using kinding_weakening_empty
        end;
    apply_kind_inv; simpl_cofin?; simp_hyps;
    try first [ eexists; typing_kinding_intro; eauto; fast_set_solver!!
              (* Types may be opened. *)
              | eexists; qauto use: kinding_open_preservation
                               solve: fast_set_solver!! ].

  (* Boxed injection case *)
  sfirstorder use: otval_well_kinded, ovalty_elim.
Qed.

(** Oblivious type can not be typed. *)
Lemma obliv_type_not_typed Σ Φ X τ e Γ τ' :
  Σ !! X = Some (DOADT τ e) ->
  Σ; Φ; Γ ⊢ gvar X : τ' ->
  False.
Proof.
  intros.
  apply_type_inv.
  scongruence.
Qed.

Lemma typing_actx_cut_subst Σ Φ Γ e e' e1 e2 τ :
  Σ; ({{e1 ≡ e'}}Φ); Γ ⊢ e : τ ->
  Σ; Φ ⊢ e1 ≡ e2 ->
  Σ; ({{e2 ≡ e'}}Φ); Γ ⊢ e : τ.
Proof.
  intros.
  eapply typing_actx_cut; eauto.
  rewrite set_insert_comm.
  eauto using weakening_actx_insert.
  etrans.
  - eauto using expr_equiv_weakening_actx_insert.
  - eauto using expr_equiv_actx_id.
Qed.

(** ** Preservation *)

Theorem pared_preservation_ Σ :
  gctx_wf Σ ->
  (forall Φ Γ e τ,
      Σ; Φ; Γ ⊢ e : τ ->
      Φ = ∅ ->
      (* can i fix this ∅ -> Φ *)
      forall e', Σ; Φ ⊢ e ==>! e' ->
            Σ; Φ; Γ ⊢ e' : τ) /\
  (forall Φ Γ τ κ,
      Σ; Φ; Γ ⊢ τ :: κ ->
      Φ = ∅ ->
      forall τ', Σ; Φ ⊢ τ ==>! τ' ->
            Σ; Φ; Γ ⊢ τ' :: κ).
Proof.
  intros Hwf.
  apply typing_kinding_mutind; intros; subst; simp_hyps.
  9: {
    lazymatch goal with
    | H : _; _ ⊢ ?e ==>! _ |- _ =>
      head_constructor e;
      (* try match goal with *)
      (*     | H' : _ -> forall _, _; _ ⊢ e ==>! _ -> _ |- _ => *)
      (*       dup_hyp H (fun H => apply H' in H); *)
      (*         [ clear H' | lattice_naive_solver ] *)
      (*     | H' : forall _, _; _ ⊢ e ==>! _ -> _ |- _ => *)
      (*       dup_hyp H (fun H => apply H' in H); *)
      (*         clear H' *)
      (*     end; *)
      sinvert H
    end; simplify_eq;
    try match goal with
        | H : _ ∈ ∅ |- _ => elim ((not_elem_of_empty _ H))
        end.
    all:
    try solve [ try case_ite_expr;
                simp_hyps;
                repeat
                  (eauto;
                   lazymatch goal with
                   | |- _; _; _ ⊢ _ : ?τ =>
                     first [ is_evar τ | econstructor ]
                   | |- _; _; _ ⊢ _ :: ?κ =>
                     first [ is_evar κ | econstructor ]
                   end) ].
    all:
    try select! (_; _; _ ⊢ _ : _)
          (fun H => dup_hyp H (fun H => eapply regularity in H;
                                    [ simp_hyp H | eauto ])).
    all:
    (* Apply inversion lemmas for typing and kinding. *)
    apply_type_inv*;
    apply_kind_inv*;
    (* Derive equivalence for the sub-expressions. *)
    try simpl_whnf_equiv;
    (* We may have cofinite quantifiers that are generated by the inversion *)
(*     lemmas. *)
    simpl_cofin?;
    simplify_eq.

  - hauto use: typing_actx_cut_refl.

  (* The discriminee of [if] takes a step *)
  - econstructor. qauto ctrs: typing use: typing_actx_cut_subst, expr_equiv_step.
    admit.
    admit.
    admit.
  }
  Abort.

(** The combined preservation theorems for expressions and types. *)
Theorem preservation_ Σ :
  gctx_wf Σ ->
  (forall Φ Γ e τ,
      Σ; Φ; Γ ⊢ e : τ ->
      Φ = ∅ ->
      forall e', Σ ⊨ e -->! e' ->
            Σ; Φ; Γ ⊢ e' : τ) /\
  (forall Φ Γ τ κ,
      Σ; Φ; Γ ⊢ τ :: κ ->
      Φ = ∅ ->
      forall τ', Σ ⊨ τ -->! τ' ->
            Σ; Φ; Γ ⊢ τ' :: κ).
Proof.
  intros Hwf.
  apply typing_kinding_mutind; intros; subst;
    (* Repeatedly perform inversion on [step], but only if we know how to step
    it (i.e. the initial expression has a constructor for its head). *)
    repeat
      (lazymatch goal with
       | H : _ ⊨ ?e -->! _ |- _ =>
         head_constructor e;
         (* Try to apply induction hypotheses to the [step] relation first
         before we invert and remove it. *)
         try match goal with
             | H' : _ -> forall _, _ ⊨ e -->! _ -> _ |- _ =>
               dup_hyp H (fun H => apply H' in H);
               (* Discharge the side condition for the kinding induction
               hypotheses. *)
               [ clear H' | lattice_naive_solver ]
             | H' : forall _, _ ⊨ e -->! _ -> _ |- _ =>
               dup_hyp H (fun H => apply H' in H);
               clear H'
             end;
         sinvert H
       end;
       (* Try to do inversion on the evaluation contexts. *)
       try select (ectx _) (fun H => sinvert H);
       simplify_eq);
    (* Try to simplify and solve some cases involving global context. *)
    try match goal with
        | H : _ !! ?X = Some (DOADT _ _), H' : _; _; _ ⊢ gvar ?X : _ |- _ =>
          (* It is not possible to type oblivious type *)
          exfalso; eauto using obliv_type_not_typed
        | Hwf : gctx_wf ?Σ, H : ?Σ !! _ = Some _ |- _ =>
          dup_hyp H (fun H => apply Hwf in H; simp_hyp H);
            try hauto use: weakening_empty
        end;
    (* Try to solve the easy cases. *)
    try solve [ try case_ite_expr;
                simp_hyps;
                repeat
                  (eauto;
                   lazymatch goal with
                   | |- _; _; _ ⊢ _ : ?τ =>
                     first [ is_evar τ | econstructor ]
                   | |- _; _; _ ⊢ _ :: ?κ =>
                     first [ is_evar κ | econstructor ]
                   end) ];
    (* Take care of the more interesting cases. *)
    simpl_cofin?;
    (* Derive well-kindedness from typing. *)
    try select! (_; _; _ ⊢ _ : _)
          (fun H => dup_hyp H (fun H => eapply regularity in H;
                                    [ simp_hyp H | eauto ]));
    (* Apply inversion lemmas for typing and kinding. *)
    apply_type_inv*;
    apply_kind_inv*;
    (* Derive equivalence for the sub-expressions. *)
    try simpl_whnf_equiv;
    (* We may have cofinite quantifiers that are generated by the inversion
    lemmas. *)
    simpl_cofin?;
    simplify_eq;
    (* [TIf] and [TCase] are tricker. Let's deal with them later. *)
    try lazymatch goal with
        | _ : _; ({{_ ≡ _}}_); _ ⊢ _ : _ |- _ =>
          shelve
        end;
    (* Repeatedly apply substitution (open) preservation lemmas and typing
    rules. *)
    repeat
      (try case_ite_expr;
       eauto;
       match goal with
       | H : _; _; (<[_:=_]>?Γ) ⊢ ?e^_ : ?τ^_ |- _; _; ?Γ ⊢ ?e^_ : ?τ^_ =>
         eapply open_preservation
       | H : _; _; (<[_:=_]>?Γ) ⊢ ?e^_ : ?τ |- _; _; ?Γ ⊢ ?e^_ : ?τ =>
         eapply open_preservation_lc
       | H : _; _; (<[_:=_]>?Γ) ⊢ ?e^_ : _ |- _; _; ?Γ ⊢ ?e^_ : ?τ =>
         is_evar τ; eapply open_preservation
       | H : _; _; (<[_:=_]>?Γ) ⊢ ?τ^_ :: _ |- _; _; ?Γ ⊢ ?τ^_ :: _ =>
         eapply kinding_open_preservation
       | |- _; _; _ ⊢ _ : ?τ =>
         tryif is_evar τ
         then typing_intro
         else first [ typing_intro | eapply TConv ]
       | |- _; _ ⊢ _^?e ≡ _^?e =>
         is_var e; eapply expr_equiv_open1
       | |- _; _ ⊢ ?τ^_ ≡ ?τ^_ =>
         eapply expr_equiv_open2
       | |- _; _ ⊢ ?τ ≡ _ =>
         tryif (head_constructor τ)
         then econstructor
         else qauto l: on rew: off
                    solve: equiv_naive_solver
                    use: expr_equiv_step
       | |- lc _ => eauto using typing_lc
       | |- exists _, forall _, _ -> lc _ =>
         eexists; intros; eapply kinding_lc; eapply kinding_rename
       | |- _ ∉ _ => try simpl_fv_rewrite; fast_set_solver!!
       end).

  (* The case when oblivious injection steps to boxed injection [SOInj]. *)
  hauto lq: on ctrs: ovalty inv: otval use: ovalty_intro.

  (* These 4 cases are generated by the case when oblivious case analysis
  steps to [mux]: [SOCase]. *)
  1-4:
  repeat
    match goal with
    | H : ovalty ?e _ |- _ =>
      head_constructor e; sinvert H
    end;
    select! (ovalty _ _) (fun H => apply ovalty_elim in H; simp_hyp H);
    eapply TConv;
    [ eauto using weakening, map_empty_subseteq
    | eauto
    | equiv_naive_solver].

  (* The case when we apply oblivious type to its argument: [SAppOADT] *)
  eapply kinding_open_preservation; eauto.
  eapply kinding_weakening; eauto.
  qauto use: insert_union_singleton_l, map_union_subseteq_l.
  simpl_fv_rewrite; fast_set_solver!!.

  (* Handle the trickier [if] and [case] *)
  Unshelve.

  (* [SIte] *)
  - hauto use: typing_actx_cut_refl.

  (* The discriminee of [if] takes a step *)
  - qauto ctrs: typing use: typing_actx_cut_subst, expr_equiv_step.

  (* [SCase] *)
  - case_split;
    (eapply typing_actx_cut;
     [ eapply open_preservation_lc_alt; eauto;
       lazymatch goal with
       | |- _; _; _ ⊢ _ : _ =>
         typing_intro; eauto; equiv_naive_solver
       | |- _ ∉ _ =>
         simpl_fv_rewrite; fast_set_solver!!
       end
     (* [actx] equivalence *)
     | simpl; rewrite !subst_fresh by fast_set_solver!!;
       rewrite decide_True; eauto ]).
    repeat (econstructor; eauto).
    repeat (econstructor; eauto).

  (* The discriminee of [case] takes a step *)
  - typing_intro; eauto;
      lazymatch goal with
      | |- _; _; _ ⊢ _ : _ =>
        qauto use: typing_actx_cut_subst, expr_equiv_step
      | |- _ ∉ _ =>
         simpl_fv_rewrite; fast_set_solver!!
      end.
Qed.

Theorem preservation Σ Φ Γ e e' τ :
  gctx_wf Σ ->
  Σ; Φ; Γ ⊢ e : τ ->
  Σ ⊨ e -->! e' ->
  Σ; Φ; Γ ⊢ e' : τ.
Proof.
  hauto use: preservation_.
Qed.
