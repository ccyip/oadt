From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.
From oadt Require Import lang_oadt.infrastructure.
From oadt Require Import lang_oadt.properties.
From oadt Require Import lang_oadt.progress.

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

(** ** Renaming lemmas *)

Tactic Notation "relax_actx" "by" tactic3(tac) :=
  lazymatch goal with
  | |- _; ?Φ; _ ⊢ _ : _ =>
    lazymatch Φ with
    | {{_ ≡ _}}_ =>
      let H := fresh "H" in
      eassert (Φ ≡ _) as H by tac;
      rewrite H; clear H
    end
  end.

(* Warning: this lemma is rather slow. *)
Lemma typing_kinding_rename_ Σ x y τ' :
  gctx_wf Σ ->
  (forall Φ Γ' e τ,
      Σ; Φ; Γ' ⊢ e : τ ->
      forall Γ,
        Γ' = <[x:=τ']>Γ ->
        x ∉ fv τ' ∪ dom aset Γ ->
        y ∉ {[x]} ∪ fv e ∪ fv τ' ∪ dom aset Γ ->
        Σ; (actx_map ({x↦y}) Φ); (<[y:=τ']>({x↦y} <$> Γ)) ⊢ {x↦y}e : {x↦y}τ) /\
  (forall Φ Γ' τ κ,
      Σ; Φ; Γ' ⊢ τ :: κ ->
      forall Γ,
        Γ' = <[x:=τ']>Γ ->
        x ∉ fv τ' ∪ dom aset Γ ->
        y ∉ {[x]} ∪ fv τ ∪ fv τ' ∪ dom aset Γ ->
        Σ; (actx_map ({x↦y}) Φ); (<[y:=τ']>({x↦y} <$> Γ)) ⊢ {x↦y}τ :: κ).
Proof.
  intros Hwf.
  apply typing_kinding_mutind; intros; subst; simpl in *;
    (* First we normalize the typing and kinding judgments so they are ready
    for applying typing and kinding rules to. *)
    rewrite ?subst_open_distr by constructor;
    rewrite ?subst_ite_distr;
    try lazymatch goal with
        | |- _; _; _ ⊢ [inj@_< ?ω > _] : {_↦_}?ω =>
          rewrite subst_fresh by shelve
        | |- context [decide (_ = _)] =>
          case_decide; subst
        end;
      (* Apply typing and kinding rules. *)
      econstructor;
      simpl_cofin?;
      (* We define this subroutine [go] for applying induction hypotheses. *)
      let go Γ :=
          (* We massage the typing and kinding judgments so that we can apply
          induction hypotheses to them. *)
          rewrite <- ?subst_ite_distr;
            rewrite <- ?subst_open_comm by (try constructor; shelve);
            try lazymatch Γ with
                | <[_:=_]>(<[_:=_]>({_↦_} <$> _)) =>
                  first [ rewrite <- fmap_insert
                        (* We may have to apply commutativity first. *)
                        | rewrite insert_commute by shelve;
                          rewrite <- fmap_insert ]
                end;
            (* For [TIf] and [TCase], we factor out the assumptions context and
            prove the equivalence later. *)
            try relax_actx by shelve;
            (* Apply one of the induction hypotheses. *)
            auto_apply in
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
                 apply expr_equiv_rename
               | |- <[?y:=_]>_ !! ?y = Some _ =>
                 simplify_map_eq
               | |- <[_:=_]>_ !! _ = Some _ =>
                 rewrite lookup_insert_ne; [simplify_map_eq |]
               | |- Some _ = Some _ =>
                 try reflexivity; repeat f_equal
               | |- _ = {_↦_} _ =>
                 rewrite subst_fresh
               | H : ?Σ !! ?x = Some _ |- ?Σ !! ?x = Some _ =>
                 rewrite H
               end;
        eauto.

  Unshelve.

  (* Equivalence of assumptions context *)
  all : lazymatch goal with
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

(** We also allow [x=y]. *)
Lemma typing_rename_ Σ Φ Γ e τ τ' x y :
  gctx_wf Σ ->
  Σ; Φ; (<[x:=τ']>Γ) ⊢ e : τ ->
  x ∉ fv τ' ∪ dom aset Γ ->
  y ∉ fv e ∪ fv τ' ∪ dom aset Γ ->
  Σ; (actx_map ({x↦y}) Φ); (<[y:=τ']>({x↦y} <$> Γ)) ⊢ {x↦y}e : {x↦y}τ.
Proof.
  intros.
  destruct (decide (y = x)); subst.
  - rewrite subst_actx_id. scongruence use: subst_id, subst_tctx_id.
  - qauto use: typing_kinding_rename_ solve: fast_set_solver!!.
Qed.

Lemma kinding_rename_ Σ Φ Γ τ τ' κ x y :
  gctx_wf Σ ->
  Σ; Φ; (<[x:=τ']>Γ) ⊢ τ :: κ ->
  x ∉ fv τ' ∪ dom aset Γ ->
  y ∉ fv τ ∪ fv τ' ∪ dom aset Γ ->
  Σ; (actx_map ({x↦y}) Φ); (<[y:=τ']>({x↦y} <$> Γ)) ⊢ {x↦y}τ :: κ.
Proof.
  intros.
  destruct (decide (y = x)); subst.
  - rewrite subst_actx_id. scongruence use: subst_id, subst_tctx_id.
  - qauto use: typing_kinding_rename_ solve: fast_set_solver!!.
Qed.

(** The actual renaming lemmas. The side conditions are slightly different than
the general version. *)
Lemma typing_rename Σ Φ Γ e τ τ' x y :
  gctx_wf Σ ->
  Σ; Φ; (<[x:=τ']>Γ) ⊢ e^x : τ^x ->
  x ∉ fv τ' ∪ fv e ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ∪ actx_fv Φ ->
  y ∉ fv τ' ∪ fv e ∪ dom aset Γ ->
  Σ; Φ; (<[y:=τ']>Γ) ⊢ e^y : τ^y.
Proof.
  intros.
  destruct (decide (y = x)); subst; eauto.
  rewrite <- (subst_actx_fresh Φ x y) by fast_set_solver!!.
  rewrite <- (subst_tctx_fresh Γ x y) by fast_set_solver!!.
  rewrite (subst_intro e y x) by fast_set_solver!!.
  rewrite (subst_intro τ y x) by fast_set_solver!!.
  apply typing_rename_; eauto.
  fast_set_solver!!.
  simpl_fv. fast_set_solver!!.
Qed.

Lemma kinding_rename Σ Φ Γ τ κ τ' x y :
  gctx_wf Σ ->
  Σ; Φ; (<[x:=τ']>Γ) ⊢ τ^x :: κ ->
  x ∉ fv τ' ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ∪ actx_fv Φ ->
  y ∉ fv τ' ∪ fv τ ∪ dom aset Γ ->
  Σ; Φ; (<[y:=τ']>Γ) ⊢ τ^y :: κ.
Proof.
  intros.
  destruct (decide (y = x)); subst; eauto.
  rewrite <- (subst_actx_fresh Φ x y) by fast_set_solver!!.
  rewrite <- (subst_tctx_fresh Γ x y) by fast_set_solver!!.
  rewrite (subst_intro τ y x) by fast_set_solver!!.
  apply kinding_rename_; eauto.
  fast_set_solver!!.
  simpl_fv. fast_set_solver!!.
Qed.

Lemma typing_rename_lc Σ Φ Γ e τ τ' x y :
  gctx_wf Σ ->
  Σ; Φ; (<[x:=τ']>Γ) ⊢ e^x : τ ->
  x ∉ fv τ' ∪ fv e ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ∪ actx_fv Φ ->
  y ∉ fv τ' ∪ fv e ∪ dom aset Γ ->
  Σ; Φ; (<[y:=τ']>Γ) ⊢ e^y : τ.
Proof.
  intros Hwf H. intros.
  erewrite <- (open_lc_intro τ y) by eauto using typing_type_lc.
  erewrite <- (open_lc_intro τ x) in H by eauto using typing_type_lc.
  eapply typing_rename; eauto.
Qed.

Lemma typing_rename_alt Σ Φ Γ e e1 e2 τ τ' x y :
  gctx_wf Σ ->
  Σ; ({{e1 ≡ e2}}Φ); (<[x:=τ']>Γ) ⊢ e^x : τ^x ->
  x ∉ fv τ' ∪ fv e ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ∪ actx_fv Φ ->
  y ∉ fv τ' ∪ fv e ∪ fv e1 ∪ fv e2 ∪ dom aset Γ ->
  Σ; ({{({x↦y}e1) ≡ ({x↦y}e2)}}Φ); (<[y:=τ']>Γ) ⊢ e^y : τ^y.
Proof.
  intros.
  destruct (decide (y = x)); subst.
  - rewrite !subst_fresh by fast_set_solver!!; eauto.
  (* I could have reduced this proof to [typing_rename], but the current [subst]
  and the way I treat oblivious values make it impossible. So I simply prove it
  from scratch. But I may redo the oblivious value formalization later. *)
  - rewrite <- (subst_tctx_fresh Γ x y) by fast_set_solver!!.
    rewrite (subst_intro e y x) by fast_set_solver!!.
    rewrite (subst_intro τ y x) by fast_set_solver!!.
    relax_actx by shelve.
    apply typing_rename_; eauto.
    fast_set_solver!!.
    simpl_fv. fast_set_solver!!.

  Unshelve.
  rewrite actx_map_insert.
  f_equiv.
  rewrite subst_actx_fresh by fast_set_solver!!.
  reflexivity.
Qed.

Lemma typing_rename_lc_alt Σ Φ Γ e e1 e2 τ τ' x y :
  gctx_wf Σ ->
  Σ; ({{e1 ≡ e2}}Φ); (<[x:=τ']>Γ) ⊢ e^x : τ ->
  x ∉ fv τ' ∪ fv e ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ∪ actx_fv Φ ->
  y ∉ fv τ' ∪ fv e ∪ fv e1 ∪ fv e2 ∪ dom aset Γ ->
  Σ; ({{({x↦y}e1) ≡ ({x↦y}e2)}}Φ); (<[y:=τ']>Γ) ⊢ e^y : τ.
Proof.
  intros Hwf H. intros.
  erewrite <- (open_lc_intro τ y) by eauto using typing_type_lc.
  erewrite <- (open_lc_intro τ x) in H by eauto using typing_type_lc.
  eapply typing_rename_alt; eauto.
Qed.

(** ** Admissible typing and kinding introduction rules *)
Section typing_kinding_intro.

  Context {Σ : gctx} (Hwf : gctx_wf Σ).
  Notation "Φ ; Γ '⊢' e ':' τ" := (Σ; Φ; Γ ⊢ e : τ)
                                    (at level 40,
                                     Γ constr at level 0,
                                     e custom oadt at level 99,
                                     τ custom oadt at level 99).
  Notation "Φ ; Γ '⊢' τ '::' κ" := (Σ; Φ; Γ ⊢ τ :: κ)
                                     (at level 40,
                                      Γ constr at level 0,
                                      τ custom oadt at level 99,
                                      κ custom oadt at level 99).

  Ltac typing_intro_solver :=
    intros; econstructor; eauto; simpl_cofin?;
    lazymatch goal with
    | |- _; _ ⊢ _ : _^_ => eapply typing_rename
    | |- _; _ ⊢ _ :: _ => eapply kinding_rename
    | |- ?Φ; _ ⊢ _ : _ =>
      first [ relax_actx by shelve; eapply typing_rename_lc_alt
            | eapply typing_rename_lc ]
    end; eauto;
    try fast_set_solver!!; simpl_fv; fast_set_solver!!.

  Lemma TAbs_intro Φ Γ e τ1 τ2 κ x :
    Φ; <[x:=τ2]>Γ ⊢ e^x : τ1^x ->
    Φ; Γ ⊢ τ2 :: κ ->
    x ∉ fv e ∪ fv τ1 ∪ dom aset Γ ∪ tctx_fv Γ ∪ actx_fv Φ ->
    Φ; Γ ⊢ \:τ2 => e : (Π:τ2, τ1).
  Proof.
    typing_intro_solver.
  Qed.

  Lemma TLet_intro Φ Γ e1 e2 τ1 τ2 x :
    Φ; <[x:=τ1]>Γ ⊢ e2^x : τ2^x ->
    Φ; Γ ⊢ e1 : τ1 ->
    x ∉ fv e2 ∪ fv τ2 ∪ dom aset Γ ∪ tctx_fv Γ ∪ actx_fv Φ ->
    Φ; Γ ⊢ let e1 in e2 : τ2^e1.
  Proof.
    typing_intro_solver.
  Qed.

  Lemma TCase_intro Φ Γ e0 e1 e2 τ1 τ2 τ κ x :
    {{e0 ≡ inl<τ1 + τ2> x}}Φ; <[x:=τ1]>Γ ⊢ e1^x : τ ->
    {{e0 ≡ inr<τ1 + τ2> x}}Φ; <[x:=τ2]>Γ ⊢ e2^x : τ ->
    Φ; Γ ⊢ e0 : τ1 + τ2 ->
    Φ; Γ ⊢ τ :: κ ->
    x ∉ fv e1 ∪ fv e2 ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ∪ actx_fv Φ ->
    Φ; Γ ⊢ case e0 of e1 | e2 : τ.
  Proof.
    typing_intro_solver.

    Unshelve.

    all : simpl; rewrite decide_True by reflexivity;
      rewrite !subst_fresh by (simpl_fv; fast_set_solver!!); reflexivity.
  Qed.

  Lemma TOCase_intro Φ Γ e0 e1 e2 τ1 τ2 τ x :
    Φ; <[x:=τ1]>Γ ⊢ e1^x : τ ->
    Φ; <[x:=τ2]>Γ ⊢ e2^x : τ ->
    Φ; Γ ⊢ e0 : τ1 ~+ τ2 ->
    Φ; Γ ⊢ τ :: *@O ->
    x ∉ fv e1 ∪ fv e2 ∪ dom aset Γ ∪ tctx_fv Γ ∪ actx_fv Φ ->
    Φ; Γ ⊢ ~case e0 of e1 | e2 : τ.
  Proof.
    typing_intro_solver.
  Qed.

  Lemma KPi_intro Φ Γ τ1 τ2 κ1 κ2 x :
    Φ; <[x:=τ1]>Γ ⊢ τ2^x :: κ2 ->
    Φ; Γ ⊢ τ1 :: κ1 ->
    x ∉ fv τ2 ∪ dom aset Γ ∪ tctx_fv Γ ∪ actx_fv Φ ->
    Φ; Γ ⊢ (Π:τ1, τ2) :: *@M.
  Proof.
    typing_intro_solver.
  Qed.

  Lemma KCase_intro Φ Γ e0 τ1 τ2 τ1' τ2' x :
    Φ; <[x:=τ1']>Γ ⊢ τ1^x :: *@O ->
    Φ; <[x:=τ2']>Γ ⊢ τ2^x :: *@O ->
    Φ; Γ ⊢ e0 : τ1' + τ2' ->
    x ∉ fv τ1 ∪ fv τ2 ∪ dom aset Γ ∪ tctx_fv Γ ∪ actx_fv Φ ->
    Φ; Γ ⊢ case e0 of τ1 | τ2 :: *@O.
  Proof.
    typing_intro_solver.
  Qed.

  Lemma KLet_intro Φ Γ e τ τ' x :
    Φ; <[x:=τ']>Γ ⊢ τ^x :: *@O ->
    Φ; Γ ⊢ e : τ' ->
    x ∉ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ∪ actx_fv Φ ->
    Φ; Γ ⊢ let e in τ :: *@O.
  Proof.
    typing_intro_solver.
  Qed.

  Lemma KProd_intro Φ Γ τ1 τ2 κ1 κ2 :
    Φ; Γ ⊢ τ1 :: κ1 ->
    Φ; Γ ⊢ τ2 :: κ2 ->
    Φ; Γ ⊢ τ1 * τ2 :: (κ1 ⊔ κ2).
  Proof.
    eauto using join_ub_l, join_ub_r with kinding.
  Qed.

End typing_kinding_intro.

(** Tactics for apply typing/kinding rules. Similar to [econstructor], but it
uses the admissible rules. It also fails rather than applying [TConv]
blindly. *)
(* NOTE: it would be great if [econstructor] can apply all but some
constructors. *)
Ltac typing_intro_ Σ T :=
  lazymatch T with
  | Σ; _; _ ⊢ fvar _ : _ => eapply TFVar
  | Σ; _; _ ⊢ gvar _ : _ => eapply TGVar
  | Σ; _; _ ⊢ \:_ => _ : _ => eapply TAbs_intro
  | Σ; _; _ ⊢ let _ in _ : _ => eapply TLet_intro
  | Σ; _; _ ⊢ _ _ : _ => eapply TApp
  | Σ; _; _ ⊢ () : _ => eapply TUnit
  | Σ; _; _ ⊢ lit _ : _ => eapply TLit
  | Σ; _; _ ⊢ s𝔹 _ : _ => eapply TSec
  | Σ; _; _ ⊢ (_, _) : _ => eapply TPair
  | Σ; _; _ ⊢ ~if _ then _ else _ : _ => eapply TMux
  | Σ; _; _ ⊢ π@_ _ : _ => eapply TProj
  | Σ; _; _ ⊢ inj{_}@_<_> _ : _ => eapply TInj
  | Σ; _; _ ⊢ ~case _ of _ | _ : _ => eapply TOCase_intro
  | Σ; _; _ ⊢ fold<_> _ : _ => eapply TFold
  | Σ; _; _ ⊢ unfold<_> _ : _ => eapply TUnfold
  | Σ; _; _ ⊢ if _ then _ else _ : _ => eapply TIte
  | Σ; _; _ ⊢ case _ of _ | _ : _ => eapply TCase_intro
  | Σ; _; _ ⊢ [_] : _ => eapply TBoxedLit
  | Σ; _; _ ⊢ [inj@_<_> _] : _ => eapply TBoxedInj
  | Σ; _; _ ⊢ ?e : ?τ => is_var e; assert_fails (is_evar τ); eapply TConv
  end.

Ltac kinding_intro_ Σ T :=
  lazymatch T with
  | Σ; _; _ ⊢ gvar _ :: _ => eapply KVarADT
  | Σ; _; _ ⊢ 𝟙 :: _ => eapply KUnit
  | Σ; _; _ ⊢ 𝔹{_} :: _ => eapply KBool
  | Σ; _; _ ⊢ Π:_, _ :: _ => eapply KPi_intro
  | Σ; _; _ ⊢ (gvar _) _ :: _ => eapply KApp
  | Σ; _; _ ⊢ _ * _ :: _ => eapply KProd_intro
  | Σ; _; _ ⊢ _ + _ :: _ => eapply KSum
  | Σ; _; _ ⊢ _ ~+ _ :: _ => eapply KOSum
  | Σ; _; _ ⊢ if _ then _ else _ :: _ => eapply KIte
  | Σ; _; _ ⊢ case _ of _ | _ :: _ => eapply KCase_intro
  | Σ; _; _ ⊢ let _ in _ :: _ => eapply KLet_intro
  | Σ; _; _ ⊢ ?τ :: _ => is_var τ; eapply KSub
  end.

Tactic Notation "typing_kinding_intro_" tactic3(tac) :=
  match goal with
  | H : gctx_wf ?Σ |- ?T =>
    tac Σ T;
    try match goal with
        | |- gctx_wf Σ => apply H
        end
  end.

Tactic Notation "typing_intro" :=
  typing_kinding_intro_ (fun Σ T => typing_intro_ Σ T).

Tactic Notation "kinding_intro" :=
  typing_kinding_intro_ (fun Σ T => kinding_intro_ Σ T).

Tactic Notation "typing_kinding_intro" :=
  lazymatch goal with
  | |- _; _; _ ⊢ _ : _ => typing_intro
  | |- _; _; _ ⊢ _ :: _ => kinding_intro
  end.

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
  sfirstorder use: otval_well_kinded, oval_elim.
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

Ltac case_ite_expr :=
  lazymatch goal with
  | |- _; _; _ ⊢ ?e : _ =>
    lazymatch e with
    | context [<{ ite ?b _ _ }>] => destruct b
    end
  | |- _; _; _ ⊢ ?τ :: _ =>
    lazymatch τ with
    | context [<{ ite ?b _ _ }>] => destruct b
    end
  end.

(** The combined preservation theorems for expressions and types. *)
Theorem preservation_ Σ :
  gctx_wf Σ ->
  (forall Φ Γ e τ,
      Σ; Φ; Γ ⊢ e : τ ->
      forall e', Σ ⊨ e -->! e' ->
            Σ; Φ; Γ ⊢ e' : τ) /\
  (forall Φ Γ τ κ,
      Σ; Φ; Γ ⊢ τ :: κ ->
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
         then apply expr_equiv_iff_whnf_equiv; econstructor
         else qauto l: on rew: off
                    solve: equiv_naive_solver
                    use: expr_equiv_step
       | |- lc _ => eauto using typing_lc
       | |- exists _, forall _, _ -> lc _ =>
         eexists; intros; eapply kinding_lc; eapply kinding_rename
       | |- _ ∉ _ => fast_set_solver!!
       end).

  (* The case when oblivious injection steps to boxed injection [SOInj]. *)
  hauto lq: on ctrs: oval inv: otval use: oval_intro.

  (* These 4 cases are generated by the case when oblivious case analysis
  steps to [mux]: [SOCase]. *)
  1-4:
  repeat
    match goal with
    | H : oval ?e _ |- _ =>
      head_constructor e; sinvert H
    end;
    select! (oval _ _) (fun H => apply oval_elim in H; simp_hyp H);
    eapply TConv;
    [ eauto using weakening, map_empty_subseteq
    | eauto
    | equiv_naive_solver].

  (* The case when we apply oblivious type to its argument: [SAppOADT] *)
  eapply kinding_open_preservation; eauto.
  eapply kinding_weakening; eauto.
  fast_set_solver!!.
  qauto use: insert_union_singleton_l, map_union_subseteq_l.
  fast_set_solver!!.

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
         fast_set_solver!!
       end
     (* [actx] equivalence *)
     | simpl; rewrite !subst_fresh by fast_set_solver!!;
       rewrite decide_True; eauto;
       repeat (eapply expr_equiv_iff_whnf_equiv; econstructor);
       equiv_naive_solver ]).

  (* The discriminee of [case] takes a step *)
  - typing_intro; eauto;
      lazymatch goal with
      | |- _; _; _ ⊢ _ : _ =>
        qauto use: typing_actx_cut_subst, expr_equiv_step
      | |- _ ∉ _ =>
        fast_set_solver!!
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
