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
    econstructor; eauto using insert_mono, expr_equiv_weakening.
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

(* Warning: this lemma is rather slow. *)
Lemma typing_kinding_rename_ Σ x y τ' :
  gctx_wf Σ ->
  (forall Γ' e τ,
      Σ; Γ' ⊢ e : τ ->
      forall Γ,
        Γ' = <[x:=τ']>Γ ->
        x ∉ fv τ' ∪ dom aset Γ ->
        y ∉ {[x]} ∪ fv e ∪ fv τ' ∪ dom aset Γ ->
        Σ; (<[y:=τ']>({x↦y} <$> Γ)) ⊢ {x↦y}e : {x↦y}τ) /\
  (forall Γ' τ κ,
      Σ; Γ' ⊢ τ :: κ ->
      forall Γ,
        Γ' = <[x:=τ']>Γ ->
        x ∉ fv τ' ∪ dom aset Γ ->
        y ∉ {[x]} ∪ fv τ ∪ fv τ' ∪ dom aset Γ ->
        Σ; (<[y:=τ']>({x↦y} <$> Γ)) ⊢ {x↦y}τ :: κ).
Proof.
  intros Hwf.
  apply typing_kinding_mutind; intros; subst; simpl in *;
    (* First we normalize the typing and kinding judgments so they are ready
    for applying typing and kinding rules to. *)
    rewrite ?subst_open_distr by constructor;
    rewrite ?subst_ite_distr;
    try lazymatch goal with
        | |- _; _ ⊢ [inj@_< ?ω > _] : {_↦_}?ω =>
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
            (* Apply one of the induction hypotheses. *)
            auto_apply in
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

  all : try fast_set_solver!!; simpl_fv; fast_set_solver*!!.
Qed.

(** We also allow [x=y]. *)
Lemma typing_rename_ Σ Γ e τ τ' x y :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ e : τ ->
  x ∉ fv τ' ∪ dom aset Γ ->
  y ∉ fv e ∪ fv τ' ∪ dom aset Γ ->
  Σ; (<[y:=τ']>({x↦y} <$> Γ)) ⊢ {x↦y}e : {x↦y}τ.
Proof.
  intros.
  destruct (decide (y = x)); subst.
  - scongruence use: subst_id, subst_tctx_id.
  - qauto use: typing_kinding_rename_ solve: fast_set_solver!!.
Qed.

Lemma kinding_rename_ Σ Γ τ τ' κ x y :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ τ :: κ ->
  x ∉ fv τ' ∪ dom aset Γ ->
  y ∉ fv τ ∪ fv τ' ∪ dom aset Γ ->
  Σ; (<[y:=τ']>({x↦y} <$> Γ)) ⊢ {x↦y}τ :: κ.
Proof.
  intros.
  destruct (decide (y = x)); subst.
  - scongruence use: subst_id, subst_tctx_id.
  - qauto use: typing_kinding_rename_ solve: fast_set_solver!!.
Qed.

(** The actual renaming lemmas. The side conditions are slightly different than
the general version. *)
Lemma typing_rename Σ Γ e τ τ' x y :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ e^x : τ^x ->
  x ∉ fv τ' ∪ fv e ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ->
  y ∉ fv τ' ∪ fv e ∪ dom aset Γ ->
  Σ; (<[y:=τ']>Γ) ⊢ e^y : τ^y.
Proof.
  intros.
  destruct (decide (y = x)); subst; eauto.
  rewrite <- (subst_tctx_fresh Γ x y) by fast_set_solver!!.
  rewrite (subst_intro e y x) by fast_set_solver!!.
  rewrite (subst_intro τ y x) by fast_set_solver!!.
  apply typing_rename_; eauto.
  fast_set_solver!!.
  simpl_fv. fast_set_solver!!.
Qed.

Lemma kinding_rename Σ Γ τ κ τ' x y :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ τ^x :: κ ->
  x ∉ fv τ' ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ->
  y ∉ fv τ' ∪ fv τ ∪ dom aset Γ ->
  Σ; (<[y:=τ']>Γ) ⊢ τ^y :: κ.
Proof.
  intros.
  destruct (decide (y = x)); subst; eauto.
  rewrite <- (subst_tctx_fresh Γ x y) by fast_set_solver!!.
  rewrite (subst_intro τ y x) by fast_set_solver!!.
  apply kinding_rename_; eauto.
  fast_set_solver!!.
  simpl_fv. fast_set_solver!!.
Qed.

Lemma typing_rename_lc Σ Γ e τ τ' x y :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ e^x : τ ->
  x ∉ fv τ' ∪ fv e ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ->
  y ∉ fv τ' ∪ fv e ∪ dom aset Γ ->
  Σ; (<[y:=τ']>Γ) ⊢ e^y : τ.
Proof.
  intros Hwf H. intros.
  erewrite <- (open_lc_intro τ y) by eauto using typing_type_lc.
  erewrite <- (open_lc_intro τ x) in H by eauto using typing_type_lc.
  eapply typing_rename; eauto.
Qed.

(** ** Admissible typing and kinding introduction rules *)
Section typing_kinding_intro.

  #[local]
  Set Warnings "-notation-overridden,-parsing".

  Context {Σ : gctx} (Hwf : gctx_wf Σ).
  Notation "Γ '⊢' e ':' τ" := (Σ; Γ ⊢ e : τ)
                                (at level 40,
                                 e custom oadt at level 99,
                                 τ custom oadt at level 99).
  Notation "Γ '⊢' τ '::' κ" := (Σ; Γ ⊢ τ :: κ)
                                 (at level 40,
                                  τ custom oadt at level 99,
                                  κ custom oadt at level 99).

  Ltac typing_intro_solver :=
    intros; econstructor; eauto; simpl_cofin?;
    lazymatch goal with
    | |- _ ⊢ _ : _^_ => eapply typing_rename
    | |- _ ⊢ _ : _ => eapply typing_rename_lc
    | |- _ ⊢ _ :: _ => eapply kinding_rename
    end; eauto;
    try fast_set_solver!!; simpl_fv; fast_set_solver!!.

  Lemma TAbs_intro Γ e τ1 τ2 κ x :
    <[x:=τ2]>Γ ⊢ e^x : τ1^x ->
    Γ ⊢ τ2 :: κ ->
    x ∉ fv e ∪ fv τ1 ∪ dom aset Γ ∪ tctx_fv Γ ->
    Γ ⊢ \:τ2 => e : (Π:τ2, τ1).
  Proof.
    typing_intro_solver.
  Qed.

  Lemma TLet_intro Γ e1 e2 τ1 τ2 x :
    <[x:=τ1]>Γ ⊢ e2^x : τ2^x ->
    Γ ⊢ e1 : τ1 ->
    x ∉ fv e2 ∪ fv τ2 ∪ dom aset Γ ∪ tctx_fv Γ ->
    Γ ⊢ let e1 in e2 : τ2^e1.
  Proof.
    typing_intro_solver.
  Qed.

  Lemma TCase_intro Γ e0 e1 e2 τ1 τ2 τ κ x :
    <[x:=τ1]>Γ ⊢ e1^x : τ ->
    <[x:=τ2]>Γ ⊢ e2^x : τ ->
    Γ ⊢ e0 : τ1 + τ2 ->
    Γ ⊢ τ :: κ ->
    x ∉ fv e1 ∪ fv e2 ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ->
    Γ ⊢ case e0 of e1 | e2 : τ.
  Proof.
    typing_intro_solver.
  Qed.

  Lemma TOCase_intro Γ e0 e1 e2 τ1 τ2 τ x :
    <[x:=τ1]>Γ ⊢ e1^x : τ ->
    <[x:=τ2]>Γ ⊢ e2^x : τ ->
    Γ ⊢ e0 : τ1 ~+ τ2 ->
    Γ ⊢ τ :: *@O ->
    x ∉ fv e1 ∪ fv e2 ∪ dom aset Γ ∪ tctx_fv Γ ->
    Γ ⊢ ~case e0 of e1 | e2 : τ.
  Proof.
    typing_intro_solver.
  Qed.

  Lemma KPi_intro Γ τ1 τ2 κ1 κ2 x :
    <[x:=τ1]>Γ ⊢ τ2^x :: κ2 ->
    Γ ⊢ τ1 :: κ1 ->
    x ∉ fv τ2 ∪ dom aset Γ ∪ tctx_fv Γ ->
    Γ ⊢ (Π:τ1, τ2) :: *@M.
  Proof.
    typing_intro_solver.
  Qed.

  Lemma KCase_intro Γ e0 τ1 τ2 τ1' τ2' x :
    <[x:=τ1']>Γ ⊢ τ1^x :: *@O ->
    <[x:=τ2']>Γ ⊢ τ2^x :: *@O ->
    Γ ⊢ e0 : τ1' + τ2' ->
    x ∉ fv τ1 ∪ fv τ2 ∪ dom aset Γ ∪ tctx_fv Γ ->
    Γ ⊢ case e0 of τ1 | τ2 :: *@O.
  Proof.
    typing_intro_solver.
  Qed.

  Lemma KLet_intro Γ e τ τ' x :
    <[x:=τ']>Γ ⊢ τ^x :: *@O ->
    Γ ⊢ e : τ' ->
    x ∉ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ->
    Γ ⊢ let e in τ :: *@O.
  Proof.
    typing_intro_solver.
  Qed.

  Lemma KProd_intro Γ τ1 τ2 κ1 κ2 :
    Γ ⊢ τ1 :: κ1 ->
    Γ ⊢ τ2 :: κ2 ->
    Γ ⊢ τ1 * τ2 :: (κ1 ⊔ κ2).
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
  | Σ; _ ⊢ fvar _ : _ => eapply TFVar
  | Σ; _ ⊢ gvar _ : _ => eapply TGVar
  | Σ; _ ⊢ \:_ => _ : _ => eapply TAbs_intro
  | Σ; _ ⊢ let _ in _ : _ => eapply TLet_intro
  | Σ; _ ⊢ _ _ : _ => eapply TApp
  | Σ; _ ⊢ () : _ => eapply TUnit
  | Σ; _ ⊢ lit _ : _ => eapply TLit
  | Σ; _ ⊢ s𝔹 _ : _ => eapply TSec
  | Σ; _ ⊢ (_, _) : _ => eapply TPair
  | Σ; _ ⊢ ~if _ then _ else _ : _ => eapply TMux
  | Σ; _ ⊢ π@_ _ : _ => eapply TProj
  | Σ; _ ⊢ inj{_}@_<_> _ : _ => eapply TInj
  | Σ; _ ⊢ ~case _ of _ | _ : _ => eapply TOCase_intro
  | Σ; _ ⊢ fold<_> _ : _ => eapply TFold
  | Σ; _ ⊢ unfold<_> _ : _ => eapply TUnfold
  | Σ; _ ⊢ if _ then _ else _ : _ => eapply TIte
  | Σ; _ ⊢ case _ of _ | _ : _ => eapply TCase_intro
  | Σ; _ ⊢ [_] : _ => eapply TBoxedLit
  | Σ; _ ⊢ [inj@_<_> _] : _ => eapply TBoxedInj
  | Σ; _ ⊢ ?e : ?τ => is_var e; assert_fails (is_evar τ); eapply TConv
  end.

Ltac kinding_intro_ Σ T :=
  lazymatch T with
  | Σ; _ ⊢ gvar _ :: _ => eapply KVarADT
  | Σ; _ ⊢ 𝟙 :: _ => eapply KUnit
  | Σ; _ ⊢ 𝔹{_} :: _ => eapply KBool
  | Σ; _ ⊢ Π:_, _ :: _ => eapply KPi_intro
  | Σ; _ ⊢ (gvar _) _ :: _ => eapply KApp
  | Σ; _ ⊢ _ * _ :: _ => eapply KProd_intro
  | Σ; _ ⊢ _ + _ :: _ => eapply KSum
  | Σ; _ ⊢ _ ~+ _ :: _ => eapply KOSum
  | Σ; _ ⊢ if _ then _ else _ :: _ => eapply KIte
  | Σ; _ ⊢ case _ of _ | _ :: _ => eapply KCase_intro
  | Σ; _ ⊢ let _ in _ :: _ => eapply KLet_intro
  | Σ; _ ⊢ ?τ :: _ => is_var τ; eapply KSub
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
  | |- _; _ ⊢ _ : _ => typing_intro
  | |- _; _ ⊢ _ :: _ => kinding_intro
  end.

(** ** Substitution lemma *)

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
      | |- _; ?Γ ⊢ ?e : ?τ =>
        auto_apply || lazymatch goal with
                      | H : _ -> _; ?Γ' ⊢ e : τ |- _ =>
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
            rewrite <- ?subst_open_comm by (try assumption; shelve);
            try lazymatch Γ with
                | <[_:=_]>({_↦_} <$> _) =>
                  rewrite <- fmap_insert
                end;
            (* Apply one of the induction hypotheses. *)
            auto_eapply in
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
                 apply expr_equiv_subst1
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

(** Types of well-typed expressions are well-kinded *)
Lemma regularity Σ Γ e τ :
  gctx_wf Σ ->
  Σ; Γ ⊢ e : τ ->
  exists κ, Σ; Γ ⊢ τ :: κ.
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
Lemma obliv_type_not_typed Σ X τ e Γ τ' :
  Σ !! X = Some (DOADT τ e) ->
  Σ; Γ ⊢ gvar X : τ' ->
  False.
Proof.
  intros.
  apply_type_inv.
  scongruence.
Qed.

(** ** Preservation *)

Ltac case_ite_expr :=
  lazymatch goal with
  | |- _; _ ⊢ ?e : _ =>
    lazymatch e with
    | context [<{ ite ?b _ _ }>] => destruct b
    end
  | |- _; _ ⊢ ?τ :: _ =>
    lazymatch τ with
    | context [<{ ite ?b _ _ }>] => destruct b
    end
  end.

(** The combined preservation theorems for expressions and types. *)
Theorem preservation_ Σ :
  gctx_wf Σ ->
  (forall Γ e τ,
      Σ; Γ ⊢ e : τ ->
      forall e', Σ ⊨ e -->! e' ->
            Σ; Γ ⊢ e' : τ) /\
  (forall Γ τ κ,
      Σ; Γ ⊢ τ :: κ ->
      forall τ', Σ ⊨ τ -->! τ' ->
            Σ; Γ ⊢ τ' :: κ).
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
        | H : _ !! ?X = Some (DOADT _ _), H' : _; _ ⊢ gvar ?X : _ |- _ =>
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
                   | |- _; _ ⊢ _ : ?τ =>
                     first [ is_evar τ | econstructor ]
                   | |- _; _ ⊢ _ :: ?κ =>
                     first [ is_evar κ | econstructor ]
                   end) ];
    (* Take care of the more interesting cases. *)
    simpl_cofin?;
    (* Derive well-kindedness from typing. *)
    try select! (_; _ ⊢ _ : _)
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
    (* Repeatedly apply substitution (open) preservation lemmas and typing
    rules. *)
    repeat
      (try case_ite_expr;
       eauto;
       match goal with
       | H : _; (<[_:=_]>?Γ) ⊢ ?e^_ : ?τ^_ |- _; ?Γ ⊢ ?e^_ : ?τ^_ =>
         eapply open_preservation
       | H : _; (<[_:=_]>?Γ) ⊢ ?e^_ : ?τ |- _; ?Γ ⊢ ?e^_ : ?τ =>
         eapply open_preservation_lc
       | H : _; (<[_:=_]>?Γ) ⊢ ?e^_ : _ |- _; ?Γ ⊢ ?e^_ : ?τ =>
         is_evar τ; eapply open_preservation
       | H : _; (<[_:=_]>?Γ) ⊢ ?τ^_ :: _ |- _; ?Γ ⊢ ?τ^_ :: _ =>
         eapply kinding_open_preservation
       | |- _; _ ⊢ _ : ?τ =>
         tryif is_evar τ
         then typing_intro
         else first [ typing_intro | eapply TConv ]
       | |- _ ⊢ _^?e ≡ _^?e =>
         is_var e; eapply expr_equiv_open1
       | |- _ ⊢ ?τ^_ ≡ ?τ^_ =>
         eapply expr_equiv_open2
       | |- _ ⊢ ?τ ≡ _ =>
         tryif (head_constructor τ)
         then apply expr_equiv_iff_whnf_equiv; econstructor
         else qauto l: on rew: off
                    solve: equiv_naive_solver
                    use: expr_equiv_step
       | |- lc _ => eauto using typing_lc
       | |- forall _, _ -> lc _ =>
         intros; eapply kinding_lc; eapply kinding_rename
       | |- _ ∉ _ => fast_set_solver!!
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
  - eapply kinding_weakening; eauto.
    rewrite insert_union_singleton_l.
    apply map_union_subseteq_l.
  - fast_set_solver!!.
Qed.

Theorem preservation Σ Γ e e' τ :
  gctx_wf Σ ->
  Σ; Γ ⊢ e : τ ->
  Σ ⊨ e -->! e' ->
  Σ; Γ ⊢ e' : τ.
Proof.
  hauto use: preservation_.
Qed.
