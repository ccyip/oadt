(** Admissible rules for semantics, typing and kinding. *)
From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.
From oadt Require Import lang_oadt.infrastructure.
From oadt Require Import lang_oadt.equivalence.

Import syntax.notations.
Import semantics.notations.
Import typing.notations.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

#[local]
Coercion EFVar : atom >-> expr.

(** * Admissible step introduction rules *)

(** These lemma is equivalent to the corresponding constructor, but more
friendly for automation. *)
Lemma SCtx_intro Σ ℇ e e' E E' :
    Σ ⊨ e -->! e' ->
    ℇ e = E ->
    ℇ e' = E' ->
    ectx ℇ ->
    Σ ⊨ E -->! E'.
Proof.
  hauto ctrs: step.
Qed.

(** * Renaming lemmas *)

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
            rewrite <- ?subst_open_distr by constructor;
            rewrite <- ?subst_open_comm by (try constructor; shelve);
            try lazymatch Γ with
                | <[_:=_]>(<[_:=_]>({_↦_} <$> _)) =>
                  first [ rewrite <- fmap_insert
                        (* We may have to apply commutativity first. *)
                        | rewrite insert_commute by shelve;
                          rewrite <- fmap_insert ]
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
                 apply pared_equiv_rename
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

  (* Prove the types of [if] and [case] match the induction hypotheses. *)
  all : rewrite subst_open_distr by constructor; simpl; eauto;
    rewrite decide_False by shelve; eauto.

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
Lemma typing_rename_alt Σ Γ e s τ τ' x y :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ e^x : τ^({y↦x}s) ->
  x ∉ fv τ' ∪ fv e ∪ fv τ ∪ fv s ∪ dom aset Γ ∪ tctx_fv Γ ->
  y ∉ fv τ' ∪ fv e ∪ dom aset Γ ->
  Σ; (<[y:=τ']>Γ) ⊢ e^y : τ^s.
Proof.
  intros.
  destruct (decide (y = x)); subst.
  - srewrite subst_id; eauto.
  - rewrite <- (subst_tctx_fresh Γ x y) by fast_set_solver!!.
    rewrite (subst_intro e y x) by fast_set_solver!!.
    apply_eq typing_rename_; eauto.
    fast_set_solver!!.
    simpl_fv. fast_set_solver!!.
    rewrite subst_open_distr by constructor.
    rewrite subst_trans by fast_set_solver!!.
    rewrite subst_id.
    rewrite subst_fresh by fast_set_solver!!.
    eauto.
Qed.

Lemma typing_rename Σ Γ e τ τ' x y :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ e^x : τ^x ->
  x ∉ fv τ' ∪ fv e ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ->
  y ∉ fv τ' ∪ fv e ∪ dom aset Γ ->
  Σ; (<[y:=τ']>Γ) ⊢ e^y : τ^y.
Proof.
  intros.
  destruct (decide (y = x)); subst; eauto.
  eapply typing_rename_alt; simpl; eauto.
  rewrite decide_True by eauto; eauto.
  fast_set_solver!!.
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

(** * Admissible typing and kinding introduction rules *)
Section typing_kinding_intro.

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
    | |- _ ⊢ _ : _^(fvar _) => eapply typing_rename
    | |- _ ⊢ _ : _^_ => eapply typing_rename_alt; try relax_typing_type
    | |- _ ⊢ _ : _ => eapply typing_rename_lc
    | |- _ ⊢ _ :: _ => eapply kinding_rename
    end; eauto;
      try match goal with
          | |- _ ∉ _ => try fast_set_solver!!; simpl_fv; fast_set_solver!!
          end.

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
    <[x:=τ1]>Γ ⊢ e1^x : τ^(inl<τ1 + τ2> x) ->
    <[x:=τ2]>Γ ⊢ e2^x : τ^(inr<τ1 + τ2> x) ->
    Γ ⊢ e0 : τ1 + τ2 ->
    Γ ⊢ τ^e0 :: κ ->
    x ∉ fv e1 ∪ fv e2 ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ->
    Γ ⊢ case e0 of e1 | e2 : τ^e0.
  Proof.
    typing_intro_solver.

    all : simpl; rewrite decide_True by eauto;
      rewrite !subst_fresh by fast_set_solver!!; eauto.
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
    eauto using kinding, join_ub_l, join_ub_r.
  Qed.

End typing_kinding_intro.

(** * Tactics *)

(** Tactics for apply typing/kinding rules. Similar to [econstructor], but it
uses the admissible rules. It also fails rather than applying [TConv]
blindly. *)
(* NOTE: it would be great if [econstructor] can apply all but some
constructors. *)
Ltac typing_intro_ Σ T :=
  lazymatch T with
  | Σ; _ ⊢ fvar _ : _ => eapply TFVar
  | Σ; _ ⊢ gvar _ : _ => eapply TFun
  | Σ; _ ⊢ \:_ => _ : _ => eapply TAbs_intro
  | Σ; _ ⊢ let _ in _ : _ => eapply TLet_intro
  | Σ; _ ⊢ _ _ : _ => eapply TApp
  | Σ; _ ⊢ () : _ => eapply TUnit
  | Σ; _ ⊢ lit _ : _ => eapply TLit
  | Σ; _ ⊢ s𝔹 _ : _ => eapply TSec
  | Σ; _ ⊢ (_, _) : _ => eapply TPair
  | Σ; _ ⊢ ~if _ then _ else _ : _ => eapply TMux
  | Σ; _ ⊢ π@_ _ : _ => eapply TProj
  | Σ; _ ⊢ inj@_<_> _ : _ => eapply TInj
  | Σ; _ ⊢ ~inj@_<_> _ : _ => eapply TOInj
  | Σ; _ ⊢ ~case _ of _ | _ : _ => eapply TOCase_intro
  | Σ; _ ⊢ fold<_> _ : _ => eapply TFold
  | Σ; _ ⊢ unfold<_> _ : _ => eapply TUnfold
  | Σ; _ ⊢ if _ then _ else _ : _ => eapply TIf
  | Σ; _ ⊢ case _ of _ | _ : _ => eapply TCase_intro
  | Σ; _ ⊢ [_] : _ => eapply TBoxedLit
  | Σ; _ ⊢ [inj@_<_> _] : _ => eapply TBoxedInj
  | Σ; _ ⊢ ?e : ?τ => is_var e; assert_fails (is_evar τ); eapply TConv
  end.

Ltac kinding_intro_ Σ T :=
  lazymatch T with
  | Σ; _ ⊢ gvar _ :: _ => eapply KADT
  | Σ; _ ⊢ 𝟙 :: _ => eapply KUnit
  | Σ; _ ⊢ 𝔹{_} :: _ => eapply KBool
  | Σ; _ ⊢ Π:_, _ :: _ => eapply KPi_intro
  | Σ; _ ⊢ (gvar _) _ :: _ => eapply KOADT
  | Σ; _ ⊢ _ * _ :: _ => eapply KProd_intro
  | Σ; _ ⊢ _ + _ :: _ => eapply KSum
  | Σ; _ ⊢ _ ~+ _ :: _ => eapply KOSum
  | Σ; _ ⊢ if _ then _ else _ :: _ => eapply KIf
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
