From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.
From oadt Require Import lang_oadt.infrastructure.
From oadt Require Import lang_oadt.properties.

(** * Admissible Rules *)

Import syntax.notations.
Import semantics.notations.
Import typing.notations.

Implicit Types (x X y Y : atom) (L : aset).
Implicit Types (b : bool).

#[local]
Coercion EFVar : atom >-> expr.

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
