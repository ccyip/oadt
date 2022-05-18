From oadt.lang_oadt Require Import
     base syntax semantics typing infrastructure
     equivalence admissible inversion values weakening.
Import syntax.notations semantics.notations typing.notations equivalence.notations.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

#[local]
Coercion EFVar : atom >-> expr.

(** * Substitution lemmas *)

Section fix_gctx.

Context (Σ : gctx).
Context (Hwf : gctx_wf Σ).

#[local]
Set Default Proof Using "Hwf".

Lemma subst_tctx_typing_kinding_ x s :
  (forall Γ e l τ,
      Γ ⊢ e :{l} τ ->
      x ∉ fv τ ∪ dom aset Γ ->
      ({x↦s} <$> Γ) ⊢ e :{l} τ) /\
  (forall Γ τ κ,
      Γ ⊢ τ :: κ ->
      x ∉ dom aset Γ ->
      ({x↦s} <$> Γ) ⊢ τ :: κ).
Proof.
  apply typing_kinding_mutind; intros; subst; simpl in *;
    econstructor; eauto;
      simpl_cofin?;
      (* Try to apply induction hypotheses. *)
      lazymatch goal with
      | |- ?Γ ⊢ ?e : _ =>
        auto_apply || lazymatch goal with
                      | H : _ -> ?Γ' ⊢ e : _ |- _ =>
                        replace Γ with Γ'; [auto_apply |]
                      end
      | |- ?Γ ⊢ ?τ :: _ =>
        auto_apply || lazymatch goal with
                      | H : _ -> ?Γ' ⊢ τ :: _ |- _ =>
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
                 rewrite <- ?lexpr_subst_distr; rewrite subst_fresh
               end;
        eauto.

  Unshelve.

  all : try fast_set_solver!!; simpl_fv; fast_set_solver!!.
Qed.

Lemma subst_tctx_typing Γ e l τ x s :
  Γ ⊢ e :{l} τ ->
  x ∉ fv τ ∪ dom aset Γ ->
  ({x↦s} <$> Γ) ⊢ e :{l} τ.
Proof.
  qauto use: subst_tctx_typing_kinding_.
Qed.

(* Note that [lc s] is not needed, and it is here only for convenience. I will
drop it in the actual lemma. *)
Lemma subst_preservation_ x s l' τ' :
  lc s ->
  (forall Γ' e l τ,
      Γ' ⊢ e :{l} τ ->
      forall Γ,
        Γ' = <[x:=(l', τ')]>Γ ->
        x ∉ fv τ' ∪ dom aset Γ ->
        Γ ⊢ s :{l'} τ' ->
        ({x↦s} <$> Γ) ⊢ {x↦s}e :{l} {x↦s}τ) /\
  (forall Γ' τ κ,
      Γ' ⊢ τ :: κ ->
      forall Γ,
        Γ' = <[x:=(l', τ')]>Γ ->
        x ∉ fv τ' ∪ dom aset Γ ->
        Γ ⊢ s :{l'} τ' ->
        ({x↦s} <$> Γ) ⊢ {x↦s}τ :: κ).
Proof.
  intros Hlc.
  apply typing_kinding_mutind; intros; subst; simpl in *;
    (* First we normalize the typing and kinding judgments so they are ready
    for applying typing and kinding rules to. *)
    rewrite ?subst_open_distr by assumption;
    rewrite ?subst_ite_distr;
    try lazymatch goal with
        | |- _ ⊢ [inj@_< ?ω > _] : {_↦_}?ω =>
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
                  try rewrite lexpr_subst_distr;
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
      | |- ?Γ ⊢ _ : _ => go Γ
      | |- ?Γ ⊢ _ :: _ => go Γ
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
               | |- _ ≡ _ =>
                 apply pared_equiv_subst2
               | |- (_ <$> _) !! _ = Some _ =>
                 simplify_map_eq
               | |- <[_:=_]>_ ⊢ _ : _ =>
                 apply weakening_insert
               | |- Some _ = Some _ =>
                 try reflexivity; repeat f_equal
               | |- _ = <{ {_↦_} _ }> =>
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
Lemma subst_preservation x s l' τ' Γ e l τ :
  <[x:=(l', τ')]>Γ ⊢ e :{l} τ ->
  Γ ⊢ s :{l'} τ' ->
  x ∉ fv τ' ∪ dom aset Γ ∪ tctx_fv Γ ->
  Γ ⊢ {x↦s}e :{l} {x↦s}τ.
Proof.
  intros.
  rewrite <- (subst_tctx_fresh Γ x s) by fast_set_solver!!.
  eapply subst_preservation_; eauto using typing_lc.
  fast_set_solver!!.
Qed.

Lemma kinding_subst_preservation x s l' τ' Γ τ κ :
  <[x:=(l', τ')]>Γ ⊢ τ :: κ ->
  Γ ⊢ s :{l'} τ' ->
  x ∉ fv τ' ∪ dom aset Γ ∪ tctx_fv Γ ->
  Γ ⊢ {x↦s}τ :: κ.
Proof.
  intros.
  rewrite <- (subst_tctx_fresh Γ x s) by fast_set_solver!!.
  eapply subst_preservation_; eauto using typing_lc.
  fast_set_solver!!.
Qed.

Lemma open_preservation_alt x s l' τ' Γ e l τ :
  <[x:=(l', τ')]>Γ ⊢ e^x :{l} τ ->
  Γ ⊢ s :{l'} τ' ->
  x ∉ fv τ' ∪ fv e ∪ dom aset Γ ∪ tctx_fv Γ ->
  Γ ⊢ e^s :{l} {x↦s}τ.
Proof.
  intros.
  rewrite (subst_intro e s x) by fast_set_solver!!.
  eapply subst_preservation; eauto.
  fast_set_solver!!.
Qed.

Lemma open_preservation x s l' τ' Γ e l τ :
  <[x:=(l', τ')]>Γ ⊢ e^x :{l} τ^x ->
  Γ ⊢ s :{l'} τ' ->
  x ∉ fv τ' ∪ fv e ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ->
  Γ ⊢ e^s :{l} τ^s.
Proof.
  intros.
  rewrite (subst_intro e s x) by fast_set_solver!!.
  rewrite (subst_intro τ s x) by fast_set_solver!!.
  eapply subst_preservation; eauto.
  fast_set_solver!!.
Qed.

Lemma kinding_open_preservation x s l' τ' Γ τ κ :
  <[x:=(l', τ')]>Γ ⊢ τ^x :: κ ->
  Γ ⊢ s :{l'} τ' ->
  x ∉ fv τ' ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ->
  Γ ⊢ τ^s :: κ.
Proof.
  intros.
  rewrite (subst_intro τ s x) by fast_set_solver!!.
  eapply kinding_subst_preservation; eauto.
  fast_set_solver!!.
Qed.

Lemma open_preservation_lc x s l' τ' Γ e l τ :
  <[x:=(l', τ')]>Γ ⊢ e^x :{l} τ ->
  Γ ⊢ s :{l'} τ' ->
  x ∉ fv τ' ∪ fv e ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ->
  Γ ⊢ e^s :{l} τ.
Proof.
  intros H. intros.
  erewrite <- (open_lc_intro τ s) by eauto using typing_type_lc.
  erewrite <- (open_lc_intro τ x) in H by eauto using typing_type_lc.
  eapply open_preservation; eauto.
Qed.

(** * Other lemmas *)

(** Types of well-typed expressions are well-kinded *)
Lemma regularity Γ e l τ :
  Γ ⊢ e :{l} τ ->
  exists κ, Γ ⊢ τ :: κ.
Proof.
  induction 1; simp_hyps; eauto using kinding;
    try (apply_gctx_wf; eauto using kinding_weakening_empty);
    kind_inv; simpl_cofin?; simp_hyps;
    try first [ eexists; typing_kinding_intro; eauto; fast_set_solver!!
              (* Types may be opened. *)
              | eexists; qauto use: kinding_open_preservation
                               solve: fast_set_solver!! ].
  (* Boxed injection case *)
  sfirstorder use: otval_well_kinded, ovalty_elim.
Qed.

Ltac apply_regularity :=
  select! (_ ⊢ _ : _)
        (fun H => dup_hyp H (fun H => eapply regularity in H; simp_hyp H)).

(** We can substitute with an equivalent type and a more permissive label in the
typing contexts. *)
Lemma subst_conv_ x l1 l2 τ1 τ2 :
  τ1 ≡ τ2 ->
  (forall Γ' e l τ,
      Γ' ⊢ e :{l} τ ->
      forall Γ κ',
        Γ' = <[x:=(l1, τ1)]>Γ ->
        x ∉ dom aset Γ ->
        Γ ⊢ τ2 :: κ' ->
        l2 ⊑ l1 ->
        <[x:=(l2, τ2)]>Γ ⊢ e :{l} τ) /\
  (forall Γ' τ κ,
      Γ' ⊢ τ :: κ ->
      forall Γ κ',
        Γ' = <[x:=(l1, τ1)]>Γ ->
        x ∉ dom aset Γ ->
        Γ ⊢ τ2 :: κ' ->
        l2 ⊑ l1 ->
        <[x:=(l2, τ2)]>Γ ⊢ τ :: κ).
Proof.
  intros Heq.
  apply typing_kinding_mutind; intros; subst;
    (* [TFVar] is the key base case. Prove it later *)
    try lazymatch goal with
        | |- _ ⊢ fvar _ : _ =>
          shelve
        end;
    try solve [ econstructor; eauto ];
    simpl_cofin?;
    repeat
      match goal with
      | H : forall _ _, _ -> _ -> _ -> _ -> _ |- _ =>
        efeed specialize H;
          [ try reflexivity; rewrite insert_commute by shelve; reflexivity
          | fast_set_solver!!
          | eauto using kinding_weakening_insert
          | solve [eauto]
          | .. ];
          try rewrite insert_commute in H by shelve
      end;

    try apply_regularity;
    try eapply TConv;
      repeat
        (eauto;
         lazymatch goal with
         | |- _ ⊢ _ : _ =>
           typing_intro
         | |- _ ⊢ _^_ :: _ =>
           eapply kinding_open_preservation
         | |- _ ⊢ _ :: _ =>
           kinding_intro
         | |- _ ≡ _ =>
           equiv_naive_solver
         | |- _ ∉ _ =>
           shelve
         end).

  Unshelve.

  (* [TFVar] *)
  match goal with
  | |- _ ⊢ fvar ?x' : _ => destruct (decide (x' = x))
  end; subst;
    try solve [ econstructor; simplify_map_eq; eauto ].
  simplify_map_eq.
  eapply TConv; eauto.
  typing_intro; simplify_map_eq; eauto.
  eauto using kinding_weakening_insert.
  equiv_naive_solver.

  all : try fast_set_solver!!; simpl_fv; fast_set_solver!!.
Qed.

Lemma subst_conv Γ e l τ κ' x l1 l2 τ1 τ2 :
  <[x:=(l1, τ1)]>Γ ⊢ e :{l} τ ->
  Γ ⊢ τ2 :: κ' ->
  τ1 ≡ τ2 ->
  l2 ⊑ l1 ->
  x ∉ dom aset Γ ->
  <[x:=(l2, τ2)]>Γ ⊢ e :{l} τ.
Proof.
  hauto use: subst_conv_.
Qed.

Lemma kinding_subst_conv Γ τ κ κ' x l1 l2 τ1 τ2 :
  <[x:=(l1, τ1)]>Γ ⊢ τ :: κ ->
  Γ ⊢ τ2 :: κ' ->
  τ1 ≡ τ2 ->
  l2 ⊑ l1 ->
  x ∉ dom aset Γ ->
  <[x:=(l2, τ2)]>Γ ⊢ τ :: κ.
Proof.
  hauto use: subst_conv_.
Qed.

Lemma oval_safe Γ v l τ :
  Γ ⊢ v :{l} τ ->
  oval v ->
  Γ ⊢ v :{⊥} τ.
Proof.
  intros Ht Hv.
  apply_regularity.
  apply woval_otval in Ht; eauto using oval_woval. simp_hyps.
  eapply ovalty_intro in Hv; eauto.
  select (_ ⊢ _ : _) (fun H => clear H).
  eapply ovalty_elim in Hv. simp_hyps.
  econstructor; eauto.
Qed.

(** * Preservation *)

(** The combined preservation theorems for parallel reduction. *)
Lemma pared_preservation_ :
  (forall Γ e l τ,
      Γ ⊢ e :{l} τ ->
      forall e', e ⇛ e' ->
            Γ ⊢ e' :{l} τ) /\
  (forall Γ τ κ,
      Γ ⊢ τ :: κ ->
      forall τ', τ ⇛ τ' ->
            Γ ⊢ τ' :: κ).
Proof.
  apply typing_kinding_mutind; intros; subst;
    (* Inversion on parallel reduction. *)
    repeat pared_inv;
    simplify_eq;
    try apply_gctx_wf;
    simpl_cofin?;
    (* Solve some trivial cases. *)
    try solve [ lazymatch goal with
                | H : _ !! _ = Some (DFun _ _) |- _ =>
                  eauto using weakening_empty
                end
              | lazymatch goal with
                | H : oval _ |- _ =>
                    eauto using oval_safe
                end
              | try case_ite_expr;
                simp_hyps;
                repeat
                  (eauto;
                   lazymatch goal with
                   | |- _ ⊢ _ : ?τ =>
                     first [ is_evar τ | econstructor ]
                   | |- _ ⊢ _ :: ?κ =>
                     first [ is_evar κ | econstructor ]
                   end)];
    (* Now turn to the more interesting cases. *)
    (* Derive some equivalence for later convenience. *)
    try select! (_ ⇛ _)
        (fun H => dup_hyp H (fun H => apply pared_equiv_pared in H));
    (* Derive well-kindedness from typing. *)
    try apply_regularity;
    (* Apply inversion lemmas for typing and kinding. *)
    kind_inv;
    type_inv;
    (* Instantiate induction hypotheses. *)
    repeat
      match goal with
      | H : forall _, _ ⇛ _ -> _ |- _ =>
        efeed specialize H; [
          solve [ repeat
                    (eauto;
                     lazymatch goal with
                     | |- ?e ⇛ _ =>
                       first [ lazymatch e with
                               | <{ ~if _ then _ else _ }> =>
                                 eapply RCgrIte
                               end
                             | match goal with
                               | H : ?e1 ⇛ _ |- _ =>
                                   let e1 := lazymatch e1 with
                                             | <{ ?e1^_ }> => e1
                                             | _ => e1
                                             end in
                                   lazymatch e with
                                   | context [e1] =>
                                       head_constructor e; pared_intro
                                   end
                               end
                             | eapply pared_open1
                             | lcrefl ]
                     | |- lc _ => eauto using lc, kinding_lc
                     | |- _ ∉ _ => shelve
                     end) ]
         |];
        try type_inv H;
        try kind_inv H
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
       | H : <[_:=_]>_ ⊢ _ :{?l} _ |- <[_:=_]>_ ⊢ _ :{?l} _ =>
           eapply subst_conv
       | |- <[_:=_]>_ ⊢ _ :{?l} _ =>
           is_evar l; eapply subst_conv
       | |- <[_:=_]>_ ⊢ _ :: _ =>
           eapply kinding_subst_conv
       (* Apply substitution/open lemmas. *)
       | H : <[_:=_]>?Γ ⊢ ?e^(fvar _) : ?τ |- ?Γ ⊢ ?e^_ : ?τ =>
           eapply open_preservation_lc
       | H : <[_:=_]>?Γ ⊢ ?e^(fvar _) : _^(fvar _) |- ?Γ ⊢ ?e^_ : _ =>
           eapply open_preservation
       (* This is for the dependent case expression. *)
       | H : <[_:=_]>?Γ ⊢ ?e^(fvar _) : _^_ |- ?Γ ⊢ ?e^_ : _ =>
           eapply open_preservation_alt
       | H : <[_:=_]>?Γ ⊢ ?e^(fvar _) :: _ |- ?Γ ⊢ ?e^_ :: _ =>
           eapply kinding_open_preservation
       (* Apply typing rules. *)
       | |- _ ⊢ _ : _ =>
           typing_intro
       | |- _ ⊢ _ : ?τ =>
           assert_fails is_evar τ; eapply TConv
       (* Apply kinding rules. *)
       | |- _ ⊢ _ :: ?κ =>
           eauto using kinding_weakening_empty; kinding_intro
       (* Solve equivalence. *)
       | |- _ ≡ _ =>
           try case_split; equiv_naive_solver
       | |- _ ≡ _ =>
           apply_pared_equiv_congr
       | |- <{ _^_ }> ≡ <{ _^_ }> =>
           eapply pared_equiv_open1; simpl_cofin?
       | |- <{ _^_ }> ≡ <{ _^_ }> =>
           eapply pared_equiv_open
       (* Solve other side conditions. *)
       | |- lc _ =>
           eauto using lc, open_respect_lc,
           typing_type_lc, typing_lc, kinding_lc
       | |- _ ⊑ _ =>
           first [ lattice_naive_solver
                     by eauto using (top_ub (A:=bool)),
                                    (join_ub_l (A:=bool)), (join_ub_r (A:=bool))
                 | hauto use: (join_lub (A:=bool)) ]
       | |- _ ∉ _ => shelve
       end).

  (* The case when oblivious injection steps to boxed injection. *)
  hauto lq: on ctrs: ovalty inv: otval use: ovalty_intro.

  (* These equivalence are generated by the case when the case discriminee takes
  a step. *)
  1-2 :
  rewrite subst_open_distr by eauto using typing_lc; simpl;
  rewrite decide_True by auto;
  rewrite !subst_fresh by shelve;
  eapply pared_equiv_open1; simpl_cofin?;
  eauto 7 using lc, open_respect_lc, typing_lc, kinding_lc, pared_equiv_congr_inj
          with equiv_naive_solver.

  (* These 4 cases are generated by the case when oblivious case analysis steps
  to oblivious condition. *)
  1-4 :
  repeat ovalty_inv;
  select! (ovalty _ _) (fun H => apply ovalty_elim in H; simp_hyp H);
  eapply TConv;
  eauto using weakening, map_empty_subseteq with equiv_naive_solver.

  (* The case when we apply oblivious type to its argument: [RAppOADT] *)
  eapply kinding_open_preservation; eauto; try set_shelve.
  eapply kinding_weakening; eauto.
  rewrite insert_union_singleton_l.
  apply map_union_subseteq_l.

  Unshelve.

  all : fast_set_solver!!.
Qed.

Lemma pared_preservation Γ e l e' τ :
  Γ ⊢ e :{l} τ ->
  e ⇛ e' ->
  Γ ⊢ e' :{l} τ.
Proof.
  hauto use: pared_preservation_.
Qed.

Lemma pared_kinding_preservation Γ τ τ' κ :
  Γ ⊢ τ :: κ ->
  τ ⇛ τ' ->
  Γ ⊢ τ' :: κ.
Proof.
  hauto use: pared_preservation_.
Qed.

(** The preservation theorem for [step]. *)
Theorem preservation Γ e l e' τ :
  Γ ⊢ e :{l} τ ->
  e -->! e' ->
  Γ ⊢ e' :{l} τ.
Proof.
  hauto use: pared_preservation, pared_step, typing_lc.
Qed.

Theorem kinding_preservation Γ τ τ' κ :
  Γ ⊢ τ :: κ ->
  τ -->! τ' ->
  Γ ⊢ τ' :: κ.
Proof.
  hauto use: pared_kinding_preservation, pared_step, kinding_lc.
Qed.

End fix_gctx.

Ltac apply_regularity :=
  select! (_ ⊢ _ : _)
        (fun H => dup_hyp H (fun H => eapply regularity in H;
                                  [ simp_hyp H | assumption ])).
