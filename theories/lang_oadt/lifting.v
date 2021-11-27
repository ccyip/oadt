From oadt.lang_oadt Require Import
     base syntax semantics typing infrastructure
     admissible inversion values weakening preservation progress reveal.
Import syntax.notations semantics.notations typing.notations.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

#[local]
Coercion EFVar : atom >-> expr.

(** * Definitions *)

(** ** Section and retraction context (Δ) *)
(** Map ADT and OADT pair to section and retraction functions. *)
Notation srctx := (aamap (atom * atom)).

Definition srctx_wf (Σ : gctx) : srctx -> Prop :=
  map_Forall (fun '(X, X') '(s, r) =>
                exists τ τk e se re,
                  Σ !! X = Some (DADT τ) /\
                  Σ !! X' = Some (DOADT τk e) /\
                  Σ !! s = Some (DFun (⊥, <{ Π:τk, Π~:(gvar X), X'@(bvar 1) }>)
                                 se) /\
                  Σ !! r = Some (DFun (⊤, <{ Π:τk, Π~:(X'@(bvar 0)), gvar X }>)
                                 re)).

(* Destructive *)
Ltac apply_srctx_wf :=
  match goal with
  | Hwf : srctx_wf _ ?Δ, H : ?Δ !! _ = Some _ |- _ =>
    apply Hwf in H; try simp_hyp H
  end.

Section lifting.

Context (Σ : gctx).
Context (Hwf : gctx_wf Σ).
Context (Δ : srctx).
Context (Hsrwf : srctx_wf Σ Δ).

(** ** Generalized section *)
(** Compute the section of [e] from public type [τ] to oblivious type [τ']. [e]
is assumed a [body]. Alternatively, we may assume [e] is locally closed, and
open/close the expressions accordingly. That way we also need to record the used
atoms in an extra arguments, similar to the lifting functions below. *)
Fixpoint gsec (τ τ' : expr) (e : expr) : option expr :=
  match τ, τ' with
  | <{ 𝟙 }>, <{ 𝟙 }> => Some <{ tape e }>
  | <{ 𝔹 }>, <{ ~𝔹 }> => Some <{ tape (s𝔹 e) }>
  | <{ τ1 * τ2 }>, <{ τ1' * τ2' }> =>
    e1 <- gsec τ1 τ1' <{ π1 e }>;
    e2 <- gsec τ2 τ2' <{ π2 e }>;
    Some <{ (e1, e2) }>
  | <{ τ1 + τ2 }>, <{ τ1' ~+ τ2' }> =>
    e1 <- gsec τ1 τ1' <{ bvar 0 }>;
    e2 <- gsec τ2 τ2' <{ bvar 0 }>;
    Some <{ tape (case e of ~inl<τ1' ~+ τ2'> e1 | ~inr<τ1' ~+ τ2'> e2) }>
  (* Outsource to predefined context *)
  | <{ gvar X }>, <{ X'@k }> =>
    '(s, _) <- Δ !! (X, X');
    Some <{ (gvar s) k e }>
  | _, _ => None
  end.

(** ** Generalized retraction *)
(** Compute the retraction of [e] from oblivious type [τ'] to public type [τ]. *)
Fixpoint gret (τ τ' : expr) (e : expr) : option expr :=
  match τ, τ' with
  (* Unlike section, retraction also allows the oblivious type [τ'] to contain
  non-oblivious components, as long as they match the corresponding components
  in [τ]. *)
  | <{ 𝟙 }>, <{ 𝟙 }> | <{ 𝔹 }>, <{ 𝔹 }> => Some e
  | <{ gvar X }>, <{ gvar Y }> =>
    if decide (X = Y) then Some e else None
  | <{ Π:{_}_, _ }>, <{ Π:{_}_, _ }> =>
    if decide (τ = τ') then Some e else None
  | <{ 𝔹 }>, <{ ~𝔹 }> => Some <{ ~if tape e then true else false }>
  | <{ τ1 * τ2 }>, <{ τ1' * τ2' }> =>
    e1 <- gret τ1 τ1' <{ π1 e }>;
    e2 <- gret τ2 τ2' <{ π2 e }>;
    Some <{ (e1, e2) }>
  | <{ τ1 + τ2 }>, <{ τ1' + τ2' }> =>
    e1 <- gret τ1 τ1' <{ bvar 0 }>;
    e2 <- gret τ2 τ2' <{ bvar 0 }>;
    Some <{ case e of inl<τ1 + τ2> e1 | inr<τ1 + τ2> e2 }>
  | <{ τ1 + τ2 }>, <{ τ1' ~+ τ2' }> =>
    e1 <- gret τ1 τ1' <{ bvar 0 }>;
    e2 <- gret τ2 τ2' <{ bvar 0 }>;
    Some <{ ~case tape e of inl<τ1 + τ2> e1 | inr<τ1 + τ2> e2 }>
  (* Outsource to predefined context *)
  | <{ gvar X }>, <{ X'@k }> =>
    '(_, r) <- Δ !! (X, X');
    Some <{ (gvar r) k e }>
  | _, _ => None
  end.

(** ** Lifting *)

(** The core lifting function. All arguments are supposed to be locally closed,
and the indices in [τ'] have been instantiated with free variables in [xs]. [e]
of type [τ] is lifted to the oblivious counterpart of type [τ']. [xs] keeps
track of used free variables. *)
Fixpoint lift_core (τ τ' : expr) (xs : aset) (e : expr) : option expr :=
  match τ, τ' with
  | <{ Π:{l}τ1, τ2 }>, <{ Π:{l'}τ1', τ2' }> =>
    (* The function argument of [e] should have a leakage label of [⊤]
    ([LLeak]), because it is applied to retraction. *)
    if l
    then let x := fresh xs in
         r <- gret τ1 τ1' <{ fvar x }>;
         (* [τ] and [τ'] are assumed non-dependent types, so [τ2] and [τ2']
         are locally closed. *)
         e' <- lift_core τ2 τ2' ({[x]} ∪ xs) <{ e r }>;
         Some <{ \:{l'}τ1' => ,(close x e') }>
    else None
  | _, _ => gsec τ τ' e
  end.

(** This function handles type index arguments and calls [lift_core] to do the
heavy lifting (pun intended). All arguments are locally closed. It lifts [e] of
type [τ] to the oblivious counterpart of type [τ']. Unlike [lift_core], [τ']
contains all the type index arguments from [τs]. *)
Fixpoint lift_ (τ τ' : expr) (τs : list expr) (xs : aset) (e : expr) : option expr :=
  match τs with
  | _::τs =>
    match τ' with
    | <{ Π:{_}τ1, τ2' }> =>
      let x := fresh xs in
      e' <- lift_ τ <{ τ2'^x }> τs ({[x]} ∪ xs) e;
      Some <{ \:τ1 => ,(close x e') }>
    | _ => None
    end
  | [] => lift_core τ τ' xs e
  end.

(** The top level lifting function. It lifts [e] of type [τ] to the oblivious
counterpart of type [τ'], whose public indices are [τs]. *)
Definition lift (τ τ' : expr) (τs : list expr) (e : expr) : option expr :=
  lift_ τ τ' τs ∅ e.

(** ** Well-formedness of lifting input *)

(** [τ] is not a dependent type (at top level). It may still take a higher-order
function that is dependently typed. *)
Fixpoint nodep (τ : expr) : Prop :=
  match τ with
  | <{ Π:{_}_, τ2 }> =>
    lc τ2 /\ nodep τ2
  | _ => True
  end.

(** [lift_type_wf τs τ'] means [τ'] is a valid lifted oblivious type with
indices [τs]. First, [τs] should be the "prefix" of [τ'], i.e. [τ'] is of the
form [Π:τ1, Π:τ2, ..., τ] where [τs] is [τ1, τ2, ...]. Second, index types in
[τs] are locally closed, i.e. there is no dependent type in indices. Third, the
type with indices instantiated is non-dependent, i.e. [τ] should have the form
[τ1 -> τ2 -> ...]. They can of course depend on the indices though. *)
Inductive lift_type_wf : list expr -> expr -> Prop :=
| LTVNil τ' : nodep τ' -> lift_type_wf [] τ'
| LTVCons τk τs τ' L :
    lc τk ->
    (forall x, x ∉ L -> lift_type_wf τs <{ τ'^x }>) ->
    lift_type_wf (τk::τs) <{ Π:τk, τ' }>
.

Instance list_expr_stale : Stale (list expr) := foldr (fun e S => fv e ∪ S) ∅.
Arguments list_expr_stale /.

(** * Theorems *)

(** ** Well-typedness of section and retraction *)

#[local]
Set Default Proof Using "Type".

Arguments open /.

Ltac simpl_sr :=
  intros; simpl in *; simplify_eq;
  repeat (case_split; simpl in *; simplify_eq);
  simplify_option_eq;
  simp_hyps; intros; subst; simpl in *.

Lemma gsec_body τ : forall τ' e e',
  gsec τ τ' e = Some e' ->
  lc τ' ->
  body e ->
  body e'.
Proof.
  unfold body, open.
  induction τ; simpl_sr;
      try solve [ eexists; simpl_cofin; eauto with lc ];
      repeat lc_inv;
      (* Apply induction hypotheses. *)
      repeat match goal with
             | IH : context [gsec ?τ _ _ = _ -> _], H : gsec ?τ _ _ = _ |- _ =>
               apply IH in H; clear IH
             end;
      simpl;
      eauto using lc;
      simp_hyps;
      eexists; simpl_cofin;
        try solve [ repeat econstructor; eauto; by rewrite open_lc ].

  econstructor.
  econstructor; eauto;
    simpl_cofin; simpl;
      repeat econstructor;
      try solve [ repeat (rewrite open_lc; eauto) ];
      rewrite open_comm by eauto using lc;
      rewrite open_lc; eauto with lc.

  Unshelve.
  all: exact ∅.
Qed.

Lemma gsec_open τ s : forall τ' e e',
  gsec τ τ' e = Some e' ->
  lc τ' ->
  gsec τ τ' <{ e^s }> = Some <{ e'^s }>.
Proof.
  unfold open.
  induction τ; simpl_sr; eauto;
    repeat lc_inv;
    repeat f_equal; try solve [ by rewrite !open_lc by eauto ].

  repeat match goal with
         | IH : context [gsec ?τ _ _ = _ -> _], H : gsec ?τ _ _ = _ |- _ =>
           apply IH in H; clear IH; [ simpl in H; rewrite H | .. ]
         end;
    eauto.

  all: rewrite open_body; eauto using gsec_body, body_bvar.
Qed.

Lemma gsec_well_typed τ : forall τ' e e' Γ κ κ',
  gsec τ τ' e = Some e' ->
  Γ ⊢ τ :: κ ->
  Γ ⊢ τ' :: κ' ->
  Γ ⊢ e :{⊤} τ ->
  Γ ⊢ e' :{⊥} τ'.
Proof using Hsrwf.
  induction τ; simpl_sr;
    eauto using typing, kinding;
    kind_inv.
  (* OADT application *)
  - apply_srctx_wf. simplify_eq.
    relax_typing_type.
    econstructor; eauto.
    relax_typing_type.
    econstructor; eauto.
    econstructor; eauto.
    reflexivity.
    simpl.
    rewrite open_lc; eauto with lc.
  (* Product *)
  - econstructor;
      try match goal with
          | H : _ -> _ |- _ ⊢ _ :{_} _ =>
            eapply H; eauto using kinding;
              solve [ relax_typing_type; econstructor; eauto ]
          end.
    reflexivity.
  (* Sum *)
  - econstructor; eauto using kinding.
    econstructor; eauto using kinding;
        simpl; simpl_cofin;
        match goal with
        | |- context [<{ ?τ1 ~+ ?τ2 }>] =>
          rewrite open_lc with (e := τ1) by eauto with lc;
            rewrite open_lc with (e := τ2) by eauto with lc
        end;
        econstructor; eauto using kinding, kinding_weakening_insert;
          match goal with
          | IH : context [gsec ?τ _ _ = _ -> _],
                 H : gsec ?τ ?τ' _ = _ |- _ ⊢ _:{_} ?τ' =>
            eapply IH
          end;
          eauto using gsec_open, kinding_weakening_insert with lc;
          simpl; econstructor; simplify_map_eq;
            eauto using kinding_weakening_insert.
Qed.

Lemma gret_body τ : forall τ' e e',
  gret τ τ' e' = Some e ->
  lc τ ->
  lc τ' ->
  body e' ->
  body e.
Proof.
  unfold body, open.
  induction τ; simpl_sr;
      try solve [ eexists; simpl_cofin; eauto with lc ];
      repeat lc_inv;
      (* Apply induction hypotheses. *)
      repeat match goal with
             | IH : context [gret ?τ _ _ = _ -> _], H : gret ?τ _ _ = _ |- _ =>
               apply IH in H; clear IH
             end;
      simpl;
      eauto using lc;
      simp_hyps;
      eexists; simpl_cofin;
        try solve [ repeat econstructor; eauto; by rewrite open_lc ].

  all: econstructor; eauto using lc;
    simpl_cofin; simpl;
      repeat econstructor;
      try solve [ repeat (rewrite open_lc; eauto) ];
      rewrite open_comm by eauto using lc;
      rewrite open_lc; eauto with lc.

  Unshelve.
  all: exact ∅.
Qed.

Lemma gret_open τ s : forall τ' e e',
  gret τ τ' e' = Some e ->
  lc τ ->
  lc τ' ->
  gret τ τ' <{ e'^s }> = Some <{ e^s }>.
Proof.
  unfold open.
  induction τ; simpl_sr; eauto;
    repeat lc_inv;
    repeat f_equal; try solve [ by rewrite !open_lc by eauto ].

  repeat match goal with
         | IH : context [gret ?τ _ _ = _ -> _], H : gret ?τ _ _ = _ |- _ =>
           apply IH in H; clear IH; [ simpl in H; rewrite H | .. ]
         end;
    eauto.

  all: repeat f_equal;
    try solve [ by rewrite !open_lc by eauto ];
    rewrite open_body; eauto using gret_body, body_bvar.
Qed.

Lemma gret_well_typed τ : forall τ' e e' Γ κ κ',
  gret τ τ' e' = Some e ->
  Γ ⊢ τ :: κ ->
  Γ ⊢ τ' :: κ' ->
  Γ ⊢ e' :{⊤} τ' ->
  Γ ⊢ e :{⊤} τ.
Proof using Hsrwf.
  induction τ; simpl_sr;
    eauto using typing, kinding;
    kind_inv.

  (* OADT application *)
  apply_srctx_wf. simplify_eq.
  relax_typing_type.
  econstructor; eauto.
  relax_typing_type.
  econstructor; eauto.
  econstructor; eauto.
  reflexivity.
  reflexivity.

  (* Product *)
  econstructor;
    try match goal with
        | H : _ -> _ |- _ ⊢ _ :{_} _ =>
          eapply H; eauto using kinding;
            solve [ relax_typing_type; econstructor; eauto ]
        end.
  reflexivity.

  (* Sum *)
  all: econstructor; eauto using typing, kinding;
    simpl; simpl_cofin;
      match goal with
      | |- context [<{ ?τ1 + ?τ2 }>] =>
        rewrite open_lc with (e := τ1) by eauto with lc;
          rewrite open_lc with (e := τ2) by eauto with lc
      end;
      econstructor; eauto using kinding, kinding_weakening_insert;
        match goal with
        | IH : context [gret ?τ _ _ = _ -> _] |- _ ⊢ _:{_} ?τ =>
          eapply IH
        end;
        eauto using gret_open, kinding_weakening_insert with lc;
        simpl; (eapply TConv; [ econstructor; simplify_map_eq | .. ];
                eauto using kinding_weakening_insert; reflexivity).
Qed.

(** ** Properties of input well-formedness *)

Lemma nodep_rename_ τ x y :
  nodep <{ τ }> ->
  nodep <{ {x↦y}τ }>.
Proof.
  induction τ; simpl; intros; eauto.
  - case_decide; eauto.
  - simp_hyps. eauto with lc.
Qed.

Lemma lift_type_wf_rename_ τs τ' x y :
  x # τs ->
  lift_type_wf τs τ' ->
  lift_type_wf τs <{ {x↦y}τ' }>.
Proof.
  intros ?.
  induction 1; intros; subst; simpl in *.
  - econstructor. eauto using nodep_rename_.
  - rewrite subst_fresh.
    econstructor; eauto.
    simpl_cofin.
    rewrite <- subst_open_comm; eauto using lc.
    auto_eapply.
    all: fast_set_solver!!.
Qed.

Lemma lift_type_wf_rename τs τ' x y :
  x # τs ->
  x # τ' ->
  lift_type_wf τs <{ τ'^x }> ->
  lift_type_wf τs <{ τ'^y }>.
Proof.
  intros.
  rewrite (subst_intro τ' y x) by auto.
  eauto using lift_type_wf_rename_.
Qed.


(** ** Well-typedness of lifting *)

#[local]
Set Default Proof Using "All".

Arguments gret : simpl never.
Arguments gsec : simpl never.

Lemma lift_core_well_typed τ : forall τ' xs e e' κ' Γ,
  lift_core τ τ' xs e = Some e' ->
  nodep τ ->
  nodep τ' ->
  dom aset Γ ∪ tctx_fv Γ ⊆ xs ->
  Γ ⊢ τ' :: κ' ->
  Γ ⊢ e :{⊤} τ ->
  Γ ⊢ e' :{⊥} τ'.
Proof.
  induction τ; simpl; intros;
    apply_regularity;
    eauto using gsec_well_typed.

  repeat case_split; simplify_eq.
  simplify_option_eq.
  simp_hyps.
  kind_inv*. subst.
  pose proof (atom_is_fresh xs).

  match goal with
  | IH : context[ lift_core _ _ _ _ = _ -> _ ], H : lift_core _ _ _ _ = _ |- _ =>
    eapply IH in H
  end; eauto; try set_shelve.
  - typing_intro; eauto; try set_shelve.
    rewrite open_close by eauto with lc.
    rewrite open_lc_intro by auto.
    eauto.
  - simpl_cofin.
    eapply_eq kinding_rename; eauto; try set_shelve.
    by rewrite open_lc_intro by auto.
  - relax_typing_type.
    econstructor.
    + eapply weakening_insert; eauto; try set_shelve.
    + eapply gret_well_typed;
        try (goal_is (_ ⊢ _ :: _); eapply kinding_weakening_insert);
        eauto; try set_shelve.
      eapply TConv.
      econstructor. by simplify_map_eq.
      eapply kinding_weakening_insert; eauto; try set_shelve.
      reflexivity.
      eapply kinding_weakening_insert; eauto; try set_shelve.
      apply top_ub.
    + by rewrite open_lc_intro.

  Unshelve.
  all: try fast_set_solver!!;
           simpl_fv; rewrite ?close_fv by eauto with lc; try fast_set_solver*!!.
Qed.

Lemma lift_well_typed_ τ τs : forall τ' xs e e' κ' Γ,
  lift_ τ τ' τs xs e = Some e' ->
  nodep τ ->
  lift_type_wf τs τ' ->
  dom aset Γ ∪ tctx_fv Γ ⊆ xs ->
  Γ ⊢ τ' :: κ' ->
  Γ ⊢ e :{⊤} τ ->
  Γ ⊢ e' :{⊥} τ'.
Proof.
  induction τs; simpl; intros.
  - qauto use: lift_core_well_typed inv: lift_type_wf.
  - case_split; simplify_eq.
    simplify_option_eq.
    select (lift_type_wf _ _) (fun H => sinvert H).
    kind_inv*. subst.
    pose proof (atom_is_fresh xs).
    simpl_cofin.
    match goal with
    | IH : context [lift_ ?τ _ _ _ _ = _ -> _], H : lift_ _ _ _ _ _ = _ |- _ =>
      eapply IH in H
    end; try set_shelve.
    + typing_intro; eauto; try set_shelve.
      rewrite open_close; eauto with lc.
    + eauto.
    + eauto using lift_type_wf_rename.
    + eapply kinding_rename; eauto; try set_shelve.
    + eapply weakening_insert; eauto; try set_shelve.

  Unshelve.
  all: try fast_set_solver!!;
           simpl_fv; rewrite ?close_fv by eauto with lc; try fast_set_solver*!!.
Qed.

Theorem lift_well_typed τ τs τ' e e' κ :
  lift τ τ' τs e = Some e' ->
  nodep τ ->
  lift_type_wf τs τ' ->
  ∅ ⊢ τ' :: κ ->
  ∅ ⊢ e :{⊤} τ ->
  ∅ ⊢ e' :{⊥} τ'.
Proof.
  unfold lift.
  intros.
  eapply lift_well_typed_; eauto.
  fast_set_solver!!.
Qed.

End lifting.
