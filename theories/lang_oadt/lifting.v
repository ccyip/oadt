From oadt.lang_oadt Require Import
     base syntax semantics typing infrastructure
     admissible inversion values weakening preservation progress reveal.
Import syntax.notations semantics.notations typing.notations reveal.notations.

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
(** [gsec τ τ' e e'] means [e'] of oblivious type [τ'] is a section of [e] which
has a public type [τ]. *)
Inductive gsec : expr -> expr -> expr -> expr -> Prop :=
| GSUnit e : gsec <{ 𝟙 }> <{ 𝟙 }> e <{ tape e }>
| GSBool e : gsec <{ 𝔹 }> <{ ~𝔹 }> e <{ tape (s𝔹 e) }>
| GSProd τ1 τ1' τ2 τ2' e e1 e2 :
    gsec τ1 τ1' <{ π1 e }> e1 ->
    gsec τ2 τ2' <{ π2 e }> e2 ->
    gsec <{ τ1 * τ2 }> <{ τ1' * τ2' }> e <{ (e1, e2) }>
| GSSum τ1 τ1' τ2 τ2' e e1 e2 L1 L2 :
    (forall x, x ∉ L1 -> gsec τ1 τ1' x <{ e1^x }>) ->
    (forall x, x ∉ L2 -> gsec τ2 τ2' x <{ e2^x }>) ->
    gsec <{ τ1 + τ2 }> <{ τ1' ~+ τ2' }> e
         <{ tape (case e of ~inl<τ1' ~+ τ2'> e1 | ~inr<τ1' ~+ τ2'> e2) }>
(* Outsource to predefined context *)
| GSOADT X X' k s r e :
    Δ !! (X, X') = Some (s, r) ->
    gsec <{ gvar X }> <{ X'@k }> e <{ (gvar s) k e }>
.

(** ** Generalized retraction *)
(** [gret τ τ' e' e] means [e] of public type [τ] is a retraction of [e'] which
has an oblivious type [τ']. Unlike [gsec], retraction also allow the oblivious
type [τ'] to contain non-oblivious components, as long as they match the
corresponding components in [τ]. *)
Inductive gret : expr -> expr -> expr -> expr -> Prop :=
| GRId τ e : gret τ τ e e
| GRBool e' : gret <{ 𝔹 }> <{ ~𝔹 }> e' <{ ~if tape e' then true else false }>
| GRProd τ1 τ1' τ2 τ2' e' e1 e2 :
    <{ τ1 * τ2 }> <> <{ τ1' * τ2' }> ->
    gret τ1 τ1' <{ π1 e' }> e1 ->
    gret τ2 τ2' <{ π2 e' }> e2 ->
    gret <{ τ1 * τ2 }> <{ τ1' * τ2' }> e' <{ (e1, e2) }>
| GRSum τ1 τ1' τ2 τ2' e' e1 e2 L1 L2 :
    <{ τ1 + τ2 }> <> <{ τ1' + τ2' }> ->
    (forall x, x ∉ L1 -> gret τ1 τ1' x <{ e1^x }>) ->
    (forall x, x ∉ L2 -> gret τ2 τ2' x <{ e2^x }>) ->
    gret <{ τ1 + τ2 }> <{ τ1' + τ2' }> e'
         <{ case e' of inl<τ1 + τ2> e1 | inr<τ1 + τ2> e2 }>
| GROSum τ1 τ1' τ2 τ2' e' e1 e2 L1 L2 :
    (forall x, x ∉ L1 -> gret τ1 τ1' x <{ e1^x }>) ->
    (forall x, x ∉ L2 -> gret τ2 τ2' x <{ e2^x }>) ->
    gret <{ τ1 + τ2 }> <{ τ1' ~+ τ2' }> e'
         <{ ~case tape e' of inl<τ1 + τ2> e1 | inr<τ1 + τ2> e2 }>
(* Outsource to predefined context *)
| GROADT X X' k s r e' :
    Δ !! (X, X') = Some (s, r) ->
    gret <{ gvar X }> <{ X'@k }> e' <{ (gvar r) k e' }>
.

(** ** Lifting *)

(** The core lifting relation. [lift_core τ τ' e e'] means [e'] of oblivious
type [τ'] is the lifted result from [e] of public type [τ]. *)
Inductive lift_core : expr -> expr -> expr -> expr -> Prop :=
| LPi τ1 τ1' τ2 τ2' e e' r l' L1 L2 :
    (forall x, x ∉ L1 -> gret τ1 τ1' x <{ r^x }>) ->
    (* Types in [lift_core] are assumed to be non-dependent types, so [τ2] and
    [τ2'] are locally closed. *)
    (forall x, x ∉ L2 -> lift_core τ2 τ2' <{ e (r^x) }> <{ e'^x }>) ->
    (* The function argument of [e] should have a leakage label of [⊤]
    ([LLeak]), because [e] is applied to retraction. *)
    lift_core <{ Π:{⊤}τ1, τ2 }> <{ Π:{l'}τ1', τ2' }> e
              <{ \:{l'}τ1' => e' }>
| LSec τ τ' e e' :
    gsec τ τ' e e' ->
    lift_core τ τ' e e'
.

(** Top-level relation that handles type index arguments and calls [lift_core]
to do the heavy lifting (pun intended). [lift τs τ τ' e e'] means [e] of type
[τ] is lifted to [e'] of type [τ'] which has type indices [τs]. *)
Inductive lift : list expr -> expr -> expr -> expr -> expr -> Prop :=
| LCons τs τ τ1 τ2' e e' L :
    (forall x, x ∉ L -> lift τs τ <{ τ2'^x }> e <{ e'^x }>) ->
    lift (τ1::τs) τ <{ Π:τ1, τ2' }> e <{ \:τ1 => e' }>
| LNil τ τ' e e' : lift_core τ τ' e e' -> lift [] τ τ' e e'
.


(** ** Well-formedness of lifting input *)

(** [τ] is not a dependent type (at top level). It may still take as argument a
dependently typed higher-order function. *)
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

(** * Theorems *)

(** ** Well-typedness of section and retraction *)

#[local]
Set Default Proof Using "Type".

Arguments open /.

Lemma gsec_well_typed τ τ' e e' Γ κ κ' :
  gsec τ τ' e e' ->
  Γ ⊢ τ :: κ ->
  Γ ⊢ τ' :: κ' ->
  Γ ⊢ e :{⊤} τ ->
  Γ ⊢ e' :{⊥} τ'.
Proof using Hsrwf.
  intros H. revert Γ κ κ'.
  induction H; intros;
    eauto using typing, kinding;
    kind_inv.
  (* GSProd *)
  - econstructor;
      try auto_eapply; eauto using kinding;
        solve [ relax_typing_type; [ econstructor | ]; eauto ].
  (* GSSum *)
  - econstructor; eauto using kinding.
    econstructor; eauto using kinding;
      simpl; simpl_cofin;
        match goal with
        | |- context [<{ ?τ1 +{_} ?τ2 }>] =>
          rewrite open_lc with (e := τ1) by eauto with lc;
            rewrite open_lc with (e := τ2) by eauto with lc
        end;
        econstructor; eauto using kinding, kinding_weakening_insert;
          auto_eapply;
          eauto using typing, kinding_weakening_insert with lc simpl_map.
  (* GSOADT *)
  - apply_srctx_wf. simplify_eq.
    repeat (first [ typing_intro
                  | relax_typing_type; [ econstructor | ] ];
            eauto); simpl; eauto.
    rewrite open_lc; eauto with lc.
Qed.

Lemma gret_well_typed τ τ' e e' Γ κ κ' :
  gret τ τ' e' e ->
  Γ ⊢ τ :: κ ->
  Γ ⊢ τ' :: κ' ->
  Γ ⊢ e' :{⊤} τ' ->
  Γ ⊢ e :{⊤} τ.
Proof using Hsrwf.
  intros H. revert Γ κ κ'.
  induction H; intros;
    eauto using typing, kinding;
    kind_inv.

  (* GRProd *)
  econstructor;
    try auto_eapply; eauto using kinding;
      solve [ relax_typing_type; [ econstructor | ]; eauto ].

  (* GRSum and GROSum *)
  1-2:
    econstructor; eauto using typing, kinding;
    simpl; simpl_cofin;
      match goal with
      | |- context [<{ ?τ1 +{_} ?τ2 }>] =>
        rewrite open_lc with (e := τ1) by eauto with lc;
          rewrite open_lc with (e := τ2) by eauto with lc
      end;
      econstructor; eauto using kinding, kinding_weakening_insert;
        auto_eapply;
        try eapply TConv;
        eauto using typing, kinding_weakening_insert with lc simpl_map;
        reflexivity.

  (* GROADT *)
  apply_srctx_wf. simplify_eq.
  repeat (first [ typing_intro
                | relax_typing_type; [ econstructor | ] ];
          eauto); simpl; eauto.
Qed.


(** ** Well-typedness of lifting *)

#[local]
Set Default Proof Using "All".

Lemma lift_core_well_typed τ τ' e e' Γ κ' :
  lift_core τ τ' e e' ->
  nodep τ ->
  nodep τ' ->
  Γ ⊢ τ' :: κ' ->
  Γ ⊢ e :{⊤} τ ->
  Γ ⊢ e' :{⊥} τ'.
Proof.
  intros H. revert Γ κ'.
  induction H; intros;
    apply_regularity;
    eauto using gsec_well_typed.

  kind_inv. subst.
  econstructor; eauto.
  cbn in *. simp_hyps.
  simpl_cofin.
  repeat match goal with
         | H : lc ?τ |- _ =>
           rewrite (open_lc τ) in * by apply H
         end.
  auto_eapply; eauto.
  relax_typing_type; [ econstructor | ];
    eauto using weakening_insert, open_lc_intro.
  eapply gret_well_typed; eauto using kinding_weakening_insert.
  eapply TConv; eauto using typing, kinding_weakening_insert with simpl_map.
  reflexivity.
  apply top_ub.
Qed.

Lemma lift_well_typed_ τs τ τ' e e' Γ κ' :
  lift τs τ τ' e e' ->
  nodep τ ->
  lift_type_wf τs τ' ->
  Γ ⊢ τ' :: κ' ->
  Γ ⊢ e :{⊤} τ ->
  Γ ⊢ e' :{⊥} τ'.
Proof.
  intros H. revert Γ κ'.
  induction H; intros.
  - select (lift_type_wf _ _) (fun H => sinvert H).
    kind_inv. subst.
    econstructor; eauto.
    simpl_cofin.
    auto_eapply; eauto.
    eauto using weakening_insert.
  - qauto use: lift_core_well_typed inv: lift_type_wf.
Qed.

Theorem lift_well_typed τs τ τ' e e' κ' :
  lift τs τ τ' e e' ->
  nodep τ ->
  lift_type_wf τs τ' ->
  ∅ ⊢ τ' :: κ' ->
  ∅ ⊢ e :{⊤} τ ->
  ∅ ⊢ e' :{⊥} τ'.
Proof.
  eauto using lift_well_typed_.
Qed.

End lifting.
