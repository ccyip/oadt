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
                  Σ !! s = Some (DFun (⊥, <{ Π!:τk, Π:(gvar X), X'@(bvar 1) }>)
                                 se) /\
                  Σ !! r = Some (DFun (⊤, <{ Π!:τk, Π!:(X'@(bvar 0)), gvar X }>)
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
has a public type [τ]. The section [e'] is always safe, i.e. properly taped. *)
Inductive gsec : expr -> expr -> expr -> expr -> Prop :=
| GSUnit e : gsec <{ 𝟙 }> <{ 𝟙 }> e <{ tape e }>
| GSBool e : gsec <{ 𝔹 }> <{ ~𝔹 }> e <{ tape (s𝔹 e) }>
| GSProd τ1 τ1' τ2 τ2' e e1 e2 :
    gsec τ1 τ1' <{ π1 e }> e1 ->
    gsec τ2 τ2' <{ π2 e }> e2 ->
    gsec <{ τ1 * τ2 }> <{ τ1' ~* τ2' }> e <{ ~(e1, e2) }>
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
corresponding components in [τ]. [e'] is assumed safe. *)
Inductive gret : expr -> expr -> expr -> expr -> Prop :=
| GRId τ e : gret τ τ e e
| GRBool e' : gret <{ 𝔹 }> <{ ~𝔹 }> e' <{ ~if e' then true else false }>
| GRProd τ1 τ1' τ2 τ2' e' e1 e2 :
    <{ τ1 * τ2 }> <> <{ τ1' * τ2' }> ->
    gret τ1 τ1' <{ π1 e' }> e1 ->
    gret τ2 τ2' <{ π2 e' }> e2 ->
    gret <{ τ1 * τ2 }> <{ τ1' * τ2' }> e' <{ (e1, e2) }>
| GROProd τ1 τ1' τ2 τ2' e' e1 e2 :
    gret τ1 τ1' <{ ~π1 e' }> e1 ->
    gret τ2 τ2' <{ ~π2 e' }> e2 ->
    gret <{ τ1 * τ2 }> <{ τ1' ~* τ2' }> e' <{ (e1, e2) }>
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
         <{ ~case e' of inl<τ1 + τ2> e1 | inr<τ1 + τ2> e2 }>
(* Outsource to predefined context *)
| GROADT X X' k s r e' :
    Δ !! (X, X') = Some (s, r) ->
    gret <{ gvar X }> <{ X'@k }> e' <{ (gvar r) k e' }>
.

(** ** Lifting *)

(** The core lifting relation. [lift_core τ τ' e e'] means [e'] of oblivious
type [τ'] is the lifted result from [e] of public type [τ]. *)
Inductive lift_core : expr -> expr -> expr -> expr -> Prop :=
| LPi τ1 τ1' τ2 τ2' e e' r L1 L2 :
    (forall x, x ∉ L1 -> gret τ1 τ1' x <{ r^x }>) ->
    (* Types in [lift_core] are assumed to be non-dependent types, so [τ2] and
    [τ2'] are locally closed. *)
    (forall x, x ∉ L2 -> lift_core τ2 τ2' <{ e (r^x) }> <{ e'^x }>) ->
    (* The function argument of [e] should have a leakage label of [⊤]
    ([LLeak]), because [e] is applied to retraction. *)
    lift_core <{ Π:τ1, τ2 }> <{ Π!:τ1', τ2' }> e
              <{ \!:τ1' => e' }>
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
    lift (τ1::τs) τ <{ Π!:τ1, τ2' }> e <{ \!:τ1 => e' }>
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
| LTVCons τk τs τ' l L :
    lc τk ->
    (forall x, x ∉ L -> lift_type_wf τs <{ τ'^x }>) ->
    lift_type_wf (τk::τs) <{ Π:{l}τk, τ' }>
.

#[global]
Instance list_expr_stale : Stale (list expr) := foldr (fun e S => fv e ∪ S) ∅.

(** ** Equivalence up to revelation *)

(** [in_range τ τ' v] means value [v] of type [τ] is in the range of the
oblivious type [τ']. In other words, it is constrained by the indices in τ'. *)
Inductive in_range : expr -> expr -> expr -> Prop :=
| IRSame τ v : in_range τ τ v
| IRBool b : in_range <{ 𝔹 }> <{ ~𝔹 }> b
| IRProd τ1 τ1' τ2 τ2' l v1 v2 :
    in_range τ1 τ1' v1 ->
    in_range τ2 τ2' v2 ->
    in_range <{ τ1 * τ2 }> <{ τ1' *{l} τ2' }> <{ (v1, v2) }>
| IRSum τ1 τ1' τ2 τ2' l b v :
    in_range <{ ite b τ1 τ2 }> <{ ite b τ1' τ2' }> v ->
    in_range <{ τ1 + τ2 }> <{ τ1' +{l} τ2' }> <{ inj@b<τ1 + τ2> v }>
| IROADT X X' k v v' s r :
    Δ !! (X, X') = Some (s, r) ->
    (* We may want to use small-step semantics here instead, but it doesn't
    matter: as reveal semantics is a weaker semantics and [in_range] is used in
    assumptions, this formulation can only result in a stronger correctness
    statement. *)
    <{ (gvar s) k v }> ↓ v' ->
    <{ (gvar r) k v' }> ↓ v ->
    in_range <{ gvar X }> <{ X'@k }> v
.


(** We define the equivalence between a public expression and an oblivious
expression up to revelation. The definition is essentially logical equivalence,
but we do not treat higher-order arguments. The reason is rather subtle. *)

(** [val_requiv τ τ' v v'] means value [v] of public type [τ] and [v'] of
(possibly) oblivious type [τ'] are equivalent up to revelation. *)
Inductive val_requiv : expr -> expr -> expr -> expr -> Prop :=
| VQRefl τ v : val_requiv τ τ v v
| VQBool b : val_requiv <{ 𝔹 }> <{ ~𝔹 }> <{ b }> <{ [b] }>
| VQProd τ1 τ1' τ2 τ2' v1 v1' v2 v2' :
    val_requiv τ1 τ1' v1 v1' ->
    val_requiv τ2 τ2' v2 v2' ->
    val_requiv <{ τ1 * τ2 }> <{ τ1' * τ2' }> <{ (v1, v2) }> <{ (v1', v2') }>
| VQOProd τ1 τ1' τ2 τ2' v1 v1' v2 v2' :
    val_requiv τ1 τ1' v1 v1' ->
    val_requiv τ2 τ2' v2 v2' ->
    val_requiv <{ τ1 * τ2 }> <{ τ1' ~* τ2' }> <{ (v1, v2) }> <{ ~(v1', v2') }>
| VQSum τ1 τ1' τ2 τ2' b v v' :
    val_requiv <{ ite b τ1 τ2 }> <{ ite b τ1' τ2' }> v v' ->
    val_requiv <{ τ1 + τ2 }> <{ τ1' + τ2' }>
               <{ inj@b<τ1 + τ2> v }> <{ inj@b<τ1' + τ2'> v' }>
| VQOSum τ1 τ1' τ2 τ2' ω1 ω2 b v v' :
    val_requiv <{ ite b τ1 τ2 }> <{ ite b τ1' τ2' }> v v' ->
    val_requiv <{ τ1 + τ2 }> <{ τ1' ~+ τ2' }>
               <{ inj@b<τ1 + τ2> v }> <{ [inj@b<ω1 ~+ ω2> v'] }>
| VQOADT X X' k v v' s r :
    Δ !! (X, X') = Some (s, r) ->
    <{ (gvar r) k v' }> ↓ v ->
    val_requiv <{ gvar X }> <{ X'@k }> v v'
.

Section simple.

(** This handles the case when at least one of the expressions has simple type,
i.e. not function types. The top-level equivalence is defined parametric in this
relation, so we can instantiate it with different semantics or equi-termination
later. *)
Variable expr_simple_requiv : expr -> expr -> expr -> expr -> Prop.

(** Expression [e] of public type [τ] and [e'] of oblivious type [τ'] are
equivalent up to revelation. *)
Fixpoint expr_requiv_ (τ τ' : expr) (e e' : expr) : Prop :=
  match τ, τ' with
  | <{ Π:{_}τ1, τ2 }>, <{ Π:{_}τ1', τ2' }> =>
    forall v v',
      val v -> val v' ->
      ∅ ⊢ v :{⊥} τ1 ->
      ∅ ⊢ v' :{⊥} τ1' ->
      val_requiv τ1 τ1' v v' ->
      expr_requiv_ τ2 τ2' <{ e v }> <{ e' v' }>
  | _, _ => expr_simple_requiv τ τ' e e'
  end.

(** [e] of public type [τ] and [e'] of oblivious type [τ'] with indices [τs] are
equivalent up to revelation. Essentially this says [e] and [e'] are equivalent
expressions, i.e. [expr_requiv], given any well-typed indices. *)
Fixpoint lift_requiv_ (τs : list expr) (τ τ' : expr) (e e' : expr) : Prop :=
  match τs with
  | _::τs =>
    match τ' with
    | <{ Π:{_}τ1, τ2 }> =>
      forall k : expr,
        ∅ ⊢ k :{⊥} τ1 ->
        val k ->
        lift_requiv_ τs τ <{ τ2^k }> e <{ e' k }>
    | _ => False
    end
  | [] => expr_requiv_ τ τ' e e'
  end.

End simple.

(** This is the definitional equivalence, using the small-step semantics. Note
that we only consider partial equivalence here, i.e. we assume they both
terminate. Equi-termination can be handled separately. *)
Definition expr_simple_requiv (τ τ' : expr) (e e' : expr) : Prop :=
  forall w w',
    e -->* w ->
    wval w ->
    in_range τ τ' (⟦w⟧) ->
    e' -->* w' ->
    wval w' ->
    val_requiv τ τ' (⟦w⟧) (⟦w'⟧).

Definition expr_requiv := expr_requiv_ expr_simple_requiv.
Definition lift_requiv := lift_requiv_ expr_simple_requiv.


(** * Theorems *)

(** ** Well-typedness of section and retraction *)

#[local]
Set Default Proof Using "Type".

Arguments open /.

Lemma gsec_well_typed τ τ' e e' l Γ κ κ' :
  gsec τ τ' e e' ->
  Γ ⊢ τ :: κ ->
  Γ ⊢ τ' :: κ' ->
  Γ ⊢ e :{l} τ ->
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
    relax_typing_type; [ econstructor | ].
    repeat (relax_typing_type; [ econstructor | ]; eauto);
      simpl; eauto.
    eapply TConv; eauto using kinding. reflexivity. apply top_ub.
    rewrite open_lc_intro; eauto with lc.
Qed.

Lemma gret_well_typed τ τ' e e' Γ κ κ' :
  gret τ τ' e' e ->
  Γ ⊢ τ :: κ ->
  Γ ⊢ τ' :: κ' ->
  Γ ⊢ e' :{⊥} τ' ->
  Γ ⊢ e :{⊤} τ.
Proof using Hsrwf.
  intros H. revert Γ κ κ'.
  induction H; intros;
    eauto using typing, kinding;
    kind_inv.

  econstructor; eauto; lattice_naive_solver.

  (* GRProd and GROProd *)
  1-2:
  econstructor;
    try auto_eapply; eauto using kinding;
    solve [ relax_typing_type; [ econstructor | ]; eauto ].

  (* GRSum and GROSum *)
  1-2:
  econstructor;
    lazymatch goal with
    | |- _ = _ => idtac
    | |- _ =>
        eauto using kinding;
        simpl; simpl_cofin;
        match goal with
        | |- context [<{ ?τ1 +{_} ?τ2 }>] =>
            rewrite open_lc with (e := τ1) by eauto with lc;
            rewrite open_lc with (e := τ2) by eauto with lc
        end;
        econstructor;
        try auto_eapply;
        eauto using typing, kinding, kinding_weakening_insert with simpl_map
    end; eauto.

  (* GROADT *)
  apply_srctx_wf. simplify_eq.
  repeat (first [ typing_intro
                | relax_typing_type; [ econstructor | ] ];
          eauto); simpl; eauto.
Qed.


(** ** Well-typedness of lifting *)

#[local]
Set Default Proof Using "All".

Lemma lift_core_well_typed τ τ' e e' l Γ κ' :
  lift_core τ τ' e e' ->
  nodep τ ->
  nodep τ' ->
  Γ ⊢ τ' :: κ' ->
  Γ ⊢ e :{l} τ ->
  Γ ⊢ e' :{⊥} τ'.
Proof.
  intros H. revert Γ κ'.
  induction H; intros;
    apply_regularity;
    eauto using gsec_well_typed.

  kind_inv.
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
Qed.

Lemma lift_well_typed_ τs τ τ' e e' l Γ κ' :
  lift τs τ τ' e e' ->
  nodep τ ->
  lift_type_wf τs τ' ->
  Γ ⊢ τ' :: κ' ->
  Γ ⊢ e :{l} τ ->
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

Theorem lift_well_typed τs τ τ' e e' l κ' :
  lift τs τ τ' e e' ->
  nodep τ ->
  lift_type_wf τs τ' ->
  ∅ ⊢ τ' :: κ' ->
  ∅ ⊢ e :{l} τ ->
  ∅ ⊢ e' :{⊥} τ'.
Proof.
  eauto using lift_well_typed_.
Qed.

(** ** Stronger equivalence up to revelation *)

(** This version of equivalence uses the reveal semantics [reval]. It is
stronger than the definitional version, and much more convenient for proofs
because we do not have to deal with weak values and the wacky semantics. *)
Definition expr_simple_requiv_reval (τ τ' : expr) (e e' : expr) : Prop :=
  forall v v',
    e ↓ v ->
    in_range τ τ' v ->
    e' ↓ v' ->
    val_requiv τ τ' v v'.

Definition expr_requiv_reval := expr_requiv_ expr_simple_requiv_reval.
Definition lift_requiv_reval := lift_requiv_ expr_simple_requiv_reval.

Lemma expr_simple_requiv_reval_sound τ τ' e e' :
  expr_simple_requiv_reval τ τ' e e' ->
  expr_simple_requiv τ τ' e e'.
Proof.
  intros. hnf.
  eauto using mstep_wval_reval.
Qed.

Lemma expr_requiv_reval_sound τ : forall τ' e e',
  expr_requiv_reval τ τ' e e' ->
  expr_requiv τ τ' e e'.
Proof.
  induction τ; cbn; intros;
    try case_split; eauto using expr_simple_requiv_reval_sound.
Qed.

Lemma lift_requiv_reval_sound τs : forall τ τ' e e',
    lift_requiv_reval τs τ τ' e e' ->
    lift_requiv τs τ τ' e e'.
Proof.
  induction τs; cbn; intros;
    try case_split; eauto; hauto use: expr_requiv_reval_sound.
Qed.

(** ** Substitution lemmas *)

(** These lemmas are crucial to the proofs. They are used to keep terms closed
throughout the proofs. Alternatively, we may use parallel substitution but it
would need more work. *)

Lemma gsec_subst_ τ τ' e e' x s :
  lc s ->
  gsec τ τ' e e' ->
  gsec <{ {x↦s}τ }> <{ {x↦s}τ' }> <{ {x↦s}e }> <{ {x↦s}e' }>.
Proof.
  induction 2; simpl; econstructor; eauto;
    (* GSCase *)
    simpl_cofin;
    match goal with
    | H : ?R ?τ ?τ' _ _ |- ?R ?τ ?τ' _ _ =>
      apply_eq H
    end;
    solve [ by rewrite subst_open_comm by (eauto; shelve)
          | by rewrite subst_fresh by shelve ].

  Unshelve.
  all: fast_set_solver!!.
Qed.

Lemma gsec_subst τ τ' e e' x s :
  gsec τ τ' e e' ->
  lc s ->
  x ∉ fv τ ∪ fv τ' ->
  gsec τ τ' <{ {x↦s}e }> <{ {x↦s}e' }>.
Proof.
  intros.
  apply_eq gsec_subst_; eauto;
    by rewrite subst_fresh by fast_set_solver!!.
Qed.

Lemma gret_subst_type_neq τ τ' e' e x s :
  gret τ τ' e' e ->
  τ <> τ' ->
  <{ {x↦s}τ }> <> <{ {x↦s}τ' }>.
Proof.
  induction 1; intros; try scongruence;
    simpl_cofin?; hauto lq: on.
Qed.

Lemma gret_subst_ τ τ' e' e x s :
  lc s ->
  gret τ τ' e' e ->
  gret <{ {x↦s}τ }> <{ {x↦s}τ' }> <{ {x↦s}e' }> <{ {x↦s}e }>.
Proof.
  induction 2; simpl; econstructor; eauto;
    try match goal with
        | H : _ <> _ |- _ <> _ =>
            eapply gret_subst_type_neq in H; eauto using gret
        end;
    (* GRCase and GROCase *)
    simpl_cofin;
    match goal with
    | H : ?R ?τ ?τ' _ _ |- ?R ?τ ?τ' _ _ =>
      apply_eq H
    end;
    solve [ by rewrite subst_open_comm by (eauto; shelve)
          | by rewrite subst_fresh by shelve ].

  Unshelve.
  all: fast_set_solver!!.
Qed.

Lemma gret_subst τ τ' e e' x s :
  gret τ τ' e e' ->
  lc s ->
  x ∉ fv τ ∪ fv τ' ->
  gret τ τ' <{ {x↦s}e }> <{ {x↦s}e' }>.
Proof.
  intros.
  apply_eq gret_subst_; eauto;
    by rewrite subst_fresh by fast_set_solver!!.
Qed.

Lemma lift_core_subst_ τ τ' e e' x s :
  lc s ->
  lift_core τ τ' e e' ->
  lift_core <{ {x↦s}τ }> <{ {x↦s}τ' }> <{ {x↦s}e }> <{ {x↦s}e' }>.
Proof.
  induction 2; simpl in *; econstructor; eauto using gsec_subst_.
  - simpl_cofin.
    eapply_eq gret_subst_; eauto.
    by rewrite subst_fresh by shelve.
    by rewrite subst_open_comm by (eauto; shelve).
  - simpl_cofin.
    rewrite !subst_open_comm in * by (eauto; shelve).
    eauto.

  Unshelve.
  all: fast_set_solver!!.
Qed.

Lemma lift_core_subst τ τ' e e' x s :
  lift_core τ τ' e e' ->
  lc s ->
  x ∉ fv τ ∪ fv τ' ->
  lift_core τ τ' <{ {x↦s}e }> <{ {x↦s}e' }>.
Proof.
  intros.
  apply_eq lift_core_subst_; eauto;
    by rewrite subst_fresh by fast_set_solver!!.
Qed.

Lemma lift_subst_ τs τ τ' e e' x s :
  lc s ->
  lift τs τ τ' e e' ->
  x # τs ->
  lift τs <{ {x↦s}τ }> <{ {x↦s}τ' }> <{ {x↦s}e }> <{ {x↦s}e' }>.
Proof.
  induction 2; intros; simpl in *.
  - match goal with
    | |- lift (?τ :: _) _ _ _ _ => rewrite (subst_fresh τ) by fast_set_solver!!
    end.
    econstructor. simpl_cofin.
    rewrite <- !subst_open_comm by (auto; fast_set_solver!!).
    auto_apply. fast_set_solver!!.
  - econstructor.
    eauto using lift_core_subst_.
Qed.

Lemma lift_subst τs τ τ' e e' x s :
  lc s ->
  lift τs τ τ' e e' ->
  x ∉ stale τs ∪ fv τ ∪ fv e ->
  lift τs τ <{ {x↦s}τ' }> e <{ {x↦s}e' }>.
Proof.
  intros.
  apply_eq lift_subst_; eauto;
    rewrite ?subst_fresh by fast_set_solver!!; eauto; fast_set_solver!!.
Qed.

(** ** Reveal semantics refinement *)

Ltac apply_reval_deterministic :=
  match goal with
  | H : ?e ↓ ?v, H' : ?e ↓ ?v' |- _ =>
      assert (v = v') by eauto using reval_deterministic;
      simplify_eq; clear H
  end.

(** [e1] refines [e2]. *)
Definition reval_refine (e1 e2 : expr) : Prop :=
  forall v, e1 ↓ v -> e2 ↓ v.

#[global]
Instance reval_refine_preorder : PreOrder reval_refine.
Proof.
  split; hnf; unfold reval_refine.
  - auto.
  - auto.
Qed.

Lemma reval_refine_strengthen e e' :
  (forall v, e ↓ v -> reval_refine e e') ->
  reval_refine e e'.
Proof.
  unfold reval_refine.
  eauto.
Qed.

Lemma reval_refine_reval1 e v :
  e ↓ v ->
  reval_refine e v.
Proof.
  intros. hnf. intros.
  apply_reval_deterministic.
  eauto using reval_idemp.
Qed.

Lemma reval_refine_reval2 e v :
  e ↓ v ->
  reval_refine v e.
Proof.
  intros. hnf. intros.
  eapply reval_trans; eauto.
Qed.

Lemma reval_refine_erase1 e v :
  reval_refine (⟦e⟧) v ->
  reval_refine e v.
Proof.
  intros. hnf.
  eauto using reval_erase, erase_idemp.
Qed.

Lemma reval_refine_erase2 e v :
  reval_refine e (⟦v⟧) ->
  reval_refine e v.
Proof.
  intros. hnf.
  eauto using reval_erase, erase_idemp.
Qed.

Lemma reval_refine_congr_app e1 e2 s1 s2 :
  reval_refine e1 e2 ->
  reval_refine s1 s2 ->
  reval_refine <{ e1 s1 }> <{ e2 s2 }>.
Proof.
  unfold reval_refine. intros.
  reval_inv*. reval_intro; eauto.
Qed.

Lemma reval_refine_congr_app1 e1 e2 v :
  reval_refine e1 e2 ->
  reval_refine <{ e1 v }> <{ e2 v }>.
Proof.
  qauto use: reval_refine_congr_app solve: reflexivity.
Qed.

Lemma reval_refine_congr_app2 e1 e2 e :
  reval_refine e1 e2 ->
  reval_refine <{ e e1 }> <{ e e2 }>.
Proof.
  qauto use: reval_refine_congr_app solve: reflexivity.
Qed.

Lemma reval_refine_beta l τ e v :
  val v ->
  reval_refine <{ (\:{l}τ => e) v }> <{ e^v }>.
Proof.
  unfold reval_refine. intros.
  reval_inv*.
  select (val _) (fun H => eapply reval_val_inv in H); eauto; subst.
  eauto using reval_erase, erase_open.
Qed.

Lemma reval_refine_beta_tape e :
  reval_refine <{ tape e }> <{ e }>.
Proof.
  unfold reval_refine. intros.
  reval_inv*. eauto.
Qed.

Lemma reval_refine_eta_prod e v1 v2 :
  e ↓ <{ (v1, v2) }> ->
  reval_refine e <{ (π1 e, π2 e) }>.
Proof.
  unfold reval_refine. intros.
  apply_reval_deterministic.
  econstructor; reval_intro; eauto.
Qed.

Lemma reval_refine_eta_prod_wt e l τ1 τ2 :
  ∅ ⊢ e :{l} τ1 * τ2 ->
  reval_refine e <{ (π1 e, π2 e) }>.
Proof.
  intros.
  apply reval_refine_strengthen. intros.
  select (_ ⊢ _ :{_} _ ) (fun H => eapply reval_soundness_strong in H);
    eauto; simp_hyps.
  select (val _) (fun H => eapply canonical_form_prod in H);
    eauto; simp_hyps; subst.
  eauto using reval_refine_eta_prod.
Qed.

Lemma reval_refine_eta_sum e b τ1 τ2 v :
  e ↓ <{ inj@b<τ1 + τ2> v }> ->
  lc τ1 -> lc τ2 ->
  reval_refine e <{ case e of inl<τ1 + τ2> (bvar 0) | inr<τ1 + τ2> (bvar 0) }>.
Proof.
  unfold reval_refine. intros.
  apply_reval_deterministic.
  econstructor. eauto.
  select (_ ↓ _) (fun H => apply reval_idemp in H).
  reval_inv*. simpl.
  rewrite !open_lc by eauto.
  case_split; reval_intro; eauto; scongruence.
Qed.

(** ** Properties of equivalence-up-to-revelation *)

Lemma expr_simple_requiv_reval_proper τ τ' e1 e2 e1' e2' :
  expr_simple_requiv_reval τ τ' e1 e1' ->
  reval_refine e2 e1 ->
  reval_refine e2' e1' ->
  expr_simple_requiv_reval τ τ' e2 e2'.
Proof.
  intros. hnf. eauto.
Qed.

Lemma expr_requiv_reval_proper τ : forall τ' e1 e2 e1' e2',
  expr_requiv_reval τ τ' e1 e1' ->
  reval_refine e2 e1 ->
  reval_refine e2' e1' ->
  expr_requiv_reval τ τ' e2 e2'.
Proof.
  induction τ; intros; simpl in *; eauto using expr_simple_requiv_reval_proper.
  case_split; eauto using expr_simple_requiv_reval_proper.
  intros. auto_eapply; eauto; eauto using reval_refine_congr_app1.
Qed.

Lemma lift_requiv_reval_proper τs : forall τ τ' e1 e2 e1' e2',
  lift_requiv_reval τs τ τ' e1 e1' ->
  reval_refine e2 e1 ->
  reval_refine e2' e1' ->
  lift_requiv_reval τs τ τ' e2 e2'.
Proof.
  induction τs; intros; simpl in *.
  eapply expr_requiv_reval_proper; eauto.
  case_split; eauto; intros.
  auto_eapply; eauto; eauto using reval_refine_congr_app1.
Qed.

#[global]
Instance expr_simple_requiv_reval_proper' τ τ' :
  Proper (reval_refine ==> reval_refine ==> flip impl)
         (expr_simple_requiv_reval τ τ').
Proof.
  repeat (intros; hnf).
  eauto using expr_simple_requiv_reval_proper.
Qed.

#[global]
Instance expr_requiv_reval_proper' τ τ' :
  Proper (reval_refine ==> reval_refine ==> flip impl)
         (expr_requiv_reval τ τ').
Proof.
  repeat (intros; hnf).
  eapply expr_requiv_reval_proper; eauto.
Qed.

#[global]
Instance lift_requiv_reval_proper' τs τ τ' :
  Proper (reval_refine ==> reval_refine ==> flip impl)
         (lift_requiv_reval τs τ τ').
Proof.
  repeat (intros; hnf).
  eapply lift_requiv_reval_proper; eauto.
Qed.

Lemma val_requiv_same_type_ τ τ' e e' :
  val_requiv τ τ' e e' ->
  τ = τ' ->
  e = e'.
Proof.
  induction 1; intros; simplify_eq; eauto;
    try case_split; qauto.
Qed.

Lemma val_requiv_same_type τ e e' :
  val_requiv τ τ e e' ->
  e = e'.
Proof.
  eauto using val_requiv_same_type_.
Qed.

Lemma expr_simple_requiv_refl τ e :
  expr_simple_requiv_reval τ τ e e.
Proof.
  hnf. intros.
  apply_reval_deterministic.
  econstructor.
Qed.

Lemma expr_requiv_refl τ : forall e,
  expr_requiv_reval τ τ e e.
Proof.
  induction τ; simpl; intros; eauto using expr_simple_requiv_refl.
  qauto use: val_requiv_same_type.
Qed.

Lemma expr_simple_requiv_strengthen τ τ' e e' :
  (forall v v', e ↓ v ->
           e' ↓ v' ->
           in_range τ τ' v ->
           expr_simple_requiv_reval τ τ' e e') ->
  expr_simple_requiv_reval τ τ' e e'.
Proof.
  unfold expr_simple_requiv_reval.
  eauto.
Qed.

Lemma expr_simple_requiv_congr_prod τ1 τ2 τ1' τ2' l e1 e2 e1' e2' :
  expr_simple_requiv_reval τ1 τ1' e1 e1' ->
  expr_simple_requiv_reval τ2 τ2' e2 e2' ->
  expr_simple_requiv_reval <{ τ1 * τ2 }> <{ τ1' *{l} τ2' }>
                           <{ (e1, e2) }> <{ (e1', e2'){l} }>.
Proof.
  unfold expr_simple_requiv_reval.
  intros. reval_inv*.
  case_label; econstructor; eauto;
    auto_apply; eauto;
    qauto l: on inv: in_range ctrs: in_range.
Qed.

Lemma expr_simple_requiv_congr_osum τ1 τ2 τ1' τ2' b e e' τ τ3 τ4 :
  expr_simple_requiv_reval <{ ite b τ1 τ2 }> <{ ite b τ1' τ2' }> e e' ->
  expr_simple_requiv_reval <{ τ1 + τ2 }> <{ τ1' ~+ τ2' }>
                           <{ inj@b<τ> e }> <{ ~inj@b<τ3 ~+ τ4> e' }>.
Proof.
  unfold expr_simple_requiv_reval.
  intros. reval_inv*.
  select (in_range _ _ _) (fun H => sinvert H).
  econstructor; eauto.
Qed.

Lemma expr_simple_requiv_congr_case τ τ' e e1 e2 e1' e2' :
  (forall v b τ0, e ↓ <{ inj@b<τ0> v }> ->
             expr_simple_requiv_reval τ τ' <{ e1^v }> <{ e1'^v }>) ->
  (forall v b τ0, e ↓ <{ inj@b<τ0> v }> ->
             expr_simple_requiv_reval τ τ' <{ e2^v }> <{ e2'^v }>) ->
  expr_simple_requiv_reval τ τ' <{ case e of e1 | e2 }> <{ case e of e1' | e2' }>.
Proof.
  unfold expr_simple_requiv_reval.
  intros. reval_inv*.
  apply_reval_deterministic.
  case_split; eauto.
Qed.

(** ** Local closure properties *)

Lemma gsec_lc τ τ' e e' :
  gsec τ τ' e' e ->
  lc τ -> lc τ' -> lc e' ->
  lc e.
Proof.
  induction 1; intros; repeat lc_inv; eauto 10 using lc.
  (* Oblivious sum *)
  econstructor.
  econstructor; eauto using lc;
    simpl_cofin; simpl;
    rewrite !open_lc by eauto;
    eauto 10 using lc.
Qed.

Lemma gret_lc τ τ' e e' :
  gret τ τ' e e' ->
  lc τ -> lc τ' -> lc e ->
  lc e'.
Proof.
  induction 1; intros; repeat lc_inv; eauto 10 using lc;
    (* Sum and Oblivious sum *)
    econstructor; eauto using lc;
    simpl_cofin; simpl;
    rewrite !open_lc by eauto;
    eauto 10 using lc.
Qed.

Lemma lift_core_lc τ τ' e e' :
  lift_core τ τ' e e' ->
  nodep τ -> nodep τ' ->
  lc τ -> lc τ' -> lc e ->
  lc e'.
Proof.
  induction 1; simpl; intros; simp_hyps; repeat lc_inv;
    eauto using gsec_lc.
  econstructor; eauto.
  simpl_cofin.
  eauto using lc, gret_lc.
Qed.

Lemma lift_lc τs τ τ' e e' :
  lift τs τ τ' e e' ->
  nodep τ ->
  lift_type_wf τs τ' ->
  lc τ -> lc τ' -> lc e ->
  lc e'.
Proof.
  induction 1; simpl; intros; simp_hyps; repeat lc_inv;
    select (lift_type_wf _ _) (fun H => sinvert H);
    eauto using lift_core_lc.
  econstructor; eauto.
  simpl_cofin.
  eauto.
Qed.

(** ** Correctness of section and retraction *)

Lemma gsec_reval_reflect τ τ' e e' v' :
  gsec τ τ' e e' ->
  e' ↓ v' ->
  exists v, e ↓ v.
Proof.
  intros H. revert v'.
  induction H; intros; reval_inv*; eauto.
  select! (forall v, _ -> exists _, _) (fun H => edestruct H); eauto using reval_oval.
  reval_inv*. eauto.
Qed.

Lemma gsec_correct τ : forall τ' e e',
  gsec τ τ' e e' ->
  lc e ->
  expr_simple_requiv_reval τ τ' e e'.
Proof.
  induction τ; intros ??? H; sinvert H; intros.
  (* OADT *)
  - hnf. intros. econstructor; eauto.
    select (in_range _ _ _) (fun H => sinvert H).
    simplify_map_eq.
    match goal with
    | H : ?e ↓ ?v, H' : <{ _ ?e }> ↓ _ |- _ =>
        eapply reval_refine_congr_app2 in H';
        eauto using reval_refine_reval1
    end.
    apply_reval_deterministic.
    eauto.
  (* Unit *)
  - rewrite reval_refine_beta_tape.
    apply expr_simple_requiv_refl.
  (* Boolean *)
  - rewrite reval_refine_beta_tape.
    hnf. intros. reval_inv*.
    apply_reval_deterministic.
    econstructor.
  (* Product *)
  - apply expr_simple_requiv_strengthen; intros.
    reval_inv*.
    select! (gsec _ _ _ _)
          (fun H => dup_hyp H (fun H => eapply gsec_reval_reflect in H)); eauto.
    simp_hyps.
    reval_inv*.
    apply_reval_deterministic.
    match goal with
    | |- expr_simple_requiv_reval _ _ ?e _ =>
        rewrite (reval_refine_eta_prod e) by eauto
    end.
    eapply expr_simple_requiv_congr_prod; auto_eapply; eauto using lc.
  (* Oblivious Sum *)
  - apply expr_simple_requiv_strengthen; intros.
    reval_inv*.
    select (in_range _ _ _) (fun H => sinvert H).
    apply_reval_deterministic.
    match goal with
    | H : ?e ↓ _, H' : lc ?e |- _ =>
        dup_hyp H (fun H => apply reval_lc in H); eauto
    end.
    repeat lc_inv.
    rewrite reval_refine_beta_tape.
    match goal with
    | |- expr_simple_requiv_reval _ _ ?e _ =>
        rewrite (reval_refine_eta_sum e) at 1 by eauto
    end.
    simpl_cofin.
    repeat
      match goal with
      | H : gsec _ _ <{ fvar ?x }> _, H' : _ ↓ <{ inj@_<_> ?v }> |- _ =>
          eapply gsec_subst with (x:=x) (s:=v) in H;
          [ simpl in H;
            rewrite decide_True in H by auto;
            rewrite <- subst_intro in H by fast_set_solver!!
          | eauto | fast_set_solver!! ]
      end.
    eapply expr_simple_requiv_congr_case; intros;
      apply_reval_deterministic; simpl;
      eauto using expr_simple_requiv_congr_osum.
Qed.

Lemma gret_correct_ τ τ' v v' :
  val_requiv τ τ' v v' ->
  forall e e',
    gret τ τ' e' e ->
    lc τ -> lc e' ->
    e' ↓ ⟦v'⟧ ->
    e ↓ ⟦v⟧.
Proof.
  induction 1; intros;
    select (gret _ _ _ _) (fun H => sinvert H);
    eauto; try solve [ exfalso; eauto ];
    repeat
      match goal with
      | H : val_requiv ?τ ?τ _ _ |- _ =>
          eapply val_requiv_same_type in H; subst
      end; eauto;
    match goal with
    | H : ?e ↓ _, H' : lc ?e |- _ =>
        dup_hyp H (fun H => apply reval_lc in H); eauto
    end;
    simpl in *; repeat lc_inv.
  (* [VQBool] *)
  - econstructor; eauto.
    hauto ctrs: reval, val.
  (* [VQProd] *)
  - econstructor; auto_eapply; eauto using lc;
      reval_intro; eauto.
  (* [VQOProd] *)
  - econstructor; auto_eapply; eauto using lc;
      reval_intro; eauto.
  (* [VQSum] *)
  - econstructor; eauto.
    simpl. rewrite !open_lc by eauto.
    simpl_cofin.
    repeat
      match goal with
      | H : gret _ _ <{ fvar ?x }> _, H' : _ ↓ <{ inj@_<_> ?v }> |- _ =>
          eapply gret_subst with (x:=x) (s:=v) in H;
          [ simpl in H;
            rewrite decide_True in H by auto;
            rewrite <- subst_intro in H by fast_set_solver!!
          | eauto | fast_set_solver!! ]
      end.
    select (_ ↓ <{ inj@_<_> _ }>) (fun H => apply reval_idemp in H).
    reval_inv*.
    case_split; econstructor; auto_eapply; eauto.
  (* [VQOSum] *)
  - econstructor; eauto.
    simpl. rewrite !open_lc by eauto.
    simpl_cofin.
    repeat
      match goal with
      | H : gret _ _ <{ fvar ?x }> _, H' : _ ↓ <{ [inj@_<_> ?v] }> |- _ =>
          eapply gret_subst with (x:=x) (s:=v) in H;
          [ simpl in H;
            rewrite decide_True in H by auto;
            rewrite <- subst_intro in H by fast_set_solver!!
          | eauto with lc | fast_set_solver!! ]
      end.
    case_split; econstructor; auto_eapply; eauto using reval, oval_val with lc.
  (* VQOADT *)
  - erewrite <- reval_fix_erase by eauto.
    eapply reval_refine_congr_app2; eauto.
    eauto using reval_refine_erase1, reval_refine_reval2.
Qed.

Lemma gret_correct τ τ' v v' e :
  val_requiv τ τ' v v' ->
  gret τ τ' v' e ->
  lc τ -> lc v' ->
  val v' ->
  e ↓ ⟦v⟧.
Proof.
  intros.
  eapply gret_correct_; eauto using reval.
Qed.

(** ** Correctness of lifting *)

Lemma lift_core_correct τ : forall τ' e e',
  lift_core τ τ' e e' ->
  lc e ->
  expr_requiv_reval τ τ' e e'.
Proof.
  induction τ; intros ??? H; sinvert H; simpl; intros;
    eauto using gsec_correct;
    try qauto l: on inv: gsec.

  simpl_cofin.
  let go H lem x v :=
    eapply lem with (x:=x) (s:=v) in H;
    [ | eauto with lc | fast_set_solver!! ];
    simpl in H;
    rewrite ?decide_True in H by eauto;
    rewrite <- ?subst_intro in H by eauto;
    rewrite ?subst_fresh in H by eauto
        in match goal with
     | H : gret _ _ <{ fvar ?x }> _, H' : lift_core _ _ _ _ |-
         expr_requiv_reval _ _ _ <{ _ ?v }> =>
         go H gret_subst x v;
         go H' lift_core_subst x v
     end.
  rewrite reval_refine_beta by eauto.
  rewrite reval_refine_congr_app2.
  - eauto 10 using gret_lc with lc.
  - eauto 10 using gret_correct, reval_refine_erase1, reval_refine_reval2 with lc.
Qed.

Lemma lift_correct_ τs : forall τ τ' e e',
  lift τs τ τ' e e' ->
  lc e ->
  lift_requiv_reval τs τ τ' e e'.
Proof.
  induction τs; intros ???? H; sinvert H; simpl; intros.
  - eapply lift_core_correct; eauto.
  - simpl_cofin.
    match goal with
    | H : lift _ _ _ _ <{ _^(fvar ?x) }> |- lift_requiv_reval _ _ _ _ <{ _ ?v }> =>
        eapply lift_subst with (x:=x) (s:=v) in H;
        [ | eauto with lc | fast_set_solver!! ];
        rewrite <- ?subst_intro in H by eauto
    end.
    rewrite reval_refine_beta by eauto.
    eauto.
Qed.

Theorem lift_correct τs τ τ' e e' :
  lift τs τ τ' e e' ->
  lc e ->
  lift_requiv τs τ τ' e e'.
Proof.
  eauto using lift_correct_, lift_requiv_reval_sound.
Qed.


(** * Computation *)

(** ** Implementation of lifting *)

Fixpoint Gsec (τ τ' : expr) (e : expr) : option expr :=
  match τ, τ' with
  | <{ 𝟙 }>, <{ 𝟙 }> => Some <{ tape e }>
  | <{ 𝔹 }>, <{ ~𝔹 }> => Some <{ tape (s𝔹 e) }>
  | <{ τ1 * τ2 }>, <{ τ1' ~* τ2' }> =>
    e1 <- Gsec τ1 τ1' <{ π1 e }>;
    e2 <- Gsec τ2 τ2' <{ π2 e }>;
    Some <{ ~(e1, e2) }>
  | <{ τ1 + τ2 }>, <{ τ1' ~+ τ2' }> =>
    e1 <- Gsec τ1 τ1' <{ bvar 0 }>;
    e2 <- Gsec τ2 τ2' <{ bvar 0 }>;
    Some <{ tape (case e of ~inl<τ1' ~+ τ2'> e1 | ~inr<τ1' ~+ τ2'> e2) }>
  | <{ gvar X }>, <{ X'@k }> =>
    '(s, _) <- Δ !! (X, X');
    Some <{ (gvar s) k e }>
  | _, _ => None
  end.

Fixpoint Gret (τ τ' : expr) (e : expr) : option expr :=
  if decide (τ = τ')
  then Some e
  else match τ, τ' with
       | <{ 𝔹 }>, <{ ~𝔹 }> => Some <{ ~if e then true else false }>
       | <{ τ1 * τ2 }>, <{ τ1' * τ2' }> =>
         e1 <- Gret τ1 τ1' <{ π1 e }>;
         e2 <- Gret τ2 τ2' <{ π2 e }>;
         Some <{ (e1, e2) }>
       | <{ τ1 * τ2 }>, <{ τ1' ~* τ2' }> =>
         e1 <- Gret τ1 τ1' <{ ~π1 e }>;
         e2 <- Gret τ2 τ2' <{ ~π2 e }>;
         Some <{ (e1, e2) }>
       | <{ τ1 + τ2 }>, <{ τ1' + τ2' }> =>
         e1 <- Gret τ1 τ1' <{ bvar 0 }>;
         e2 <- Gret τ2 τ2' <{ bvar 0 }>;
         Some <{ case e of inl<τ1 + τ2> e1 | inr<τ1 + τ2> e2 }>
       | <{ τ1 + τ2 }>, <{ τ1' ~+ τ2' }> =>
         e1 <- Gret τ1 τ1' <{ bvar 0 }>;
         e2 <- Gret τ2 τ2' <{ bvar 0 }>;
         Some <{ ~case e of inl<τ1 + τ2> e1 | inr<τ1 + τ2> e2 }>
       | <{ gvar X }>, <{ X'@k }> =>
         '(_, r) <- Δ !! (X, X');
         Some <{ (gvar r) k e }>
       | _, _ => None
       end.

Fixpoint Lift_core (τ τ' : expr) (xs : aset) (e : expr) : option expr :=
  match τ, τ' with
  | <{ Π:{l}τ1, τ2 }>, <{ Π:{l'}τ1', τ2' }> =>
    if l && negb l'
    then let x := fresh xs in
         r <- Gret τ1 τ1' <{ fvar x }>;
         e' <- Lift_core τ2 τ2' ({[x]} ∪ xs) <{ e r }>;
         Some <{ \:{l'}τ1' => ,(close x e') }>
    else None
  | _, _ => Gsec τ τ' e
  end.

Fixpoint Lift_ (τs : list expr) (τ τ' : expr) (xs : aset) (e : expr) : option expr :=
  match τs with
  | _::τs =>
    match τ' with
    | <{ Π!:τ1, τ2' }> =>
      let x := fresh xs in
      e' <- Lift_ τs τ <{ τ2'^x }> ({[x]} ∪ xs) e;
      Some <{ \!:τ1 => ,(close x e') }>
    | _ => None
    end
  | [] => Lift_core τ τ' xs e
  end.

Definition Lift (τs : list expr) (τ τ' : expr) (e : expr) : option expr :=
  Lift_ τs τ τ' ∅ e.

(** ** Lemmas about opening, renaming and free variables *)

Arguments open : simpl never.

Ltac simpl_lift :=
  intros; cbn in *;
  repeat (first [ case_decide | case_split_var ]; cbn in *; simplify_eq);
  simplify_option_eq;
  simp_hyps; intros; subst; cbn in *.

Lemma Gsec_body τ : forall τ' e e',
  Gsec τ τ' e = Some e' ->
  lc τ' ->
  body e ->
  body e'.
Proof.
  unfold body, open.
  induction τ; simpl_lift;
    repeat lc_inv;
    (* Apply induction hypotheses. *)
    repeat match goal with
           | IH : context [Gsec ?τ _ _ = _ -> _], H : Gsec ?τ _ _ = _ |- _ =>
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

Lemma Gsec_open τ s : forall τ' e e',
  Gsec τ τ' e = Some e' ->
  lc τ' ->
  Gsec τ τ' <{ e^s }> = Some <{ e'^s }>.
Proof.
  unfold open.
  induction τ; simpl_lift; eauto;
    repeat lc_inv;
    repeat f_equal; try solve [ by rewrite !open_lc by eauto ].

  repeat match goal with
         | IH : context [Gsec ?τ _ _ = _ -> _], H : Gsec ?τ _ _ = _ |- _ =>
           apply IH in H; clear IH; [ simpl in H; rewrite H | .. ]
         end;
    eauto.

  all: rewrite open_body; eauto using Gsec_body, body_bvar.
Qed.

Lemma Gret_body τ : forall τ' e e',
  Gret τ τ' e' = Some e ->
  lc τ ->
  lc τ' ->
  body e' ->
  body e.
Proof.
  unfold body, open.
  induction τ; simpl_lift; eauto;
      repeat lc_inv;
      (* Apply induction hypotheses. *)
      repeat match goal with
             | IH : context [Gret ?τ _ _ = _ -> _], H : Gret ?τ _ _ = _ |- _ =>
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

Lemma Gret_open τ s : forall τ' e e',
  Gret τ τ' e' = Some e ->
  lc τ ->
  lc τ' ->
  Gret τ τ' <{ e'^s }> = Some <{ e^s }>.
Proof.
  unfold open.
  induction τ; simpl_lift; eauto;
    repeat lc_inv;
    repeat f_equal; try solve [ by rewrite !open_lc by eauto ].

  1-2:
  repeat match goal with
         | IH : context [Gret ?τ _ _ = _ -> _], H : Gret ?τ _ _ = _ |- _ =>
           apply IH in H; clear IH; [ simpl in H; rewrite H | .. ]
         end;
    eauto.

  all: repeat f_equal;
    try solve [ by rewrite !open_lc by eauto ];
    rewrite open_body; eauto using Gret_body, body_bvar.
Qed.

Lemma nodep_rename τ x y :
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
  - econstructor. eauto using nodep_rename.
  - rewrite subst_fresh.
    econstructor; eauto.
    simpl_cofin.
    rewrite <- subst_open_comm; eauto using lc.
    auto_eapply.
    all: fast_set_solver!!.
Qed.

Lemma lift_type_wf_rename τs τ' x y :
  lift_type_wf τs <{ τ'^x }> ->
  x # τs ->
  x # τ' ->
  lift_type_wf τs <{ τ'^y }>.
Proof.
  intros.
  rewrite (subst_intro τ' y x) by auto.
  eauto using lift_type_wf_rename_.
Qed.

Lemma gret_fv τ τ' e e' :
  gret τ τ' e' e ->
  fv e ⊆ fv τ ∪ fv τ' ∪ fv e'.
Proof.
  induction 1; simpl; eauto;
    simpl_cofin?; simpl_fv; fast_set_solver*!.
Qed.

Lemma lift_type_wf_fv τs τ :
  lift_type_wf τs τ ->
  stale τs ⊆ fv τ.
Proof.
  induction 1; simpl.
  - fast_set_solver!!.
  - simpl_cofin.
    simpl_fv.
    fast_set_solver*!.
Qed.

(** ** Correctness of the implementation *)

Lemma Gsec_refine τ : forall τ' e e',
  Gsec τ τ' e = Some e' ->
  lc τ' ->
  gsec τ τ' e e'.
Proof.
  induction τ; simpl_lift; try repeat lc_inv; eauto using gsec.
  (* Sum *)
  econstructor; simpl_cofin;
    match goal with
    | H : Gsec ?τ _ _ = _ |- gsec ?τ _ <{ fvar ?x }> _ =>
        eapply Gsec_open with (s:=x) in H; eauto
    end.
Qed.

Lemma Gret_refine τ : forall τ' e e',
  Gret τ τ' e = Some e' ->
  lc τ ->
  lc τ' ->
  gret τ τ' e e'.
Proof.
  induction τ; simpl_lift; try repeat lc_inv; eauto using gret.
  (* Sum and oblivious sum *)
  all:
    econstructor; eauto; simpl_cofin;
    match goal with
    | H : Gret ?τ _ _ = _ |- gret ?τ _ <{ fvar ?x }> _ =>
        eapply Gret_open with (s:=x) in H; eauto
    end.
Qed.

Arguments Gsec : simpl never.
Arguments Gret : simpl never.

Lemma Lift_core_refine τ : forall τ' xs e e',
  Lift_core τ τ' xs e = Some e' ->
  nodep τ -> nodep τ' ->
  lc e -> lc τ -> lc τ' ->
  fv τ ∪ fv τ' ∪ fv e ⊆ xs ->
  lift_core τ τ' e e'.
Proof.
  induction τ; simpl_lift;
    eauto using lift_core, Gsec_refine.
  case_match; [ | easy ].
  srewrite andb_true_iff. srewrite negb_true_iff. simp_hyps. subst.
  simplify_option_eq.
  repeat lc_inv.
  match goal with
  | H : context [ fresh ?xs ] |- _ =>
      let y := fresh "y" in
      set (fresh xs) as y in *;
      assert (y ∉ xs) by apply atom_is_fresh
  end.
  match goal with
  | H : Gret _ _ <{ fvar ?y }> = Some ?e' |- _ =>
      apply Gret_refine in H; eauto;
      assert (lc e') by eauto using lc, gret_lc;
      dup_hyp H (fun H => eapply gret_fv in H);
      rewrite <- (open_close e' y) in H by assumption
  end.
  match goal with
  | H : Lift_core ?τ _ _ _ = Some ?e', IH : context [ lift_core ?τ _ _ _ ] |- _ =>
      eapply IH in H; eauto using lc; try set_shelve;
      assert (lc e') by eauto using lc, lift_core_lc
  end.

  econstructor; simpl_cofin.
  - match goal with
    | H : gret _ _ <{ fvar ?y }> _ |- gret _ _ <{ fvar ?x }> _ =>
        eapply gret_subst with (x:=y) (s:=x) in H;
        [ | eauto using lc | shelve ];
        simpl in H;
        rewrite decide_True in H by eauto;
        rewrite <- subst_intro in H by shelve
    end.
    eassumption.
  - rewrite !open_close_subst by eauto.
    match goal with
    | H : lift_core _ _ <{ ?e _ }> _ |- context [ <{ {?y↦fvar ?x}_ }> ] =>
        eapply lift_core_subst with (x:=y) (s:=x) in H;
        [ | eauto using lc | shelve ];
        simpl in H;
        rewrite (subst_fresh e) in H by shelve
    end.
    eassumption.

  Unshelve.
  all: simpl; rewrite ?close_fv by eauto; fast_set_solver*!!.
Qed.

Lemma Lift_refine_ τs : forall τ τ' xs e e',
  Lift_ τs τ τ' xs e = Some e' ->
  nodep τ ->
  lift_type_wf τs τ' ->
  lc e -> lc τ -> lc τ' ->
  fv τ ∪ fv τ' ∪ fv e ⊆ xs ->
  lift τs τ τ' e e'.
Proof.
  induction τs; simpl_lift;
    select (lift_type_wf _ _) (fun H => sinvert H);
    eauto using Lift_core_refine, lift.
  repeat lc_inv.
  match goal with
  | H : context [ fresh ?xs ] |- _ =>
      let y := fresh "y" in
      set (fresh xs) as y in *;
      assert (y ∉ xs) by apply atom_is_fresh
  end.
  econstructor.
  simpl_cofin.
  select (lift_type_wf _ _)
         (fun H => dup_hyp H (fun H => apply lift_type_wf_fv in H);
                 eapply lift_type_wf_rename in H); eauto.
  match goal with
  | H : Lift_ _ _ _ _ _ = Some ?e', IH : context [ lift _ _ _ _ _ ] |- _ =>
      eapply IH in H; eauto with lc; try set_shelve;
      assert (lc e') by eauto using lift_lc with lc
  end.
  rewrite open_close_subst by eauto.
  match goal with
  | H : lift _ _ _ _ _ |- context [ <{ {?y↦(fvar ?x)}_ }> ] =>
      eapply lift_subst with (x:=y) (s:=x) in H;
      [ | eauto using lc | shelve ];
      rewrite <- subst_intro in H by shelve
  end.
  eassumption.

  Unshelve.
  all: simpl_fv; fast_set_solver*!.
Qed.

Theorem Lift_refine τs τ τ' e e' κ' :
  Lift τs τ τ' e = Some e' ->
  nodep τ ->
  lift_type_wf τs τ' ->
  ∅ ⊢ τ' :: κ' ->
  ∅ ⊢ e :{⊤} τ ->
  lift τs τ τ' e e'.
Proof.
  intros.
  eapply Lift_refine_; eauto with lc.
  simpl_fv.
  fast_set_solver*!!.
Qed.

Theorem Lift_well_typed_correct τs τ τ' e e' κ' :
  Lift τs τ τ' e = Some e' ->
  nodep τ ->
  lift_type_wf τs τ' ->
  ∅ ⊢ τ' :: κ' ->
  ∅ ⊢ e :{⊤} τ ->
  ∅ ⊢ e' :{⊥} τ' /\ lift_requiv τs τ τ' e e'.
Proof.
  eauto 10 using Lift_refine, lift_well_typed, lift_correct with lc.
Qed.

End lifting.
