(** Common tactics and lemmas, and definitions related to locally nameless
representation and free variables. *)
From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.

Import syntax.notations.
Import semantics.notations.
Import typing.notations.

Implicit Types (b : bool) (x X y Y z : atom) (L : aset).

#[local]
Coercion EFVar : atom >-> expr.

(** * Definitions *)

(** ** Variable closing *)
Section close.

Reserved Notation "'{' k '<~' x '}' e" (in custom oadt at level 20, k constr).

Fixpoint close_ (k : nat) (x : atom) (e : expr) : expr :=
  match e with
  | <{ fvar y }> => if decide (x = y) then <{ bvar k }> else e
  | <{ Π:τ1, τ2 }> => <{ Π:{k<~x}τ1, {S k<~x}τ2 }>
  | <{ \:τ => e }> => <{ \:{k<~x}τ => {S k<~x}e }>
  | <{ let e1 in e2 }> => <{ let {k<~x}e1 in {S k<~x}e2 }>
  | <{ case{l} e0 of e1 | e2 }> => <{ case{l} {k<~x}e0 of {S k<~x}e1 | {S k<~x}e2 }>
  (* Congruence rules *)
  | <{ τ1 * τ2 }> => <{ ({k<~x}τ1) * ({k<~x}τ2) }>
  | <{ τ1 +{l} τ2 }> => <{ ({k<~x}τ1) +{l} ({k<~x}τ2) }>
  | <{ e1 e2 }> => <{ ({k<~x}e1) ({k<~x}e2) }>
  | <{ s𝔹 e }> => <{ s𝔹 ({k<~x}e) }>
  | <{ if{l} e0 then e1 else e2 }> => <{ if{l} {k<~x}e0 then {k<~x}e1 else {k<~x}e2 }>
  | <{ (e1, e2) }> => <{ ({k<~x}e1, {k<~x}e2) }>
  | <{ π@b e }> => <{ π@b ({k<~x}e) }>
  | <{ inj{l}@b<τ> e }> => <{ inj{l}@b<({k<~x}τ)> ({k<~x}e) }>
  | <{ fold<X> e }> => <{ fold<X> ({k<~x}e) }>
  | <{ unfold<X> e }> => <{ unfold<X> ({k<~x}e) }>
  | _ => e
  end

where "'{' k '<~' x '}' e" := (close_ k x e) (in custom oadt).

End close.

Definition close x e := close_ 0 x e.

(** ** Free variables *)
Fixpoint fv (e : expr) : aset :=
  match e with
  | <{ fvar x }> => {[x]}
  (* Congruence rules *)
  | <{ \:τ => e }> | <{ inj{_}@_<τ> e }> | <{ [inj@_<τ> e] }> =>
    fv τ ∪ fv e
  | <{ Π:τ1, τ2 }> | <{ τ1 * τ2 }> | <{ τ1 +{_} τ2 }> =>
    fv τ1 ∪ fv τ2
  | <{ let e1 in e2 }> | <{ (e1, e2) }> | <{ e1 e2 }> =>
    fv e1 ∪ fv e2
  | <{ case{_} e0 of e1 | e2 }> | <{ if{_} e0 then e1 else e2 }> =>
    fv e0 ∪ fv e1 ∪ fv e2
  | <{ s𝔹 e }> | <{ π@_ e }>
  | <{ fold<_> e }> | <{ unfold<_> e }> =>
    fv e
  | _ => ∅
  end.

(** Free variables in the range of [tctx]. *)
Definition tctx_fv : tctx -> aset :=
  map_fold (fun x τ S => fv τ ∪ S) ∅.

Definition closed e := fv e ≡ ∅.

Instance atom_stale : @Stale aset atom := singleton.
Arguments atom_stale /.

Instance aset_stale : Stale aset := id.
Arguments aset_stale /.

Instance expr_stale : Stale expr := fv.
Arguments expr_stale /.

Instance tctx_stale : Stale tctx := fun Γ => dom aset Γ ∪ tctx_fv Γ.
Arguments tctx_stale /.

Arguments stale /.

(** * Instances *)

(** [kind] forms a [SemiLattice].  *)
Instance kind_semilattice : SemiLattice kind.
Proof.
  split; try reflexivity; repeat intros []; auto.
Qed.

(** * Tactics *)

Ltac set_shelve :=
  lazymatch goal with
  | |- _ ∉ _ => shelve
  | |- _ ⊆ _ => shelve
  | |- _ <> _ => shelve
  end.

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

Ltac case_label :=
  lazymatch goal with
  | |- context [<{ inj{?l}@_<_> _ }>] => destruct l
  | |- context [<{ if{?l} _ then _ else _ }>] => destruct l
  | |- context [<{ case{?l} _ of _ | _ }>] => destruct l
  | |- context [<{ 𝔹{?l} }>] => destruct l
  | |- context [<{ _ +{?l} _ }>] => destruct l
  end.

Ltac apply_lc_inv :=
  match goal with
  | H : lc ?e |- _ => head_constructor e; sinvert H
  end.

Ltac apply_gctx_wf :=
  match goal with
  | Hwf : gctx_wf ?Σ, H : ?Σ !! _ = _ |- _ =>
    dup_hyp H (fun H => apply Hwf in H; try simp_hyp H)
  end.

Ltac relax_typing_type :=
  match goal with
  | |- ?Σ; ?Γ ⊢ ?e : _ =>
    refine (eq_ind _ (fun τ => Σ; Γ ⊢ e : τ) _ _ _)
  end.

(** * Lemmas *)

(** ** Properties of opening and closing *)

(* NOTE: [inversion] is the culprit for the slowness of this proof. *)
Lemma open_lc_ e : forall s u i j,
  <{ {j~>u}({i~>s}e) }> = <{ {i~>s}e }> ->
  i <> j ->
  <{ {j~>u}e }> = e.
Proof.
  induction e; hauto.
Qed.

(** Open a locally-closed expression does not change it. *)
Lemma open_lc e : forall s,
  lc e -> forall k, <{ {k~>s}e }> = e.
Proof.
  induction 1; try scongruence;
    (* expressions with binders *)
    simpl_cofin; hauto use: open_lc_.
Qed.

Lemma open_lc_intro e s :
  lc e -> <{ e^s }> = e.
Proof.
  unfold open.
  qauto use: open_lc.
Qed.

(* Rather slow because we have to do induction on [e1] and then destruct [e2],
which produces a lot of cases (quadratic in the number of the language
constructs). A better way to handle this may be to prove a "lock-step" induction
principle, similar to [rect2] for [Vector]. *)
Lemma open_inj x e1 : forall e2,
  <{ e1^x }> = <{ e2^x }> ->
  x ∉ fv e1 ∪ fv e2 ->
  e1 = e2.
Proof.
  unfold open. generalize 0.
  induction e1; intros; subst; simpl in *;
  lazymatch goal with
  | H : ?e' = <{ {_~>_}?e }> |- _ =>
    destruct e; simpl in *; repeat (try scongruence; case_decide);
      try (head_constructor e'; sinvert H)
  end;
    repeat f_equal;
    try (auto_eapply; eauto; fast_set_solver!!).

  all: set_unfold; sfirstorder.
Qed.

Lemma close_open e x :
  x # e ->
  close x (open x e) = e.
Proof.
  intros.
  unfold open, close. generalize 0.
  induction e; intros; simpl;
    hauto solve: fast_set_solver!!.
Qed.

Lemma open_close_ x y z e : forall i j,
  i <> j ->
  y # e ->
  y <> x ->
  open_ i y (open_ j z (close_ j x e)) = open_ j z (close_ j x (open_ i y e)).
Proof.
  induction e; intros; simpl;
    solve [ repeat (case_decide; subst; simpl; try scongruence; eauto)
          | f_equal; auto_apply; eauto; fast_set_solver!! ].
Qed.

Lemma open_close e x :
  lc e ->
  open x (close x e) = e.
Proof.
  intros H.
  unfold open, close. generalize 0.
  induction H; intros; simpl; try hauto;
    f_equal; eauto;
      match goal with
      | |- ?e = _ => simpl_cofin (fv e)
      end;
      (eapply open_inj; [ unfold open; rewrite open_close_ | ]);
      eauto; fast_set_solver!!.
Qed.

(** ** Properties of substitution *)

Lemma subst_fresh e : forall x s,
  x # e -> <{ {x↦s}e }> = e.
Proof.
  induction e; simpl; intros; f_equal;
    (* Case analysis for [EFVar] case *)
    try case_split; subst;
    try auto_apply; fast_set_solver!.
Qed.

Lemma subst_open_distr e : forall x s v,
  lc s ->
  <{ {x↦s}(e^v) }> = <{ ({x↦s}e)^({x↦s}v) }>.
Proof.
  unfold open. generalize 0.
  induction e; try qauto rew: off use: open_lc; qauto use: open_lc.
Qed.

Lemma subst_open_comm e : forall x y s,
  x <> y ->
  lc s ->
  <{ {x↦s}(e^y) }> = <{ ({x↦s}e)^y }>.
Proof.
  qauto use: subst_open_distr.
Qed.

Lemma subst_trans x y s e :
  y # e ->
  {y↦s}({x↦y}e) = {x↦s}e.
Proof.
  intros.
  induction e; simpl in *; eauto;
    try (f_equal; auto_apply; fast_set_solver!!).
  repeat (case_decide; subst; simpl); try qauto.
  fast_set_solver!!.
Qed.

Lemma subst_ite_distr b e1 e2 x s :
  <{ {x↦s}(ite b e1 e2) }> = <{ ite b ({x↦s}e1) ({x↦s}e2) }>.
Proof.
  destruct b; reflexivity.
Qed.

Lemma subst_id e x :
  {x↦x}e = e.
Proof.
  induction e; simpl; try case_decide; scongruence.
Qed.

Lemma subst_tctx_id (Γ : tctx) x :
  {x↦x} <$> Γ = Γ.
Proof.
  rewrite <- map_fmap_id.
  apply map_fmap_ext.
  scongruence use: subst_id.
Qed.

(** We may prove this one using [subst_open_distr] and [subst_fresh], but a
direct induction gives us a slightly stronger version (without the local closure
constraint). *)
Lemma subst_intro e : forall s x,
  x # e ->
  <{ e^s }> = <{ {x↦s}(e^x) }>.
Proof.
  unfold open. generalize 0.
  induction e; simpl; intros; f_equal;
    (* Case analysis for [EFVar] case *)
    try case_split; subst;
    try auto_apply; fast_set_solver*!.
Qed.

(** ** Properties of values *)

Lemma ovalty_elim v ω:
  ovalty v ω ->
  oval v /\ otval ω /\ forall Σ Γ, Σ; Γ ⊢ v : ω.
Proof.
  induction 1; hauto lq: on ctrs: oval, ovalty, otval, typing.
Qed.

(** ** Properties of local closure *)

Lemma otval_lc ω :
  otval ω ->
  lc ω.
Proof.
  induction 1; hauto ctrs: lc.
Qed.

Lemma oval_lc v :
  oval v ->
  lc v.
Proof.
  induction 1; hauto ctrs: lc use: otval_lc.
Qed.

Lemma ovalty_lc v ω :
  ovalty v ω ->
  lc v /\ lc ω.
Proof.
  induction 1; try hauto ctrs: lc.

  hauto use: otval_lc, ovalty_elim ctrs: otval, lc.
Qed.

(** Well-typed and well-kinded expressions are locally closed. *)
Lemma typing_lc Σ Γ e τ :
  Σ; Γ ⊢ e : τ ->
  lc e
with kinding_lc  Σ Γ τ κ :
  Σ; Γ ⊢ τ :: κ ->
  lc τ.
Proof.
  all: destruct 1; try hauto q: on rew: off ctrs: lc use: ovalty_lc;
    econstructor; simpl_cofin; qauto.
Qed.

Lemma subst_lc x e s :
  lc s ->
  lc e ->
  lc <{ {x↦s}e }>.
Proof.
  intros H.
  induction 1; simpl; try qauto ctrs: lc;
    repeat econstructor; simpl_cofin?; eauto using lc;
      rewrite <- subst_open_comm; eauto; fast_set_solver!!.
Qed.

Lemma subst_respect_lc x s t e :
  lc <{ {x↦s}e }> ->
  lc s ->
  lc t ->
  lc <{ {x↦t}e }>.
Proof.
  intros H. intros Hs Ht. remember ({x↦s}e).
  revert dependent e.
  induction H;
    intros []; simpl; inversion 1; subst; simp_hyps;
      try (case_decide; subst); try scongruence;
        econstructor; eauto;
          simpl_cofin?;
          rewrite <- ?subst_open_comm in *; eauto; fast_set_solver!!.
Qed.

Lemma open_respect_lc e s t :
  lc <{ e^s }> ->
  lc s ->
  lc t ->
  lc <{ e^t }>.
Proof.
  intros.
  destruct (exist_fresh (fv e)) as [y ?].
  erewrite subst_intro in *; eauto.
  eauto using lc, subst_respect_lc.
Qed.

Lemma open_respect_lc_atom x e s :
  lc <{ e^x }> ->
  lc s ->
  lc <{ e^s }>.
Proof.
  intros.
  eapply open_respect_lc; eauto using lc.
Qed.

Lemma lc_rename e x y :
  lc <{ e^x }> ->
  lc <{ e^y }>.
Proof.
  eauto using lc, open_respect_lc_atom.
Qed.

(** The type of well-typed expression is also locally closed. *)
Lemma typing_type_lc Σ Γ e τ :
  gctx_wf Σ ->
  Σ; Γ ⊢ e : τ ->
  lc τ.
Proof.
  intros Hwf.
  induction 1; eauto using lc, kinding_lc;
    try
      lazymatch goal with
      | H : Σ !! _ = Some _ |- _ =>
        apply Hwf in H; simp_hyps; eauto using kinding_lc
      | H : _; _ ⊢ _ : _ |- _ => apply typing_lc in H
      | H : ovalty _ _ |- _ => apply ovalty_lc in H
      end;
    try apply_lc_inv; simpl_cofin?;
      hauto l: on use: open_respect_lc, typing_lc, typing_lc ctrs: lc.
Qed.


(** ** Properties of free variables *)

Lemma open_fv_l e s :
  fv <{ e^s }> ⊆ fv e ∪ fv s.
Proof.
  unfold open. generalize 0.
  induction e; intros; simpl in *;
    try case_split; fast_set_solver*.
Qed.

Lemma open_fv_r e s :
  fv e ⊆ fv <{ e^s }>.
Proof.
  unfold open. generalize 0.
  induction e; intros; simpl in *;
    fast_set_solver.
Qed.

Lemma open_fresh x e s :
  x # e ->
  x # s ->
  x # <{ e^s }>.
Proof.
  qauto use: open_fv_l solve: set_solver.
Qed.

Lemma open_fresh_atom x e x' :
  x # e ->
  x <> x' ->
  x # <{ e^x' }>.
Proof.
  eauto using open_fresh with set_solver.
Qed.

Ltac induction_map_fold :=
  (* Massage the goal so it is ready for [map_fold_ind]. *)
  match goal with
  | |- context [ map_fold ?f ?b ?m ] =>
    let a := fresh "a" in
    set (map_fold f b m) as a; pattern a, m; subst a
  end;
  apply map_fold_ind.

Lemma tctx_fv_consistent Γ x :
  x ∉ tctx_fv Γ <-> map_Forall (fun _ τ => x # τ) Γ.
Proof.
  unfold tctx_fv.
  split; induction_map_fold;
    eauto using map_Forall_empty with set_solver;
    qauto use: map_Forall_insert solve: fast_set_solver.
Qed.

Lemma tctx_fv_subseteq Γ τ x :
  Γ !! x = Some τ ->
  fv τ ⊆ tctx_fv Γ.
Proof.
  intros. set_unfold. intros.
  (* Prove by contradiction; alternatively we can prove by [map_fold_ind]. *)
  apply dec_stable.
  hauto use: tctx_fv_consistent.
Qed.

Lemma tctx_fv_insert_subseteq Γ x τ :
  tctx_fv (<[x:=τ]>Γ) ⊆ fv τ ∪ tctx_fv Γ.
Proof.
  intros ? H.
  apply dec_stable. contradict H.
  set_unfold.
  qauto l: on use: tctx_fv_consistent, map_Forall_insert_2.
Qed.

Lemma tctx_fv_insert Γ x τ :
  x ∉ dom aset Γ ->
  tctx_fv (<[x:=τ]>Γ) ≡ fv τ ∪ tctx_fv Γ.
Proof.
  split; intros; try qauto use: tctx_fv_insert_subseteq.
  apply dec_stable.
  set_unfold.
  qauto l: on use: tctx_fv_consistent, map_Forall_insert, not_elem_of_dom.
Qed.

Lemma tctx_stale_inv Γ x :
  x # Γ -> x ∉ dom aset Γ /\ map_Forall (fun _ τ => x # τ) Γ.
Proof.
  hauto use: tctx_fv_consistent solve: fast_set_solver.
Qed.

Lemma subst_tctx_fresh (Γ : tctx) x s :
  x ∉ tctx_fv Γ ->
  {x↦s} <$> Γ = Γ.
Proof.
  intros.
  rewrite <- map_fmap_id.
  apply map_fmap_ext.
  intros; simpl.
  rewrite subst_fresh; eauto.
  hauto use: tctx_fv_consistent solve: fast_set_solver.
Qed.

Lemma otval_closed ω :
  otval ω ->
  closed ω.
Proof.
  induction 1; set_solver.
Qed.

Lemma oval_closed v :
  oval v ->
  closed v.
Proof.
  induction 1; qauto use: otval_closed solve: fast_set_solver*.
Qed.

Lemma ovalty_closed v ω :
  ovalty v ω ->
  closed ω /\ closed v.
Proof.
  induction 1; qauto use: otval_closed solve: fast_set_solver*.
Qed.

Lemma close_open_fresh_ x y e : forall k,
  x ∉ fv (close_ k x (open y e)) ->
  x ∉ fv (close_ k x e).
Proof.
  unfold open. generalize 0.
  induction e; intros; simpl in *;
    fast_set_solver*!!.
Qed.

Lemma close_fresh x e :
  (* This assumption is stronger than necessary. Ideally we only need to assume
  the boxed injection case is well-formed. But it is nonetheless good enough. *)
  lc e ->
  x # close x e.
Proof.
  (* Perhaps a better proof is to formalize the well-formedness regarding the
  boxed injection case and use it as the assumption. Then prove local closure
  entails that well-formedness. But it is quite annoying to add all these
  boilerplates when they are only used in this lemma so far. *)
  intros H.
  unfold close. generalize 0.
  induction H; intros; simpl;
    try solve [ try case_decide; fast_set_solver*!!
              | simpl_cofin;
                repeat select (forall n, _ # close_ n _ <{ _^_ }>)
                              (fun H => eapply close_open_fresh_ in H);
                fast_set_solver* ].

  select (otval _) (fun H => apply otval_closed in H).
  select (oval _) (fun H => apply oval_closed in H).
  fast_set_solver*.
Qed.

Lemma close_fv_subseteq1 x e :
  fv e ⊆ fv (close x e) ∪ {[ x ]}.
Proof.
  unfold close. generalize 0.
  induction e; intros; simpl;
    solve [ try case_decide; subst; try fast_set_solver!!
          | repeat
            match goal with
            | H : context [fv (close_ _ _ ?e)] |- context [fv (close_ ?k _ ?e)] =>
              rewrite (H k)
            end; fast_set_solver!! ].
Qed.

Lemma close_fv_subseteq2 x e :
  fv (close x e) ⊆ fv e.
Proof.
  unfold close. generalize 0.
  induction e; intros; simpl;
    solve [ try case_decide; subst; try fast_set_solver!!
          | repeat
            match goal with
            | H : context [fv (close_ _ _ ?e)] |- context [fv (close_ ?k _ ?e)] =>
              rewrite (H k)
            end; fast_set_solver!! ].
Qed.

Lemma close_fv x e :
  lc e ->
  fv (close x e) ≡ fv e ∖ {[x]}.
Proof.
  intros H.
  apply (close_fresh x) in H.
  use (close_fv_subseteq1 x e).
  use (close_fv_subseteq2 x e).
  fast_set_solver*!!.
Qed.

(** Simplifier for free variables. *)

Tactic Notation "fv_rewrite" constr(T) :=
  match T with
  | context [dom aset (<[_:=_]>_)] =>
    rewrite dom_insert
  end.

Tactic Notation "fv_rewrite" constr(T) "in" hyp(H) :=
  match T with
  | context [dom aset (<[_:=_]>_)] =>
    rewrite dom_insert in H
  end.

Tactic Notation "fv_rewrite_l" constr(T) :=
  match T with
  | context [ fv <{ _ ^ _ }> ] =>
    rewrite open_fv_l
  | context [tctx_fv (<[_:=_]>_)] =>
    rewrite tctx_fv_insert_subseteq
  end.

Tactic Notation "fv_rewrite_l" constr(T) "in" hyp(H) :=
  match T with
  | context [ fv <{ _ ^ _ }> ] =>
    rewrite open_fv_l in H
  | context [tctx_fv (<[_:=_]>_)] =>
    rewrite tctx_fv_insert_subseteq in H
  end.

Tactic Notation "fv_rewrite_r" constr(T) :=
  match T with
  | context [ fv <{ _ ^ _ }> ] =>
    rewrite <- open_fv_r
  end.

Tactic Notation "fv_rewrite_r" constr(T) "in" hyp(H) :=
  match T with
  | context [ fv <{ _ ^ _ }> ] =>
    rewrite <- open_fv_r in H
  end.

(* It would be ideal if we check the positivity of the set relation occurrence.
But this works fine and we have to avoid unnecessary setoid rewriting, which is
rather slow when they succeed and extremely slow when they fail. *)
Ltac simpl_fv_rewrite :=
  match goal with
  | |- ?L ⊆ ?R =>
    first [ fv_rewrite (L ⊆ R)
          | fv_rewrite_l L
          | fv_rewrite_r R ]; simpl
  | |- _ ∉ ?T =>
    first [ fv_rewrite T
          | fv_rewrite_l T ]; simpl
  | |- _ ∈ ?T =>
    first [ fv_rewrite T
          | fv_rewrite_r T ]; simpl
  | H : ?L ⊆ ?R |- _ =>
    first [ fv_rewrite_l R in H
          | fv_rewrite_r L in H ]; simpl in H
  | H : _ ∉ ?T |- _ =>
    fv_rewrite_r T in H; simpl in H
  | H : _ ∈ ?T |- _ =>
    fv_rewrite_l T in H; simpl in H
  | H : context [?L ⊆ ?R] |- _ =>
    fv_rewrite (L ⊆ R) in H; simpl in H
  | H : context [_ ∉ ?T] |- _ =>
    fv_rewrite T in H; simpl in H
  | H : context [_ ∈ ?T] |- _ =>
    fv_rewrite T in H; simpl in H
  end.

Tactic Notation "simpl_fv_rewrite_more" "by" tactic3(tac) :=
  match goal with
  | |- context [tctx_fv (<[_:=_]>_)] =>
    rewrite tctx_fv_insert by tac
  | H : context [tctx_fv (<[_:=_]>_)] |- _ =>
    rewrite tctx_fv_insert in H by tac
  end.

(** We thread the saturation-style simplifiers using the [Smpl] plugin, and
then do the rewriting. *)
Smpl Create fv.
Tactic Notation "simpl_fv" :=
  set_fold_not; repeat (smpl fv); clear_blocked; repeat simpl_fv_rewrite.
Tactic Notation "simpl_fv" "*" "by" tactic3(tac) :=
  simpl_fv; repeat simpl_fv_rewrite_more by tac.
Tactic Notation "simpl_fv" "*" :=
  simpl_fv* by fast_set_solver!!.

Ltac simpl_fv_core :=
  match goal with
  | H : ovalty _ _ |- _ =>
    apply ovalty_closed in H; unfold closed in H; destruct H
  | H : oval _ |- _ =>
    apply oval_closed in H; unfold closed in H
  | H : otval _ |- _ =>
    apply otval_closed in H; unfold closed in H
  | H : ?Σ !! _ = Some ?D, Hwf : gctx_wf ?Σ |- _ =>
    lazymatch D with
    (* Handle [DFun] later *)
    | DFun _ _ => fail
    | _ => dup_hyp! H (fun H => apply Hwf in H) with (fun H => try simp_hyp H)
    end
  | H : ?Γ !! _ = Some _ |- _ =>
    lazymatch type of Γ with
    | tctx =>
      dup_hyp! H (fun H => apply elem_of_dom_2 in H);
      dup_hyp! H (fun H => apply tctx_fv_subseteq in H)
    end
  end.
Smpl Add simpl_fv_core : fv.

(** Well-typed and well-kinded terms are closed under typing context. *)
Lemma typing_kinding_fv Σ :
  (forall Γ e τ,
      Σ; Γ ⊢ e : τ ->
      fv e ⊆ dom aset Γ) /\
  (forall Γ τ κ,
      Σ; Γ ⊢ τ :: κ ->
      fv τ ⊆ dom aset Γ).
Proof.
  apply typing_kinding_mutind; intros; simpl in *;
    simpl_cofin?; simpl_fv; fast_set_solver*!.
Qed.

Lemma typing_fv Σ Γ e τ :
  Σ; Γ ⊢ e : τ ->
  fv e ⊆ dom aset Γ.
Proof.
  qauto use: typing_kinding_fv.
Qed.

Lemma kinding_fv Σ Γ τ κ :
  Σ; Γ ⊢ τ :: κ ->
  fv τ ⊆ dom aset Γ.
Proof.
  qauto use: typing_kinding_fv.
Qed.

Ltac simpl_typing_kinding_fv :=
  match goal with
  | H : _; _ ⊢ _ : _ |- _ =>
    dup_hyp! H (fun H => apply typing_fv in H)
  | H : _; _ ⊢ _ :: _ |- _ =>
    dup_hyp! H (fun H => apply kinding_fv in H)
  end.
Smpl Add simpl_typing_kinding_fv : fv.

(** Well-formed contexts are closed. *)
Lemma gctx_wf_closed Σ :
  gctx_wf Σ ->
  map_Forall (fun _ D =>
                match D with
                | DADT τ =>
                  closed τ
                | DOADT τ e | DFun τ e =>
                  closed τ /\ closed e
                end) Σ.
Proof.
  intros Hwf.
  intros ?? H.
  case_split; apply_gctx_wf;
    simpl_cofin?; simpl_fv; set_solver.
Qed.

Ltac simpl_wf_fv :=
  match goal with
  | H : ?Σ !! _ = Some _, Hwf : gctx_wf ?Σ |- _ =>
    dup_hyp! H (fun H => apply gctx_wf_closed in H;
                       [ | apply Hwf])
      with (fun H => unfold closed in H; destruct H)
  end.
Smpl Add simpl_wf_fv : fv.

(** Free variables in the type of a well-typed term are bounded in typing
context. *)
Lemma typing_type_fv Σ Γ e τ :
  gctx_wf Σ ->
  Σ; Γ ⊢ e : τ ->
  fv τ ⊆ dom aset Γ.
Proof.
  intros Hwf.
  induction 1; intros; simpl in *;
    simpl_cofin?; simpl_fv; fast_set_solver*!.
Qed.

Ltac simpl_typing_type_fv :=
  match goal with
  | H : ?Σ; ?Γ ⊢ _ : _, Hwf : gctx_wf ?Σ |- _ =>
    dup_hyp! H (fun H => apply typing_type_fv in H; [| apply Hwf])
              with (fun H => simpl in H)
  end.
Smpl Add simpl_typing_type_fv : fv.

(** ** Properties of parallel reduction and local closure *)
Lemma pared_lc1 Σ e e' :
  gctx_wf Σ ->
  Σ ⊢ e ⇛ e' ->
  lc e.
Proof.
  intros ?.
  induction 1; eauto using lc;
    repeat econstructor; eauto;
      qauto use: ovalty_elim, oval_lc, otval_lc.
Qed.

Lemma pared_lc2 Σ e e' :
  gctx_wf Σ ->
  Σ ⊢ e ⇛ e' ->
  lc e'.
Proof.
  intros ?.
  induction 1; eauto using lc;
    try apply_gctx_wf;
    simpl_cofin?;
    eauto using open_respect_lc_atom, typing_lc, kinding_lc;
    repeat econstructor;
    qauto use: open_respect_lc_atom, ovalty_elim, oval_lc.
Qed.

Lemma pared_lc Σ e e' :
  gctx_wf Σ ->
  Σ ⊢ e ⇛ e' ->
  lc e /\ lc e'.
Proof.
  eauto using pared_lc1, pared_lc2.
Qed.
