From Coq Require Export Relations.Relation_Operators.
From stdpp Require Export prelude fin_maps fin_map_dom.
From smpl Require Export Smpl.
From Hammer Require Export Tactics.

(** * Definitions *)

Definition nf {A : Type} (R : relation A) (a : A) : Prop :=
  ¬ exists a', R a a'.

(** * Lemmas *)

Lemma insert_fresh_subseteq `{FinMapDom K M D} {A} k (m : M A) v :
  k ∉ dom D m ->
  m ⊆ <[k:=v]>m.
Proof.
  intros. apply insert_subseteq. apply not_elem_of_dom. auto.
Qed.

Lemma map_empty_subseteq `{FinMap K M} {A} (m : M A) :
  ∅ ⊆ m.
Proof.
  rewrite map_subseteq_spec. intros ??. by rewrite lookup_empty.
Qed.

(** * More setoid rewriting for sets *)

Section set.

  Context `{SemiSet A C}.

  #[global]
  Instance union_subseteq_proper : Proper ((⊆) ==> (⊆) ==> (⊆@{C})) (∪).
  Proof.
    intros ??????.
    set_solver.
  Qed.

  #[global]
  Instance union_subseteq_flip_proper : Proper ((⊆) --> (⊆) --> flip (⊆@{C})) (∪).
  Proof.
    intros ??????. simpl in *.
    set_solver.
  Qed.

  #[global]
  Instance elem_of_subseteq_proper :
    Proper ((=) ==> (⊆) ==> impl) (∈@{C}).
  Proof.
    intros ???????. subst.
    set_solver.
  Qed.

  #[global]
  Instance elem_of_subseteq_flip_proper :
    Proper ((=) ==> (⊆) --> flip impl) (∈@{C}).
  Proof.
    intros ???????. subst.
    set_solver.
  Qed.

  #[global]
  Instance set_Forall_proper :
    Proper ((pointwise_relation _ iff) ==> (≡) ==> iff) (set_Forall (A:=A) (C:=C)).
  Proof.
    sfirstorder.
  Qed.

End set.

(** * Finite Set *)

(** Polymorphic finite set *)
Class PolyFinSet (M : Type -> Type) := {
  poly_finset_elem_of A `{EqDecision A} :> ElemOf A (M A);
  poly_finset_empty A `{EqDecision A} :> Empty (M A);
  poly_finset_singleton A `{EqDecision A} :> Singleton A (M A);
  poly_finset_union A `{EqDecision A} :> Union (M A);
  poly_finset_intersection A `{EqDecision A} :> Intersection (M A);
  poly_finset_difference A `{EqDecision A} :>Difference (M A);
  poly_finset_elements A `{EqDecision A} :> Elements A (M A);

  poly_finset A `{EqDecision A} :> FinSet A (M A);
}.

Definition set_insert `{Singleton A C} `{Union C} (x : A) (X : C) : C := {[x]} ∪ X.

Section map.

  Context `{FinSet A C}.

  Lemma set_map_id X : set_map (C:=C) id X ≡ X.
  Proof.
    set_solver.
  Qed.

  #[global]
  Instance set_insert_proper : Proper ((=) ==> (≡) ==> (≡)) (set_insert (A:=A) (C:=C)).
  Proof.
    solve_proper.
  Qed.

  Lemma set_Forall_insert P (x : A) (X : C) :
    set_Forall P (set_insert x X) <-> P x /\ set_Forall P X.
  Proof.
    unfold set_insert.
    unfold set_Forall.
    set_solver.
  Qed.

  Lemma set_Forall_insert_1 P (x : A) (X : C) :
    set_Forall P (set_insert x X) -> P x /\ set_Forall P X.
  Proof.
    hauto use: set_Forall_insert.
  Qed.

  Lemma set_Forall_insert_2 (P : A -> Prop) (x : A) (X : C) :
    P x -> set_Forall P X -> set_Forall P (set_insert x X).
  Proof.
    hauto use: set_Forall_insert.
  Qed.

  Context `{Set_ B D}.

  Lemma set_map_insert (f : A -> B) (X : C) (x : A) :
    set_map (D:=D) f (set_insert x X) ≡ set_insert (f x) (set_map (D:=D) f X).
  Proof.
    set_solver.
  Qed.

End map.


(** * More Instances *)

Instance bool_top : Top bool := true.
Arguments bool_top /.
Instance bool_bot : Bottom bool := false.
Arguments bool_bot /.
