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

End set.

(** * More Classes *)

(** Polymorphic finite set *)
Class PolyFinSet (S : forall A, EqDecision A -> Type) := {
  poly_finset_elem_of :> forall A H, ElemOf A (S A H);
  poly_finset_empty :> forall A H, Empty (S A H);
  poly_finset_singleton :> forall A H, Singleton A (S A H);
  poly_finset_union :> forall A H, Union (S A H);
  poly_finset_intersection :> forall A H, Intersection (S A H);
  poly_finset_difference :> forall A H, Difference (S A H);
  poly_finset_elements :> forall A H, Elements A (S A H);

  poly_finset :> forall A H, FinSet A (S A H);
}.

(** * More Instances *)

Instance bool_top : Top bool := true.
Arguments bool_top /.
Instance bool_bot : Bottom bool := false.
Arguments bool_bot /.
