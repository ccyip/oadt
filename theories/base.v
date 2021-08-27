From Coq Require Export Relations.Relation_Operators Relations.Operators_Properties.
From stdpp Require Export prelude fin_maps fin_map_dom.
From smpl Require Export Smpl.
From Hammer Require Export Tactics.

(** * Definitions *)

(** Normal form *)
Definition nf {A : Type} (R : relation A) (a : A) : Prop :=
  ¬ exists a', R a a'.

(** Transitive extensions *)
Section trans_ext.

  Variable A : Type.
  Variable R : relation A.

  Inductive trans_ext (x : A) : A -> nat -> Prop :=
  | TERefl : trans_ext x x 0
  | TEStep y z n : R x y -> trans_ext y z n -> trans_ext x z (S n)
  .

End trans_ext.

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

(** * Notations *)

Notation "m '>>=' f" := (mbind f m) (at level 60, right associativity) : stdpp_scope.

Notation "x <- y ; z" := (y >>= (λ x : _, z))
  (at level 20, y at level 30, z at level 200, only parsing) : stdpp_scope.

Notation "' x <- y ; z" := (y >>= (λ x : _, z))
  (at level 20, x pattern, y at level 30, z at level 200, only parsing) : stdpp_scope.
