From stdpp Require Export prelude fin_maps fin_map_dom.
From smpl Require Export Smpl.
From Hammer Require Export Tactics.

(** * Classes *)

Class FinMapPack K M := {
  pack_finmap_decision :: EqDecision K | 0;
  pack_finmap_fmap :: FMap M | 0;
  pack_finmap_lookup :: ∀ A, Lookup K A (M A) | 0;
  pack_finmap_empty :: ∀ A, Empty (M A) | 0;
  pack_finmap_partial_alter :: ∀ A, PartialAlter K A (M A) | 0;
  pack_finmap_omap :: OMap M | 0;
  pack_finmap_merge :: Merge M | 0;
  pack_finmap_map_fold :: ∀ A, MapFold K A (M A) | 0;

  pack_finmap :: FinMap K M | 0;
}.

(** * Lemmas *)

Lemma insert_fresh_subseteq `{FinMapDom K M D} {A} k (m : M A) v :
  k ∉ dom m ->
  m ⊆ <[k:=v]>m.
Proof.
  intros. apply insert_subseteq. apply not_elem_of_dom. auto.
Qed.

Lemma rtc_preserve `{R : relation A} (P : A -> Prop) (x y : A) :
  (forall x y, P x -> R x y -> P y) ->
  P x ->
  rtc R x y ->
  P y.
Proof.
  induction 3; eauto.
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
