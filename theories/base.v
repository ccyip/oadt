From Coq Require Export Relations.Relation_Operators.
From stdpp Require Export prelude fin_maps fin_map_dom.
From Hammer Require Export Tactics.

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
