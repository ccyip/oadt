From Coq Require Export Relations.Relation_Operators.
From stdpp Require Export prelude fin_maps fin_map_dom.
From Hammer Require Export Tactics.

(** * Fold over hypotheses *)

Ltac revert_all :=
  repeat match goal with
         | H : _ |- _ => revert H
         end.

(** This cool trick to fold over hypotheses is inspired by
https://sympa.inria.fr/sympa/arc/coq-club/2014-12/msg00034.html *)
Ltac get_hyps :=
  constr:(ltac:(revert_all; constructor) : True).

(** Run [tac] on each hypothesis. *)
Tactic Notation "do_hyps" tactic3(tac) :=
  let hs := get_hyps in
  let rec go hs :=
      lazymatch hs with
      | ?hs ?H => tac H; go hs
      | _ => idtac
      end in
  go hs.

(** Fold over hypotheses and return the [constr] result. Run [tac] on each
hypothesis with the accumulator. [acc] is the initial accumulator. *)
Ltac fold_hyps acc tac :=
  let hs := get_hyps in
  let rec go hs acc :=
      lazymatch hs with
      | ?hs ?H => let acc' := tac H acc in go hs acc'
      | _ => acc
      end in
  go hs acc.

(** Fold over hypotheses with continuation. [acc] and [tac] are the same as in
[fold_hyps_nok]. [ktac] is the continuation run on the final result. *)
Tactic Notation "fold_hyps_cont" constr(acc) tactic3(tac) tactic3(ktac) :=
  let x := fold_hyps acc tac in
  ktac x.

(** * General Lemmas *)

Lemma insert_fresh_subseteq `{FinMapDom K M D} {A} : forall k (m : M A) v,
  k ∉ dom D m ->
  m ⊆ <[k:=v]>m.
Proof.
  intros. apply insert_subseteq. apply not_elem_of_dom. auto.
Qed.
