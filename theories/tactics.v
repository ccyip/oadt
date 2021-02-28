From oadt Require Import base.

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

(** Run [tac] on each hypothesis matching [pat]. *)
Tactic Notation "select" "!" open_constr(pat) tactic3(tac) :=
  let T := lazymatch goal with
           | H : pat |- _ => type of H
           end in
  do_hyps (fun H => lazymatch type of H with
                  | pat => tac H
                  | _ => idtac
                  end);
  (* Clear the shelved. *)
  unify T pat.

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

(** * General purpose tactics  *)

(** Check [a] contains [pat]. *)
Tactic Notation "contains" constr(a) open_constr(pat) :=
  lazymatch a with
  | context g [pat] => let a' := context g [pat] in
                       unify a a'
  end.

(** Check goal matches pattern [pat]. *)
Tactic Notation "goal_is" open_constr(pat) :=
  lazymatch goal with
  | |- pat => lazymatch goal with
              | |- ?T => unify T pat
              end
  end.

(** Check goal contains [pat]. *)
Tactic Notation "goal_contains" open_constr(pat) :=
  lazymatch goal with
  | |- ?T => contains T pat
  end.

Ltac higher_order_reflexivity :=
  match goal with
  | |- (?f ?a) = ?b =>
    match eval pattern a in b with
    | ?f' _ => unify f f'; reflexivity
    end
  end.

(** ** Set solving *)

(* Much faster set solving tactic, with less solving strength. *)
Tactic Notation "fast_set_solver" :=
  solve [try fast_done; repeat (set_unfold; subst; intuition)].

(* Faster set solving tactic. Stronger than [fast_set_solver], but also
slower. *)
Tactic Notation "fast_set_solver" "*" :=
  try fast_done; set_unfold; qauto.
