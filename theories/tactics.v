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

(** * Use lemmas with implicit arguments *)
(** [sauto] family unfortunately does not accept lemmas with implicit arguments.
Meanwhile, [use*] may be used to introduce these lemmas into the context. *)
(* We may use [open_constr_list] as arguments, but unfortunately Coq seems to
only allow primitive tactics to manipulate the list. *)
Tactic Notation "use" "*" uconstr(L1)
  := let H := fresh "Lem" in epose proof L1 as H.
Tactic Notation "use" "*" uconstr(L1)
                      "," uconstr(L2)
  := let H := fresh "Lem" in epose proof L1 as H;
     let H := fresh "Lem" in epose proof L2 as H.
Tactic Notation "use" "*" uconstr(L1)
                      "," uconstr(L2)
                      "," uconstr(L3)
  := let H := fresh "Lem" in epose proof L1 as H;
     let H := fresh "Lem" in epose proof L2 as H;
     let H := fresh "Lem" in epose proof L3 as H.
Tactic Notation "use" "*" uconstr(L1)
                      "," uconstr(L2)
                      "," uconstr(L3)
                      "," uconstr(L4)
  := let H := fresh "Lem" in epose proof L1 as H;
     let H := fresh "Lem" in epose proof L2 as H;
     let H := fresh "Lem" in epose proof L3 as H;
     let H := fresh "Lem" in epose proof L4 as H.
Tactic Notation "use" "*" uconstr(L1)
                      "," uconstr(L2)
                      "," uconstr(L3)
                      "," uconstr(L4)
                      "," uconstr(L5)
  := let H := fresh "Lem" in epose proof L1 as H;
     let H := fresh "Lem" in epose proof L2 as H;
     let H := fresh "Lem" in epose proof L3 as H;
     let H := fresh "Lem" in epose proof L4 as H;
     let H := fresh "Lem" in epose proof L5 as H.
