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

Ltac set_fold_not :=
  change (?x ∈ ?v -> False) with (x ∉ v) in *;
  change (?x = ?v -> False) with (x <> v) in *.

(** Pruning the hypotheses before set solving can *dramatically* improve
performance. The following pruning tactics are based on heuristics, and they can
make the goal unprovable. While they are unsound, they still work fine in our
cases. A better approach is probably similar to finding a transitive closure of
hypotheses against some "potentially needed" criteria. *)

(** This pruning tactic is conservative, hence the name "safe". However, it can
still make the goal unprovable. For example, it does not consider, say, that the
set relations may appear in a conjunction. *)
(* TODO: is it a way to check the conclusion of a hypothesis has certain "head"?
I am using [context [_ -> _]] for now, which has some false negatives. *)
Ltac set_prune_hyps_safe :=
  simpl;
  set_fold_not;
  repeat
    match goal with
    | H : ?T |- _ =>
      lazymatch T with
      | _ ⊆ _ => fail
      | _ ≡ _ => fail
      | _ ∈ _ => fail
      | _ ∉ _ => fail
      | _ <> _ => fail
      | context [_ -> _ ⊆ _] => fail
      | context [_ -> _ ≡ _] => fail
      | context [_ -> _ ∈ _] => fail
      | context [_ -> _ ∉ _] => fail
      | context [_ -> _ <> _] => fail
      | _ => clear H
      end
    end.

(** [set_hyp_filter] filters a hypothesis in continuation style, so we can
thread a few filters. *)
Tactic Notation "set_hyp_filter" constr(T) ">>=" tactic3(tac) :=
  lazymatch T with
  | _ ⊆ _ => fail
  | _ ≡ _ => fail
  | context [_ -> _ ⊆ _] => fail
  | context [_ -> _ ≡ _] => fail
  | _ => tac T
  end.

Tactic Notation "set_hyp_filter" constr(T) constr(x) ">>=" tactic3(tac) :=
  lazymatch T with
  | context [x] =>
    lazymatch T with
    | _ ∈ _ => fail
    | _ ∉ _ => fail
    | _ <> _ => fail
    | context [_ -> _ ∈ _] => fail
    | context [_ -> _ ∉ _] => fail
    | context [_ -> _ <> _] => fail
    | _ => tac T
    end
  | _ => tac T
  end.

(** This pruning tactic is more radical. It is more likely to destroy the
goal, but it also offers better performance in certain cases. *)
Ltac set_prune_hyps :=
  simpl;
  set_fold_not;
  try
    lazymatch goal with
    | |- _ ⊆ _ =>
      repeat
        match goal with
        | H : ?T |- _ =>
          set_hyp_filter T >>= (fun _ => clear H)
        end
    | |- ?y ∉ _ =>
      repeat
        match goal with
        | H : ?T |- _ =>
          set_hyp_filter T >>= (fun T =>
            set_hyp_filter T y >>= (fun _ => clear H))
        end
    | |- ?x <> ?y =>
      repeat
        match goal with
        | H : ?T |- _ =>
          set_hyp_filter T >>= (fun T =>
            set_hyp_filter T x >>= (fun T =>
              set_hyp_filter T y >>= (fun _ => clear H)))
        end
    end.

Tactic Notation "set_solver" "!" :=
  set_prune_hyps_safe; set_solver.
Tactic Notation "set_solver" "!!" :=
  set_prune_hyps; set_solver.

Tactic Notation "fast_set_solver" "!" :=
  set_prune_hyps_safe; fast_set_solver.
Tactic Notation "fast_set_solver" "!!" :=
  set_prune_hyps; fast_set_solver.

Tactic Notation "fast_set_solver" "*" "!" :=
  set_prune_hyps_safe; fast_set_solver*.
Tactic Notation "fast_set_solver" "*" "!!" :=
  set_prune_hyps; fast_set_solver*.
