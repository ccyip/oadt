From oadt Require Import base.
From oadt Require Import tactics.

(** This file contains common definitions for locally nameless representation
and tactics for automation. *)

(** * Atom  *)

(** Having type class constraints inside the structure to avoid polluting the
proof contexts. *)
Class Atom A M D := {
  (* Constraints. *)
  atom_finmap_dom :> ∀ C, Dom (M C) D;
  atom_finmap_fmap :> FMap M;
  atom_finmap_lookup :> ∀ C, Lookup A C (M C);
  atom_finmap_empty :> ∀ C, Empty (M C);
  atom_finmap_partial_alter :> ∀ C, PartialAlter A C (M C);
  atom_finmap_omap :> OMap M;
  atom_finmap_merge :> Merge M;
  atom_finmap_to_list :> ∀ C, FinMapToList A C (M C);
  atom_finset_elem_of :> ElemOf A D;
  atom_finset_empty :> Empty D;
  atom_finset_singleton :> Singleton A D;
  atom_finset_union :> Union D;
  atom_finset_intersection :> Intersection D;
  atom_finset_difference :> Difference D;
  atom_finset_elements :> Elements A D;

  (* Properties that we care about. *)
  atom_eq_decision :> EqDecision A;
  atom_infinite :> Infinite A;
  atom_finset :> FinSet A D;
  atom_finmap :> FinMap A M;

  (* Property about FinMapDom; we do it this way to avoid duplicates. *)
  atom_elem_of_dom {C} (m : M C) i : i ∈ dom D m <-> is_Some (m !! i);

  (* Decision procedure of ∈ can technically be derived from other constrains
  (by applying [elem_of_dec_slow]). But this allows an efficient
  implementation. *)
  atom_finmap_elem_of_dec :> RelDecision (∈@{D});
}.

Instance atom_dom_spec `{is_atom : Atom A M D} : FinMapDom A M D.
Proof.
  destruct is_atom. split; first [typeclasses eauto | auto].
Defined.

(* From stdpp Require Import stringmap mapset. *)
(* (** An Atom instance, showing Atom can be inhabited. This instance is not *)
(* intended to be used in the acutal implementation. *) *)
(* Module atom_instance. *)

(*   Instance atom_string : Atom string stringmap (mapset stringmap). *)
(*   Proof. *)
(*     econstructor; try typeclasses eauto. *)
(*     apply mapset_dom_spec. *)
(*   Defined. *)

(* End atom_instance. *)

(** * Tactics for cofinite quantifiers  *)

(** [stale] returns a finite set [D] that a sufficiently fresh atom of type [A]
should not belong to. *)
Class Stale {D} A := stale : A -> D.

(** If [e] has Stale instance, add it into [acc]. *)
(* [acc] could be [tt] for empty set. Quite hacky indeed. *)
Ltac collect_one_stale e acc :=
  match goal with
  | _ => lazymatch acc with
         | tt => constr:(stale e)
         | _ => constr:(acc ∪ (stale e))
         end
  | _ => acc
  end.

(** Return all stales in the context. *)
Ltac collect_stales S :=
  let stales := fold_hyps S collect_one_stale in
  lazymatch stales with
  | tt => fail "no stale available"
  | _ => stales
  end.

Ltac prettify_stales :=
  repeat match goal with
         (* | H : ?x ∉ ∅ |- _ => clear H *)
         | H : context C [stale ?v] |- _ =>
           let S := eval unfold stale in (stale v) in
           let S := eval simpl in S in
           let H' := context C [S] in
           change H' in H
         end.

(** Simplify the freshness assumptions. *)
Ltac simpl_fresh H :=
  rewrite ?not_elem_of_union in H;
  destruct_and? H;
  prettify_stales.

(** Instantiate cofinite quantifiers with atom [x] and discharge the freshness
condition. *)
Ltac inst_atom x :=
  repeat match goal with
         | H : forall _, _ ∉ ?L -> _ |- _ =>
           try specialize (H x ltac:(set_solver))
         end.

(** Check if it is meaningful to generate fresh atoms. *)
Ltac has_cofin :=
  match goal with
  | |- forall _, _ ∉ _ -> _ => idtac
  | H : forall _, _ ∉ _ -> _ |- _ => idtac
  end.

(** Introduce a sufficiently fresh atom. [S] is an extra set that this atom does
not belong to. Continue with [tac] on the freshness proof. *)
Tactic Notation "sufficiently_fresh" constr(S) tactic3(tac) :=
  set_fold_not;
  repeat lazymatch goal with
         | H : ?x ∉ ?L |- _ => is_evar L; revert x H
         end;
  has_cofin;
  let H := fresh "Hfresh" in
  let S := collect_stales S in
  match goal with
  | |- forall _, _ ∉ ?L -> _ => is_evar L; unify L S; intros ? H; tac H
  | _ => destruct (exist_fresh S) as [? H]; tac H
  end.

(** [simpl_cofin] introduces a sufficiently fresh atom and instantiates the
cofinite quantifiers. It may optionally accept an extra set [S] that the
introduced atom should not belong to. The [simpl_cofin*] variants do not
instantiate the cofinite quantifiers, but only simplify the freshness
hypotheses, so they are not destructive. *)
Tactic Notation "simpl_cofin" "*" constr(S) :=
  sufficiently_fresh S (fun H => simpl_fresh H).

Tactic Notation "simpl_cofin" constr(S) :=
  sufficiently_fresh S (fun H => match type of H with
                               | ?x ∉ _ =>
                                 simpl_fresh H; inst_atom x
                               end).

Tactic Notation "simpl_cofin" "*" := simpl_cofin* tt.

Tactic Notation "simpl_cofin" := simpl_cofin tt.

Tactic Notation "simpl_cofin" "?" := try simpl_cofin.
