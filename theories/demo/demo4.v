From oadt Require Import prelude.
From stdpp Require Import pretty.
From Coq Require Import Int63.Int63.
From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.
From oadt Require Import demo.demo_prelude.

Import notations int_notations.

(** This demo shows that higher-order function also works in this sytem. We use
 map function as an example. *)

Coercion EGVar : atom >-> expr.

(* Names *)
Definition nat : atom := "nat".
Definition tree : atom := "tree".
Definition otree : atom := "~tree".
Notation "'~tree'" := (otree) (in custom oadt).
Definition s_tree : atom := "s_tree".
Definition r_tree : atom := "r_tree".
Definition map : atom := "map".
Definition omap : atom := "~map".
Notation "'~map'" := (omap) (in custom oadt).

Notation "'zero'" := <{ fold<nat> (inl<𝟙 + @nat> ()) }>
                     (in custom oadt).
Notation "'succ' e" := <{ fold<nat> (inr<𝟙 + @nat> e) }>
                       (in custom oadt at level 1,
                           e custom oadt at level 0).
Notation "'leaf'" := <{ fold<tree> (inl<𝟙 + 𝔹 * @tree * @tree> ()) }>
                     (in custom oadt).
Notation "'node' e" := <{ fold<tree> (inr<𝟙 + 𝔹 * @tree * @tree> e) }>
                       (in custom oadt at level 0,
                           e custom oadt at level 0).


Definition defs := [{
  data nat := 𝟙 + nat;

  (* Use 𝔹 as payload for simplicity. *)
  data tree := 𝟙 + 𝔹 * tree * tree;

  (* Index is the upper bound of its depth *)
  obliv ~tree (:nat) :=
    case unfold<nat> $0 of
      𝟙
    | 𝟙 ~+ ~𝔹 * (~tree $0) * (~tree $0);
  def s_tree :{⊥} Π~:tree, Π:nat, ~tree $0 :=
    \~:tree => \:nat =>
      case unfold<nat> $0 of
        ()
      | tape (case unfold<tree> $2 of
                   ~inl<𝟙 ~+ ~𝔹 * (~tree $1) * (~tree $1)> ()
                 | ~inr<𝟙 ~+ ~𝔹 * (~tree $1) * (~tree $1)>
                     tape (s𝔹 ($0).1.1,
                           s_tree ($0).1.2 $1,
                           s_tree ($0).2 $1));
  def r_tree :{⊤} Π:nat, Π:~tree $0, tree :=
    \:nat =>
      case unfold<nat> $0 of
        \:𝟙 => leaf
      | \:𝟙 ~+ ~𝔹 * (~tree $0) * (~tree $0) =>
          ~case $0 of
            leaf
          | node (r𝔹 ($0).1.1,
                  r_tree $2 ($0).1.2,
                  r_tree $2 ($0).2);

  def map :{⊤} Π~:(Π~:𝔹, 𝔹), Π~:tree, tree :=
    \~:(Π~:𝔹, 𝔹) => \~:tree =>
      case unfold<tree> $0 of
        leaf
      | node ($2 ($0).1.1, map $2 ($0).1.2, map $2 ($0).2);

  def ~map :{⊥} Π~:(Π~:𝔹, 𝔹), Π:nat, Π:~tree $0, ~tree $1 :=
    \~:(Π~:𝔹, 𝔹) => \:nat => \:~tree $0 =>
      s_tree (map $2 (r_tree $1 $0)) $1
}].

Definition Σ : gctx := list_to_map defs.

Example example_gctx_typing : gctx_typing Σ.
Proof.
  eapply gctx_gdefs_typing; [ reflexivity | compute_done | ].
  eapply Forall_fold_right; repeat split.
  all : repeat typing_tac.
Qed.

(* An example tree. *)
Definition ex_tree :=
  <{ node (true, node (true, leaf, leaf), node (false, leaf, leaf)) }>.
Print ex_tree.

(* An example oblivious tree *)
Definition ex_otree :=
  <{ s_tree ex_tree (succ (succ zero)) }>.

Definition ex_otree_pack :
  sigT (fun v => Σ ⊨ ex_otree -->* v /\ oval v).
Proof.
  repeat esplit.
  eapply mstep_alt_mstep.

  repeat mstep_tac.

  constructor.
  repeat step_tac.
Defined.

Definition ex_otree_v := ltac:(extract ex_otree_pack).
Print ex_otree_v.

(* Map a negation function. *)
Definition ex_omap :
  sigT (fun v => Σ ⊨ <{ ~map (\~:𝔹 => if $0 then false else true) (succ (succ zero)) ex_otree_v }> -->* v /\ val v).
Proof.
  repeat esplit.
  eapply mstep_alt_mstep.

  repeat mstep_tac.

  cbn.
  constructor.
  repeat step_tac.
Defined.

Definition ex_omap_result := ltac:(extract ex_omap).
Print ex_omap_result.
