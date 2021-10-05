(** This demo shows that higher-order functions naturally work in this sytem. We
 use map function as an example. *)
From oadt Require Import demo.demo_prelude.
Import notations.

(** Names. *)
Definition nat : atom := "nat".
Definition tree : atom := "tree".
Definition otree : atom := "~tree".
Notation "'~tree'" := (otree) (in custom oadt).
Definition s_tree : atom := "s_tree".
Definition r_tree : atom := "r_tree".
Definition map : atom := "map".
Definition omap : atom := "~map".
Notation "'~map'" := (omap) (in custom oadt).

Notation "'zero'" := <{ fold<nat> (inl<𝟙 + #nat> ()) }>
                     (in custom oadt).
Notation "'succ' e" := <{ fold<nat> (inr<𝟙 + #nat> e) }>
                       (in custom oadt at level 2).
Notation "'leaf'" := <{ fold<tree> (inl<𝟙 + 𝔹 * #tree * #tree> ()) }>
                     (in custom oadt).
Notation "'node' e" := <{ fold<tree> (inr<𝟙 + 𝔹 * #tree * #tree> e) }>
                       (in custom oadt at level 2).


(** Global definitions. *)
Definition defs := [{
  data nat := 𝟙 + nat;

  (* Use 𝔹 as payload for simplicity. *)
  data tree := 𝟙 + 𝔹 * tree * tree;

  (* The public view is the maximum depth. *)
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

  (* The oblivious counterpart of the map function. Note that this idea of
  lifting a public function to its oblivious version works naturally here. *)
  def ~map :{⊥} Π~:(Π~:𝔹, 𝔹), Π:nat, Π:~tree $0, ~tree $1 :=
    \~:(Π~:𝔹, 𝔹) => \:nat => \:~tree $0 =>
      s_tree (map $2 (r_tree $1 $0)) $1
}].

Definition Σ : gctx := list_to_map defs.

(** We can type this global context. *)
Example example_gctx_typing : gctx_typing Σ.
Proof.
  gctx_typing_solver.
Qed.

(** An example tree. *)
Definition ex_tree :=
  <{ node (true, node (true, leaf, leaf), node (false, leaf, leaf)) }>.
Print ex_tree.

(** Its corresponding oblivious tree. *)
Definition ex_otree :=
  <{ s_tree ex_tree (succ (succ zero)) }>.

Definition ex_otree_pack :
  sig (fun v => Σ ⊨ ex_otree -->* v /\ oval v).
Proof.
  mstep_solver.
Defined.
Definition ex_otree_v := ltac:(extract ex_otree_pack).
Print ex_otree_v.

(** Map a negation function on this oblivious tree. *)
Definition ex_omap :
  sig (fun v => Σ ⊨ <{ ~map (\~:𝔹 => if $0 then false else true)
                          (succ (succ zero))
                          ex_otree_v }> -->* v /\ val v).
Proof.
  mstep_solver.
Defined.
Definition ex_omap_result := ltac:(extract ex_omap).
Print ex_omap_result.
