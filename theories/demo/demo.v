From oadt Require Import prelude.
From stdpp Require Import pretty.
From Coq Require Import Int63.Int63.
From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.
From oadt Require Import demo.demo_prelude.

Import notations int_notations.

(* When we write a name, it means global variable. *)
Coercion EGVar : atom >-> expr.

(* Names *)
Definition nat : atom := "nat".
Definition tree : atom := "tree".
Definition is_zero : atom := "is_zero".
Definition pred : atom := "pred".
Definition otree : atom := "~tree".
Notation "'~tree'" := (otree) (in custom oadt).
Definition s_tree : atom := "s_tree".
Definition r_tree : atom := "r_tree".
Definition insert : atom := "insert".
Definition oinsert : atom := "~insert".
Notation "'~insert'" := (oinsert) (in custom oadt).

Definition zero : atom := "zero".
Definition succ : atom := "succ".
Definition leaf : atom := "leaf".
Definition node : atom := "node".

(* Define introduction/elimination as notations for convenience.
Alternatively, we can also define them directly inside lambda oadt. *)
Notation "'zero'" := <{ fold<nat> (inl<𝟙 + @nat> ()) }>
                     (in custom oadt).
Notation "'succ' e" := <{ fold<nat> (inr<𝟙 + @nat> e) }>
                       (in custom oadt at level 1,
                           e custom oadt at level 0).
Notation "'leaf'" := <{ fold<tree> (inl<𝟙 + int * @tree * @tree> ()) }>
                     (in custom oadt).
Notation "'node' e" := <{ fold<tree> (inr<𝟙 + int * @tree * @tree> e) }>
                       (in custom oadt at level 0,
                           e custom oadt at level 0).

(* Global definitions. *)
Definition defs := [{
  data nat := 𝟙 + nat;
  data tree := 𝟙 + int * tree * tree;
  obliv ~tree (:nat) :=
    if is_zero $0
    then 𝟙
    else 𝟙 ~+ ~int * (~tree (pred $0)) * (~tree (pred $0));

  (* def zero :{⊥} @nat := fold<nat> (inl<𝟙 + nat> ()); *)

  (* def succ :{⊥} Π:nat, nat := \:nat => fold<nat> (inr<𝟙 + nat> $0); *)

  (* def leaf :{⊥} @tree := fold<tree> (inl<𝟙 + int * tree * tree> ()); *)

  (* def node :{⊤} Π~:int * tree * tree, tree := *)
  (*   \~:int * tree * tree => fold<tree> (inr<𝟙 + int * tree * tree> $0); *)

  def is_zero :{⊥} Π:nat, 𝔹 :=
    \:nat => case unfold<nat> $0 of true | false;

  def pred :{⊥} Π:nat, nat :=
    \:nat => case unfold<nat> $0 of zero | $0;

  def s_tree :{⊥} Π~:tree, Π:nat, ~tree $0 :=
    \~:tree => \:nat =>
      if is_zero $0
      then ()
      else tape (case unfold<tree> $1 of
                   ~inl<𝟙 ~+ ~int * (~tree (pred $1)) * (~tree (pred $1))> ()
                 | ~inr<𝟙 ~+ ~int * (~tree (pred $1)) * (~tree (pred $1))>
                     tape (s_int ($0).1.1,
                           s_tree ($0).1.2 (pred $1),
                           s_tree ($0).2 (pred $1)));

  def r_tree :{⊤} Π:nat, Π:~tree $0, tree :=
    \:nat =>
      if is_zero $0
      then \:𝟙 => leaf
      else \:𝟙 ~+ ~int * (~tree (pred $0)) * (~tree (pred $0)) =>
             ~case $0 of
               leaf
             | node (r_int ($0).1.1,
                     r_tree (pred $2) ($0).1.2,
                     r_tree (pred $2) ($0).2);

  def insert :{⊤} Π~:int, Π~:tree, tree :=
    \~:int => \~:tree =>
    case unfold<tree> $0 of
      node ($2, leaf, leaf)
    | if $2 <= ($0).1.1
      then node (($0).1.1, insert $2 ($0).1.2, ($0).2)
      else node (($0).1.1, ($0).1.2, insert $2 ($0).2);

  def ~insert :{⊥} Π:~int, Π:nat, Π:~tree $0, ~tree (succ $1) :=
    \:~int => \:nat => \:~tree $0 =>
      s_tree (insert (r_int $2) (r_tree $1 $0)) (succ $1)
}].

Definition Σ : gctx := list_to_map defs.

(** Typing *)
(* We can type this global context. *)
Example example_gctx_typing : gctx_typing Σ.
Proof.
  eapply gctx_gdefs_typing; [ reflexivity | compute_done | ].
  eapply Forall_fold_right; repeat split.
  all : repeat typing_tac.
Qed.


(** Semantics. *)
(* Warning: very slow. *)

(* An example oblivious tree type, with index 2. *)
Example ex_tree_type :=
  <{ ~tree (succ (succ zero)) }>.
Print ex_tree_type.

(* It can be evalute to type value. *)
Definition ex_tree_type_pack :
  sigT (fun ω => Σ ⊨ ex_tree_type -->* ω /\ otval ω).
Proof.
  repeat esplit.
  eapply mstep_alt_mstep.

  repeat mstep_tac.

  constructor.
  repeat step_tac.
Defined.

Definition ex_tree_type_v := ltac:(extract ex_tree_type_pack).
Print ex_tree_type_v.

(* An example tree. *)
Definition ex_tree :=
  <{ node (i(2), node (i(1), leaf, leaf), node (i(4), leaf, leaf)) }>.
Print ex_tree.

(* An example oblivious tree *)
Definition ex_otree :=
  <{ s_tree ex_tree (succ (succ zero)) }>.

(* We can evaluate it to an oblivious value. *)
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

(* An example of insert. *)
Definition ex_insert :
  sigT (fun v => Σ ⊨ <{ insert i(3) ex_tree }> -->* v /\ val v).
Proof.
  repeat esplit.
  eapply mstep_alt_mstep.

  repeat mstep_tac.

  constructor.
  repeat step_tac; auto using VIntLit.
Defined.

Definition ex_insert_result := ltac:(extract ex_insert).
Print ex_insert_result.

(* An example of oblivious insert. *)
Definition ex_oinsert :
  sigT (fun v => Σ ⊨ <{ ~insert i[3] (succ (succ zero)) ex_otree_v }> -->* v /\ val v).
Proof.
  repeat esplit.
  eapply mstep_alt_mstep.

  repeat mstep_tac.

  cbn.
  constructor.
  repeat step_tac.
Defined.

Definition ex_oinsert_result := ltac:(extract ex_oinsert).
Print ex_oinsert_result.
