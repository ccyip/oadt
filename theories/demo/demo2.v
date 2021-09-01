From oadt Require Import prelude.
From stdpp Require Import pretty.
From Coq Require Import Int63.Int63.
From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.
From oadt Require Import demo.demo_prelude.

Import notations int_notations.

(** This demo contains some extra oblivious ADT definitions: oblivious list,
oblivious tree with spine as its bound, etc. *)

Coercion EGVar : atom >-> expr.

(** Names. *)
Definition nat : atom := "nat".
Definition tree : atom := "tree".
Definition list : atom := "list".
Definition olist : atom := "~list".
Definition olist' : atom := "~list'".
Definition s_list : atom := "s_list".
Definition r_list : atom := "r_list".
Definition s_list' : atom := "s_list'".
Definition r_list' : atom := "r_list'".
Definition otree : atom := "otree".
Definition s_otree : atom := "s_tree".
Definition r_otree : atom := "r_tree".

Definition spine : atom := "spine".
Definition ostree : atom := "~stree".
Definition s_ostree : atom := "s_ostree".
Definition r_ostree : atom := "r_ostree".

Notation "'zero'" := <{ fold<nat> (inl<𝟙 + #nat> ()) }>
                     (in custom oadt).
Notation "'succ' e" := <{ fold<nat> (inr<𝟙 + #nat> e) }>
                       (in custom oadt at level 2).

Notation "'nil'" := <{ fold<list> (inl<𝟙 + 𝔹 * #list> ()) }>
                     (in custom oadt).
Notation "'cons' e" := <{ fold<list> (inr<𝟙 + 𝔹 * #list> e) }>
                       (in custom oadt at level 2).

Notation "'leaf'" := <{ fold<tree> (inl<𝟙 + 𝔹 * #tree * #tree> ()) }>
                     (in custom oadt).
Notation "'node' e" := <{ fold<tree> (inr<𝟙 + 𝔹 * #tree * #tree> e) }>
                       (in custom oadt at level 2).

Notation "'sleaf'" := <{ fold<spine> (inl<𝟙 + #spine * #spine> ()) }>
                      (in custom oadt).
Notation "'snode' e" := <{ fold<spine> (inr<𝟙 + #spine * #spine> e) }>
                        (in custom oadt at level 2).

(** Global definitions. *)
Definition defs := [{
  data nat := 𝟙 + nat;

  (* Use 𝔹 as payload for simplicity. *)
  data list := 𝟙 + 𝔹 * list;
  data tree := 𝟙 + 𝔹 * tree * tree;
  data spine := 𝟙 + spine * spine;

  (* Index is the upper bound of its length *)
  obliv olist (:nat) :=
    case unfold<nat> $0 of
      𝟙
    | 𝟙 ~+ ~𝔹 * (olist@$0);
  def s_list :{⊥} Π~:list, Π:nat, olist@$0 :=
    \~:list => \:nat =>
      case unfold<nat> $0 of
        ()
      | tape (case unfold<list> $2 of
                ~inl<𝟙 ~+ ~𝔹 * (olist@$1)> ()
              | ~inr<𝟙 ~+ ~𝔹 * (olist@$1)> (tape (s𝔹 ($0).1, s_list ($0).2 $1)));
  def r_list :{⊤} Π:nat, Π:olist@$0, list :=
    \:nat =>
      case unfold<nat> $0 of
        \:𝟙 => nil
      | \:𝟙 ~+ ~𝔹 * (olist@$0) =>
          ~case $0 of
            nil
          | cons (r𝔹 ($0).1, r_list $2 ($0).2);

  (* Index is the upper bound of its spine *)
  obliv ostree (:spine) :=
    case unfold<spine> $0 of
      𝟙
    | 𝟙 ~+ ~𝔹 * (ostree@($0).1) * (ostree@($0).2);
  def s_ostree :{⊥} Π~:tree, Π:spine, ostree@$0 :=
    \~:tree => \:spine =>
      case unfold<spine> $0 of
        ()
      | tape (case unfold<tree> $2 of
                   ~inl<𝟙 ~+ ~𝔹 * (ostree@($1).1) * (ostree@($1).2)> ()
                 | ~inr<𝟙 ~+ ~𝔹 * (ostree@($1).1) * (ostree@($1).2)>
                     tape (s𝔹 ($0).1.1,
                           s_ostree ($0).1.2 ($1).1,
                           s_ostree ($0).2 ($1).2));
  def r_ostree :{⊤} Π:spine, Π:ostree@$0, tree :=
    \:spine =>
      case unfold<spine> $0 of
        \:𝟙 => leaf
      | \:𝟙 ~+ ~𝔹 * (ostree@($0).1) * (ostree@($0).2) =>
          ~case $0 of
            leaf
          | node (r𝔹 ($0).1.1,
                  r_ostree ($2).1 ($0).1.2,
                  r_ostree ($2).2 ($0).2)
}].

Definition Σ : gctx := list_to_map defs.

(** We can type this global context. *)
Example example_gctx_typing : gctx_typing Σ.
Proof.
  eapply gctx_gdefs_typing; [ reflexivity | compute_done | ].
  eapply Forall_fold_right; repeat split.
  all : repeat typing_tac.
Qed.
