(** This demo encodes an oblivious tree whose public view is the upper bound of
the number of its vertices. This shows that the public view can be rather
intricate. *)
From oadt Require Import demo.demo_prelude.
Import notations.

(** Names. *)
Definition nat : atom := "nat".
Definition list : atom := "list".
Definition olist : atom := "~list".
Notation "'~list'" := (olist) (in custom oadt).
Definition s_list : atom := "s_list".
Definition r_list : atom := "r_list".

Definition tree : atom := "tree".
Definition s_tree : atom := "s_tree".
Definition r_tree : atom := "r_tree".
Definition s_V : atom := "s_V".
Definition r_V : atom := "r_V".
Definition append : atom := "append".
Definition skip : atom := "skip".
Definition tolist : atom := "tolist".
Definition fromlist : atom := "fromlist".

Notation "'V'" := <{ (𝟙 + 𝔹) }> (in custom oadt).
Notation "'~V'" := <{ (𝟙 ~+ ~𝔹) }> (in custom oadt).
Notation "'Vleaf'" := <{ inl<V> () }> (in custom oadt).
Notation "'Vnode' e" := <{ inr<V> e }> (in custom oadt at level 2).

Notation "'nil'" := <{ fold<list> (inl<𝟙 + V * #list> ()) }>
                     (in custom oadt).
Notation "'cons' e" := <{ fold<list> (inr<𝟙 + V * #list> e) }>
                       (in custom oadt at level 2).

Notation "'leaf'" := <{ fold<tree> (inl<𝟙 + 𝔹 * #tree * #tree> ()) }>
                     (in custom oadt).
Notation "'node' e" := <{ fold<tree> (inr<𝟙 + 𝔹 * #tree * #tree> e) }>
                       (in custom oadt at level 2).

Notation "'~tree'" := (olist) (in custom oadt).

(** Global definitions. *)
Definition defs := [{
  data nat := 𝟙 + nat;

  (* Use 𝔹 as payload for simplicity. *)
  data tree := 𝟙 + 𝔹 * tree * tree;

  (* The list element is either a leaf or a node with Boolean payload. *)
  data list := 𝟙 + V * list;

  def append :{⊤} Π~:list, Π~:list, list :=
    \~:list => \~:list =>
      case unfold<list> $1 of
        $1
      | cons (($0).1, append ($0).2 $1);

  (* Skip a tree *)
  def skip :{⊤} Π~:list, list :=
    \~:list =>
      case unfold<list> $0 of
        (* Bogus. Can't skip a tree in empty list. *)
        nil
      | case ($0).1 of
          (* Skip the leaf *)
          ($1).2
          (* If it is a node, then skip twice for the left and right
          subtrees. *)
        | skip (skip ($1).2);

  def s_V :{⊥} Π~:V, ~V :=
    \~:V =>
      tape (case $0 of
              ~inl<(~V)> ()
            | ~inr<(~V)> (tape (s𝔹 $0)));
  def r_V :{⊤} Π:~V, V :=
    \:~V =>
      ~case $0 of
        Vleaf
      | Vnode (r𝔹 $0);

  (* The public view is the maximum length *)
  obliv ~list (:nat) :=
    case unfold<nat> $0 of
      𝟙
    | 𝟙 ~+ ~V * (~list $0);

  def s_list :{⊥} Π~:list, Π:nat, ~list $0 :=
    \~:list => \:nat =>
      case unfold<nat> $0 of
        ()
      | tape (case unfold<list> $2 of
                ~inl<𝟙 ~+ ~V * (~list $1)> ()
              | ~inr<𝟙 ~+ ~V * (~list $1)> (tape (s_V ($0).1, s_list ($0).2 $1)));

  def r_list :{⊤} Π:nat, Π:~list $0, list :=
    \:nat =>
      case unfold<nat> $0 of
        \:𝟙 => nil
      | \:𝟙 ~+ ~V * (~list $0) =>
          ~case $0 of
            nil
          | cons (r_V ($0).1, r_list $2 ($0).2);

  (* The public view is the upper bound of the number of its vertices. The
  oblivious representation is essentially the flatten tree. So [~tree] is simply
  an alias of [~list]. *)
  def s_tree :{⊥} Π~:tree, Π:nat, ~tree $0 :=
    \~:tree => \:nat => s_list (tolist $1) $0;

  def r_tree :{⊤} Π:nat, Π:~tree $0, tree :=
    \:nat => \:~tree $0 => fromlist (r_list $1 $0);

  def tolist :{⊤} Π~:tree, list :=
    \~:tree =>
      case unfold<tree> $0 of
        cons (Vleaf, nil)
      | cons (Vnode ($0).1.1, append (tolist ($0).1.2) (tolist ($0).2));

  def fromlist :{⊤} Π~:list, tree :=
    \~:list =>
      case unfold<list> $0 of
        (* Bogus. Empty list does not correspond to any tree. *)
        leaf
      | case ($0).1 of
          leaf
        | node ($0, fromlist ($1).2, fromlist (skip ($1).2))
}].

Definition Σ : gctx := list_to_map defs.

(** We can type this global context. *)
Example example_gctx_typing : gctx_typing Σ.
Proof.
  gctx_typing_solver.
Qed.
