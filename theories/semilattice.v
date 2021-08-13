From oadt Require Import base.
From oadt Require Import tactics.

(** * Semi-lattice *)

(** Technically this definition is more than just a semilattice. It is a bounded
join-semilattice with a top element. *)
Class SemiLattice A `{Join A, Top A, Bottom A, SqSubsetEq A} := {
  join_comm :> Comm (=@{A}) (⊔);
  join_assoc :> Assoc (=@{A}) (⊔);
  join_idemp :> IdemP (=@{A}) (⊔);
  join_left_id :> LeftId (=@{A}) (⊥) (⊔);
  join_left_absorb :> LeftAbsorb (=@{A}) (⊤) (⊔);

  join_consistent (x y : A) : x ⊑ y <-> y = x ⊔ y
}.

(** * Theorems *)
Section theorems.

Context `{SemiLattice A}.

#[global]
Instance join_right_id : RightId (=@{A}) (⊥) (⊔).
Proof.
  scongruence use: join_comm, join_left_id.
Qed.

#[global]
Instance join_right_absorb : RightAbsorb (=@{A}) (⊤) (⊔).
Proof.
  scongruence use: join_comm, join_left_absorb.
Qed.

Lemma join_lub (x y z : A) :
  x ⊑ z -> y ⊑ z -> x ⊔ y ⊑ z.
Proof.
  rewrite !join_consistent.
  scongruence use: join_assoc.
Qed.

Lemma join_ub_l (x y : A) :
  x ⊑ x ⊔ y.
Proof.
  rewrite !join_consistent.
  scongruence use: join_assoc, join_idemp.
Qed.

Lemma join_ub_r (x y : A) :
  y ⊑ x ⊔ y.
Proof.
  rewrite join_comm. apply join_ub_l.
Qed.

Lemma join_prime (x y z : A) :
  z ⊑ x -> z ⊑ y -> z ⊑ x ⊔ y.
Proof.
  rewrite !join_consistent.
  scongruence use: join_assoc.
Qed.

Lemma top_ub (x : A) :
  x ⊑ ⊤.
Proof.
  rewrite !join_consistent.
  scongruence use: join_right_absorb.
Qed.

Lemma bot_lb (x : A) :
  ⊥ ⊑ x.
Proof.
  rewrite !join_consistent.
  scongruence use: join_left_id.
Qed.

Lemma top_inv (x : A) :
  ⊤ ⊑ x -> x = ⊤.
Proof.
  rewrite !join_consistent.
  scongruence use: join_left_absorb.
Qed.

Lemma bot_inv (x : A) :
  x ⊑ ⊥ -> x = ⊥.
Proof.
  rewrite !join_consistent.
  scongruence use: join_right_id.
Qed.

Lemma join_bot_iff (x y : A) :
  x ⊔ y = ⊥ <-> x = ⊥ /\ y = ⊥.
Proof.
  split.
  - intros.
    assert (x ⊔ (x ⊔ y) = x ⊔ ⊥ /\ y ⊔ (x ⊔ y) = y ⊔ ⊥)
      by sfirstorder.
    scongruence use: join_assoc, join_comm, join_idemp, join_right_id.
  - sfirstorder.
Qed.

#[global]
Instance semilattice_is_po : PartialOrder (⊑@{A}).
Proof.
  repeat split;
    unfold Reflexive, Transitive, AntiSymm;
    setoid_rewrite join_consistent;
    scongruence use: join_idemp,
                     join_assoc,
                     join_comm.
Qed.

End theorems.

(** * Instances *)

(** Boolean is also a semilattice. *)

Instance bool_join : Join bool := orb.
Instance bool_top : Top bool := true.
Instance bool_bot : Bottom bool := false.
Instance bool_le : SqSubsetEq bool := implb.

Instance bool_semilattice : SemiLattice bool.
Proof.
  split; hnf; repeat intros []; easy.
Qed.

(** * Tactics *)
Tactic Notation "lattice_naive_solver" "by" tactic3(tac) :=
  solve [ reflexivity
        | tac
        | etrans; tac ].

Ltac lattice_naive_solver :=
  solve [ reflexivity
        | eauto
        | etrans; eauto ].
