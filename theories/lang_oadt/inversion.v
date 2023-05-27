(** Typing and kinding inversion lemmas. *)
From idt Require Import all.
From oadt.lang_oadt Require Import
     base syntax semantics typing infrastructure
     equivalence.
Import syntax.notations typing.notations equivalence.notations.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

#[local]
Coercion EFVar : atom >-> expr.

(** * Kind inversion  *)

Ltac tsf_kinding ctor kinding_inv :=
  lazymatch ctor with
  | KSub => tsf_skip
  | _ =>
      let H := fresh in
      pose proof ctor as H;
      repeat
        lazymatch type of H with
        | forall e : ?T, _ =>
            refine (forall e : T, _ : Prop); specialize (H e)
        | ?Σ; ?Γ ⊢ ?τ :: ?κ =>
            let κ' := fresh "κ'" in
            refine (forall κ', _ : Prop);
            lazymatch κ with
            | <{ *@M }> => refine (κ' = <{ *@M }> -> _ : Prop)
            | <{ *@A }> => idtac
            | <{ ?κ1 ⊔ ?κ2 }> => refine (κ1 ⊑ κ' -> κ2 ⊑ κ' -> _ : Prop)
            | _ => refine (κ ⊑ κ' -> _ : Prop)
            end;
            exact (kinding_inv Σ Γ τ κ')
        end
  end.

MetaCoq Run (tsf_ind_gen_from
               kinding "kinding_inv"
               (ltac:(tsf_ctors kinding (append "I") tsf_kinding))).

Lemma kinding_inv_complete Σ Γ τ κ :
  Σ; Γ ⊢ τ :: κ ->
  kinding_inv Σ Γ τ κ.
Proof.
  induction 1; eauto using kinding_inv, join_ub_l, join_ub_r.

  select (kinding_inv _ _ _ _) (fun H => destruct H);
    econstructor; subst; eauto using top_inv with lattice_naive_solver.
Qed.

Tactic Notation "kind_inv" hyp(H) :=
  lazymatch type of H with
  | _ ⊢ ?τ :: _ =>
      head_constructor τ;
      apply kinding_inv_complete in H;
      sinvert H
  end.

Tactic Notation "kind_inv" :=
  do_hyps (fun H => try kind_inv H).

Tactic Notation "kind_inv" "*" :=
  do_hyps (fun H => try dup_hyp H (fun H => kind_inv H)).


(** * Type inversion *)

Ltac tsf_typing ctor typing_inv :=
  lazymatch ctor with
  | TConv => tsf_skip
  | _ =>
      let H := fresh in
      pose proof ctor as H;
      repeat
        lazymatch type of H with
        | forall e : ?T, _ =>
            refine (forall e : T, _ : Prop); specialize (H e)
        | ?Σ; ?Γ ⊢ ?e : ?τ =>
            let τ' := fresh "τ'" in
            refine (forall (τ' : expr), _ : Prop);
            exact (Σ ⊢ τ' ≡ τ -> typing_inv Σ Γ e τ')
        end
  end.

MetaCoq Run (tsf_ind_gen_from
               typing "typing_inv"
               ltac:(tsf_ctors typing (append "I") tsf_typing)).


Lemma typing_inv_complete Σ Γ e τ :
  gctx_wf Σ ->
  Σ; Γ ⊢ e : τ ->
  typing_inv Σ Γ e τ.
Proof.
  intros Hwf.
  induction 1; eauto using typing_inv with equiv_naive_solver.

  (* TConv *)
  - select (typing_inv _ _ _ _) (fun H => sinvert H);
    econstructor; subst;
    eauto using (top_inv (A:=bool)) with equiv_naive_solver lattice_naive_solver.
Qed.

Tactic Notation "type_inv" hyp(H) :=
  lazymatch type of H with
  | _ ⊢ ?e : _ =>
      head_constructor e;
      apply typing_inv_complete in H;
      [ sinvert H; try ovalty_inv | assumption ]
  end.

Tactic Notation "type_inv" :=
  do_hyps (fun H => try type_inv H).

Tactic Notation "type_inv" "*" :=
  do_hyps (fun H => try dup_hyp H (fun H => type_inv H)).
