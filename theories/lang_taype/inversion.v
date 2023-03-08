(** Typing and kinding inversion lemmas. *)
From idt Require Import all.
From taype.lang_taype Require Import
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

Module kernel.

Section fix_gctx.

Context (Σ : gctx).

(** [TIte] and [TCase] require special rules. *)
Inductive typing_inv : tctx -> expr -> llabel -> expr -> Prop :=
| ITIte Γ l0 l e0 e1 e2 τ :
    Γ ⊢ e0 :{l0} 𝔹 ->
    Γ ⊢ e1 :{l} τ^(lit true) ->
    Γ ⊢ e2 :{l} τ^(lit false) ->
    l0 ⊑ l ->
    forall τ',
      τ' ≡ <{ τ^e0 }> ->
      typing_inv Γ <{ if e0 then e1 else e2 }> l τ'
| ITCase Γ l0 l e0 e1 e2 τ1 τ2 τ κ L1 L2 :
    Γ ⊢ e0 :{l0} τ1 + τ2 ->
    (forall x, x ∉ L1 -> Σ; <[x:=(l0, τ1)]>Γ ⊢ e1^x :{l} τ^(inl<τ1 + τ2> x)) ->
    (forall x, x ∉ L2 -> Σ; <[x:=(l0, τ2)]>Γ ⊢ e2^x :{l} τ^(inr<τ1 + τ2> x)) ->
    Γ ⊢ τ^e0 :: κ ->
    l0 ⊑ l ->
    forall τ',
      τ' ≡ <{ τ^e0 }> ->
      typing_inv Γ <{ case e0 of e1 | e2 }> l τ'
.

End fix_gctx.

End kernel.

Ltac tsf_typing ctor typing_inv :=
  lazymatch ctor with
  (* Remove the cases about [TIte] and [TCase]. *)
  | TIte => tsf_skip | TIteNoDep => tsf_skip
  | TCase => tsf_skip | TCaseNoDep => tsf_skip
  | TConv => tsf_skip
  | _ =>
      let H := fresh in
      pose proof ctor as H;
      repeat
        lazymatch type of H with
        | forall e : ?T, _ =>
            refine (forall e : T, _ : Prop); specialize (H e)
        | ?Σ; ?Γ ⊢ ?e :{?l} ?τ =>
            let τ' := fresh "τ'" in
            refine (forall (τ' : expr), _ : Prop);
            exact (Σ ⊢ τ' ≡ τ -> typing_inv Σ Γ e l τ')
        end
  end.

MetaCoq Run (tsf_ind_gen_from
               typing "typing_inv"
               (ltac:(tsf_ctors typing (append "I") tsf_typing) ++
                ltac:(tsf_ctors_id kernel.typing_inv))).


Lemma typing_inv_complete Σ Γ e l τ :
  gctx_wf Σ ->
  Σ; Γ ⊢ e :{l} τ ->
  typing_inv Σ Γ e l τ.
Proof.
  intros Hwf.
  induction 1; eauto using typing_inv with equiv_naive_solver.

  (* TIte *)
  - econstructor; eauto;
    lazymatch goal with
    | H : _ ⊢ _ : ?τ |- _ =>
        rewrite (open_lc_intro τ) by eauto using typing_type_lc
    end; eauto with equiv_naive_solver.

  (* TCase *)
  - econstructor; eauto; intros;
    lazymatch goal with
    | H : _ ⊢ ?τ :: _ |- _ =>
        rewrite (open_lc_intro τ) by eauto using kinding_lc
    end; eauto with equiv_naive_solver.

  (* TConv *)
  - select (typing_inv _ _ _ _ _) (fun H => sinvert H);
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
