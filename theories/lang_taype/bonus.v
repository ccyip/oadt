From taype.lang_taype Require Import
     base syntax semantics typing infrastructure
     inversion equivalence weakening progress.
Import syntax.notations semantics.notations typing.notations equivalence.notations.

Section fix_gctx.

Context (Σ : gctx).
Context (Hwf : gctx_wf Σ).

#[local]
Set Default Proof Using "Hwf".

Lemma pared_equiv_public_bool_eq Γ τ κ :
  Γ ⊢ τ :: κ ->
  τ ≡ <{ 𝔹 }> ->
  τ = <{ 𝔹 }>.
Proof.
  induction 1; intros; try simpl_whnf_equiv;
    try apply_gctx_wf; eauto;
    (exfalso;
     select (_ ≡ _) (fun H => eapply pared_equiv_obliv_preservation in H); eauto;
     [ kind_inv; easy | .. ]; econstructor; eauto).
Qed.

Lemma pared_equiv_public_ADT_eq Γ τ κ κ' X :
  Γ ⊢ τ :: κ ->
  Γ ⊢ gvar X :: κ' ->
  τ ≡ <{ gvar X }> ->
  τ = <{ gvar X }>.
Proof.
  intros H. intro. kind_inv.
  induction H; intros; try simpl_whnf_equiv;
    try simplify_map_eq;
    try apply_gctx_wf; eauto;
    (exfalso;
     select (_ ≡ _) (fun H => eapply pared_equiv_obliv_preservation in H); eauto;
     [ kind_inv; easy | .. ]; econstructor; eauto).
Qed.

Lemma pared_equiv_public_prod_eq Γ τ κ κ' τ1 τ2 :
  Γ ⊢ τ :: κ ->
  Γ ⊢ τ1 * τ2 :: κ' ->
  τ ≡ <{ τ1 * τ2 }> ->
  exists τ1' τ2', τ = <{ τ1' * τ2' }> /\ τ1 ≡ τ1' /\ τ2 ≡ τ2'.
Proof.
  induction 1; intros; try simpl_whnf_equiv;
    try apply_gctx_wf; eauto;
    try solve
      [ exfalso;
        select (_ ≡ _)
          (fun H => eapply pared_equiv_obliv_preservation in H);
        eauto;
        [ kind_inv; easy | .. ]; econstructor; eauto].

  eauto with equiv_naive_solver.
Qed.

End fix_gctx.
