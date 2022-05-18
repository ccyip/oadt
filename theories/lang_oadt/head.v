(** The notion of expression head can simplify and scale down certain proofs. *)
From oadt.lang_oadt Require Import base syntax.
Import syntax.notations.

(* TODO: automate this with [idt] module. *)

Variant expr_head :=
| HBVar
| HFVar
| HGVar
| HPi
| HAbs
| HApp
| HTApp
| HLet
| HUnitT
| HUnitV
| HBool (l : olabel)
| HLit
| HSec
| HIte (l : olabel)
| HProd (l : olabel)
| HPair (l : olabel)
| HProj (l : olabel)
| HSum (l : olabel)
| HInj (l : olabel)
| HCase (l : olabel)
| HFold
| HUnfold
| HTape
| HMux
| HBoxedLit
| HBoxedInj
.

Definition expr_hd (e : expr) : expr_head :=
  match e with
  | EBVar _ => HBVar
  | EFVar _ => HFVar
  | EGVar _ => HGVar
  | EPi _ _ _ => HPi
  | EAbs _ _ _ => HAbs
  | EApp _ _ => HApp
  | ETApp _ _ => HTApp
  | ELet _ _ => HLet
  | EUnitT => HUnitT
  | EUnitV => HUnitV
  | EBool l => HBool l
  | ELit _ => HLit
  | ESec _ => HSec
  | EIte l _ _ _ => HIte l
  | EProd l _ _ => HProd l
  | EPair l _ _ => HPair l
  | EProj l _ _ => HProj l
  | ESum l _ _ => HSum l
  | EInj l _ _ _ => HInj l
  | ECase l _ _ _ => HCase l
  | EFold _ _ => HFold
  | EUnfold _ _ => HUnfold
  | ETape _ => HTape
  | EMux _ _ _ => HMux
  | EBoxedLit _ => HBoxedLit
  | EBoxedInj _ _ _ => HBoxedInj
  end.

Lemma expr_hd_inv t h :
  expr_hd t = h ->
  match h with
  | HBVar => exists k, t = EBVar k
  | HFVar => exists x, t = EFVar x
  | HGVar => exists x, t = EGVar x
  | HPi => exists l τ1 τ2, t = EPi l τ1 τ2
  | HAbs => exists l τ e, t = EAbs l τ e
  | HApp => exists e1 e2, t = EApp e1 e2
  | HTApp => exists X e, t = ETApp X e
  | HLet => exists e1 e2, t = ELet e1 e2
  | HUnitT => t = EUnitT
  | HUnitV => t = EUnitV
  | HBool l => t = EBool l
  | HLit => exists b, t = ELit b
  | HSec => exists e, t = ESec e
  | HIte l => exists e0 e1 e2, t = EIte l e0 e1 e2
  | HProd l => exists τ1 τ2, t = EProd l τ1 τ2
  | HPair l => exists e1 e2, t = EPair l e1 e2
  | HProj l => exists b e, t = EProj l b e
  | HSum l => exists τ1 τ2, t = ESum l τ1 τ2
  | HInj l => exists b τ e, t = EInj l b τ e
  | HCase l => exists e0 e1 e2, t = ECase l e0 e1 e2
  | HFold => exists X e, t = EFold X e
  | HUnfold => exists X e, t = EUnfold X e
  | HTape => exists e, t = ETape e
  | HMux => exists e0 e1 e2, t = EMux e0 e1 e2
  | HBoxedLit => exists b, t = EBoxedLit b
  | HBoxedInj => exists b τ e, t = EBoxedInj b τ e
  end.
Proof.
  destruct t; intros; subst; simpl; eauto.
Qed.

Tactic Notation "expr_hd_inv" "in" hyp(H) :=
  simpl in H; apply expr_hd_inv in H; try simp_hyp H; subst.

Ltac expr_hd_inv :=
  select (expr_hd _ = _) (fun H => expr_hd_inv in H).

Lemma open_hd e k s e' :
  <{ {k~>s}e }> = e' ->
  expr_hd e = expr_hd e' \/ (e = <{ bvar k }> /\ s = e').
Proof.
  edestruct e; intros; simplify_eq; simpl; eauto.
  case_decide; simplify_eq; simpl; eauto.
Qed.

Ltac apply_open_hd :=
  let go H :=
    (apply open_hd in H; simpl in H;
     let H' := fresh in
     destruct H as [ H' | [??] ];
     [ expr_hd_inv in H'
     | subst ])
  in
  match goal with
  | H : <{ {_~>_}_ }> = _ |- _ => go H
  | H : _ = <{ {_~>_}_ }> |- _ => symmetry in H; go H
  end.
