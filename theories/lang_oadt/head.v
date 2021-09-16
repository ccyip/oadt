(** The notion of expression head can simplify and scale down certain proofs. *)
From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.

Variant expr_head :=
| HBVar (k : nat)
| HFVar (x : atom)
| HGVar (x : atom)
| HPi (l : llabel)
| HAbs (l : llabel)
| HApp
| HTApp (X : atom)
| HLet
| HUnitT
| HUnitV
| HBool (l : olabel)
| HLit (b : bool)
| HSec
| HIte (l : olabel)
| HProd
| HPair
| HProj (b : bool)
| HSum (l : olabel)
| HInj (l : olabel) (b : bool)
| HCase (l : olabel)
| HFold (X : atom)
| HUnfold (X : atom)
| HTape
| HMux
| HBoxedLit (b : bool)
| HBoxedInj (b : bool)
.

Definition expr_hd (e : expr) : expr_head :=
  match e with
  | EBVar k => HBVar k
  | EFVar x => HFVar x
  | EGVar x => HGVar x
  | EPi l _ _ => HPi l
  | EAbs l _ _ => HAbs l
  | EApp _ _ => HApp
  | ETApp X _ => HTApp X
  | ELet _ _ => HLet
  | EUnitT => HUnitT
  | EUnitV => HUnitV
  | EBool l => HBool l
  | ELit b => HLit b
  | ESec _ => HSec
  | EIte l _ _ _ => HIte l
  | EProd _ _ => HProd
  | EPair _ _ => HPair
  | EProj b _ => HProj b
  | ESum l _ _ => HSum l
  | EInj l b _ _ => HInj l b
  | ECase l _ _ _ => HCase l
  | EFold X _ => HFold X
  | EUnfold X _ => HUnfold X
  | ETape _ => HTape
  | EMux _ _ _ => HMux
  | EBoxedLit b => HBoxedLit b
  | EBoxedInj b _ _ => HBoxedInj b
  end.

Lemma expr_hd_inv t h :
  expr_hd t = h ->
  match h with
  | HBVar k => t = EBVar k
  | HFVar x => t = EFVar x
  | HGVar x => t = EGVar x
  | HPi l => exists τ1 τ2, t = EPi l τ1 τ2
  | HAbs l => exists τ e, t = EAbs l τ e
  | HApp => exists e1 e2, t = EApp e1 e2
  | HTApp X => exists e, t = ETApp X e
  | HLet => exists e1 e2, t = ELet e1 e2
  | HUnitT => t = EUnitT
  | HUnitV => t = EUnitV
  | HBool l => t = EBool l
  | HLit b => t = ELit b
  | HSec => exists e, t = ESec e
  | HIte l => exists e0 e1 e2, t = EIte l e0 e1 e2
  | HProd => exists τ1 τ2, t = EProd τ1 τ2
  | HPair => exists e1 e2, t = EPair e1 e2
  | HProj b => exists e, t = EProj b e
  | HSum l => exists τ1 τ2, t = ESum l τ1 τ2
  | HInj l b => exists τ e, t = EInj l b τ e
  | HCase l => exists e0 e1 e2, t = ECase l e0 e1 e2
  | HFold X => exists e, t = EFold X e
  | HUnfold X => exists e, t = EUnfold X e
  | HTape => exists e, t = ETape e
  | HMux => exists e0 e1 e2, t = EMux e0 e1 e2
  | HBoxedLit b => t = EBoxedLit b
  | HBoxedInj b => exists τ e, t = EBoxedInj b τ e
  end.
Proof.
  destruct t; intros; subst; simpl; eauto.
Qed.

Tactic Notation "expr_hd_inv" "in" hyp(H) :=
  simpl in H; apply expr_hd_inv in H; try simp_hyp H; subst.

Ltac expr_hd_inv :=
  select (expr_hd _ = _) (fun H => expr_hd_inv in H).
