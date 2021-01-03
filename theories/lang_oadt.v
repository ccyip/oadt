From oadt Require Import base.

Module oadt.

Section lang.

  (* TODO: module type and parameters may be a better way to parameterize [name]
  and [nmap]. *)

  (** [name] is the type for names, with decidable equality. *)
  Context {name : Set} `{EqDecision name}.

  (** [nmap A] is a finite, partial map from [name] to [A]. *)
  Context {nmap : Type -> Type} `{FinMap name nmap}.

  (** * Syntax *)

  (** ** Expressions *)
  Inductive expr :=
  | EUnitT
  | EBool
  | EOBool
  | EProd (τ1 τ2 : expr)
  | ESum (τ1 τ2 : expr)
  | EOSum (τ1 τ2 : expr)
  | EPi (x : name) (τ1 τ2: expr)
  | EVar (x : name)
  | EApp (e1 e2 : expr)
  | EUnitV
  | ELit (b : bool)
  | ESec (e : expr)
  | ERet (e : expr)
  | EIte (e0 e1 e2 : expr)
  | EMux (e0 e1 e2 : expr)
  | EPair (e1 e2 : expr)
  | ELetP (x y : name) (e1 e2 : expr)
  | EInj (b : bool) (τ e : expr)
  | ECase (e0 : expr) (x1 : name) (e1 : expr) (x2 : name) (e2 : expr)
  | EOInj (b : bool) (τ e : expr)
  | EOCase (e0 : expr) (x1 : name) (e1 : expr) (x2 : name) (e2 : expr)
  | EAbs (x : name) (τ e : expr)
  | ELet (x : name) (e1 e2 : expr)
  | EFold (X : name) (e : expr)
  | EUnfold (X : name) (e : expr)
  (** Runtime expressions *)
  | EBoxedLit (b : bool)
  | EBoxedOInj (b : bool) (τ e : expr)
  .

  (** ** GLobal named definitions *)
  Variant gdef :=
  | DADT (X : name) (e : expr)
  | DOADT (Y : name) (x : name) (τ e : expr)
  | DFun (x : name) (τ e : expr)
  .

  (** ** Programs *)
  (* TODO: may define [program] as [list gdef * expr]. *)
  Definition program := list gdef.

  (** ** Notations *)
  (* Adapted from Software Foundations. *)
  Coercion ELit : bool >-> expr.
  Coercion EVar : name >-> expr.

  (* TODO: allow them to be used outside of this section. *)
  Declare Scope oadt_scope.
  Delimit Scope oadt_scope with oadt.
  Declare Custom Entry oadt.
  Notation "<{ e }>" := e (e custom oadt at level 99).
  Notation "( x )" := x (in custom oadt, x at level 99).
  Notation "x" := x (in custom oadt at level 0, x constr at level 0).
  Notation "'𝟙'" := EUnitT (in custom oadt at level 0).
  Notation "'Unit'" := EUnitT (in custom oadt at level 0).
  Notation "'𝔹'" := EBool (in custom oadt at level 0).
  Notation "'Bool'" := EBool (in custom oadt at level 0).
  Notation "'~𝔹'" := EOBool (in custom oadt at level 0).
  Notation "'~Bool'" := EOBool (in custom oadt at level 0).
  Notation "t1 * t2" := (EProd t1 t2) (in custom oadt at level 2,
                                          t1 custom oadt,
                                          t2 custom oadt at level 0).
  Notation "t1 + t2" := (ESum t1 t2) (in custom oadt at level 3,
                                         left associativity).
  Notation "t1 ~+ t2" := (EOSum t1 t2) (in custom oadt at level 3,
                                           left associativity).
  Notation "'Π' x : t1 , t2" := (EPi x t1 t2) (in custom oadt at level 50,
                                                  right associativity).
  Notation "e1 e2" := (EApp e1 e2) (in custom oadt at level 1, left associativity).
  Notation "()" := EUnitV (in custom oadt at level 0).
  Notation "( x , y , .. , z )" := (EPair .. (EPair x y) .. z)
                                     (in custom oadt at level 0,
                                         x custom oadt at level 99,
                                         y custom oadt at level 99,
                                         z custom oadt at level 99).
  Notation "'s𝔹' e" := (ESec e) (in custom oadt at level 0,
                                    e custom oadt at level 0).
  Notation "'r𝔹' e" := (ERet e) (in custom oadt at level 0,
                                    e custom oadt at level 0).
  Notation "'if' e0 'then' e1 'else' e2" := (EIte e0 e1 e2)
                                              (in custom oadt at level 89,
                                                  e0 custom oadt at level 99,
                                                  e1 custom oadt at level 99,
                                                  e2 custom oadt at level 99,
                                                  left associativity).
  Notation "'mux' e0 e1 e2" := (EMux e0 e1 e2) (in custom oadt at level 0,
                                                   e0 custom oadt at level 0,
                                                   e1 custom oadt at level 0,
                                                   e2 custom oadt at level 0).
  Notation "'let' ( x , y ) '=' e1 'in' e2" := (ELetP x y e1 e2)
                                                 (in custom oadt at level 0,
                                                     x custom oadt at level 99,
                                                     y custom oadt at level 99,
                                                     e1 custom oadt at level 99,
                                                     e2 custom oadt at level 99).
  Notation "'let' x '=' e1 'in' e2" := (ELet x e1 e2)
                                         (in custom oadt at level 0,
                                             x custom oadt at level 99,
                                             e1 custom oadt at level 99,
                                             e2 custom oadt at level 99).
  Notation "'inj@' b < t > e" := (EInj b t e) (in custom oadt at level 0,
                                                  b custom oadt at level 0,
                                                  t custom oadt at level 0,
                                                  e custom oadt at level 0).
  Notation "'inl' < t > e" := (EInj true t e) (in custom oadt at level 0,
                                                  t custom oadt at level 0,
                                                  e custom oadt at level 0).
  Notation "'inr' < t > e" := (EInj false t e) (in custom oadt at level 0,
                                                   t custom oadt at level 0,
                                                   e custom oadt at level 0).
  Notation "'~inj@' b < t > e" := (EOInj b t e) (in custom oadt at level 0,
                                                    b custom oadt at level 0,
                                                    t custom oadt at level 0,
                                                    e custom oadt at level 0).
  Notation "'~inl' < t > e" := (EOInj true t e) (in custom oadt at level 0,
                                                    t custom oadt at level 0,
                                                    e custom oadt at level 0).
  Notation "'~inr' < t > e" := (EOInj false t e) (in custom oadt at level 0,
                                                     t custom oadt at level 0,
                                                     e custom oadt at level 0).
  Notation "'case' e0 'of' x '=>' e1 '|' y '=>' e2" :=
    (ECase e0 x e1 y e2) (in custom oadt at level 89,
                             e0 custom oadt at level 99,
                             x custom oadt at level 99,
                             e1 custom oadt at level 99,
                             y custom oadt at level 99,
                             e2 custom oadt at level 99,
                             left associativity).
  Notation "'~case' e0 'of' x '=>' e1 '|' y '=>' e2" :=
    (EOCase e0 x e1 y e2) (in custom oadt at level 89,
                              e0 custom oadt at level 99,
                              x custom oadt at level 99,
                              e1 custom oadt at level 99,
                              y custom oadt at level 99,
                              e2 custom oadt at level 99,
                              left associativity).
  Notation "\ x : t '=>' e" := (EAbs x t e) (in custom oadt at level 90,
                                                x custom oadt at level 99,
                                                t custom oadt at level 99,
                                                e custom oadt at level 99,
                                                left associativity).
  Notation "'fold' < X > e" := (EFold X e) (in custom oadt at level 0,
                                               X custom oadt at level 0,
                                               e custom oadt at level 0).
  Notation "'unfold' < X > e" := (EUnfold X e) (in custom oadt at level 0,
                                                   X custom oadt at level 0,
                                                   e custom oadt at level 0).
  Notation "[ b ]" := (EBoxedLit b) (in custom oadt at level 0,
                                        b custom oadt at level 0).
  Notation "[ '~inj@' b < t > e ]" := (EBoxedOInj b t e)
                                        (in custom oadt at level 0,
                                            b custom oadt at level 0,
                                            t custom oadt at level 0,
                                            e custom oadt at level 0).
  Notation "[ '~inl' < t > e ]" := (EBoxedOInj true t e)
                                     (in custom oadt at level 0,
                                         t custom oadt at level 0,
                                         e custom oadt at level 0).
  Notation "[ '~inr' < t > e ]" := (EBoxedOInj false t e)
                                     (in custom oadt at level 0,
                                         t custom oadt at level 0,
                                         e custom oadt at level 0).
  Notation "'data' X := e" := (DADT X e) (in custom oadt at level 0,
                                             X custom oadt at level 0,
                                             e custom oadt at level 0).
  Notation "'obliv' X [ x : t ] := e" := (DOADT X x t e)
                                           (in custom oadt at level 0,
                                               X custom oadt at level 0,
                                               x custom oadt at level 0,
                                               t custom oadt at level 0,
                                               e custom oadt at level 0).
  Notation "'def' x : t := e" := (DFun x t e) (in custom oadt at level 0,
                                                  x custom oadt at level 0,
                                                  t custom oadt at level 0,
                                                  e custom oadt at level 0).


End lang.

End oadt.
