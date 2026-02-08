Require Import List Arith PeanoNat.
Import ListNotations.

(* --- TYPES --- *)
Inductive b_ty : Set :=
  | b_Unit : b_ty
  | b_S    : b_ty.

Definition b_context := list b_ty.

(* --- TERMS (NO CONSTANTS!) --- *)
Inductive b_tm : Set :=
  | b_var  : nat -> b_tm
  | b_unit : b_tm.

(* --- LIFT & SUBST --- *)
Definition b_lift (n : nat) (k : nat) (t : b_tm) : b_tm :=
  match t with
  | b_var i => if k <=? i then b_var (n + i) else b_var i
  | b_unit  => b_unit
  end.

Definition b_subst (k : nat) (s : b_tm) (t : b_tm) : b_tm :=
  match t with
  | b_var i => if k =? i then s else if k <? i then b_var (i - 1) else b_var i
  | b_unit  => b_unit
  end.

(* --- TYPING --- *)
Inductive b_typing : b_context -> b_tm -> b_ty -> Prop :=
  | BT_Var0 : forall G A, b_typing (A :: G) (b_var 0) A
  | BT_VarS : forall G A B i, b_typing G (b_var i) A -> b_typing (B :: G) (b_var (S i)) A
  | BT_Unit : forall G, b_typing G b_unit b_Unit.