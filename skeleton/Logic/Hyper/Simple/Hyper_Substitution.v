Require Import List.
Require Import PeanoNat.
Import ListNotations.

Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Logic.Base.Simple.Base_Equiv.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.

(* ================================================================= *)
(* 1. HELPER FUNCTIONS FOR LISTS                                     *)
(* ================================================================= *)

(* Listákra (argumentumokra) való alkalmazás *)
Definition map_shift_base (d c : nat) (ts : list b_tm) : list b_tm :=
  map (shift d c) ts.

Definition map_subst_base (k : nat) (s : b_tm) (ts : list b_tm) : list b_tm :=
  map (subst k s) ts.

(* ================================================================= *)
(* 2. HYPER SHIFT (Formula Index Eltolás)                            *)
(* ================================================================= *)
(* d: mennyivel toljuk
   c: küszöb *)

Fixpoint h_shift (d : nat) (c : nat) (Phi : h_ty) : h_ty :=
  match Phi with
  (* Konstansok *)
  | Ty_Unit => Ty_Unit
  | Ty_Void => Ty_Void

  (* Konnektívumok: Rekurzív hívás *)
  | Ty_Prod A B => Ty_Prod (h_shift d c A) (h_shift d c B)
  | Ty_Sum  A B => Ty_Sum  (h_shift d c A) (h_shift d c B)
  | Ty_Arr  A B => Ty_Arr  (h_shift d c A) (h_shift d c B)

  (* Atom: A Base termeket toljuk el *)
  | Ty_Atom p ts => Ty_Atom p (map_shift_base d c ts)

  (* Kvantorok: Belépünk egy új scope-ba, ezért a küszöb nő! *)
  | Ty_All A Body => Ty_All A (h_shift d (S c) Body)
  | Ty_Ex  A Body => Ty_Ex  A (h_shift d (S c) Body)
  end.

(* ================================================================= *)
(* 3. HYPER SUBSTITUTION                                             *)
(* ================================================================= *)
(* [s / k] Phi
   k: cserélendő változó indexe
   s: behelyettesítendő Base term
   Phi: cél formula *)

Fixpoint h_subst (k : nat) (s : b_tm) (Phi : h_ty) : h_ty :=
  match Phi with
  | Ty_Unit => Ty_Unit
  | Ty_Void => Ty_Void

  | Ty_Prod A B => Ty_Prod (h_subst k s A) (h_subst k s B)
  | Ty_Sum  A B => Ty_Sum  (h_subst k s A) (h_subst k s B)
  | Ty_Arr  A B => Ty_Arr  (h_subst k s A) (h_subst k s B)

  (* Atom: A Base termekben cserélünk *)
  | Ty_Atom p ts => Ty_Atom p (map_subst_base k s ts)

  (* Kvantorok: A behelyettesítendő termet el kell tolni (lift),
     mert egy új változó (a kvantor változója) került a verem tetejére.
     A cserélendő index (k) is eggyel nő a scope miatt. *)
  | Ty_All A Body =>
      Ty_All A (h_subst (S k) (shift 1 0 s) Body)

  | Ty_Ex A Body =>
      Ty_Ex  A (h_subst (S k) (shift 1 0 s) Body)
  end.