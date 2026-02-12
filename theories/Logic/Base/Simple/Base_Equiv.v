Require Import List.  
Require Import PeanoNat.
Import ListNotations.

Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Logic.Base.Simple.Base_Typing.

(* ================================================================= *)
(* 1. SHIFTING & SUBSTITUTION                                        *)
(* ================================================================= *)
(* Bár a Simple Base-ben nincs lambda (binder), a változók indexelése 
   miatt szükség van az eltolásra és helyettesítésre a Fibrációhoz. *)

(* d: mennyivel toljuk el
   c: küszöb (honnan kezdve toljuk) *)
Fixpoint shift (d : nat) (c : nat) (t : b_tm) : b_tm :=
  match t with
  | b_var k => if k <? c then b_var k else b_var (k + d)
  | b_unit => b_unit
  | b_pair t1 t2 => b_pair (shift d c t1) (shift d c t2)
  | b_fst t => b_fst (shift d c t)
  | b_snd t => b_snd (shift d c t)
  end.

(* Helyettesítés: [t/k] a 'target'-ben
   k: a helyettesítendő változó indexe
   s: a term, amit behelyettesítünk
   target: a term, amiben cserélünk *)
Fixpoint subst (k : nat) (s : b_tm) (target : b_tm) : b_tm :=
  match target with
  | b_var v => 
      if v =? k then s 
      else (if v <? k then b_var v else b_var (pred v))
  | b_unit => b_unit
  | b_pair t1 t2 => b_pair (subst k s t1) (subst k s t2)
  | b_fst t => b_fst (subst k s t)
  | b_snd t => b_snd (subst k s t)
  end.

(* ================================================================= *)
(* 2. EQUIVALENCE RELATION                                           *)
(* ================================================================= *)
(* Ez definiálja a Cartesian Category törvényeit szintaktikusan *)

Inductive base_equiv (G : b_context) : b_tm -> b_tm -> b_ty -> Prop :=
  
  (* --- Equivalence Properties --- *)
  | BE_Refl : forall t A,
      base_typing G t A ->
      base_equiv G t t A
      
  | BE_Sym : forall t1 t2 A,
      base_equiv G t1 t2 A ->
      base_equiv G t2 t1 A
      
  | BE_Trans : forall t1 t2 t3 A,
      base_equiv G t1 t2 A ->
      base_equiv G t2 t3 A ->
      base_equiv G t1 t3 A

  (* --- Congruence Rules --- *)
  | BE_Pair : forall t1 t1' t2 t2' A B,
      base_equiv G t1 t1' A ->
      base_equiv G t2 t2' B ->
      base_equiv G (b_pair t1 t2) (b_pair t1' t2') (b_Prod A B)
      
  | BE_Fst : forall t t' A B,
      base_equiv G t t' (b_Prod A B) ->
      base_equiv G (b_fst t) (b_fst t') A
      
  | BE_Snd : forall t t' A B,
      base_equiv G t t' (b_Prod A B) ->
      base_equiv G (b_snd t) (b_snd t') B

  (* --- Computation Rules (Beta) --- *)
  (* fst (pair a b) ~ a *)
  | BE_BetaFst : forall t1 t2 A B,
      base_typing G t1 A ->
      base_typing G t2 B ->
      base_equiv G (b_fst (b_pair t1 t2)) t1 A

  (* snd (pair a b) ~ b *)
  | BE_BetaSnd : forall t1 t2 A B,
      base_typing G t1 A ->
      base_typing G t2 B ->
      base_equiv G (b_snd (b_pair t1 t2)) t2 B

  (* --- Uniqueness Rules (Eta) --- *)
  
  (* Surjective Pairing: pair (fst t) (snd t) ~ t *)
  | BE_EtaProd : forall t A B,
      base_typing G t (b_Prod A B) ->
      base_equiv G (b_pair (b_fst t) (b_snd t)) t (b_Prod A B)

  (* Terminal Object Uniqueness: minden Unit típusú term egyenlő *)
  | BE_EtaUnit : forall t,
      base_typing G t b_Unit ->
      base_equiv G t b_unit b_Unit.