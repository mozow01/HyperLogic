Require Import List Arith PeanoNat.
Import ListNotations.

(* ================================================================= *)
(* 1. ALAPTÍPUSOK (BASE TYPES)                                       *)
(* ================================================================= *)

(* A Bázisban most már háromféle típus van: Unit, Individuum és Szorzat. *)
Inductive b_ty : Set := 
  | b_Unit : b_ty                   (* 1 *)
  | b_S    : b_ty                   (* S (Individuum) *)
  | b_Prod : b_ty -> b_ty -> b_ty.  (* A x B (Szorzat - EZ AZ ÚJ!) *)

Definition b_context := list b_ty.

(* ================================================================= *)
(* 2. KÖLCSÖNÖS SZINTAXIS (MUTUAL INDUCTIVE SYNTAX)                  *)
(* ================================================================= *)

(* Itt történik a varázslat: a Termek és a Logikai Típusok (Formulák)
   egymásra hivatkoznak. *)

Inductive b_tm : Set :=
  (* --- Standard de Bruijn változók és konstansok --- *)
  | b_var     : nat -> b_tm
  | b_const   : nat -> b_tm
  | b_unit    : b_tm

  (* --- Párok (Szükséges a Karteziánus Bázis modellhez) --- *)
  | b_pair    : b_tm -> b_tm -> b_tm
  | b_fst     : b_tm -> b_tm
  | b_snd     : b_tm -> b_tm

  (* --- AZ EPSZILON OPERÁTOR --- *)
  (* Egy term, ami egy 'A' formulától függ: epsilon x. A *)
  | b_epsilon : h_ty -> b_tm

with h_ty : Set :=
  (* --- Logikai Típusok / Formulák --- *)
  | Ty_Unit : h_ty
  | Ty_Arr  : h_ty -> h_ty -> h_ty
  | Ty_Prod : h_ty -> h_ty -> h_ty

  (* --- ATOMI FORMULÁK (RELÁCIÓK) --- *)
  (* Egy p-edik reláció, ami termek listájától függ: R(t1, t2...) *)
  | Ty_Atom : nat -> list b_tm -> h_ty.

Definition h_context := list h_ty.

(* ================================================================= *)
(* 3. INDUKCIÓS SÉMÁK (SCHEMES)                                      *)
(* ================================================================= *)

(* Mivel a definíció kölcsönös (és listát tartalmaz), a Coq alap 
   indukciója túl gyenge. Generálunk egy erőset. *)

Scheme b_tm_mut := Induction for b_tm Sort Prop
  with h_ty_mut := Induction for h_ty Sort Prop.

Combined Scheme syntax_mut_ind from b_tm_mut, h_ty_mut.

(* ================================================================= *)
(* 4. LIFTELÉS (LIFTING)                                             *)
(* ================================================================= *)

(* De Bruijn indexek eltolása, ha új hatókörbe lépünk. *)

Fixpoint b_lift_tm (n : nat) (k : nat) (t : b_tm) : b_tm :=
  match t with
  | b_var i => if k <=? i then b_var (n + i) else b_var i
  | b_const c => b_const c
  | b_unit => b_unit
  
  (* Párok rekurziója *)
  | b_pair t1 t2 => b_pair (b_lift_tm n k t1) (b_lift_tm n k t2)
  | b_fst t1 => b_fst (b_lift_tm n k t1)
  | b_snd t1 => b_snd (b_lift_tm n k t1)

  (* Epszilon rekurzió: bemegyünk a típusba! *)
  | b_epsilon A => b_epsilon (b_lift_ty n k A)
  end

with b_lift_ty (n : nat) (k : nat) (A : h_ty) : h_ty :=
  match A with
  | Ty_Unit => Ty_Unit
  | Ty_Arr A1 A2  => Ty_Arr (b_lift_ty n k A1) (b_lift_ty n k A2)
  | Ty_Prod A1 A2 => Ty_Prod (b_lift_ty n k A1) (b_lift_ty n k A2)
  
  (* Atom rekurzió: bemegyünk a termek listájába! *)
  | Ty_Atom p args => Ty_Atom p (map (b_lift_tm n k) args)
  end.

(* ================================================================= *)
(* 5. HELYETTESÍTÉS (SUBSTITUTION)                                   *)
(* ================================================================= *)

(* [s/k]t művelet: a k-adik változó helyére s-t írunk t-ben. *)

Fixpoint b_subst_tm (k : nat) (s : b_tm) (t : b_tm) : b_tm :=
  match t with
  | b_var i => 
      if k =? i then s 
      else if k <? i then b_var (i - 1) 
      else b_var i
  | b_const c => b_const c
  | b_unit => b_unit
  
  | b_pair t1 t2 => b_pair (b_subst_tm k s t1) (b_subst_tm k s t2)
  | b_fst t1 => b_fst (b_subst_tm k s t1)
  | b_snd t1 => b_snd (b_subst_tm k s t1)

  (* Epszilon: Csak bemegyünk, NINCS logikai kiértékelés! *)
  | b_epsilon A => b_epsilon (b_subst_ty k s A)
  end

with b_subst_ty (k : nat) (s : b_tm) (A : h_ty) : h_ty :=
  match A with
  | Ty_Unit => Ty_Unit
  | Ty_Arr A1 A2  => Ty_Arr (b_subst_ty k s A1) (b_subst_ty k s A2)
  | Ty_Prod A1 A2 => Ty_Prod (b_subst_ty k s A1) (b_subst_ty k s A2)
  
  (* Atom: minden argumentumon végrehajtjuk a helyettesítést *)
  | Ty_Atom p args => Ty_Atom p (map (b_subst_tm k s) args)
  end.