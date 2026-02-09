Require Import List Arith PeanoNat.
Import ListNotations.

(* ================================================================= *)
(* 0. SZIMBÓLUMOK (A "Konkrét" Nyelv Szavai)                         *)
(* ================================================================= *)

(* Itt soroljuk fel, milyen konstansaink vannak *)
Inductive ConstSym : Set :=
  | C_Zero  : ConstSym    (* 0 *)
  | C_One   : ConstSym.   (* 1 *)

(* Itt soroljuk fel, milyen függvényeink vannak *)
Inductive FunSym : Set :=
  | F_Plus  : FunSym      (* + *)
  | F_Mult  : FunSym.     (* * *)

(* ================================================================= *)
(* 1. ALAPTÍPUSOK (BASE TYPES)                                       *)
(* ================================================================= *)

Inductive b_ty : Set := 
  | b_Unit : b_ty                   (* 1 (Unit objektum) *)
  | b_S    : b_ty                   (* S (Individuum objektum) *)
  | b_Prod : b_ty -> b_ty -> b_ty.  (* A x B (Szorzat) *)

Definition b_context := list b_ty.

(* ================================================================= *)
(* 2. KÖLCSÖNÖS SZINTAXIS (MUTUAL INDUCTIVE SYNTAX)                  *)
(* ================================================================= *)

(* A Termek (b_tm) és Formulák (h_ty) egymásra épülnek. *)

Inductive b_tm : Set :=
  (* --- Változók --- *)
  | b_var     : nat -> b_tm

  (* --- Konstansok és Unit --- *)
  | b_const   : ConstSym -> b_tm      (* c : 1 -> A *)
  | b_unit    : b_tm                  (* () : 1 *)

  (* --- Karteziánus (Pár) Struktúra --- *)
  | b_pair    : b_tm -> b_tm -> b_tm  (* <t1, t2> *)
  | b_fst     : b_tm -> b_tm          (* pi1 *)
  | b_snd     : b_tm -> b_tm          (* pi2 *)

  (* --- Függvényalkalmazás (Function Application) --- *)
  (* f(t) : B (ahol t lehet egy pár is, pl. <x,y>) *)
  | b_fun     : FunSym -> b_tm -> b_tm

  (* --- EPSZILON (A Logikából a Bázisba) --- *)
  (* epsilon x. A *)
  | b_epsilon : h_ty -> b_tm

with h_ty : Set :=
  (* --- Logikai Típusok / Formulák --- *)
  | Ty_Unit : h_ty                       (* Igaz/Top *)
  | Ty_Arr  : h_ty -> h_ty -> h_ty       (* Implikáció *)
  | Ty_Prod : h_ty -> h_ty -> h_ty       (* Konjunkció *)

  (* --- Atomi Formulák (Predikátumok) --- *)
  (* P(t1, t2...) - Itt most egyszerűsítve csak sorszámmal és termlistával *)
  | Ty_Atom : nat -> list b_tm -> h_ty.

Definition h_context := list h_ty.

(* ================================================================= *)
(* 3. INDUKCIÓS SÉMÁK                                                *)
(* ================================================================= *)

Scheme b_tm_mut := Induction for b_tm Sort Prop
  with h_ty_mut := Induction for h_ty Sort Prop.

Combined Scheme syntax_mut_ind from b_tm_mut, h_ty_mut.

(* ================================================================= *)
(* 4. LIFTELÉS (LIFTING)                                             *)
(* ================================================================= *)

Fixpoint b_lift_tm (n : nat) (k : nat) (t : b_tm) : b_tm :=
  match t with
  | b_var i => if k <=? i then b_var (n + i) else b_var i
  | b_const c => b_const c
  | b_unit => b_unit
  
  | b_pair t1 t2 => b_pair (b_lift_tm n k t1) (b_lift_tm n k t2)
  | b_fst t1 => b_fst (b_lift_tm n k t1)
  | b_snd t1 => b_snd (b_lift_tm n k t1)

  (* Függvény: Csak az argumentumot kell liftelni, a jelet (f) nem *)
  | b_fun f t => b_fun f (b_lift_tm n k t)

  (* Epszilon: belépünk a formulába *)
  | b_epsilon A => b_epsilon (b_lift_ty n k A)
  end

with b_lift_ty (n : nat) (k : nat) (A : h_ty) : h_ty :=
  match A with
  | Ty_Unit => Ty_Unit
  | Ty_Arr A1 A2  => Ty_Arr (b_lift_ty n k A1) (b_lift_ty n k A2)
  | Ty_Prod A1 A2 => Ty_Prod (b_lift_ty n k A1) (b_lift_ty n k A2)
  | Ty_Atom p args => Ty_Atom p (map (b_lift_tm n k) args)
  end.

(* ================================================================= *)
(* 5. HELYETTESÍTÉS (SUBSTITUTION)                                   *)
(* ================================================================= *)

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

  (* Függvény: argumentum cseréje *)
  | b_fun f t => b_fun f (b_subst_tm k s t)

  (* Epszilon: formula cseréje *)
  | b_epsilon A => b_epsilon (b_subst_ty k s A)
  end

with b_subst_ty (k : nat) (s : b_tm) (A : h_ty) : h_ty :=
  match A with
  | Ty_Unit => Ty_Unit
  | Ty_Arr A1 A2  => Ty_Arr (b_subst_ty k s A1) (b_subst_ty k s A2)
  | Ty_Prod A1 A2 => Ty_Prod (b_subst_ty k s A1) (b_subst_ty k s A2)
  | Ty_Atom p args => Ty_Atom p (map (b_subst_tm k s) args)
  end.