Require Import List Arith PeanoNat Lia.
Import ListNotations. 

(* ================================================================= *)
(* 1. BASE TYPES (S és 1)                                            *)
(* ================================================================= *)

Inductive b_ty : Set :=
  | b_Unit : b_ty  (* 1: A terminális objektum *)
  | b_S    : b_ty. (* S: A "Sort", az alaphalmaz *)

(* Kontextus: bázis típusok listája *)
Definition b_context := list b_ty.

(* ================================================================= *)
(* 2. BASE TERMS                                                     *)
(* ================================================================= *)

Inductive b_tm : Set :=
  | b_var  : nat -> b_tm          (* De Bruijn indexek (id, kompozíció) *)
  | b_unit : b_tm                 (* A terminális elem (! morfizmus) *)
  
  (* Jövőbeli bővítés: 'nat' darab 1 -> S morfizmus *)
  | b_const : nat -> b_tm.        (* c_0, c_1, c_2 ... : 1 -> S *)

(* ================================================================= *)
(* 3. DE BRUIJN MŰVELETEK (LIFT & SUBST) a Bázison                   *)
(* ================================================================= *)
(* Mivel ez egy kategória lesz, elengedhetetlen a helyettesítés. *)

Definition b_lift (n : nat) (k : nat) (t : b_tm) : b_tm :=
  match t with
  | b_var i => if k <=? i then b_var (n + i) else b_var i
  | b_unit  => b_unit
  | b_const c => b_const c (* A konstansok zártak *)
  end.

Definition b_subst (k : nat) (s : b_tm) (t : b_tm) : b_tm :=
  match t with
  | b_var i =>
      if k =? i then s
      else if k <? i then b_var (i - 1)
      else b_var i
  | b_unit => b_unit
  | b_const c => b_const c
  end.

(* ================================================================= *)
(* 4. TYPING RULES (Morfizmusok képzése)                             *)
(* ================================================================= *)

(* Jelölés: Gamma |- t : A *)
Inductive b_typing : b_context -> b_tm -> b_ty -> Prop :=
  
  (* Változó szabály (Identity és projekciók alapja) *)
  | BT_Var0 : forall Gamma A,
      b_typing (A :: Gamma) (b_var 0) A
  | BT_VarS : forall Gamma A B i,
      b_typing Gamma (b_var i) A ->
      b_typing (B :: Gamma) (b_var (S i)) A

  (* Terminális szabály (! morfizmus) *)
  (* Bármely kontextusból van egy (és csak egy) nyíl az 1-be *)
  | BT_Unit : forall Gamma,
      b_typing Gamma b_unit b_Unit

  (* Konstans szabály (Elemek) *)
  (* c_n : 1 -> S. De mivel "bármely kontextusban" használhatóak konstansként: *)
  (* Gamma |- c_n : S *)
  | BT_Const : forall Gamma n,
      b_typing Gamma (b_const n) b_S.

Notation "Gamma '⊢b' t '[:]' A" := (b_typing Gamma t A) (at level 70).

(* ================================================================= *)
(* 5. EQUATIONAL LOGIC (A Bázis Kategória törvényei)                 *)
(* ================================================================= *)

(* Itt definiáljuk, mikor egyenlő két "morfizmus" (term) a bázisban. *)
Inductive b_equiv : b_context -> b_tm -> b_tm -> b_ty -> Prop :=
  
  (* --- Ekvivalencia reláció --- *)
  | BE_Refl : forall Gamma t A,
      Gamma ⊢b t [:] A ->
      b_equiv Gamma t t A
  | BE_Sym : forall Gamma t1 t2 A,
      b_equiv Gamma t1 t2 A ->
      b_equiv Gamma t2 t1 A
  | BE_Trans : forall Gamma t1 t2 t3 A,
      b_equiv Gamma t1 t2 A ->
      b_equiv Gamma t2 t3 A ->
      b_equiv Gamma t1 t3 A

  (* --- Terminális Objektum Törvénye (Eta rule for Unit) --- *)
  (* Ez a legfontosabb! Azt mondja ki, hogy az 1-be menő minden nyíl egyenlő.
     Ez garantálja, hogy a ! morfizmus (terminal_map) egyértelmű. *)
  | BE_Unit_Uniq : forall Gamma t,
      Gamma ⊢b t [:] b_Unit ->
      b_equiv Gamma t b_unit b_Unit.

Notation "Gamma '⊢b' t1 '≈' t2 '[:]' A" := (b_equiv Gamma t1 t2 A) (at level 70).