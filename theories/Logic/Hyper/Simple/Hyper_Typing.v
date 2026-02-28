Require Import List.
Import ListNotations.

(* Importáljuk mindkét szintaxist és a base typingot *)
Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Logic.Base.Simple.Base_Typing.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.

(* --- Szignatúra definíciója --- *)
Definition predicate_sig (p : nat) : list b_ty :=
  match p with
  | 0 => [b_S; b_S]  (* Pl. Egyenlőség *)
  | _ => []
  end.

(* --- Argumentum lista ellenőrzése --- *)
Inductive check_args : b_context -> list b_tm -> list b_ty -> Prop :=
  | CA_Nil : forall G, check_args G [] []
  | CA_Cons : forall G t ts A As,
      base_typing G t A ->       
      check_args G ts As ->      
      check_args G (t :: ts) (A :: As).

(* --- Formula Helyessége (Well-formedness) --- *)
Inductive formula_wf : b_context -> h_ty -> Prop :=
  (* Logikai alapok *)
  | WF_Unit : forall G, formula_wf G Ty_Unit
  | WF_Void : forall G, formula_wf G Ty_Void
  | WF_Prod : forall G A B, formula_wf G A -> formula_wf G B -> formula_wf G (Ty_Prod A B)
  | WF_Sum  : forall G A B, formula_wf G A -> formula_wf G B -> formula_wf G (Ty_Sum A B)
  | WF_Arr  : forall G A B, formula_wf G A -> formula_wf G B -> formula_wf G (Ty_Arr A B)

  (* Atom *)
  | WF_Atom : forall G p ts,
      check_args G ts (predicate_sig p) ->
      formula_wf G (Ty_Atom p ts)

  (* Kvantorok: Itt látszik a Base és Hyper szétválása! *)
  (* A kontextus (Base) bővül egy A típussal, és ebben a bővített kontextusban vizsgáljuk a formulát (Hyper) *)
  
  | WF_All : forall G A Phi,
      formula_wf (A :: G) Phi ->
      formula_wf G (Ty_All A Phi)

  | WF_Ex : forall G A Phi,
      formula_wf (A :: G) Phi ->
      formula_wf G (Ty_Ex A Phi).
      
(* ================================================================= *)
(* DERIVATION TREES (DATA LAYER - Set)                               *)
(* ================================================================= *)
(* Ezek az adatszerkezetek elengedhetetlenek a szemantika 
   (kategóriaelméleti morfizmusok és objektumok) felépítéséhez. *)

(* Argumentumok típusozása (Set verzió) *)
Inductive args_derivation : b_context -> list b_tm -> list b_ty -> Set :=
  | AD_Nil : forall G, args_derivation G [] []
  | AD_Cons : forall G t ts A As,
      base_typing G t A -> (* Ez szerencsére már Set! *)
      args_derivation G ts As ->
      args_derivation G (t :: ts) (A :: As).

(* Formula helyessége (Set verzió) *)
Inductive formula_derivation : b_context -> h_ty -> Set :=
  (* Logikai alapok *)
  | FD_Unit : forall G, formula_derivation G Ty_Unit
  | FD_Void : forall G, formula_derivation G Ty_Void
  | FD_Prod : forall G A B, formula_derivation G A -> formula_derivation G B -> formula_derivation G (Ty_Prod A B)
  | FD_Sum  : forall G A B, formula_derivation G A -> formula_derivation G B -> formula_derivation G (Ty_Sum A B)
  | FD_Arr  : forall G A B, formula_derivation G A -> formula_derivation G B -> formula_derivation G (Ty_Arr A B)

  (* Atom *)
  | FD_Atom : forall G p ts,
      args_derivation G ts (predicate_sig p) ->
      formula_derivation G (Ty_Atom p ts)

  (* Kvantorok *)
  | FD_All : forall G A Phi,
      formula_derivation (A :: G) Phi ->
      formula_derivation G (Ty_All A Phi)

  | FD_Ex : forall G A Phi,
      formula_derivation (A :: G) Phi ->
      formula_derivation G (Ty_Ex A Phi).

(* ================================================================= *)
(* BRIDGES (Set -> Prop)                                             *)
(* ================================================================= *)
(* Ezek a függvények eldobják a kiszámítható struktúrát, és 
   visszaadják a logikai (Prop) állítást. *)

Fixpoint forget_args {G ts As} (d : args_derivation G ts As) : check_args G ts As :=
  match d with
  | AD_Nil _ => CA_Nil _
  | AD_Cons _ t ts' A As' bt ad' => CA_Cons _ t ts' A As' bt (forget_args ad')
  end.

Fixpoint forget_formula {G Phi} (d : formula_derivation G Phi) : formula_wf G Phi :=
  match d with
  | FD_Unit _ => WF_Unit _
  | FD_Void _ => WF_Void _
  | FD_Prod _ A B d1 d2 => WF_Prod _ A B (forget_formula d1) (forget_formula d2)
  | FD_Sum  _ A B d1 d2 => WF_Sum  _ A B (forget_formula d1) (forget_formula d2)
  | FD_Arr  _ A B d1 d2 => WF_Arr  _ A B (forget_formula d1) (forget_formula d2)
  | FD_Atom _ p ts ad => WF_Atom _ p ts (forget_args ad)
  | FD_All  _ A Phi' d' => WF_All _ A Phi' (forget_formula d')
  | FD_Ex   _ A Phi' d' => WF_Ex  _ A Phi' (forget_formula d')
  end.