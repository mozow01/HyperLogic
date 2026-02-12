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