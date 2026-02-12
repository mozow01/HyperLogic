Require Import List.
Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.

Inductive h_ty : Type :=
  (* --- BCCC Logikai Operátorok --- *)
  | Ty_Unit : h_ty            (* Truth *)
  | Ty_Void : h_ty            (* Falsity *)
  | Ty_Prod : h_ty -> h_ty -> h_ty (* And *)
  | Ty_Sum  : h_ty -> h_ty -> h_ty (* Or *)
  | Ty_Arr  : h_ty -> h_ty -> h_ty (* Implies *)
  
  (* --- Kapcsolat a Base-sel (Fibráció) --- *)
  
  (* Predikátum: P(t1, ..., tn) *)
  | Ty_Atom : nat -> list b_tm -> h_ty 

  (* Kvantorok: Ezek a Simple rendszer lényegei! *)
  (* Forall x:A. Phi *)
  | Ty_All  : b_ty -> h_ty -> h_ty 
  (* Exists x:A. Phi *)
  | Ty_Ex   : b_ty -> h_ty -> h_ty.