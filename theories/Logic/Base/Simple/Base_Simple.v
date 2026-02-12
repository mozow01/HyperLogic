Require Import List.

(* --- Base Types (Objektumok) --- *)
Inductive b_ty : Type :=
  | b_Unit : b_ty                 (* Terminális objektum (üres kontextus vége) *)
  | b_Prod : b_ty -> b_ty -> b_ty (* Szorzat (Kontextus bővítés) *)
  | b_S    : b_ty.                (* Sort / Individuum típus *)

(* Kontextus: Típusok listája *)
Definition b_context := list b_ty.

(* --- Base Terms (Morfizmusok) --- *)
(* Nincs konstans, nincs függvényjel, nincs epszilon! *)
Inductive b_tm : Type :=
  | b_var  : nat -> b_tm
  | b_unit : b_tm
  | b_pair : b_tm -> b_tm -> b_tm
  | b_fst  : b_tm -> b_tm
  | b_snd  : b_tm -> b_tm.