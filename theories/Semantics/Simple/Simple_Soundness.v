Require Import List.
Require Import PeanoNat. 
Require Import Coq.Classes.Morphisms.
Import ListNotations.

(* Cat Imports *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Fibration.

(* Logic Imports *)
Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Logic.Base.Simple.Base_Typing.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Logic.

(* ================================================================= *)
(* 1. MODEL DEFINITION                                               *)
(* ================================================================= *)

Class SimpleModel (B : SetoidCategory) {CB : CartesianCategory B} {GF : GoodFibration B} := {
  interp_sort : @obj B;
  interp_atom : forall (p : nat) (dom : @obj B), @obj (Fiber dom)
}.

(* ================================================================= *)
(* 2. BASE INTERPRETATION (Contexts & Terms)                         *)
(* ================================================================= *)

(* Típusok interpretációja *)
(* Fontos: Mindenhol explicit típusokat adunk meg a {..}-ben *)
Fixpoint interp_base_ty {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {M : SimpleModel B} 
  (A : b_ty) : @obj B :=
  match A with
  | b_Unit => terminal
  | b_Prod A B => prod (interp_base_ty A) (interp_base_ty B)
  | b_S => interp_sort
  end.

(* Kontextusok interpretációja *)
Fixpoint interp_ctx {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {M : SimpleModel B} 
  (G : b_context) : @obj B :=
  match G with
  | nil => terminal
  | A :: G' => prod (interp_ctx G') (interp_base_ty A)
  end.
  

 