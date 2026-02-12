Require Import HyperLogic.Cat.Core. 
Require Import HyperLogic.Cat.CC.   
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC. 
Require Import HyperLogic.Cat.Functor. 
Require Import HyperLogic.Cat.Adjoint.
Require Import Coq.Classes.Morphisms.

(* ================================================================= *)
(* GOOD FIBRATION DEFINITION                                         *)
(* ================================================================= *)

(* A Base kategóriának (B) Cartesian-nak kell lennie {CB}, 
   hogy tudjuk kezelni a kontextusokat (szorzatokat). *)
Class GoodFibration (B : SetoidCategory) {CB : CartesianCategory B} := mk_GoodFibration {
  
  (* 1. Indexelt kategóriák (Fiber) - Ez a logika (típusok/formulák) *)
  Fiber : @obj B -> SetoidCategory;

  (* 2. A Fiberek BCCC-k (Teljes Logika: ∧, ∨, →, ⊤, ⊥) *)
  (* Három lépésben építjük fel, hogy a típusosztályok lássák a függőségeket *)
  Fiber_is_Cartesian : forall (I : @obj B), CartesianCategory (Fiber I);
  Fiber_is_Closed    : forall (I : @obj B), @CartesianClosedCategory (Fiber I) (Fiber_is_Cartesian I);
  Fiber_is_BiClosed  : forall (I : @obj B), @BiCartesianClosedCategory (Fiber I) (Fiber_is_Cartesian I) (Fiber_is_Closed I);

  (* 3. Pullback Funktor (Helyettesítés) *)
  (* (I -> J) morfizmushoz (term) rendel egy Functor-t visszafelé (formulák transzformációja) *)
  Pullback {I J : @obj B} : (hom I J) -> Functor (Fiber J) (Fiber I);

  (* 4. Pullback tulajdonságok (Izomorfizmusok) *)
  
  (* Pullback(id) ≅ Id *)
  pullback_id_iso : forall {I : @obj B} (A : @obj (Fiber I)), 
      (@fobj (Fiber I) (Fiber I) (Pullback (id I)) A) ≅O A;

  (* Pullback(g ∘ f) ≅ Pullback(f) ∘ Pullback(g) *)
  pullback_comp_iso : forall {I J K : @obj B} (g : hom J K) (f : hom I J) (A : @obj (Fiber K)),
      (@fobj (Fiber K) (Fiber I) (Pullback (compose g f)) A) ≅O 
      (@fobj (Fiber J) (Fiber I) (Pullback f) 
        (@fobj (Fiber K) (Fiber J) (Pullback g) A));

  (* 5. Adjungáltak (Kvantorok) létezése *)
  
  (* Sigma (Exists): Bal adjungáltja a Pullback-nek *)
  pullback_has_left_adjoint {I J : @obj B} (f : hom I J) :
      IsRightAdjoint (Pullback f);

  (* Pi (Forall): Jobb adjungáltja a Pullback-nek *)
  pullback_has_right_adjoint {I J : @obj B} (f : hom I J) :
      IsLeftAdjoint (Pullback f)
}.

(* --- Instance regisztráció --- *)
(* Explicit típusmegadás szükséges a {CB}-hez, hogy a Coq felismerje a kapcsolatot *)

Global Instance GF_Fiber_CC 
  {B : SetoidCategory} 
  {CB : CartesianCategory B} 
  {GF : GoodFibration B} 
  (I : @obj B) 
  : CartesianCategory (Fiber I) := Fiber_is_Cartesian I.

Global Instance GF_Fiber_CCC 
  {B : SetoidCategory} 
  {CB : CartesianCategory B} 
  {GF : GoodFibration B} 
  (I : @obj B) 
  : CartesianClosedCategory (Fiber I) := Fiber_is_Closed I.

Global Instance GF_Fiber_BCCC 
  {B : SetoidCategory} 
  {CB : CartesianCategory B} 
  {GF : GoodFibration B} 
  (I : @obj B) 
  : BiCartesianClosedCategory (GF_Fiber_CCC I) := Fiber_is_BiClosed I.

(* ================================================================= *)
(* KVANTOROK KONSTRUKCIÓJA (Sigma és Pi)                             *)
(* ================================================================= *)

Definition Sigma_f {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {I J : @obj B} (f : hom I J)
  : Functor (Fiber I) (Fiber J).
Proof.
   pose proof (@pullback_has_left_adjoint B CB GF I J f) as adj_proof.
   exact (LeftAdjointFunctor (Pullback f) adj_proof).
Defined.

Definition Pi_f {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {I J : @obj B} (f : hom I J)
  : Functor (Fiber I) (Fiber J).
Proof.
  pose proof (@pullback_has_right_adjoint B CB GF I J f) as adj_proof.
  exact (RightAdjointFunctor (Pullback f) adj_proof).
Defined.

(* ================================================================= *)
(* BASE LOGIC (Individuumok)                                         *)
(* ================================================================= *)

Class TwoSortCategory (B : SetoidCategory) {CB : CartesianCategory B} := mk_TwoSortCategory {
  (* A 'One' (terminális) már jön a CB-ből, itt csak az S-t (Individuum típus) definiáljuk *)
  S : @obj B;
  S_is_not_Terminal : S <> terminal 
}.

(* A "bang" morfizmus: S -> 1 (terminális leképezés) *)
(* Most már közvetlenül használhatjuk a CartesianCategory 'terminal_map'-jét *)
Definition bang (B : SetoidCategory) {CB : CartesianCategory B} {TSC : TwoSortCategory B} : hom (@S B CB TSC) terminal :=
  terminal_map.

(* ================================================================= *)
(* LOGIKAI KVANTOROK (Exists / Forall)                               *)
(* ================================================================= *)

(** Exisztenciális kvantor: Sigma a bang mentén (S -> 1) *)
Definition ExistsQuantifier (B : SetoidCategory) {CB : CartesianCategory B} {GF : GoodFibration B} {TSC : TwoSortCategory B}
  : Functor (Fiber S) (Fiber terminal).
Proof.
 exact (Sigma_f (bang B)). 
Defined.

(** Univerzális kvantor: Pi a bang mentén (S -> 1) *)
Definition ForallQuantifier (B : SetoidCategory) {CB : CartesianCategory B} {GF : GoodFibration B} {TSC : TwoSortCategory B}
  : Functor (Fiber S) (Fiber terminal).
Proof.
  exact (Pi_f (bang B)).
Defined.