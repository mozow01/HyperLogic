Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.Functor. 
Require Import HyperLogic.Cat.Adjoint.
Require Import Coq.Classes.Morphisms.

Class GoodFibration (B : SetoidCategory) := mk_GoodFibration {
  
  (* 1. Indexelt kategóriák (Fiber) *)
  Fiber : @obj B -> SetoidCategory;

  (* 2. A Fiberek CCC-k *)
  Fiber_is_CCC : forall (I : @obj B), CartesianClosedCategory (Fiber I);

  (* 3. Pullback Funktor (Most már a Functor.v definícióját használjuk) *)
  (* (I -> J) morfizmushoz rendel egy Functor-t visszafelé *)
  Pullback {I J : @obj B} : (hom I J) -> Functor (Fiber J) (Fiber I);

  (* 4. Pullback tulajdonságok *)
  
  (* Pullback(id) ≅ Id *)
  (* F_Obj helyett 'fobj'-ot használunk a Functor.v-ből *)
  pullback_id_iso : forall {I : @obj B} (A : @obj (Fiber I)), 
      (@fobj (Fiber I) (Fiber I) (Pullback (id I)) A) ≅O A;

  (* Pullback(g ∘ f) ≅ Pullback(f) ∘ Pullback(g) *)
  (* A kompozíciót itt objektum szinten fejtjük ki: fobj (P(gf)) A ≅ fobj (P f) (fobj (P g) A) *)
  pullback_comp_iso : forall {I J K : @obj B} (g : hom J K) (f : hom I J) (A : @obj (Fiber K)),
      (@fobj (Fiber K) (Fiber I) (Pullback (compose g f)) A) ≅O 
      (@fobj (Fiber J) (Fiber I) (Pullback f) 
        (@fobj (Fiber K) (Fiber J) (Pullback g) A));

  (* 5. Adjungáltak (Kvantorok) létezése *)
  
  (* A Pullback f-nek van bal adjungáltja (Sigma) *)
  (* Ez azt jelenti, hogy a Pullback f egy jobb adjungált *)
  pullback_has_left_adjoint {I J : @obj B} (f : hom I J) :
      IsRightAdjoint (Pullback f);
      
  (* A Pullback f-nek van jobb adjungáltja (Pi) *)
  (* Ez azt jelenti, hogy a Pullback f egy bal adjungált *)
  pullback_has_right_adjoint {I J : @obj B} (f : hom I J) :
      IsLeftAdjoint (Pullback f)
}.

(* Automatikus láthatóság a CCC instance-hoz *)
Global Existing Instance Fiber_is_CCC.

(* ================================================================= *)
(* KVANTOROK KONSTRUKCIÓJA (Sigma és Pi)                             *)
(* ================================================================= *)

(* A Sigma funktor (Bal adjungált) kinyerése *)
Definition Sigma_f {B : SetoidCategory} {GF : GoodFibration B} {I J : @obj B} (f : hom I J)
  : Functor (Fiber I) (Fiber J). (* CovariantFunctor -> Functor *)
Proof.
   pose proof (@pullback_has_left_adjoint B GF I J f) as adj_proof.
   (* LeftAdjFunc most Functor-t ad vissza *)
   exact (LeftAdjointFunctor (Pullback f) adj_proof).
Defined.

(* A Pi funktor (Jobb adjungált) kinyerése *)
Definition Pi_f {B : SetoidCategory} {GF : GoodFibration B} {I J : @obj B} (f : hom I J)
  : Functor (Fiber I) (Fiber J).
Proof.
  pose proof (@pullback_has_right_adjoint B GF I J f) as adj_proof.
  exact (RightAdjointFunctor (Pullback f) adj_proof).
Defined.

(* ================================================================= *)
(* BASE LOGIC (Kétfajtájú Kategória)                                 *)
(* ================================================================= *)

Class TwoSortCategory (B : SetoidCategory) := mk_TwoSortCategory {
  One : @obj B;
  terminal_map_base : forall X, hom X One;
  terminal_map_base_unique : forall X (f : hom X One), f ≅ terminal_map_base X;
  
  S : @obj B;
  S_is_not_Terminal : S <> One 
}.

(* A "bang" morfizmus: S -> 1 *)
Definition bang (B : SetoidCategory) {TSC : TwoSortCategory B} : hom (@S B TSC) (@One B TSC) :=
  terminal_map_base S.

(* ================================================================= *)
(* LOGIKAI KVANTOROK (Exists / Forall)                               *)
(* ================================================================= *)

(** Exisztenciális kvantor: Sigma a bang mentén *)
Definition ExistsQuantifier (B : SetoidCategory) {GF : GoodFibration B} {TSC : TwoSortCategory B}
  : Functor (Fiber S) (Fiber One).
Proof.
 exact (Sigma_f (bang B)). 
Defined.

(** Univerzális kvantor: Pi a bang mentén *)
Definition ForallQuantifier (B : SetoidCategory) {GF : GoodFibration B} {TSC : TwoSortCategory B}
  : Functor (Fiber S) (Fiber One).
Proof.
  exact (Pi_f (bang B)).
Defined.