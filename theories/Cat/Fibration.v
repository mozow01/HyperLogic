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

  Fiber : @obj B -> SetoidCategory;
  Fiber_is_Cartesian : forall (I : @obj B), CartesianCategory (Fiber I);
  Fiber_is_Closed    : forall (I : @obj B), @CartesianClosedCategory (Fiber I) (Fiber_is_Cartesian I);
  Fiber_is_BiClosed  : forall (I : @obj B), @BiCartesianClosedCategory (Fiber I) (Fiber_is_Cartesian I) (Fiber_is_Closed I);
  
  Pullback : forall {I J : @obj B}, (hom I J) -> Functor (Fiber J) (Fiber I);

  pullback_id_iso : forall {I : @obj B} (A : @obj (Fiber I)),
      (@fobj _ _ (Pullback (id I)) A) ≅O A;
      
  pullback_comp_iso : forall {I J K : @obj B} (g : hom J K) (f : hom I J) (A : @obj (Fiber K)),
      (@fobj _ _ (Pullback (compose g f)) A) ≅O
      (@fobj _ _ (Pullback f) (@fobj _ _ (Pullback g) A));

  (* ========================================================= *)
  (* A PULLBACK FUNKTOR MEGŐRZI A LOGIKAI (BiCCC) STRUKTÚRÁT   *)
  (* ========================================================= *)
  
  pb_term_iso : forall {I J : @obj B} (f : hom I J), 
      (@fobj _ _ (Pullback f) (@terminal _ (Fiber_is_Cartesian J))) ≅O 
      (@terminal _ (Fiber_is_Cartesian I));
      
  pb_prod_iso : forall {I J : @obj B} (f : hom I J) (A B : @obj (Fiber J)),
      (@fobj _ _ (Pullback f) (@prod _ (Fiber_is_Cartesian J) A B)) ≅O 
      (@prod _ (Fiber_is_Cartesian I) (@fobj _ _ (Pullback f) A) (@fobj _ _ (Pullback f) B));
      
  pb_init_iso : forall {I J : @obj B} (f : hom I J),
      (@fobj _ _ (Pullback f) (@initial _ _ (Fiber_is_Closed J) (Fiber_is_BiClosed J))) ≅O 
      (@initial _ _ (Fiber_is_Closed I) (Fiber_is_BiClosed I));
      
  pb_coprod_iso : forall {I J : @obj B} (f : hom I J) (A B : @obj (Fiber J)),
      (@fobj _ _ (Pullback f) (@coprod _ _ (Fiber_is_Closed J) (Fiber_is_BiClosed J) A B)) ≅O 
      (@coprod _ _ (Fiber_is_Closed I) (Fiber_is_BiClosed I) (@fobj _ _ (Pullback f) A) (@fobj _ _ (Pullback f) B));
      
  pb_exp_iso : forall {I J : @obj B} (f : hom I J) (A B : @obj (Fiber J)),
      (@fobj _ _ (Pullback f) (@exp _ _ (Fiber_is_Closed J) A B)) ≅O 
      (@exp _ _ (Fiber_is_Closed I) (@fobj _ _ (Pullback f) A) (@fobj _ _ (Pullback f) B));

  (* ========================================================= *)
  (* KVANTOR ADJUNGÁLTAK ÉS BECK-CHEVALLEY FELTÉTELEK          *)
  (* ========================================================= *)
  
  pullback_has_left_adjoint : forall {I J : @obj B} (f : hom I J), IsRightAdjoint (Pullback f);
  pullback_has_right_adjoint : forall {I J : @obj B} (f : hom I J), IsLeftAdjoint (Pullback f);

  beck_chevalley_sigma : forall {I J K : @obj B} (f : hom K I) (A : @obj (Fiber (@prod B CB I J))),
      (@fobj _ _ (Pullback f) (@left_adj_obj _ _ _ (pullback_has_left_adjoint (@prod_fst B CB I J)) A)) ≅O 
      (@left_adj_obj _ _ _ (pullback_has_left_adjoint (@prod_fst B CB K J)) 
          (@fobj _ _ (Pullback (@prod_map B CB (prod K J) I J (compose f (@prod_fst B CB K J)) (@prod_snd B CB K J))) A));

  beck_chevalley_pi : forall {I J K : @obj B} (f : hom K I) (A : @obj (Fiber (@prod B CB I J))),
      (@fobj _ _ (Pullback f) (@right_adj_obj _ _ _ (pullback_has_right_adjoint (@prod_fst B CB I J)) A)) ≅O 
      (@right_adj_obj _ _ _ (pullback_has_right_adjoint (@prod_fst B CB K J)) 
          (@fobj _ _ (Pullback (@prod_map B CB (prod K J) I J (compose f (@prod_fst B CB K J)) (@prod_snd B CB K J))) A));
          (* ... a többi mező után ... *)
  
  (* Pullback tiszteli a bázis morfizmusok egyenlőségét *)
  pb_iso : forall {I J : @obj B} (f g : hom I J), 
      f ≅ g -> forall (A : @obj (Fiber J)), (@fobj _ _ (Pullback f) A) ≅O (@fobj _ _ (Pullback g) A);
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