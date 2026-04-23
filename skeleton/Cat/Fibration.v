Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import Coq.Classes.Morphisms.

(** * 1. The Core Fibration (Hyperdoctrine) *)

(** WHAT IT IS:
  The [GoodFibration] class defines a categorical hyperdoctrine, serving as the
  semantic foundation for our logic. It maps a Cartesian base category of individuals
  to a family of BiCartesian Closed Categories (fibers) representing propositions.

  WHY WE CHOSE THIS SOLUTION:
  1. Local Proof. Admitted.

Instance TotalCategory {B : SetoidCategory} {CB : CartesianCategory B}
  (GF : GoodFibration B) (SGF : StrictGoodFibration B GF) : SetoidCategory.
Proof. Admitted.

(** * 5. Logical Quantifiers and the Base Individual Type *)

(** The Category representing two sorts: the standard terminal object and
  the sort of individuals (S).
*)
Class TwoSortCategory (B : SetoidCategory) {CB : CartesianCategory B} := mk_TwoSortCategory {
  S : @obj B;
  S_is_not_Terminal : S <> terminal
}.
Arguments S {B CB}.

(** The 'bang' morphism mapping the individual sort to the terminal object. *)
Definition bang (B : SetoidCategory) {CB : CartesianCategory B} {TSC : TwoSortCategory B} : hom (@S B CB TSC) terminal :=
  terminal_map.

Lemma pi_iso_cong :
  forall {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B}
         {I A : @obj B} (X Y : @obj (Fiber (@prod B CB I A))),
  X ≅O Y ->
  @right_adj_obj _ _ _ (@pullback_has_right_adjoint B CB GF I A) X ≅O
  @right_adj_obj _ _ _ (@pullback_has_right_adjoint B CB GF I A) Y.
Proof. Admitted.

Lemma sigma_iso_cong :
  forall {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B}
         {I A : @obj B} (X Y : @obj (Fiber (@prod B CB I A))),
  X ≅O Y ->
  @left_adj_obj _ _ _ (@pullback_has_left_adjoint B CB GF I A) X ≅O
  @left_adj_obj _ _ _ (@pullback_has_left_adjoint B CB GF I A) Y.
Proof. Admitted.