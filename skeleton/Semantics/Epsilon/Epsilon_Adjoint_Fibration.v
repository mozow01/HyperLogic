(*theories/Semantics/Epsilon/Epsilon_Fibration.v*)

Require Import Coq.Classes.Morphisms.
Require Import List.
Import ListNotations.

(* Kategóriaelméleti alapok *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import HyperLogic.Cat.Fibration.

(* Szintaxis és Orákulum *)
Require Import HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.
Require Import HyperLogic.Semantics.Epsilon.Epsilon_Fibration.

Class AdjointEpsilonFibration
  {Sign : Type} {SM : SkolemMapping Sign}
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonModel} {GF : GoodFibration C}
  {SGF : StrictGoodFibration C GF}
  {EHM : EpsilonHyperModel SGF} := {

    eps_is_left_adj_obj : forall (I A : b_ty) (Phi : @h_ty Sign),
    @left_adj_obj _ _ _ (pullback_has_left_adjoint (interp_tm (BT_Fst (Sign:=Sign) (A:=I) (B:=A))))
      (interp_h_ty (b_Prod I A) Phi)
    ≅O
    interp_h_ty I (form_pullback (b_pair b_id (b_const A (skolem_index A Phi))) Phi) ;

    eps_functorial : forall (I A : b_ty) (Phi Psi : @h_ty Sign),
    interp_h_ty (b_Prod I A) Phi ≅O interp_h_ty (b_Prod I A) Psi ->
    interp_h_ty I (form_pullback (b_pair b_id (b_const A (skolem_index A Phi))) Phi)
    ≅O
    interp_h_ty I (form_pullback (b_pair b_id (b_const A (skolem_index A Psi))) Psi)
}.