(* theories/Semantics/Epsilon/Epsilon_Completeness.v *)

Require Import List.
Import ListNotations.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Fibration.

Require Import HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.
Require Import HyperLogic.Semantics.Epsilon.Epsilon_Fibration.
Require Import HyperLogic.Semantics.Epsilon.Epsilon_Soundness.

(* This file used to contain an old syntactic-model sketch for a previous
   one-parameter epsilon syntax.  The current epsilon language is the
   Pasquali-style fragment: no primitive [Ty_Ex], only epsilon instances.

   Rebuilding completeness for this fragment requires a fresh syntactic
   GoodFibration and a syntactic [EpsilonGoodFibration].  The old file already
   relied on axioms/admitted construction pieces, so for now we expose the
   intended metatheorem explicitly as an axiom rather than keeping a misleading
   half-updated construction. *)

Axiom hyper_completeness_inhabitational :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred}
    {SM : SkolemMapping Sign Func Pred}
    (I : b_ty) (Phi Psi : @h_ty Sign Func Pred),
  (forall (C : SetoidCategory) (CC : CartesianCategory C)
          (CCC : @CartesianClosedCategory C CC)
          (BCCC : @BiCartesianClosedCategory C CC CCC)
          (TSC : TwoSortCategory C)
          (BEM : @BaseEpsilonModel Sign Func H C CC TSC)
          (CBM : @CoherentBaseModel Sign Func H C CC TSC BEM)
          (GF : GoodFibration C) (SGF : StrictGoodFibration C GF)
          (EHM : @EpsilonHyperModel Sign Func Pred H H0 C CC TSC BEM GF SGF)
          (EGF : @EpsilonGoodFibration Sign Func Pred H H0 SM C CC TSC BEM GF SGF EHM),
      inhabited (hom (interp_h_ty I Phi) (interp_h_ty I Psi))) ->
  exists (p : @h_tm Sign Func Pred), inhabited (h_derivation I (Phi :: nil) p Psi).
