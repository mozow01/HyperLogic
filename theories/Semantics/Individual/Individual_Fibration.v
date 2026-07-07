(* theories/Semantics/Individual/Individual_Fibration.v *)

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.Adjoint.
Require Import HyperLogic.Cat.Fibration.
Require Import HyperLogic.Logic.Base.Individual.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Individual.Hyper_Syntax.
Require Export HyperLogic.Semantics.EpsilonFull.EpsilonFull_Fibration.

(* The individual/iFOLFull semantics uses the same categorical interpretation of
   base terms, predicates, forall, and exists as EpsilonFull.  What it omits is
   the extra adjoint-epsilon structure from [AdjointEpsilonFullFibration]. *)

Lemma individual_sigma_adjoints_unique_pointwise :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred}
    {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
    {BEM : BaseEpsilonFullModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
    {EHM : EpsilonHyperModel SGF}
    (I A : b_ty)
    (RA2 : IsRightAdjoint (Pullback (@prod_fst C CC (interp_ty I) (interp_ty A))))
    (Phi : @h_ty Sign Func Pred),
    @left_adj_obj _ _ _ (@pullback_has_left_adjoint C CC GF (interp_ty I) (interp_ty A))
      (interp_h_ty (b_Prod I A) Phi)
    ≅O
    @left_adj_obj _ _ _ RA2
      (interp_h_ty (b_Prod I A) Phi).
Proof.
  intros Sign Func Pred HFunc HPred C CC TSC BEM GF SGF EHM I A RA2 Phi.
  apply sigma_adjoints_unique_pointwise.
Defined.

Lemma individual_ty_ex_adjoints_unique_pointwise :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred}
    {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
    {BEM : BaseEpsilonFullModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
    {EHM : EpsilonHyperModel SGF}
    (I A : b_ty)
    (RA2 : IsRightAdjoint (Pullback (@prod_fst C CC (interp_ty I) (interp_ty A))))
    (Phi : @h_ty Sign Func Pred),
    interp_h_ty I (Ty_Ex A Phi)
    ≅O
    @left_adj_obj _ _ _ RA2
      (interp_h_ty (b_Prod I A) Phi).
Proof.
  intros Sign Func Pred HFunc HPred C CC TSC BEM GF SGF EHM I A RA2 Phi.
  simpl.
  apply individual_sigma_adjoints_unique_pointwise.
Defined.
