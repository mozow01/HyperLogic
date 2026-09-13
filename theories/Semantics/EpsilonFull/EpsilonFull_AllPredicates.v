(* Epsilon selection for every semantic predicate over syntactic base types.
   This is an all-predicate "enough epsilon terms" comparison relative to the
   Sigma already present in GoodFibration.  It does not formalize equality
   predicates or Pasquali's full notion of epsilon doctrine.  Unlike the
   epsilon-only, formula-indexed comparison in [Pasquali_Epsilon], the object
   Q below is an arbitrary object of the relevant semantic fiber. *)

Require Import List.
Import ListNotations.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Fibration.
Require Import HyperLogic.Cat.EpsilonSelection.

Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_Fibration.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_Soundness.
Require Import HyperLogic.Semantics.EpsilonFull.Base_EpsilonFull_Completeness.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_Completeness.

Section EpsilonFullAllPredicates.

Context {Sign Func Pred : Type}.
Context `{HFunc : FunctionSignature Func}.
Context `{HPred : PredicateSignature Pred}.
Context {SM : SkolemMapping Sign Func Pred}.

Context {C : SetoidCategory}.
Context {CC : CartesianCategory C}.
Context {TSC : TwoSortCategory C}.
Context {BEM : @BaseEpsilonFullModel Sign Func HFunc C CC TSC}.
Context {GF : GoodFibration C}.
Context {EHM : @EpsilonHyperModel Sign Func Pred HFunc HPred
  C CC TSC BEM GF}.
Context {AEF : @AdjointEpsilonFullFibration Sign Func Pred HFunc HPred SM
  C CC TSC BEM GF EHM}.

Definition interpreted_epsilon_morphism
  (I A : b_ty) (Phi : @h_ty Sign Func Pred) :
  @hom C (interp_ty I) (interp_ty A) :=
  @interp_tm Sign Func HFunc C CC TSC BEM I A
    (b_const A (skolem_index A Phi))
    (@BT_Const Sign Func HFunc I A (skolem_index A Phi)).

Lemma interpreted_formula_epsilon_selection :
  forall (I A : b_ty) (Phi : @h_ty Sign Func Pred),
  WellFormed (b_Prod I A) Phi ->
  @EpsilonSelection C CC GF
    (interp_ty I) (interp_ty A)
    (interp_h_ty (b_Prod I A) Phi)
    (interpreted_epsilon_morphism I A Phi).
Proof.
  intros I A Phi Hwf.
  unfold EpsilonSelection, epsilon_section, interpreted_epsilon_morphism.
  eapply iso_trans.
  - apply eps_is_left_adj_obj.
    exact Hwf.
  - eapply iso_trans.
    + exact (form_subst_iso I (b_Prod I A)
        (b_pair b_id (b_const A (skolem_index A Phi)))
        (BT_Pair BT_Id BT_Const) Phi).
    + apply pb_iso.
      reflexivity.
Defined.

Lemma interpreted_formula_epsilon_selection_adjunction :
  forall (I A : b_ty) (Phi : @h_ty Sign Func Pred),
  WellFormed (b_Prod I A) Phi ->
  @EpsilonSelectionAdjunction C CC GF
    (interp_ty I) (interp_ty A)
    (interp_h_ty (b_Prod I A) Phi)
    (interpreted_epsilon_morphism I A Phi).
Proof.
  intros I A Phi Hwf.
  apply epsilon_selection_to_adjunction.
  apply interpreted_formula_epsilon_selection.
  exact Hwf.
Defined.

Record FormulaFiberCover
  (I A : b_ty)
  (Q : @obj (Fiber (interp_ty (b_Prod I A)))) : Type := {
  formula_cover_formula : @h_ty Sign Func Pred;
  formula_cover_well_formed :
    WellFormed (b_Prod I A) formula_cover_formula;
  formula_cover_iso :
    Q ≅O interp_h_ty (b_Prod I A) formula_cover_formula
}.

Definition FormulaFiberCoverage : Type :=
  forall (I A : b_ty)
    (Q : @obj (Fiber (interp_ty (b_Prod I A)))),
  FormulaFiberCover I A Q.

Definition epsilon_selection_from_formula_cover
  (I A : b_ty)
  (Q : @obj (Fiber (interp_ty (b_Prod I A))))
  (cover : FormulaFiberCover I A Q) :
  @ChosenEpsilonSelection C CC GF
    (interp_ty I) (interp_ty A) Q.
Proof.
  destruct cover as [Phi Hwf Hcover].
  refine {|
    chosen_epsilon_morphism := interpreted_epsilon_morphism I A Phi
  |}.
  eapply iso_trans.
  - apply sigma_iso_cong.
    exact Hcover.
  - eapply iso_trans.
    + apply interpreted_formula_epsilon_selection.
      exact Hwf.
    + apply functor_iso_cong.
      apply iso_sym.
      exact Hcover.
Defined.

(* The indices range only over interpretations of syntactic base types I,A.
   No claim is made about unrelated objects that may also live in C. *)
Class AllPredicateEpsilonFullFibration : Type := {
  all_predicate_epsilon_selection :
    forall (I A : b_ty)
      (Q : @obj (Fiber (interp_ty (b_Prod I A)))),
    @ChosenEpsilonSelection C CC GF
      (interp_ty I) (interp_ty A) Q
}.

Definition all_predicate_fibration_from_formula_coverage
  (coverage : FormulaFiberCoverage) :
  AllPredicateEpsilonFullFibration.
Proof.
  constructor.
  intros I A Q.
  apply epsilon_selection_from_formula_cover.
  exact (coverage I A Q).
Defined.

Definition all_predicate_epsilon_selection_exists
  `{APEF : AllPredicateEpsilonFullFibration}
  (I A : b_ty)
  (Q : @obj (Fiber (interp_ty (b_Prod I A)))) :
  @EpsilonSelectionExists C CC GF
    (interp_ty I) (interp_ty A) Q :=
  @chosen_epsilon_selection_exists C CC GF
    (interp_ty I) (interp_ty A) Q
    (all_predicate_epsilon_selection I A Q).

End EpsilonFullAllPredicates.

(* This class extends all data of the existing epsilon-exists model.  Its
   additional field is the syntax-indexed, all-predicate selection structure. *)
Class AllPredicateEpsilonFullModel
  {Sign Func Pred : Type}
  `{HFunc : FunctionSignature Func}
  `{HPred : PredicateSignature Pred}
  {SM : SkolemMapping Sign Func Pred}
  {C : SetoidCategory}
  {CC : CartesianCategory C}
  {TSC : TwoSortCategory C}
  {BEM : @BaseEpsilonFullModel Sign Func HFunc C CC TSC}
  {GF : GoodFibration C}
  {EHM : @EpsilonHyperModel Sign Func Pred HFunc HPred
    C CC TSC BEM GF}
  {AEF : @AdjointEpsilonFullFibration Sign Func Pred HFunc HPred SM
    C CC TSC BEM GF EHM} : Type := {
  all_predicate_epsilonfull_fibration :
    @AllPredicateEpsilonFullFibration C CC TSC GF
}.

Definition all_predicate_epsilonfull_model_selection
  {Sign Func Pred : Type}
  `{HFunc : FunctionSignature Func}
  `{HPred : PredicateSignature Pred}
  {SM : SkolemMapping Sign Func Pred}
  {C : SetoidCategory}
  {CC : CartesianCategory C}
  {TSC : TwoSortCategory C}
  {BEM : @BaseEpsilonFullModel Sign Func HFunc C CC TSC}
  {GF : GoodFibration C}
  {EHM : @EpsilonHyperModel Sign Func Pred HFunc HPred
    C CC TSC BEM GF}
  {AEF : @AdjointEpsilonFullFibration Sign Func Pred HFunc HPred SM
    C CC TSC BEM GF EHM}
  (APM : @AllPredicateEpsilonFullModel
    Sign Func Pred HFunc HPred SM
    C CC TSC BEM GF EHM AEF)
  (I A : b_ty)
  (Q : @obj (Fiber (interp_ty (b_Prod I A)))) :
  @ChosenEpsilonSelection C CC GF
    (interp_ty I) (interp_ty A) Q :=
  @all_predicate_epsilon_selection C CC TSC GF
    (@all_predicate_epsilonfull_fibration
      Sign Func Pred HFunc HPred SM
      C CC TSC BEM GF EHM AEF APM)
    I A Q.

Section TermModelAllPredicates.

Context {Sign Func Pred : Type}.
Context `{HFunc : FunctionSignature Func}.
Context `{HPred : PredicateSignature Pred}.
Context {SM : SkolemMapping Sign Func Pred}.

Definition term_model_formula_fiber_cover
  (I A : b_ty)
  (Q : @obj
    (@Fiber
      (Base_SetoidCategory Sign Func)
      (Base_CartesianCategory Sign Func)
      (@TermModel_GoodFibration Sign Func Pred HFunc HPred SM)
      (@interp_ty
        (Base_SetoidCategory Sign Func)
        (Base_CartesianCategory Sign Func)
        (Base_TwoSortCategory Sign Func)
        (b_Prod I A)))) :
  @FormulaFiberCover Sign Func Pred HFunc HPred
    (Base_SetoidCategory Sign Func)
    (Base_CartesianCategory Sign Func)
    (Base_TwoSortCategory Sign Func)
    (Base_SyntacticEpsilonFullModel Sign Func)
    TermModel_GoodFibration
    TermModel_EpsilonHyperModel
    I A Q.
Proof.
  destruct Q as [Phi Hwf].
  assert (Hwf_syn : WellFormed (b_Prod I A) Phi).
  {
    rewrite <- (interp_ty_id Sign Func (b_Prod I A)).
    exact Hwf.
  }
  refine (@Build_FormulaFiberCover
    Sign Func Pred HFunc HPred
    (Base_SetoidCategory Sign Func)
    (Base_CartesianCategory Sign Func)
    (Base_TwoSortCategory Sign Func)
    (Base_SyntacticEpsilonFullModel Sign Func)
    TermModel_GoodFibration
    TermModel_EpsilonHyperModel
    I A _ Phi Hwf_syn _).
  apply form_equiv_to_iso.
  pose proof (term_model_interp_id (b_Prod I A) Phi Hwf_syn) as Hinterp.
  cbn [projT1] in Hinterp |- *.
  rewrite Hinterp.
  apply FE_Refl.
  exact Hwf.
Defined.

Definition term_model_formula_fiber_coverage :
  @FormulaFiberCoverage Sign Func Pred HFunc HPred
    (Base_SetoidCategory Sign Func)
    (Base_CartesianCategory Sign Func)
    (Base_TwoSortCategory Sign Func)
    (Base_SyntacticEpsilonFullModel Sign Func)
    TermModel_GoodFibration
    TermModel_EpsilonHyperModel :=
  term_model_formula_fiber_cover.

Global Instance TermModel_AllPredicateEpsilonFullFibration :
  @AllPredicateEpsilonFullFibration
    (Base_SetoidCategory Sign Func)
    (Base_CartesianCategory Sign Func)
    (Base_TwoSortCategory Sign Func)
    (@TermModel_GoodFibration Sign Func Pred HFunc HPred SM).
Proof.
  eapply (@all_predicate_fibration_from_formula_coverage
    Sign Func Pred HFunc HPred SM
    (Base_SetoidCategory Sign Func)
    (Base_CartesianCategory Sign Func)
    (Base_TwoSortCategory Sign Func)
    (Base_SyntacticEpsilonFullModel Sign Func)
    TermModel_GoodFibration
    TermModel_EpsilonHyperModel
    TermModel_AdjointEpsilonFullFibration).
  exact term_model_formula_fiber_coverage.
Defined.

Global Instance TermModel_AllPredicateEpsilonFullModel :
  @AllPredicateEpsilonFullModel
    Sign Func Pred HFunc HPred SM
    (Base_SetoidCategory Sign Func)
    (Base_CartesianCategory Sign Func)
    (Base_TwoSortCategory Sign Func)
    (Base_SyntacticEpsilonFullModel Sign Func)
    TermModel_GoodFibration
    TermModel_EpsilonHyperModel
    TermModel_AdjointEpsilonFullFibration.
Proof.
  constructor.
  exact TermModel_AllPredicateEpsilonFullFibration.
Defined.

End TermModelAllPredicates.

Section AllPredicateValidity.

Context {Sign Func Pred : Type}.
Context `{HFunc : FunctionSignature Func}.
Context `{HPred : PredicateSignature Pred}.
Context {SM : SkolemMapping Sign Func Pred}.

Definition all_predicate_epsilonfull_valid
  (I : b_ty) (G : @h_context Sign Func Pred)
  (Phi : @h_ty Sign Func Pred) : Prop :=
  forall
    (C : SetoidCategory)
    (CC : CartesianCategory C)
    (TSC : TwoSortCategory C)
    (BEM : @BaseEpsilonFullModel Sign Func HFunc C CC TSC)
    (GF : GoodFibration C)
    (EHM : @EpsilonHyperModel Sign Func Pred HFunc HPred
      C CC TSC BEM GF)
    (AEF : @AdjointEpsilonFullFibration Sign Func Pred HFunc HPred SM
      C CC TSC BEM GF EHM)
    (APM : @AllPredicateEpsilonFullModel
      Sign Func Pred HFunc HPred SM
      C CC TSC BEM GF EHM AEF),
  inhabited
    (@hom (Fiber (interp_ty I))
      (@interp_h_ctx Sign Func Pred HFunc HPred
        C CC TSC BEM GF EHM I G)
      (@interp_h_ty Sign Func Pred HFunc HPred
        C CC TSC BEM GF EHM I Phi)).

Theorem all_predicate_epsilonfull_soundness_completeness :
  forall (I : b_ty) (G : @h_context Sign Func Pred)
    (Phi : @h_ty Sign Func Pred),
  All_WellFormed I G ->
  WellFormed I Phi ->
  ((exists p : @h_tm Sign Func Pred,
      inhabited (h_derivation I G p Phi))
   <-> all_predicate_epsilonfull_valid I G Phi).
Proof.
  intros I G Phi HwfG HwfPhi.
  split.
  - intros [p [D]] C CC TSC BEM GF EHM AEF APM.
    constructor.
    exact (@soundness Sign Func Pred HFunc HPred SM
      C CC TSC BEM GF EHM AEF I G p Phi D).
  - intros Hvalid.
    eapply term_model_inhabited_to_derivation.
    + exact HwfG.
    + exact HwfPhi.
    + exact (Hvalid
        (Base_SetoidCategory Sign Func)
        (Base_CartesianCategory Sign Func)
        (Base_TwoSortCategory Sign Func)
        (Base_SyntacticEpsilonFullModel Sign Func)
        TermModel_GoodFibration
        TermModel_EpsilonHyperModel
        TermModel_AdjointEpsilonFullFibration
        TermModel_AllPredicateEpsilonFullModel).
Defined.

End AllPredicateValidity.
