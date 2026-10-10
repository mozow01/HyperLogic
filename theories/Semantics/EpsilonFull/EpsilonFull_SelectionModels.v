(** Chosen selection units for the EpsilonFull semantic interface. *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.Adjoint.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Fibration.
Require Import HyperLogic.Cat.EpsilonSelection.
Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_Fibration.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_Soundness.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_ModelCategory.

Section ChosenSelectionModels.
Context {Sign Func Pred : Type}.
Context `{HFunc : FunctionSignature Func}.
Context `{HPred : PredicateSignature Pred}.
Context {SM : SkolemMapping Sign Func Pred}.
Context {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}.
Context {BEM : @BaseEpsilonFullModel Sign Func HFunc C CC TSC}.
Context {GF : @GoodFibration C CC}.
Context {EHM : @EpsilonHyperModel Sign Func Pred HFunc HPred C CC TSC BEM GF}.

Definition selected_witness (A : b_ty) (Phi : @h_ty Sign Func Pred) :
  @b_tm Sign Func := b_const A (skolem_index A Phi).

Definition selected_section (I A : b_ty) (Phi : @h_ty Sign Func Pred) :
  @hom C (interp_ty I) (@prod C CC (interp_ty I) (interp_ty A)) :=
  epsilon_section (interp_ty I) (interp_ty A)
    (interp_tm (@BT_Const Sign Func HFunc I A (skolem_index A Phi))).

Definition selected_section_projection
  (I A : b_ty) (Phi : @h_ty Sign Func Pred) :
  @compose C _ _ _ (@prod_fst C CC (interp_ty I) (interp_ty A))
    (selected_section I A Phi) ≅ @id C (interp_ty I).
Proof. apply prod_map_fst. Defined.

Definition selected_instance_interpretation
  (I A : b_ty) (Phi : @h_ty Sign Func Pred) :
  interp_h_ty I
    (form_subst (b_pair b_id (selected_witness A Phi)) Phi)
  ≅O
  @fobj _ _ (Pullback (selected_section I A Phi))
    (interp_h_ty (b_Prod I A) Phi) :=
  form_subst_iso I (b_Prod I A)
    (b_pair b_id (selected_witness A Phi))
    (BT_Pair BT_Id BT_Const) Phi.

Definition FullChosenSelectionUnits : Type :=
  forall (I A : b_ty) (Phi : @h_ty Sign Func Pred),
    WellFormed (b_Prod I A) Phi ->
    EpsilonSelectionUnit (interp_ty I) (interp_ty A)
      (interp_h_ty (b_Prod I A) Phi)
      (interp_tm (@BT_Const Sign Func HFunc I A (skolem_index A Phi))).

Definition full_selection_iso
  (U : FullChosenSelectionUnits)
  (I A : b_ty) (Phi : @h_ty Sign Func Pred)
  (wf : WellFormed (b_Prod I A) Phi) :
  @left_adj_obj _ _ _ pullback_has_left_adjoint
    (interp_h_ty (b_Prod I A) Phi)
  ≅O
  interp_h_ty I
    (form_subst (b_pair b_id (selected_witness A Phi)) Phi).
Proof.
  eapply iso_trans.
  - exact (epsilon_selection_from_unit
      (interp_ty I) (interp_ty A)
      (interp_h_ty (b_Prod I A) Phi)
      (interp_tm (@BT_Const Sign Func HFunc I A (skolem_index A Phi)))
      (U I A Phi wf)).
  - apply iso_sym.
    exact (form_subst_iso I (b_Prod I A)
      (b_pair b_id (selected_witness A Phi))
      (BT_Pair BT_Id BT_Const) Phi).
Defined.

Definition FullModelFromChosenSelectionUnits
  (U : FullChosenSelectionUnits) : AdjointEpsilonFullFibration.
Proof.
  refine {| eps_is_left_adj_obj := full_selection_iso U;
            eps_functorial := _ |}.
  apply eps_functorial_from_eps_is_left_adj_obj.
  exact (full_selection_iso U).
Defined.

Definition FullChosenSelectionUnitsFromModel
  (F : AdjointEpsilonFullFibration) : FullChosenSelectionUnits.
Proof.
  intros I A Phi wf.
  apply epsilon_selection_to_unit.
  eapply iso_trans.
  - exact (@eps_is_left_adj_obj Sign Func Pred HFunc HPred SM
      C CC TSC BEM GF EHM F I A Phi wf).
  - exact (form_subst_iso I (b_Prod I A)
      (b_pair b_id (selected_witness A Phi))
      (BT_Pair BT_Id BT_Const) Phi).
Defined.
End ChosenSelectionModels.

Section PackagedFullModel.
Context {Sign Func Pred : Type}.
Context `{HFunc : FunctionSignature Func}.
Context `{HPred : PredicateSignature Pred}.
Context {SM : SkolemMapping Sign Func Pred}.
Context {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}.
Context {BEM : @BaseEpsilonFullModel Sign Func HFunc C CC TSC}.
Context {CBM : @CoherentBaseModel Sign Func HFunc C CC TSC BEM}.
Context {GF : @GoodFibration C CC}.
Context {EHM : @EpsilonHyperModel Sign Func Pred HFunc HPred C CC TSC BEM GF}.

Definition EpsilonFullModel_from_chosen_units
  (U : @FullChosenSelectionUnits Sign Func Pred HFunc HPred SM
    C CC TSC BEM GF EHM) :
  @EpsilonFullModel Sign Func Pred HFunc HPred SM :=
  {| efm_cat := C;
     efm_cartesian := CC;
     efm_twosort := TSC;
     efm_base_model := BEM;
     efm_base_coherent := CBM;
     efm_good_fibration := GF;
     efm_hyper_model := EHM;
     efm_adjoint_epsilon := FullModelFromChosenSelectionUnits U |}.
End PackagedFullModel.
