(** Chosen selection units for the epsilon-only calculus. *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import HyperLogic.Cat.Fibration.
Require Import HyperLogic.Cat.EpsilonSelection.
Require Import HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon.Epsilon_Syntax_Lemmas.
Require Import HyperLogic.Semantics.Epsilon.Epsilon_Fibration.
Require Import HyperLogic.Semantics.Epsilon.Epsilon_Soundness.

Section ChosenEpsilonUnits.
Context {Sign Func Pred : Type}.
Context `{HFunc : FunctionSignature Func}.
Context `{HPred : PredicateSignature Pred}.
Context {SM : SkolemMapping Sign Func Pred}.
Context {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}.
Context {BEM : @BaseEpsilonModel Sign Func HFunc C CC TSC}.
Context {GF : @GoodFibration C CC}.
Context {EHM : @EpsilonHyperModel Sign Func Pred HFunc HPred C CC TSC BEM GF}.

Definition EpsilonChosenSelectionUnits : Type :=
  forall (I A : b_ty) (Phi : @h_ty Sign Func Pred),
    WellFormed (b_Prod I A) Phi ->
    EpsilonSelectionUnit (interp_ty I) (interp_ty A)
      (interp_h_ty (b_Prod I A) Phi)
      (interp_tm (@BT_Const Sign Func HFunc I A (skolem_index A Phi))).

Definition epsilon_selected_iso
  (U : EpsilonChosenSelectionUnits)
  (I A : b_ty) (Phi : @h_ty Sign Func Pred)
  (wf : WellFormed (b_Prod I A) Phi) :
  @left_adj_obj _ _ _ pullback_has_left_adjoint
    (interp_h_ty (b_Prod I A) Phi)
  ≅O interp_h_ty I (eps_instance A Phi).
Proof.
  eapply iso_trans.
  - exact (epsilon_selection_from_unit
      (interp_ty I) (interp_ty A)
      (interp_h_ty (b_Prod I A) Phi)
      (interp_tm (@BT_Const Sign Func HFunc I A (skolem_index A Phi)))
      (U I A Phi wf)).
  - apply iso_sym.
    exact (form_subst_iso I (b_Prod I A)
      (b_pair b_id (b_const A (skolem_index A Phi)))
      (BT_Pair BT_Id BT_Const) Phi).
Defined.

Definition epsilon_functorial_from_units
  (U : EpsilonChosenSelectionUnits)
  (I A : b_ty) (Phi Psi : @h_ty Sign Func Pred)
  (wf_Phi : WellFormed (b_Prod I A) Phi)
  (wf_Psi : WellFormed (b_Prod I A) Psi)
  (H : interp_h_ty (b_Prod I A) Phi ≅O
       interp_h_ty (b_Prod I A) Psi) :
  interp_h_ty I (eps_instance A Phi) ≅O
  interp_h_ty I (eps_instance A Psi).
Proof.
  eapply iso_trans.
  - apply iso_sym. exact (epsilon_selected_iso U I A Phi wf_Phi).
  - eapply iso_trans.
    + apply sigma_iso_cong. exact H.
    + exact (epsilon_selected_iso U I A Psi wf_Psi).
Defined.

Definition epsilon_beck_chevalley_from_units
  (U : EpsilonChosenSelectionUnits)
  (I J A : b_ty) (g : @b_tm Sign Func)
  (dg : base_typing I g J) (Phi : @h_ty Sign Func Pred)
  (wf : WellFormed (b_Prod J A) Phi) :
  interp_h_ty I (form_subst g (eps_instance A Phi)) ≅O
  interp_h_ty I (eps_instance A (form_subst (b_subst_ext g) Phi)).
Proof.
  eapply iso_trans.
  - exact (form_subst_iso I J g dg (eps_instance A Phi)).
  - eapply iso_trans.
    + apply functor_iso_cong.
      apply iso_sym. exact (epsilon_selected_iso U J A Phi wf).
    + eapply iso_trans.
      * apply beck_chevalley_sigma.
      * eapply iso_trans.
        -- apply sigma_iso_cong.
           apply iso_sym.
           exact (form_subst_iso (b_Prod I A) (b_Prod J A)
             (b_subst_ext g) (typing_subst_ext dg) Phi).
        -- apply (epsilon_selected_iso U I A
             (form_subst (b_subst_ext g) Phi)).
           eapply wf_subst.
           ++ exact (typing_subst_ext dg).
           ++ exact wf.
Defined.

Definition epsilon_unit_from_units
  (U : EpsilonChosenSelectionUnits)
  (I A : b_ty) (Phi : @h_ty Sign Func Pred)
  (wf : WellFormed (b_Prod I A) Phi) :
  @hom (Fiber (interp_ty (b_Prod I A)))
    (interp_h_ty (b_Prod I A) Phi)
    (interp_h_ty (b_Prod I A) (form_subst b_fst (eps_instance A Phi))).
Proof.
  eapply compose.
  - exact (@iso_from _ _ _
      (form_subst_iso (b_Prod I A) I b_fst BT_Fst
        (eps_instance A Phi))).
  - eapply compose.
    + eapply fmap.
      exact (@iso_to _ _ _ (epsilon_selected_iso U I A Phi wf)).
    + exact (@unit _ _ _ pullback_has_left_adjoint
        (interp_h_ty (b_Prod I A) Phi)).
Defined.

Definition epsilon_intro_from_units
  (U : EpsilonChosenSelectionUnits)
  (I A : b_ty) (Phi : @h_ty Sign Func Pred) (f : @b_tm Sign Func)
  (wf : WellFormed (b_Prod I A) Phi)
  (df : base_typing I f A) :
  @hom (Fiber (interp_ty I))
    (interp_h_ty I (form_subst (b_pair b_id f) Phi))
    (interp_h_ty I (eps_instance A Phi)).
Proof.
  eapply compose.
  - exact (@iso_to _ _ _ (epsilon_selected_iso U I A Phi wf)).
  - eapply compose.
    + exact (@iso_to _ _ _
        (epsilon_section_reindex_iso (interp_ty I) (interp_ty A)
          (interp_tm df)
          (@left_adj_obj _ _ _ pullback_has_left_adjoint
            (interp_h_ty (b_Prod I A) Phi)))).
    + eapply compose.
      * eapply fmap.
        exact (@unit _ _ _ pullback_has_left_adjoint
          (interp_h_ty (b_Prod I A) Phi)).
      * exact (@iso_to _ _ _ (form_subst_iso I (b_Prod I A)
          (b_pair b_id f) (BT_Pair BT_Id df) Phi)).
Defined.

Definition epsilon_elim_from_units
  (U : EpsilonChosenSelectionUnits)
  (I A : b_ty) (G : @h_context Sign Func Pred)
  (Phi Chi : @h_ty Sign Func Pred)
  (wf_G : All_WellFormed I G)
  (wf_Phi : WellFormed (b_Prod I A) Phi)
  (wf_Chi : WellFormed I Chi)
  (h : @hom (Fiber (interp_ty (b_Prod I A)))
    (@prod (Fiber (interp_ty (b_Prod I A))) _
      (interp_h_ctx (b_Prod I A) (ctx_subst b_fst G))
      (interp_h_ty (b_Prod I A) Phi))
    (interp_h_ty (b_Prod I A) (form_subst b_fst Chi))) :
  @hom (Fiber (interp_ty I))
    (@prod (Fiber (interp_ty I)) _
      (interp_h_ctx I G) (interp_h_ty I (eps_instance A Phi)))
    (interp_h_ty I Chi).
Proof.
  eapply epsilon_selection_contextual_elimination.
  - exact (epsilon_selected_iso U I A Phi wf_Phi).
  - eapply compose.
    + exact (@iso_to _ _ _
        (form_subst_iso (b_Prod I A) I b_fst BT_Fst Chi)).
    + eapply compose.
      * exact h.
      * exact (@iso_from _ _ _
          (prod_iso_cong (ctx_subst_iso I A G)
            (iso_refl (interp_h_ty (b_Prod I A) Phi)))).
Defined.

Definition EpsilonGoodFibration_from_chosen_units
  (U : EpsilonChosenSelectionUnits) : EpsilonGoodFibration.
Proof.
  refine {|
    eps_unit := epsilon_unit_from_units U;
    eps_intro := epsilon_intro_from_units U;
    eps_elim_frobenius := epsilon_elim_from_units U;
    eps_functorial_iso := epsilon_functorial_from_units U;
    eps_beck_chevalley_iso := epsilon_beck_chevalley_from_units U
  |}.
Defined.

Definition EpsilonChosenSelectionUnits_from_model
  (M : EpsilonGoodFibration) : EpsilonChosenSelectionUnits.
Proof.
  intros I A Phi wf.
  eapply compose.
  - eapply fmap.
    exact (@iso_to _ _ _
      (form_subst_iso I (b_Prod I A)
        (b_pair b_id (b_const A (skolem_index A Phi)))
        (BT_Pair BT_Id BT_Const) Phi)).
  - eapply compose.
    + exact (@iso_to _ _ _
        (form_subst_iso (b_Prod I A) I b_fst BT_Fst
          (eps_instance A Phi))).
    + exact (@eps_unit Sign Func Pred HFunc HPred SM
        C CC TSC BEM GF EHM M I A Phi wf).
Defined.

End ChosenEpsilonUnits.
