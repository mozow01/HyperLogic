(* H3 and H5 specializations of the finite-valued epsilon characterization. *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Fibration.
Require Import HyperLogic.Cat.EpsilonSelection.

Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_Fibration.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_Soundness.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_AllPredicates.
Require Import HyperLogic.Semantics.EpsilonFull.FiniteHeytingPredicates.
Require Import HyperLogic.Semantics.EpsilonFull.Canonical_FiniteChain_Model.
Require Import HyperLogic.Semantics.EpsilonFull.LEM_disproved.
Require Import HyperLogic.Semantics.IFOL.DualDrinker.

Module OldH3 := HyperLogic.Semantics.EpsilonFull.LEM_disproved.
Module OldH5 := HyperLogic.Semantics.IFOL.DualDrinker.

Definition H3_eq_dec (x y : OldH3.H3) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition H3_le_dec (x y : OldH3.H3) :
  {OldH3.H3_le x y} + {~ OldH3.H3_le x y}.
Proof.
  destruct x, y; cbn; try (left; exact I); right; tauto.
Defined.

Definition H3FiniteHeytingAlgebra : FiniteHeytingAlgebra.
Proof.
  refine {|
    fh_carrier := OldH3.H3;
    fh_eq_dec := H3_eq_dec;
    fh_le := OldH3.H3_le;
    fh_le_dec := H3_le_dec;
    fh_le_refl := OldH3.H3_le_refl;
    fh_le_trans := _;
    fh_le_antisym := _;
    fh_bot := OldH3.HBot;
    fh_top := OldH3.HTop;
    fh_meet := OldH3.H3_meet;
    fh_join := OldH3.H3_join;
    fh_impl := OldH3.H3_impl;
    fh_bot_le := _;
    fh_le_top := _;
    fh_meet_le_l := _;
    fh_meet_le_r := _;
    fh_le_meet := _;
    fh_le_join_l := _;
    fh_le_join_r := _;
    fh_join_le := _;
    fh_impl_intro := _;
    fh_impl_elim := _;
    fh_enum := [OldH3.HBot; OldH3.HMid; OldH3.HTop];
    fh_enum_nodup := _;
    fh_enum_complete := _
  |}.
  - intros x y z Hxy Hyz. eapply OldH3.H3_le_trans; eassumption.
  - destruct x, y; cbn; intros; try contradiction; reflexivity.
  - destruct x; exact I.
  - destruct x; exact I.
  - destruct x, y; exact I.
  - destruct x, y; exact I.
  - destruct x, y, z; cbn; tauto.
  - destruct x, y; exact I.
  - destruct x, y; exact I.
  - destruct x, y, z; cbn; tauto.
  - destruct x, y, z; cbn; tauto.
  - destruct x, y, z; cbn; tauto.
  - apply NoDup_cons; [cbn; intuition congruence |].
    apply NoDup_cons; [cbn; intuition congruence |].
    apply NoDup_cons; [cbn; intuition congruence |].
    apply NoDup_nil.
  - intros x. destruct x; cbn; auto.
Defined.

Lemma H3_is_chain : @FiniteHeytingChain H3FiniteHeytingAlgebra.
Proof. intros x y. destruct x, y; cbn; auto. Defined.

Lemma H3_LEM_algebra_value :
  OldH3.H3_join OldH3.HMid
    (OldH3.H3_impl OldH3.HMid OldH3.HBot) = OldH3.HMid.
Proof. reflexivity. Defined.

Lemma H3_mid_not_top : OldH3.HMid <> OldH3.HTop.
Proof. discriminate. Defined.

Inductive H3CanonicalFunc : Type := .

Global Instance H3CanonicalFunctionSignature :
  FunctionSignature H3CanonicalFunc.
Proof. constructor; intro f; destruct f. Defined.

Inductive H3CanonicalPred : Type :=
| H3BoolAtom
| H3MidAtom.

Global Instance H3CanonicalPredicateSignature :
  PredicateSignature H3CanonicalPred :=
  {| pred_dom p :=
      match p with H3BoolAtom => b_S | H3MidAtom => b_Unit end |}.

Definition H3CanonicalFunctionValue (f : H3CanonicalFunc) :
  fh_base_denote (FHModelBase (func_dom f)) ->
  fh_base_denote (FHModelBase (func_cod f)).
Proof. destruct f. Defined.

Definition H3CanonicalPredicateValue (p : H3CanonicalPred) :
  fh_base_denote (FHModelBase (pred_dom p)) -> OldH3.H3.
Proof.
  destruct p; cbn [FHModelBase FHBaseTwoSort].
  - intro b. exact (if b then OldH3.HMid else OldH3.HBot).
  - intro u. exact OldH3.HMid.
Defined.

Lemma H3_bool_atom_is_nonconstant :
  H3CanonicalPredicateValue H3BoolAtom true = OldH3.HMid /\
  H3CanonicalPredicateValue H3BoolAtom false = OldH3.HBot /\
  OldH3.HMid <> OldH3.HBot.
Proof. repeat split; reflexivity || discriminate. Defined.

Definition H3CanonicalBaseModel :=
  @FHCanonicalBaseEpsilonFullModel H3FiniteHeytingAlgebra
    H3CanonicalFunc H3CanonicalPred
    H3CanonicalFunctionSignature H3CanonicalPredicateSignature
    H3CanonicalFunctionValue H3CanonicalPredicateValue.

Definition H3CanonicalCoherentModel :=
  @FHCanonicalCoherentBaseModel H3FiniteHeytingAlgebra
    H3CanonicalFunc H3CanonicalPred
    H3CanonicalFunctionSignature H3CanonicalPredicateSignature
    H3CanonicalFunctionValue H3CanonicalPredicateValue.

Definition H3CanonicalHyperModel :=
  @FHCanonicalEpsilonHyperModel H3FiniteHeytingAlgebra
    H3CanonicalFunc H3CanonicalPred
    H3CanonicalFunctionSignature H3CanonicalPredicateSignature
    H3CanonicalFunctionValue H3CanonicalPredicateValue.

Definition H3CanonicalAdjointModel :=
  @FHCanonicalAdjointEpsilonFullFibration H3FiniteHeytingAlgebra H3_is_chain
    H3CanonicalFunc H3CanonicalPred
    H3CanonicalFunctionSignature H3CanonicalPredicateSignature
    H3CanonicalFunctionValue H3CanonicalPredicateValue.

Definition H3CanonicalAllPredicateModel :=
  @FHCanonicalAllPredicateEpsilonFullModel H3FiniteHeytingAlgebra H3_is_chain
    H3CanonicalFunc H3CanonicalPred
    H3CanonicalFunctionSignature H3CanonicalPredicateSignature
    H3CanonicalFunctionValue H3CanonicalPredicateValue.

Definition H3CanonicalFullModel :=
  @FHCanonicalEpsilonFullModel H3FiniteHeytingAlgebra H3_is_chain
    H3CanonicalFunc H3CanonicalPred
    H3CanonicalFunctionSignature H3CanonicalPredicateSignature
    H3CanonicalFunctionValue H3CanonicalPredicateValue.

Definition H3DiagonalPredicate :
  @FHPredicate H3FiniteHeytingAlgebra (b_Prod b_S b_S) :=
  fun xa => if Bool.eqb (fst xa) (snd xa)
    then OldH3.HMid else OldH3.HBot.

Definition H3DiagonalSelector : FHBaseHom b_S b_S :=
  fh_maximum_selector
    (FHChainMaximumSelectionData H3_is_chain)
    b_S b_S H3DiagonalPredicate.

Theorem H3_diagonal_selector_is_identity :
  forall x : bool, H3DiagonalSelector x = x.
Proof. destruct x; reflexivity. Defined.

Theorem H3_diagonal_selector_is_maximum :
  FHPointwiseMaximum b_S b_S H3DiagonalPredicate H3DiagonalSelector.
Proof.
  apply (fh_maximum_selector_spec
    (FHChainMaximumSelectionData H3_is_chain)).
Defined.

Definition H3MidFormula :
  @h_ty (CFLabel (Func:=H3CanonicalFunc) (Pred:=H3CanonicalPred))
    H3CanonicalFunc H3CanonicalPred :=
  Ty_Atom H3MidAtom b_unit.

Definition H3LEMFormula :
  @h_ty (CFLabel (Func:=H3CanonicalFunc) (Pred:=H3CanonicalPred))
    H3CanonicalFunc H3CanonicalPred :=
  Ty_Sum H3MidFormula (Ty_Arrow H3MidFormula Ty_Void).

Theorem H3_canonical_LEM_value :
  FHPredicateValue
    (@interp_h_ty
      (CFLabel (Func:=H3CanonicalFunc) (Pred:=H3CanonicalPred))
      H3CanonicalFunc H3CanonicalPred
      H3CanonicalFunctionSignature H3CanonicalPredicateSignature
      FHBaseCategory FHBaseCartesian FHBaseTwoSort H3CanonicalBaseModel
      (@FHGoodFibration H3FiniteHeytingAlgebra)
      (@FHStrictGoodFibration H3FiniteHeytingAlgebra)
      H3CanonicalHyperModel b_Unit H3LEMFormula) tt = OldH3.HMid.
Proof. reflexivity. Defined.

Theorem H3_canonical_LEM_not_top :
  FHPredicateValue
    (@interp_h_ty
      (CFLabel (Func:=H3CanonicalFunc) (Pred:=H3CanonicalPred))
      H3CanonicalFunc H3CanonicalPred
      H3CanonicalFunctionSignature H3CanonicalPredicateSignature
      FHBaseCategory FHBaseCartesian FHBaseTwoSort H3CanonicalBaseModel
      (@FHGoodFibration H3FiniteHeytingAlgebra)
      (@FHStrictGoodFibration H3FiniteHeytingAlgebra)
      H3CanonicalHyperModel b_Unit H3LEMFormula) tt <>
  @fh_top H3FiniteHeytingAlgebra.
Proof. rewrite H3_canonical_LEM_value. discriminate. Defined.

Theorem H3_canonical_LEM_refuted :
  @hom
    (Fiber (@interp_ty FHBaseCategory FHBaseCartesian FHBaseTwoSort b_Unit))
    (@interp_h_ctx
      (CFLabel (Func:=H3CanonicalFunc) (Pred:=H3CanonicalPred))
      H3CanonicalFunc H3CanonicalPred
      H3CanonicalFunctionSignature H3CanonicalPredicateSignature
      FHBaseCategory FHBaseCartesian FHBaseTwoSort H3CanonicalBaseModel
      (@FHGoodFibration H3FiniteHeytingAlgebra)
      (@FHStrictGoodFibration H3FiniteHeytingAlgebra)
      H3CanonicalHyperModel b_Unit nil)
    (@interp_h_ty
      (CFLabel (Func:=H3CanonicalFunc) (Pred:=H3CanonicalPred))
      H3CanonicalFunc H3CanonicalPred
      H3CanonicalFunctionSignature H3CanonicalPredicateSignature
      FHBaseCategory FHBaseCartesian FHBaseTwoSort H3CanonicalBaseModel
      (@FHGoodFibration H3FiniteHeytingAlgebra)
      (@FHStrictGoodFibration H3FiniteHeytingAlgebra)
      H3CanonicalHyperModel b_Unit H3LEMFormula) -> False.
Proof.
  intro Hlem.
  cbn [Fiber FHGoodFibration FHPredicateCategory FHPredicateLe
    interp_h_ctx] in Hlem.
  specialize (Hlem tt).
  cbn [interp_h_ty FHPredicateBiClosed FHPredicateClosed
    FHPredicateCartesian Build_Thin_BiCCC Build_Thin_CCC Build_Thin_CC
    H3CanonicalHyperModel FHCanonicalAtom H3CanonicalPredicateValue
    FHCanonicalRawTermEval FHModelBase FHBaseTwoSort] in Hlem.
  exact Hlem.
Defined.

Definition H3CanonicalLEMDerivation : Type :=
  { p : @h_tm
      (CFLabel (Func:=H3CanonicalFunc) (Pred:=H3CanonicalPred))
      H3CanonicalFunc H3CanonicalPred &
    @h_derivation
      (CFLabel (Func:=H3CanonicalFunc) (Pred:=H3CanonicalPred))
      H3CanonicalFunc H3CanonicalPred
      H3CanonicalFunctionSignature H3CanonicalPredicateSignature
      (CFLabels.CanonicalSkolemMapping H3CanonicalFunc H3CanonicalPred)
      b_Unit nil p H3LEMFormula }.

Theorem H3_canonical_LEM_underivable : H3CanonicalLEMDerivation -> False.
Proof.
  intros [p d]. apply H3_canonical_LEM_refuted.
  exact (@soundness
    (CFLabel (Func:=H3CanonicalFunc) (Pred:=H3CanonicalPred))
    H3CanonicalFunc H3CanonicalPred
    H3CanonicalFunctionSignature H3CanonicalPredicateSignature
    (CFLabels.CanonicalSkolemMapping H3CanonicalFunc H3CanonicalPred)
    FHBaseCategory FHBaseCartesian FHBaseTwoSort H3CanonicalBaseModel
    (@FHGoodFibration H3FiniteHeytingAlgebra)
    (@FHStrictGoodFibration H3FiniteHeytingAlgebra)
    H3CanonicalHyperModel H3CanonicalAdjointModel
    b_Unit nil p H3LEMFormula d).
Defined.

Definition H5_eq_dec (x y : OldH5.H5) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition H5_le_dec (x y : OldH5.H5) :
  {OldH5.H5_le x y} + {~ OldH5.H5_le x y}.
Proof.
  destruct x, y; cbn; try (left; exact I); right; tauto.
Defined.

Definition H5FiniteHeytingAlgebra : FiniteHeytingAlgebra.
Proof.
  refine {|
    fh_carrier := OldH5.H5;
    fh_eq_dec := H5_eq_dec;
    fh_le := OldH5.H5_le;
    fh_le_dec := H5_le_dec;
    fh_le_refl := OldH5.H5_le_refl;
    fh_le_trans := _;
    fh_le_antisym := _;
    fh_bot := OldH5.HBot;
    fh_top := OldH5.HTop;
    fh_meet := OldH5.H5_meet;
    fh_join := OldH5.H5_join;
    fh_impl := OldH5.H5_impl;
    fh_bot_le := _;
    fh_le_top := _;
    fh_meet_le_l := _;
    fh_meet_le_r := _;
    fh_le_meet := _;
    fh_le_join_l := _;
    fh_le_join_r := _;
    fh_join_le := _;
    fh_impl_intro := _;
    fh_impl_elim := _;
    fh_enum := [OldH5.HBot; OldH5.H1; OldH5.H2; OldH5.H12; OldH5.HTop];
    fh_enum_nodup := _;
    fh_enum_complete := _
  |}.
  - intros x y z Hxy Hyz. eapply OldH5.H5_le_trans; eassumption.
  - destruct x, y; cbn; intros; try contradiction; reflexivity.
  - destruct x; exact I.
  - destruct x; exact I.
  - destruct x, y; exact I.
  - destruct x, y; exact I.
  - destruct x, y, z; cbn; tauto.
  - destruct x, y; exact I.
  - destruct x, y; exact I.
  - destruct x, y, z; cbn; tauto.
  - destruct x, y, z; cbn; tauto.
  - destruct x, y, z; cbn; tauto.
  - apply NoDup_cons; [cbn; intuition congruence |].
    apply NoDup_cons; [cbn; intuition congruence |].
    apply NoDup_cons; [cbn; intuition congruence |].
    apply NoDup_cons; [cbn; intuition congruence |].
    apply NoDup_cons; [cbn; intuition congruence |].
    apply NoDup_nil.
  - intros x. destruct x; cbn; intuition.
Defined.

Lemma H5_incomparable :
  ~ (@fh_le H5FiniteHeytingAlgebra OldH5.H1 OldH5.H2 \/
     @fh_le H5FiniteHeytingAlgebra OldH5.H2 OldH5.H1).
Proof. cbn. tauto. Defined.

Lemma H5_not_chain : ~ @FiniteHeytingChain H5FiniteHeytingAlgebra.
Proof.
  intro Hchain. apply H5_incomparable. apply Hchain.
Defined.

Lemma H5_incomparable_join :
  @fh_join H5FiniteHeytingAlgebra OldH5.H1 OldH5.H2 = OldH5.H12 /\
  OldH5.H12 <> OldH5.H1 /\ OldH5.H12 <> OldH5.H2.
Proof. repeat split; cbn; discriminate || reflexivity. Defined.

Definition H5ObstructionPredicate :
  @FHPredicate H5FiniteHeytingAlgebra (b_Prod b_Unit b_S) :=
  fun xb => if snd xb then OldH5.H1 else OldH5.H2.

Lemma H5_obstruction_has_no_maximum_selector :
  forall e : FHBaseHom b_Unit b_S,
  ~ @FHPointwiseMaximum H5FiniteHeytingAlgebra
      b_Unit b_S H5ObstructionPredicate e.
Proof.
  intros e Hmax. specialize (Hmax tt).
  destruct (e tt); cbn in Hmax; discriminate.
Defined.

Theorem H5_no_full_maximum_selection :
  ~ @FHMaximumSelectionProperty H5FiniteHeytingAlgebra.
Proof.
  intro Hsel. apply H5_not_chain.
  apply FHMaximumSelectionProperty_chain. exact Hsel.
Defined.

Theorem H5_no_all_predicate_epsilon_selection :
  ~ (forall (X A : b_ty)
      (Q : @FHPredicate H5FiniteHeytingAlgebra (b_Prod X A)),
      @EpsilonSelectionExists FHBaseCategory FHBaseCartesian
        (@FHGoodFibration H5FiniteHeytingAlgebra) X A Q).
Proof.
  intro Hall.
  destruct (Hall b_Unit b_S H5ObstructionPredicate) as [e He].
  apply (H5_obstruction_has_no_maximum_selector e).
  apply FHEpsilonSelection_to_PointwiseMaximum. exact He.
Defined.
