(* A semantic countermodel for base-level epsilon substitutivity. *)

Require Import Coq.Bool.Bool.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Equality.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import HyperLogic.Cat.Fibration.

Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.
Require Import HyperLogic.Semantics.EpsilonFull.Base_EpsilonFull_Soundness.
Require Import HyperLogic.Semantics.EpsilonFull.Base_EpsilonFull_Completeness.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_Fibration.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_ModelCategory.
Require Import HyperLogic.Semantics.EpsilonFull.LEM_disproved.

Module EpsilonFullSubstitutivity.

Inductive TestFunc : Type := .

Definition test_func_dom (f : TestFunc) : b_ty := match f with end.
Definition test_func_cod (f : TestFunc) : b_ty := match f with end.

Instance TestFunctionSignature : FunctionSignature TestFunc :=
  {| func_dom := test_func_dom; func_cod := test_func_cod |}.

Instance TestPredicateSignature : PredicateSignature Datatypes.unit :=
  {| pred_dom _ := b_S |}.

(* The epsilon signature is the inductive closure of formula-indexed names. *)
Inductive TestSign : Type :=
| test_skolem : forall (A : b_ty), @h_ty TestSign TestFunc Datatypes.unit -> TestSign.

Instance TestSkolemMapping : SkolemMapping TestSign TestFunc Datatypes.unit.
Proof.
  refine {| skolem_index := test_skolem |}.
  intros A B Phi Psi H.
  inversion H.
  split; reflexivity.
Defined.

Definition test_g : @b_tm TestSign TestFunc :=
  b_const b_S (skolem_index b_S Ty_Unit).

Definition test_g_typing :
  @base_typing TestSign TestFunc TestFunctionSignature b_Unit test_g b_S :=
  BT_Const.

Definition test_Phi : @h_ty TestSign TestFunc Datatypes.unit :=
  Ty_Atom tt b_fst.

Definition test_Phi_wellformed :
  @WellFormed TestSign TestFunc Datatypes.unit
    TestFunctionSignature TestPredicateSignature
    (b_Prod b_S b_S) test_Phi :=
  WF_Atom (b_Prod b_S b_S) tt b_fst BT_Fst.

Definition test_Phi_sub : @h_ty TestSign TestFunc Datatypes.unit :=
  form_subst (b_subst_ext test_g) test_Phi.

Definition test_Phi_sub_wellformed :
  @WellFormed TestSign TestFunc Datatypes.unit
    TestFunctionSignature TestPredicateSignature
    (b_Prod b_Unit b_S) test_Phi_sub.
Proof.
  unfold test_Phi_sub, test_Phi, b_subst_ext.
  apply WF_Atom.
  refine (@BT_Comp TestSign TestFunc TestFunctionSignature
    (b_Prod b_Unit b_S) (b_Prod b_S b_S) b_S
    b_fst
    (b_pair (b_comp test_g b_fst) b_snd)
    (@BT_Fst TestSign TestFunc TestFunctionSignature b_S b_S)
    _).
  refine (@BT_Pair TestSign TestFunc TestFunctionSignature
    (b_Prod b_Unit b_S) b_S b_S
    (b_comp test_g b_fst) b_snd _
    (@BT_Snd TestSign TestFunc TestFunctionSignature b_Unit b_S)).
  exact (@BT_Comp TestSign TestFunc TestFunctionSignature
    (b_Prod b_Unit b_S) b_Unit b_S
    test_g b_fst test_g_typing
    (@BT_Fst TestSign TestFunc TestFunctionSignature b_Unit b_S)).
Defined.

Definition test_eps_sub : @b_tm TestSign TestFunc :=
  b_const b_S (skolem_index b_S test_Phi_sub).

Definition test_eps_comp : @b_tm TestSign TestFunc :=
  b_comp (b_const b_S (skolem_index b_S test_Phi)) test_g.

Definition test_eps_sub_typing :
  @base_typing TestSign TestFunc TestFunctionSignature b_Unit test_eps_sub b_S :=
  BT_Const.

Definition test_eps_comp_typing :
  @base_typing TestSign TestFunc TestFunctionSignature b_Unit test_eps_comp b_S :=
  BT_Comp BT_Const BT_Const.

Definition test_substitutivity_judgement : Prop :=
  test_eps_sub ≡_[b_Unit,b_S] test_eps_comp.

(* A finite Cartesian base in which the individual sort is [bool]. *)
Inductive FinObj : Type :=
| F_Unit : FinObj
| F_Bool : FinObj
| F_Prod : FinObj -> FinObj -> FinObj.

Fixpoint fin_carrier (A : FinObj) : Type :=
  match A with
  | F_Unit => Datatypes.unit
  | F_Bool => bool
  | F_Prod A B => (fin_carrier A * fin_carrier B)%type
  end.

Definition FinHom (A B : FinObj) : Type := fin_carrier A -> fin_carrier B.
Definition FinEquiv {A B : FinObj} (f g : FinHom A B) : Prop :=
  forall x, f x = g x.

Ltac fin_crush :=
  repeat intro;
  repeat match goal with
  | |- Proper _ _ => red
  | |- respectful _ _ _ _ => red
  | |- RelationClasses.Equivalence _ => split; red
  end;
  repeat intro;
  simpl in *;
  auto;
  try congruence.

Instance Fin_Setoid : SetoidCategory.
Proof.
  refine (mk_SetoidCategory FinObj FinHom
    (fun A x => x)
    (fun A B C f g x => f (g x))
    (@FinEquiv)
    _ _ _ _ _).
  Unshelve. all: fin_crush.
Defined.

Instance Fin_Cartesian : CartesianCategory Fin_Setoid.
Proof.
  refine (mk_CartesianCategory Fin_Setoid
    F_Unit (fun A x => tt) _
    F_Prod (fun A B C f g x => (f x, g x))
    (fun A B xy => fst xy) (fun A B xy => snd xy)
    _ _ _ _).
  Unshelve.
  all: fin_crush.
  - destruct (f x0). reflexivity.
  - destruct (h x0). reflexivity.
Defined.

Instance Fin_TwoSort : TwoSortCategory Fin_Setoid.
Proof.
  refine (mk_TwoSortCategory Fin_Setoid Fin_Cartesian F_Bool _).
  discriminate.
Defined.

Lemma fin_equiv_refl : forall {A B : FinObj} (f : FinHom A B),
  @hom_equiv Fin_Setoid A B f f.
Proof.
  intros A B f x.
  reflexivity.
Defined.

Fixpoint fin_interp_ty (A : b_ty) : FinObj :=
  match A with
  | b_Unit => F_Unit
  | b_S => F_Bool
  | b_Prod A B => F_Prod (fin_interp_ty A) (fin_interp_ty B)
  end.

Lemma interp_ty_fin : forall A,
  @interp_ty Fin_Setoid Fin_Cartesian Fin_TwoSort A = fin_interp_ty A.
Proof.
  intros A.
  induction A; simpl; congruence.
Defined.

Fixpoint fin_default (A : b_ty) : fin_carrier (fin_interp_ty A) :=
  match A with
  | b_Unit => tt
  | b_S => false
  | b_Prod A B => (fin_default A, fin_default B)
  end.

Definition selected_epsilon_sign : TestSign :=
  skolem_index b_S test_Phi_sub.

Definition fin_epsilon_value (s : TestSign) : bool :=
  match s with
  | test_skolem b_S
      (Ty_Atom tt
        (b_comp b_fst
          (b_pair (b_comp (b_const b_S (test_skolem b_S Ty_Unit)) b_fst) b_snd))) => true
  | _ => false
  end.

Definition fin_const (I A : b_ty) (s : TestSign) :
  FinHom (fin_interp_ty I) (fin_interp_ty A) :=
  match A return FinHom (fin_interp_ty I) (fin_interp_ty A) with
  | b_Unit => fun _ => tt
  | b_S => fun _ => fin_epsilon_value s
  | b_Prod A B => fun _ => fin_default (b_Prod A B)
  end.

Instance Fin_BaseModel :
  @BaseEpsilonFullModel TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort.
Proof.
  constructor.
  - intros I A s.
    rewrite (interp_ty_fin I), (interp_ty_fin A).
    exact (fin_const I A s).
  - intros f. destruct f.
Defined.

Instance Fin_CoherentBaseModel :
  @CoherentBaseModel TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort Fin_BaseModel.
Proof.
  constructor.
  intros A B f d1.
  induction d1; intros d2; dependent destruction d2.
  - apply fin_equiv_refl.
  - assert (H_B : B = B0).
    { eapply base_typing_unique. exact d1_2. exact d2_2. }
    subst B0.
    apply comp_proper.
    + apply IHd1_1.
    + apply IHd1_2.
  - apply fin_equiv_refl.
  - apply prod_map_proper_ax.
    + apply IHd1_1.
    + apply IHd1_2.
  - apply fin_equiv_refl.
  - apply fin_equiv_refl.
  - apply fin_equiv_refl.
  - destruct f.
Defined.

Lemma interp_test_eps_sub :
  @interp_tm TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort Fin_BaseModel
    b_Unit b_S test_eps_sub test_eps_sub_typing =
  (fun _ : Datatypes.unit => true).
Proof. reflexivity. Defined.

Lemma interp_test_eps_comp :
  @interp_tm TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort Fin_BaseModel
    b_Unit b_S test_eps_comp test_eps_comp_typing =
  (fun _ : Datatypes.unit => false).
Proof. reflexivity. Defined.

Lemma finite_base_countermodel :
  ~ (@interp_tm TestSign TestFunc TestFunctionSignature
       Fin_Setoid Fin_Cartesian Fin_TwoSort Fin_BaseModel
       b_Unit b_S test_eps_sub test_eps_sub_typing
     ≅
     @interp_tm TestSign TestFunc TestFunctionSignature
       Fin_Setoid Fin_Cartesian Fin_TwoSort Fin_BaseModel
       b_Unit b_S test_eps_comp test_eps_comp_typing).
Proof.
  intro H.
  rewrite interp_test_eps_sub in H.
  rewrite interp_test_eps_comp in H.
  specialize (H tt).
  discriminate H.
Defined.

(* This is the syntactic conclusion: the finite semantic separation is fed
   through base soundness, so no base-term equality derivation can exist. *)
Theorem test_substitutivity_not_derivable :
  ~ test_substitutivity_judgement.
Proof.
  intro H.
  apply finite_base_countermodel.
  eapply (@base_soundness_equational
    TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort Fin_BaseModel Fin_CoherentBaseModel
    b_Unit b_S test_eps_sub test_eps_comp
    test_eps_sub_typing test_eps_comp_typing).
  exact H.
Defined.

(* The H3 fiber from [LEM_disproved] is constant over this finite base.
   Consequently it validates the full EpsilonFull fibration interface while
   leaving the interpretation of base epsilon constants unconstrained. *)
Instance Fin_H3_GoodFibration : GoodFibration Fin_Setoid.
Proof.
  refine {|
    Fiber := fun _ => H3_Setoid;
    fiber_is_thin := fun _ _ _ _ _ => I;
    Fiber_is_Cartesian := fun _ => H3_Cartesian;
    Fiber_is_Closed := fun _ => H3_Closed;
    Fiber_is_BiClosed := fun _ => H3_BiClosed;
    Pullback := fun _ _ _ => H3_IdentityFunctor;
    pullback_has_left_adjoint := fun _ _ => H3_AdjointR;
    pullback_has_right_adjoint := fun _ _ => H3_AdjointL
  |}.
  Unshelve. all: intros; h3_crush. all: reflexivity.
Defined.

Instance Fin_H3_StrictGoodFibration :
  StrictGoodFibration Fin_Setoid Fin_H3_GoodFibration.
Proof.
  econstructor.
  intros X Y M1 M2 Heq.
  assert (H_sym : h_base M2 ≅ h_base M1) by (symmetry; exact Heq).
  exists H_sym.
  exact I.
Defined.

Definition Fin_H3_EpsilonHyperModel_for
  (BEM : @BaseEpsilonFullModel TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort) :
  @EpsilonHyperModel TestSign TestFunc Datatypes.unit
    TestFunctionSignature TestPredicateSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort BEM
    Fin_H3_GoodFibration Fin_H3_StrictGoodFibration.
Proof.
  unshelve econstructor.
  - exact (fun _ _ _ => HMid).
  - intros. reflexivity.
  - intros. reflexivity.
Defined.

Instance Fin_H3_EpsilonHyperModel :
  @EpsilonHyperModel TestSign TestFunc Datatypes.unit
    TestFunctionSignature TestPredicateSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort Fin_BaseModel
    Fin_H3_GoodFibration Fin_H3_StrictGoodFibration :=
  Fin_H3_EpsilonHyperModel_for Fin_BaseModel.

Lemma fin_H3_interp_h_ty_subst_const
  (BEM : @BaseEpsilonFullModel TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort) :
  forall (I J : b_ty) (Phi : @h_ty TestSign TestFunc Datatypes.unit)
    (f : @b_tm TestSign TestFunc),
  @interp_h_ty TestSign TestFunc Datatypes.unit
    TestFunctionSignature TestPredicateSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort BEM
    Fin_H3_GoodFibration Fin_H3_StrictGoodFibration
    (Fin_H3_EpsilonHyperModel_for BEM)
    I (form_subst f Phi)
  =
  @interp_h_ty TestSign TestFunc Datatypes.unit
    TestFunctionSignature TestPredicateSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort BEM
    Fin_H3_GoodFibration Fin_H3_StrictGoodFibration
    (Fin_H3_EpsilonHyperModel_for BEM)
    J Phi.
Proof.
  intros I J Phi.
  revert I J.
  induction Phi; intros I J f; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (IHPhi1 I J f).
    rewrite (IHPhi2 I J f).
    reflexivity.
  - rewrite (IHPhi1 I J f).
    rewrite (IHPhi2 I J f).
    reflexivity.
  - rewrite (IHPhi1 I J f).
    rewrite (IHPhi2 I J f).
    reflexivity.
  - reflexivity.
  - rewrite (IHPhi (b_Prod I b) (b_Prod J b) (b_subst_ext f)).
    reflexivity.
  - rewrite (IHPhi (b_Prod I b) (b_Prod J b) (b_subst_ext f)).
    reflexivity.
Defined.

Definition Fin_H3_AdjointEpsilonFullFibration_for
  (BEM : @BaseEpsilonFullModel TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort) :
  @AdjointEpsilonFullFibration TestSign TestFunc Datatypes.unit
    TestFunctionSignature TestPredicateSignature TestSkolemMapping
    Fin_Setoid Fin_Cartesian Fin_TwoSort BEM
    Fin_H3_GoodFibration Fin_H3_StrictGoodFibration
    (Fin_H3_EpsilonHyperModel_for BEM).
Proof.
  constructor.
  - intros I A Phi Hwf_Phi.
    cbn [left_adj_obj pullback_has_left_adjoint
      Fin_H3_GoodFibration H3_AdjointR].
    rewrite (@fin_H3_interp_h_ty_subst_const BEM
      I (b_Prod I A) Phi
      (b_pair b_id (b_const A (skolem_index A Phi)))).
    reflexivity.
  - intros I A Phi Psi Hwf_Phi Hwf_Psi H_iso.
    rewrite (@fin_H3_interp_h_ty_subst_const BEM
      I (b_Prod I A) Phi
      (b_pair b_id (b_const A (skolem_index A Phi)))).
    rewrite (@fin_H3_interp_h_ty_subst_const BEM
      I (b_Prod I A) Psi
      (b_pair b_id (b_const A (skolem_index A Psi)))).
    exact H_iso.
Defined.

Instance Fin_H3_AdjointEpsilonFullFibration :
  @AdjointEpsilonFullFibration TestSign TestFunc Datatypes.unit
    TestFunctionSignature TestPredicateSignature TestSkolemMapping
    Fin_Setoid Fin_Cartesian Fin_TwoSort Fin_BaseModel
    Fin_H3_GoodFibration Fin_H3_StrictGoodFibration Fin_H3_EpsilonHyperModel :=
  Fin_H3_AdjointEpsilonFullFibration_for
    Fin_BaseModel.

Definition separating_EpsilonFullModel :
  @EpsilonFullModel TestSign TestFunc Datatypes.unit
    TestFunctionSignature TestPredicateSignature TestSkolemMapping :=
  {| efm_cat := Fin_Setoid;
     efm_cartesian := Fin_Cartesian;
     efm_twosort := Fin_TwoSort;
     efm_base_model := Fin_BaseModel;
     efm_base_coherent := Fin_CoherentBaseModel;
     efm_good_fibration := Fin_H3_GoodFibration;
     efm_strict_fibration := Fin_H3_StrictGoodFibration;
     efm_hyper_model := Fin_H3_EpsilonHyperModel;
     efm_adjoint_epsilon := Fin_H3_AdjointEpsilonFullFibration |}.

Definition test_substitutivity_valid_in
  (M : @EpsilonFullModel TestSign TestFunc Datatypes.unit
    TestFunctionSignature TestPredicateSignature TestSkolemMapping) : Prop :=
  EpsilonFull_ModelCategory.efm_interp_tm M test_eps_sub_typing
  ≅
  EpsilonFull_ModelCategory.efm_interp_tm M test_eps_comp_typing.

Theorem finite_hyperdoctrine_countermodel :
  ~ (@interp_tm TestSign TestFunc TestFunctionSignature
       Fin_Setoid Fin_Cartesian Fin_TwoSort Fin_BaseModel
       b_Unit b_S test_eps_sub test_eps_sub_typing
     ≅
     @interp_tm TestSign TestFunc TestFunctionSignature
       Fin_Setoid Fin_Cartesian Fin_TwoSort Fin_BaseModel
       b_Unit b_S test_eps_comp test_eps_comp_typing).
Proof. exact finite_base_countermodel. Defined.

(* A second, equally valid EpsilonFull hyperdoctrine uses a uniform default
   value for every base epsilon constant.  It validates the same equation. *)
Definition uniform_fin_const (I A : b_ty) (_ : TestSign) :
  FinHom (fin_interp_ty I) (fin_interp_ty A) :=
  match A return FinHom (fin_interp_ty I) (fin_interp_ty A) with
  | b_Unit => fun _ => tt
  | b_S => fun _ => false
  | b_Prod A B => fun _ => fin_default (b_Prod A B)
  end.

Definition UniformFin_BaseModel :
  @BaseEpsilonFullModel TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort.
Proof.
  constructor.
  - intros I A s.
    rewrite (interp_ty_fin I), (interp_ty_fin A).
    exact (uniform_fin_const I A s).
  - intros f. destruct f.
Defined.

Definition UniformFin_CoherentBaseModel :
  @CoherentBaseModel TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort UniformFin_BaseModel.
Proof.
  constructor.
  intros A B f d1.
  induction d1; intros d2; dependent destruction d2.
  - apply fin_equiv_refl.
  - assert (H_B : B = B0).
    { eapply base_typing_unique. exact d1_2. exact d2_2. }
    subst B0.
    apply comp_proper.
    + apply IHd1_1.
    + apply IHd1_2.
  - apply fin_equiv_refl.
  - apply prod_map_proper_ax.
    + apply IHd1_1.
    + apply IHd1_2.
  - apply fin_equiv_refl.
  - apply fin_equiv_refl.
  - apply fin_equiv_refl.
  - destruct f.
Defined.

Definition UniformFin_H3_EpsilonHyperModel :
  @EpsilonHyperModel TestSign TestFunc Datatypes.unit
    TestFunctionSignature TestPredicateSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort UniformFin_BaseModel
    Fin_H3_GoodFibration Fin_H3_StrictGoodFibration :=
  Fin_H3_EpsilonHyperModel_for UniformFin_BaseModel.

Definition UniformFin_H3_AdjointEpsilonFullFibration :
  @AdjointEpsilonFullFibration TestSign TestFunc Datatypes.unit
    TestFunctionSignature TestPredicateSignature TestSkolemMapping
    Fin_Setoid Fin_Cartesian Fin_TwoSort UniformFin_BaseModel
    Fin_H3_GoodFibration Fin_H3_StrictGoodFibration
    UniformFin_H3_EpsilonHyperModel :=
  Fin_H3_AdjointEpsilonFullFibration_for UniformFin_BaseModel.

Definition uniform_EpsilonFullModel :
  @EpsilonFullModel TestSign TestFunc Datatypes.unit
    TestFunctionSignature TestPredicateSignature TestSkolemMapping :=
  {| efm_cat := Fin_Setoid;
     efm_cartesian := Fin_Cartesian;
     efm_twosort := Fin_TwoSort;
     efm_base_model := UniformFin_BaseModel;
     efm_base_coherent := UniformFin_CoherentBaseModel;
     efm_good_fibration := Fin_H3_GoodFibration;
     efm_strict_fibration := Fin_H3_StrictGoodFibration;
     efm_hyper_model := UniformFin_H3_EpsilonHyperModel;
     efm_adjoint_epsilon := UniformFin_H3_AdjointEpsilonFullFibration |}.

Lemma uniform_interp_test_eps_sub :
  @interp_tm TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort UniformFin_BaseModel
    b_Unit b_S test_eps_sub test_eps_sub_typing =
  (fun _ : Datatypes.unit => false).
Proof. reflexivity. Defined.

Lemma uniform_interp_test_eps_comp :
  @interp_tm TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort UniformFin_BaseModel
    b_Unit b_S test_eps_comp test_eps_comp_typing =
  (fun _ : Datatypes.unit => false).
Proof. reflexivity. Defined.

Theorem uniform_hyperdoctrine_validates_substitutivity :
  @interp_tm TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort UniformFin_BaseModel
    b_Unit b_S test_eps_sub test_eps_sub_typing
  ≅
  @interp_tm TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort UniformFin_BaseModel
    b_Unit b_S test_eps_comp test_eps_comp_typing.
Proof.
  rewrite uniform_interp_test_eps_sub.
  rewrite uniform_interp_test_eps_comp.
  intro x.
  reflexivity.
Defined.

Theorem separating_model_refutes_substitutivity :
  ~ test_substitutivity_valid_in separating_EpsilonFullModel.
Proof. exact finite_hyperdoctrine_countermodel. Defined.

Theorem uniform_model_validates_substitutivity :
  test_substitutivity_valid_in uniform_EpsilonFullModel.
Proof. exact uniform_hyperdoctrine_validates_substitutivity. Defined.

End EpsilonFullSubstitutivity.
