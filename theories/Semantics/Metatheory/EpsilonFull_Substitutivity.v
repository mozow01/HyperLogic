(** A semantic countermodel for base-level epsilon substitutivity. *)

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
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax_Lemmas.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Canonical_Skolem.
Require Import HyperLogic.Semantics.EpsilonFull.Base_EpsilonFull_Soundness.
Require Import HyperLogic.Semantics.EpsilonFull.Base_EpsilonFull_Completeness.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_Fibration.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_ModelCategory.
Require Import HyperLogic.Semantics.EpsilonFull.LEM_disproved.

Module EpsilonFullSubstitutivity.

(* These are properties of the existing calculus, not additional rules. *)
Definition DefinitionalSubstitutivity
  {Sign Func Pred : Type} `{FunctionSignature Func}
  `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred} : Prop :=
  forall (I J A : b_ty) (g : @b_tm Sign Func)
    (dg : base_typing I g J) (Phi : @h_ty Sign Func Pred)
    (wf : WellFormed (b_Prod J A) Phi),
    @base_equiv_typed Sign Func H I A
      (b_const A (skolem_index A (form_subst (b_subst_ext g) Phi)))
      (b_comp (b_const A (skolem_index A Phi)) g).

Definition DefinitionalExtensionality
  {Sign Func Pred : Type} `{FunctionSignature Func}
  `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred} : Prop :=
  forall (I A : b_ty) (Phi Psi : @h_ty Sign Func Pred)
    (wf_Phi : WellFormed (b_Prod I A) Phi)
    (wf_Psi : WellFormed (b_Prod I A) Psi),
    form_equiv (b_Prod I A) Phi Psi ->
    @base_equiv_typed Sign Func H I A
      (b_const A (skolem_index A Phi))
      (b_const A (skolem_index A Psi)).

Module CanonicalLabels :=
  HyperLogic.Logic.Hyper.EpsilonFull.Canonical_Skolem.CanonicalEpsilonFull.

Inductive TestFunc : Type := .

Definition counterexample_func_dom (f : TestFunc) : b_ty := match f with end.
Definition counterexample_func_cod (f : TestFunc) : b_ty := match f with end.

Instance TestFunctionSignature : FunctionSignature TestFunc :=
  {| func_dom := counterexample_func_dom; func_cod := counterexample_func_cod |}.

Instance TestPredicateSignature : PredicateSignature Datatypes.unit :=
  {| pred_dom _ := b_S |}.

(* The test uses the general canonical closure, specialized to its signature. *)
Definition TestSign : Type :=
  CanonicalLabels.EpsilonLabel TestFunc Datatypes.unit.

Notation counterexample_skolem := CanonicalLabels.epsilon_label.

Instance TestSkolemMapping : SkolemMapping TestSign TestFunc Datatypes.unit :=
  CanonicalLabels.CanonicalSkolemMapping TestFunc Datatypes.unit.

Definition counterexample_substitution : @b_tm TestSign TestFunc :=
  b_const b_S (skolem_index b_S Ty_Unit).

Definition counterexample_substitution_typing :
  @base_typing TestSign TestFunc TestFunctionSignature b_Unit counterexample_substitution b_S :=
  BT_Const.

Definition substitution_counterexample_formula : @h_ty TestSign TestFunc Datatypes.unit :=
  Ty_Atom tt b_fst.

Definition substitution_counterexample_formula_wellformed :
  @WellFormed TestSign TestFunc Datatypes.unit
    TestFunctionSignature TestPredicateSignature
    (b_Prod b_S b_S) substitution_counterexample_formula :=
  WF_Atom (b_Prod b_S b_S) tt b_fst BT_Fst.

Definition substituted_counterexample_formula : @h_ty TestSign TestFunc Datatypes.unit :=
  form_subst (b_subst_ext counterexample_substitution) substitution_counterexample_formula.

Definition substituted_counterexample_formula_wellformed :
  @WellFormed TestSign TestFunc Datatypes.unit
    TestFunctionSignature TestPredicateSignature
    (b_Prod b_Unit b_S) substituted_counterexample_formula.
Proof.
  unfold substituted_counterexample_formula, substitution_counterexample_formula, b_subst_ext.
  apply WF_Atom.
  refine (@BT_Comp TestSign TestFunc TestFunctionSignature
    (b_Prod b_Unit b_S) (b_Prod b_S b_S) b_S
    b_fst
    (b_pair (b_comp counterexample_substitution b_fst) b_snd)
    (@BT_Fst TestSign TestFunc TestFunctionSignature b_S b_S)
    _).
  refine (@BT_Pair TestSign TestFunc TestFunctionSignature
    (b_Prod b_Unit b_S) b_S b_S
    (b_comp counterexample_substitution b_fst) b_snd _
    (@BT_Snd TestSign TestFunc TestFunctionSignature b_Unit b_S)).
  exact (@BT_Comp TestSign TestFunc TestFunctionSignature
    (b_Prod b_Unit b_S) b_Unit b_S
    counterexample_substitution b_fst counterexample_substitution_typing
    (@BT_Fst TestSign TestFunc TestFunctionSignature b_Unit b_S)).
Defined.

Definition witness_of_substituted_formula : @b_tm TestSign TestFunc :=
  b_const b_S (skolem_index b_S substituted_counterexample_formula).

Definition substituted_witness : @b_tm TestSign TestFunc :=
  b_comp (b_const b_S (skolem_index b_S substitution_counterexample_formula)) counterexample_substitution.

Definition witness_of_substituted_formula_typing :
  @base_typing TestSign TestFunc TestFunctionSignature b_Unit witness_of_substituted_formula b_S :=
  BT_Const.

Definition substituted_witness_typing :
  @base_typing TestSign TestFunc TestFunctionSignature b_Unit substituted_witness b_S :=
  BT_Comp BT_Const BT_Const.

Definition counterexample_substitutivity_equation : Prop :=
  witness_of_substituted_formula ≡_[b_Unit,b_S] substituted_witness.

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
  skolem_index b_S substituted_counterexample_formula.

Definition fin_epsilon_value (s : TestSign) : bool :=
  match s with
  | counterexample_skolem b_S
      (Ty_Atom tt
        (b_comp b_fst
          (b_pair (b_comp (b_const b_S (counterexample_skolem b_S Ty_Unit)) b_fst) b_snd))) => true
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

Lemma interp_witness_of_substituted_formula :
  @interp_tm TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort Fin_BaseModel
    b_Unit b_S witness_of_substituted_formula witness_of_substituted_formula_typing =
  (fun _ : Datatypes.unit => true).
Proof. reflexivity. Defined.

Lemma interp_substituted_witness :
  @interp_tm TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort Fin_BaseModel
    b_Unit b_S substituted_witness substituted_witness_typing =
  (fun _ : Datatypes.unit => false).
Proof. reflexivity. Defined.

Lemma finite_base_countermodel :
  ~ (@interp_tm TestSign TestFunc TestFunctionSignature
       Fin_Setoid Fin_Cartesian Fin_TwoSort Fin_BaseModel
       b_Unit b_S witness_of_substituted_formula witness_of_substituted_formula_typing
     ≅
     @interp_tm TestSign TestFunc TestFunctionSignature
       Fin_Setoid Fin_Cartesian Fin_TwoSort Fin_BaseModel
       b_Unit b_S substituted_witness substituted_witness_typing).
Proof.
  intro H.
  rewrite interp_witness_of_substituted_formula in H.
  rewrite interp_substituted_witness in H.
  specialize (H tt).
  discriminate H.
Defined.

(* This is the syntactic conclusion: the finite semantic separation is fed
   through base soundness, so no base-term equality derivation can exist. *)
Theorem counterexample_equation_not_derivable :
  ~ counterexample_substitutivity_equation.
Proof.
  intro H.
  apply finite_base_countermodel.
  eapply (@base_soundness_equational
    TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort Fin_BaseModel Fin_CoherentBaseModel
    b_Unit b_S witness_of_substituted_formula substituted_witness
    witness_of_substituted_formula_typing substituted_witness_typing).
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

Definition Fin_H3_EpsilonHyperModel_for
  (BEM : @BaseEpsilonFullModel TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort) :
  @EpsilonHyperModel TestSign TestFunc Datatypes.unit
    TestFunctionSignature TestPredicateSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort BEM
    Fin_H3_GoodFibration.
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
    Fin_H3_GoodFibration :=
  Fin_H3_EpsilonHyperModel_for Fin_BaseModel.

Lemma fin_H3_interp_h_ty_subst_const
  (BEM : @BaseEpsilonFullModel TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort) :
  forall (I J : b_ty) (Phi : @h_ty TestSign TestFunc Datatypes.unit)
    (f : @b_tm TestSign TestFunc),
  @interp_h_ty TestSign TestFunc Datatypes.unit
    TestFunctionSignature TestPredicateSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort BEM
    Fin_H3_GoodFibration
    (Fin_H3_EpsilonHyperModel_for BEM)
    I (form_subst f Phi)
  =
  @interp_h_ty TestSign TestFunc Datatypes.unit
    TestFunctionSignature TestPredicateSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort BEM
    Fin_H3_GoodFibration
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
    Fin_H3_GoodFibration
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
    Fin_H3_GoodFibration Fin_H3_EpsilonHyperModel :=
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
     efm_hyper_model := Fin_H3_EpsilonHyperModel;
     efm_adjoint_epsilon := Fin_H3_AdjointEpsilonFullFibration |}.

Definition counterexample_equation_valid_in
  (M : @EpsilonFullModel TestSign TestFunc Datatypes.unit
    TestFunctionSignature TestPredicateSignature TestSkolemMapping) : Prop :=
  EpsilonFull_ModelCategory.efm_interp_tm M witness_of_substituted_formula_typing
  ≅
  EpsilonFull_ModelCategory.efm_interp_tm M substituted_witness_typing.

Theorem finite_hyperdoctrine_countermodel :
  ~ (@interp_tm TestSign TestFunc TestFunctionSignature
       Fin_Setoid Fin_Cartesian Fin_TwoSort Fin_BaseModel
       b_Unit b_S witness_of_substituted_formula witness_of_substituted_formula_typing
     ≅
     @interp_tm TestSign TestFunc TestFunctionSignature
       Fin_Setoid Fin_Cartesian Fin_TwoSort Fin_BaseModel
       b_Unit b_S substituted_witness substituted_witness_typing).
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
    Fin_H3_GoodFibration :=
  Fin_H3_EpsilonHyperModel_for UniformFin_BaseModel.

Definition UniformFin_H3_AdjointEpsilonFullFibration :
  @AdjointEpsilonFullFibration TestSign TestFunc Datatypes.unit
    TestFunctionSignature TestPredicateSignature TestSkolemMapping
    Fin_Setoid Fin_Cartesian Fin_TwoSort UniformFin_BaseModel
    Fin_H3_GoodFibration
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
     efm_hyper_model := UniformFin_H3_EpsilonHyperModel;
     efm_adjoint_epsilon := UniformFin_H3_AdjointEpsilonFullFibration |}.

Lemma uniform_interp_witness_of_substituted_formula :
  @interp_tm TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort UniformFin_BaseModel
    b_Unit b_S witness_of_substituted_formula witness_of_substituted_formula_typing =
  (fun _ : Datatypes.unit => false).
Proof. reflexivity. Defined.

Lemma uniform_interp_substituted_witness :
  @interp_tm TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort UniformFin_BaseModel
    b_Unit b_S substituted_witness substituted_witness_typing =
  (fun _ : Datatypes.unit => false).
Proof. reflexivity. Defined.

Theorem uniform_hyperdoctrine_validates_substitutivity :
  @interp_tm TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort UniformFin_BaseModel
    b_Unit b_S witness_of_substituted_formula witness_of_substituted_formula_typing
  ≅
  @interp_tm TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort UniformFin_BaseModel
    b_Unit b_S substituted_witness substituted_witness_typing.
Proof.
  rewrite uniform_interp_witness_of_substituted_formula.
  rewrite uniform_interp_substituted_witness.
  intro x.
  reflexivity.
Defined.

Theorem separating_model_refutes_substitutivity :
  ~ counterexample_equation_valid_in separating_EpsilonFullModel.
Proof. exact finite_hyperdoctrine_countermodel. Defined.

Theorem uniform_model_validates_substitutivity :
  counterexample_equation_valid_in uniform_EpsilonFullModel.
Proof. exact uniform_hyperdoctrine_validates_substitutivity. Defined.

(* An identity substitution preserves formula conversion but changes the raw
   label used by the chosen epsilon constant. *)
Definition identity_substituted_formula : @h_ty TestSign TestFunc Datatypes.unit :=
  form_subst b_id substituted_counterexample_formula.

Definition identity_substituted_formula_wellformed :
  @WellFormed TestSign TestFunc Datatypes.unit
    TestFunctionSignature TestPredicateSignature
    (b_Prod b_Unit b_S) identity_substituted_formula :=
  wf_subst b_id BT_Id substituted_counterexample_formula
    substituted_counterexample_formula_wellformed.

Definition counterexample_formulas_convertible :
  form_equiv (b_Prod b_Unit b_S)
    substituted_counterexample_formula identity_substituted_formula.
Proof.
  apply FE_Sym.
  apply FE_Pullback_Id.
  exact substituted_counterexample_formula_wellformed.
Defined.

Definition witness_of_identity_substituted_formula :
  @b_tm TestSign TestFunc :=
  b_const b_S (skolem_index b_S identity_substituted_formula).

Definition witness_of_identity_substituted_formula_typing :
  @base_typing TestSign TestFunc TestFunctionSignature
    b_Unit witness_of_identity_substituted_formula b_S := BT_Const.

Lemma counterexample_labels_distinct :
  skolem_index b_S substituted_counterexample_formula <>
  skolem_index b_S identity_substituted_formula.
Proof.
  intro H.
  apply skolem_inj in H.
  destruct H as [_ H].
  unfold substituted_counterexample_formula,
    identity_substituted_formula, substitution_counterexample_formula in H.
  discriminate H.
Defined.

Lemma separating_model_distinguishes_convertible_witnesses :
  ~ (efm_interp_tm separating_EpsilonFullModel
      witness_of_substituted_formula_typing
     ≅
     efm_interp_tm separating_EpsilonFullModel
      witness_of_identity_substituted_formula_typing).
Proof.
  intro H.
  specialize (H tt).
  discriminate H.
Defined.

Lemma uniform_model_identifies_convertible_witnesses :
  efm_interp_tm uniform_EpsilonFullModel
    witness_of_substituted_formula_typing
  ≅
  efm_interp_tm uniform_EpsilonFullModel
    witness_of_identity_substituted_formula_typing.
Proof.
  intro x.
  destruct x.
  reflexivity.
Defined.

Theorem convertible_witnesses_not_definitionally_equal :
  ~ @base_equiv_typed TestSign TestFunc TestFunctionSignature
      b_Unit b_S witness_of_substituted_formula
      witness_of_identity_substituted_formula.
Proof.
  intro H.
  apply separating_model_distinguishes_convertible_witnesses.
  eapply (@base_soundness_equational
    TestSign TestFunc TestFunctionSignature
    Fin_Setoid Fin_Cartesian Fin_TwoSort Fin_BaseModel Fin_CoherentBaseModel
    b_Unit b_S witness_of_substituted_formula
    witness_of_identity_substituted_formula
    witness_of_substituted_formula_typing
    witness_of_identity_substituted_formula_typing).
  exact H.
Defined.

Theorem counterexample_refutes_definitional_extensionality :
  ~ @DefinitionalExtensionality TestSign TestFunc Datatypes.unit
      TestFunctionSignature TestPredicateSignature TestSkolemMapping.
Proof.
  intro H.
  apply convertible_witnesses_not_definitionally_equal.
  exact (H b_Unit b_S substituted_counterexample_formula
    identity_substituted_formula
    substituted_counterexample_formula_wellformed
    identity_substituted_formula_wellformed
    counterexample_formulas_convertible).
Defined.

Theorem counterexample_refutes_definitional_substitutivity :
  ~ @DefinitionalSubstitutivity TestSign TestFunc Datatypes.unit
      TestFunctionSignature TestPredicateSignature TestSkolemMapping.
Proof.
  intro H.
  apply counterexample_equation_not_derivable.
  exact (H b_Unit b_S b_S counterexample_substitution
    counterexample_substitution_typing
    substitution_counterexample_formula
    substitution_counterexample_formula_wellformed).
Defined.

End EpsilonFullSubstitutivity.
