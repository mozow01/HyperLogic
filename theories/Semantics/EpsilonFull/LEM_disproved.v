(* theories/Semantics/EpsilonFull/LEM_disproved.v *)

Require Import Coq.Classes.Morphisms.

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

Require Import HyperLogic.Semantics.EpsilonFull.Base_EpsilonFull_Completeness.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_Fibration.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_Soundness.

Inductive H3 : Type := HBot | HMid | HTop.

Definition H3_le (x y : H3) : Prop :=
  match x, y with
  | HBot, _ => True
  | _, HTop => True
  | HMid, HMid => True
  | _, _ => False
  end.

Lemma H3_le_refl : forall x, H3_le x x.
Proof. destruct x; exact I. Defined.

Lemma H3_le_trans : forall x y z, H3_le y z -> H3_le x y -> H3_le x z.
Proof. destruct x, y, z; simpl; tauto. Defined.

Definition H3_meet (x y : H3) : H3 :=
  match x, y with
  | HBot, _ | _, HBot => HBot
  | HTop, a | a, HTop => a
  | HMid, HMid => HMid
  end.

Definition H3_join (x y : H3) : H3 :=
  match x, y with
  | HTop, _ | _, HTop => HTop
  | HBot, a | a, HBot => a
  | HMid, HMid => HMid
  end.

Definition H3_impl (x y : H3) : H3 :=
  match x, y with
  | HBot, _ => HTop
  | HMid, HBot => HBot
  | HMid, HMid => HTop
  | HMid, HTop => HTop
  | HTop, a => a
  end.

Ltac h3_crush :=
  repeat intro;
  repeat match goal with
  | |- Proper _ _ => red
  | |- respectful _ _ _ _ => red
  | |- RelationClasses.Equivalence _ => split; red
  end;
  repeat intro;
  simpl in *;
  try exact I;
  try constructor;
  repeat match goal with
  | x : H3 |- _ => destruct x
  end;
  simpl in *;
  auto.

Instance H3_Setoid : SetoidCategory.
Proof.
  refine (mk_SetoidCategory H3 H3_le
    H3_le_refl H3_le_trans (fun _ _ _ _ => True) _ _ _ _ _);
  h3_crush.
Defined.

Instance H3_Cartesian : CartesianCategory H3_Setoid.
Proof.
  refine (mk_CartesianCategory H3_Setoid
    HTop (fun _ => _) _
    H3_meet (fun _ _ _ _ _ => _) (fun _ _ => _) (fun _ _ => _)
    _ _ _ _);
  h3_crush.
  Unshelve. all: h3_crush.
Defined.

Instance H3_Closed : CartesianClosedCategory H3_Setoid.
Proof.
  refine (mk_CartesianClosedCategory H3_Setoid H3_Cartesian
    (fun a b => H3_impl b a) _ _ _ _ _).
  Unshelve. all: h3_crush.
Defined.

Instance H3_BiClosed : BiCartesianClosedCategory H3_Closed.
Proof.
  refine (mk_BiCartesianClosedCategory H3_Setoid H3_Cartesian H3_Closed
    HBot _ _ H3_join _ _ _ _ _ _ _).
  Unshelve. all: h3_crush.
Defined.

Instance H3_IdentityFunctor : Functor H3_Setoid H3_Setoid.
Proof.
  refine (mk_Functor H3_Setoid H3_Setoid (fun x => x) _ _ _ _).
  Unshelve. all: h3_crush.
Defined.

Instance H3_AdjointL : IsLeftAdjoint H3_IdentityFunctor.
Proof.
  refine (mk_IsLeftAdjoint _ _ _ (fun x => x) _ _ _ _ _).
  Unshelve. all: h3_crush.
Defined.

Instance H3_AdjointR : IsRightAdjoint H3_IdentityFunctor.
Proof.
  refine (mk_IsRightAdjoint _ _ _ (fun x => x) _ _ _ _ _).
  Unshelve. all: h3_crush.
Defined.

Instance H3_GoodFibration {Sign Func : Type} `{FunctionSignature Func}
  : GoodFibration (Base_SetoidCategory Sign Func).
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

Instance H3_EpsilonHyperModel
  {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}
  : @EpsilonHyperModel
      Sign Func Pred H H0
      (Base_SetoidCategory Sign Func)
      (Base_CartesianCategory Sign Func)
      (Base_TwoSortCategory Sign Func)
      (Base_SyntacticEpsilonFullModel Sign Func)
      H3_GoodFibration.
Proof.
  unshelve econstructor.
  - exact (fun _ _ _ => HMid).
  - intros. reflexivity.
  - intros. reflexivity.
Defined.

Lemma H3_interp_h_ty_subst_const :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred}
    {SM : SkolemMapping Sign Func Pred}
    (I J : b_ty) (Phi : @h_ty Sign Func Pred) (f : @b_tm Sign Func),
  @interp_h_ty
    Sign Func Pred _ _
    (Base_SetoidCategory Sign Func)
    (Base_CartesianCategory Sign Func)
    (Base_TwoSortCategory Sign Func)
    (Base_SyntacticEpsilonFullModel Sign Func)
    H3_GoodFibration
    H3_EpsilonHyperModel
    I
    (form_subst f Phi)
  =
  @interp_h_ty
    Sign Func Pred _ _
    (Base_SetoidCategory Sign Func)
    (Base_CartesianCategory Sign Func)
    (Base_TwoSortCategory Sign Func)
    (Base_SyntacticEpsilonFullModel Sign Func)
    H3_GoodFibration
    H3_EpsilonHyperModel
    J
    Phi.
Proof.
  intros Sign Func Pred HFunc HPred SM I J Phi.
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

Instance H3_AdjointEpsilonFullFibration
  {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred}
  {SM : SkolemMapping Sign Func Pred}
  : @AdjointEpsilonFullFibration
      Sign Func Pred _ _ SM
      (Base_SetoidCategory Sign Func)
      (Base_CartesianCategory Sign Func)
      (Base_TwoSortCategory Sign Func)
      (Base_SyntacticEpsilonFullModel Sign Func)
      H3_GoodFibration
      H3_EpsilonHyperModel.
Proof.
  constructor.
  - intros I A Phi Hwf_Phi.
    cbn [left_adj_obj pullback_has_left_adjoint H3_GoodFibration H3_AdjointR].
    rewrite (@H3_interp_h_ty_subst_const
      Sign Func Pred _ _ SM
      I (b_Prod I A) Phi
      (b_pair b_id (b_const A (skolem_index A Phi)))).
    reflexivity.
  - intros I A Phi Psi Hwf_Phi Hwf_Psi H_iso.
    rewrite (@H3_interp_h_ty_subst_const
      Sign Func Pred _ _ SM
      I (b_Prod I A) Phi
      (b_pair b_id (b_const A (skolem_index A Phi)))).
    rewrite (@H3_interp_h_ty_subst_const
      Sign Func Pred _ _ SM
      I (b_Prod I A) Psi
      (b_pair b_id (b_const A (skolem_index A Psi)))).
    exact H_iso.
Defined.

Instance UnitPredicateSignature : PredicateSignature Datatypes.unit :=
  {| pred_dom _ := b_Unit |}.

Definition P_atom {Sign Func : Type} (I : b_ty) : @h_ty Sign Func Datatypes.unit :=
  Ty_Atom Datatypes.tt b_unit.

Definition LEM_Formula {Sign Func : Type} (I : b_ty) : @h_ty Sign Func Datatypes.unit :=
  Ty_Sum (P_atom I) (Ty_Arrow (P_atom I) Ty_Void).

Lemma LEM_WellFormed :
  forall {Sign Func : Type} `{FunctionSignature Func} (I : b_ty),
  @WellFormed Sign Func Datatypes.unit _ UnitPredicateSignature I (LEM_Formula I).
Proof.
  intros Sign Func HFunc I.
  apply WF_Sum.
  - eapply WF_Atom. apply BT_Unit.
  - apply WF_Arrow.
    + eapply WF_Atom. apply BT_Unit.
    + apply WF_Void.
Defined.

Lemma wf_ctx_nil_valid :
  forall {Sign Func : Type} `{FunctionSignature Func} (I : b_ty),
  @All_WellFormed Sign Func Datatypes.unit _ UnitPredicateSignature I nil.
Proof.
  intros. apply AWF_Nil.
Defined.

Definition LEM_Derivation
  {Sign Func : Type} `{FunctionSignature Func} {SM : SkolemMapping Sign Func Datatypes.unit}
  : Type :=
  { p : @h_tm Sign Func Datatypes.unit &
      @h_derivation Sign Func Datatypes.unit _ UnitPredicateSignature SM
        b_Unit nil p (LEM_Formula b_Unit) }.

Theorem H3_LEM_refuted_at_unit :
  forall {Sign Func : Type} `{FunctionSignature Func} {SM : SkolemMapping Sign Func Datatypes.unit},
  @hom
    (Fiber (@interp_ty
      (Base_SetoidCategory Sign Func)
      (Base_CartesianCategory Sign Func)
      (Base_TwoSortCategory Sign Func)
      b_Unit))
    (@interp_h_ctx
      Sign Func Datatypes.unit _ UnitPredicateSignature
      (Base_SetoidCategory Sign Func)
      (Base_CartesianCategory Sign Func)
      (Base_TwoSortCategory Sign Func)
      (Base_SyntacticEpsilonFullModel Sign Func)
      H3_GoodFibration
      H3_EpsilonHyperModel
      b_Unit nil)
    (@interp_h_ty
      Sign Func Datatypes.unit _ UnitPredicateSignature
      (Base_SetoidCategory Sign Func)
      (Base_CartesianCategory Sign Func)
      (Base_TwoSortCategory Sign Func)
      (Base_SyntacticEpsilonFullModel Sign Func)
      H3_GoodFibration
      H3_EpsilonHyperModel
      b_Unit (LEM_Formula b_Unit)) ->
  False.
Proof.
  intros Sign Func HFunc SM Hlem.
  simpl in Hlem.
  exact Hlem.
Defined.

Theorem LEM_Underivable_at_unit :
  forall {Sign Func : Type} `{FunctionSignature Func}
    {SM : SkolemMapping Sign Func Datatypes.unit},
  LEM_Derivation -> False.
Proof.
  intros Sign Func HFunc SM [p Hder].
  apply H3_LEM_refuted_at_unit.
  exact (@soundness
    Sign Func Datatypes.unit HFunc UnitPredicateSignature SM
    (Base_SetoidCategory Sign Func)
    (Base_CartesianCategory Sign Func)
    (Base_TwoSortCategory Sign Func)
    (Base_SyntacticEpsilonFullModel Sign Func)
    H3_GoodFibration
    H3_EpsilonHyperModel
    H3_AdjointEpsilonFullFibration
    b_Unit nil p (LEM_Formula b_Unit)
    Hder).
Defined.

Theorem LEM_Underivable_WF :
  forall {Sign Func : Type} `{FunctionSignature Func}
    {SM : SkolemMapping Sign Func Datatypes.unit},
  (forall I : b_ty,
      { p : @h_tm Sign Func Datatypes.unit &
          @h_derivation Sign Func Datatypes.unit _ UnitPredicateSignature SM
            I nil p (LEM_Formula I) }) -> False.
Proof.
  intros Sign Func HFunc SM H_all_der.
  apply LEM_Underivable_at_unit.
  exact (H_all_der b_Unit).
Defined.
