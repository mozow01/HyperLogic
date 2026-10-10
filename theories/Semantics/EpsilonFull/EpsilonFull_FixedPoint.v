
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Equality.
Require Import List.
Import ListNotations.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.Fibration.
Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.
Require Import HyperLogic.Semantics.EpsilonFull.Base_EpsilonFull_Soundness.
Require Import HyperLogic.Semantics.EpsilonFull.Base_EpsilonFull_Completeness.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_Completeness.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_ModelCategory.

Section EpsilonFullFixedPoint.

Context {Sign Func : Type}.
Context `{HFunc : FunctionSignature Func}.

Inductive BaseOneStepHom : b_ty -> b_ty -> Type :=
  | BOS_Id : forall A,
      BaseOneStepHom A A
  | BOS_Comp : forall A B C,
      @hom_base Sign Func HFunc B C ->
      @hom_base Sign Func HFunc A B ->
      BaseOneStepHom A C
  | BOS_Unit : forall A,
      BaseOneStepHom A b_Unit
  | BOS_Pair : forall A B C,
      @hom_base Sign Func HFunc A B ->
      @hom_base Sign Func HFunc A C ->
      BaseOneStepHom A (b_Prod B C)
  | BOS_Fst : forall A B,
      BaseOneStepHom (b_Prod A B) A
  | BOS_Snd : forall A B,
      BaseOneStepHom (b_Prod A B) B
  | BOS_Const : forall I A,
      Sign ->
      BaseOneStepHom I A
  | BOS_Func : forall f,
      BaseOneStepHom (func_dom f) (func_cod f).

Definition base_onestep_roll {I A : b_ty}
  (s : BaseOneStepHom I A) : @hom_base Sign Func HFunc I A :=
  match s with
  | BOS_Id A =>
      @mk_hom_base Sign Func HFunc A A b_id BT_Id
  | BOS_Comp A B C g f =>
      @mk_hom_base Sign Func HFunc A C
        (b_comp (tm_of g) (tm_of f))
        (BT_Comp (deriv_of g) (deriv_of f))
  | BOS_Unit A =>
      @mk_hom_base Sign Func HFunc A b_Unit b_unit BT_Unit
  | BOS_Pair A B C f g =>
      @mk_hom_base Sign Func HFunc A (b_Prod B C)
        (b_pair (tm_of f) (tm_of g))
        (BT_Pair (deriv_of f) (deriv_of g))
  | BOS_Fst A B =>
      @mk_hom_base Sign Func HFunc (b_Prod A B) A b_fst BT_Fst
  | BOS_Snd A B =>
      @mk_hom_base Sign Func HFunc (b_Prod A B) B b_snd BT_Snd
  | BOS_Const i a s =>
      @mk_hom_base Sign Func HFunc i a (b_const a s) BT_Const
  | BOS_Func f =>
      @mk_hom_base Sign Func HFunc (func_dom f) (func_cod f)
        (b_func f) BT_Func
  end.

Definition base_onestep_unroll {I A : b_ty}
  (f : @hom_base Sign Func HFunc I A) : BaseOneStepHom I A.
Proof.
  destruct f as [t dt].
  dependent destruction dt.
  - exact (BOS_Id A).
  - exact (BOS_Comp A B C
      (@mk_hom_base Sign Func HFunc B C g dt1)
      (@mk_hom_base Sign Func HFunc A B f dt2)).
  - exact (BOS_Unit A).
  - exact (BOS_Pair A B C
      (@mk_hom_base Sign Func HFunc A B f dt1)
      (@mk_hom_base Sign Func HFunc A C g dt2)).
  - exact (BOS_Fst A B).
  - exact (BOS_Snd A B).
  - exact (BOS_Const I A s).
  - exact (BOS_Func f).
Defined.

Definition base_onestep_equiv {I A : b_ty}
  (s t : BaseOneStepHom I A) : Prop :=
  @hom_equiv (Base_SetoidCategory Sign Func) I A
    (base_onestep_roll s) (base_onestep_roll t).

Global Instance base_onestep_equiv_equivalence {I A : b_ty}
  : Equivalence (@base_onestep_equiv I A).
Proof.
  unfold base_onestep_equiv.
  constructor.
  - intro x. reflexivity.
  - intros x y Hxy. symmetry. exact Hxy.
  - intros x y z Hxy Hyz. transitivity (base_onestep_roll y); assumption.
Defined.

Lemma TermModel_base_roll_unroll
  {I A : b_ty} (f : @hom_base Sign Func HFunc I A)
  : @hom_equiv (Base_SetoidCategory Sign Func) I A
      (base_onestep_roll (base_onestep_unroll f)) f.
Proof.
  destruct f as [t dt].
  dependent destruction dt; cbn; apply BE_Refl.
Defined.

Lemma TermModel_base_unroll_roll
  {I A : b_ty} (s : BaseOneStepHom I A)
  : base_onestep_equiv (base_onestep_unroll (base_onestep_roll s)) s.
Proof.
  unfold base_onestep_equiv.
  apply TermModel_base_roll_unroll.
Defined.

Class BaseOneStepFixedPoint := mk_BaseOneStepFixedPoint {
  base_fixed_roll_unroll :
    forall {I A : b_ty} (f : @hom_base Sign Func HFunc I A),
      @hom_equiv (Base_SetoidCategory Sign Func) I A
        (base_onestep_roll (base_onestep_unroll f)) f;
  base_fixed_unroll_roll :
    forall {I A : b_ty} (s : BaseOneStepHom I A),
      base_onestep_equiv (base_onestep_unroll (base_onestep_roll s)) s
}.

Instance TermModel_BaseOneStepFixedPoint : BaseOneStepFixedPoint.
Proof.
  constructor.
  - intros I A f. apply TermModel_base_roll_unroll.
  - intros I A s. apply TermModel_base_unroll_roll.
Defined.

End EpsilonFullFixedPoint.

Section EpsilonFullHyperFixedPoint.

Context {Sign Func Pred : Type}.
Context `{HFunc : FunctionSignature Func}.
Context `{HPred : PredicateSignature Pred}.
Context {SM : SkolemMapping Sign Func Pred}.

Inductive HyperOneStepDerivation :
  forall (I : b_ty) (G : @h_context Sign Func Pred)
    (p : @h_tm Sign Func Pred) (Phi : @h_ty Sign Func Pred), Type :=
  | HOS_Var0 : forall I Phi G,
      All_WellFormed I (Phi :: G) ->
      HyperOneStepDerivation I (Phi :: G) (tm_var 0) Phi
  | HOS_VarS : forall I Phi Psi G n,
      WellFormed I Psi ->
      h_derivation I G (tm_var n) Phi ->
      HyperOneStepDerivation I (Psi :: G) (tm_var (Datatypes.S n)) Phi
  | HOS_Unit : forall I G,
      All_WellFormed I G ->
      HyperOneStepDerivation I G tm_unit Ty_Unit
  | HOS_Conv : forall I G p Phi Psi,
      h_derivation I G p Phi ->
      form_equiv I Phi Psi ->
      HyperOneStepDerivation I G p Psi
  | HOS_Ctx_Conv : forall I G1 G2 p Phi,
      ctx_equiv I G1 G2 ->
      h_derivation I G1 p Phi ->
      HyperOneStepDerivation I G2 p Phi
  | HOS_Lam : forall I G p Phi Psi,
      h_derivation I (Phi :: G) p Psi ->
      HyperOneStepDerivation I G (tm_lam Phi p) (Ty_Arrow Phi Psi)
  | HOS_App : forall I G p1 p2 Phi Psi,
      h_derivation I G p1 (Ty_Arrow Phi Psi) ->
      h_derivation I G p2 Phi ->
      HyperOneStepDerivation I G (tm_app p1 p2) Psi
  | HOS_Pair : forall I G p1 p2 Phi Psi,
      h_derivation I G p1 Phi ->
      h_derivation I G p2 Psi ->
      HyperOneStepDerivation I G (tm_pair p1 p2) (Ty_Prod Phi Psi)
  | HOS_Fst : forall I G p Phi Psi,
      h_derivation I G p (Ty_Prod Phi Psi) ->
      HyperOneStepDerivation I G (tm_fst p) Phi
  | HOS_Snd : forall I G p Phi Psi,
      h_derivation I G p (Ty_Prod Phi Psi) ->
      HyperOneStepDerivation I G (tm_snd p) Psi
  | HOS_Inl : forall I G p Phi Psi,
      WellFormed I Psi ->
      h_derivation I G p Phi ->
      HyperOneStepDerivation I G (tm_inl Psi p) (Ty_Sum Phi Psi)
  | HOS_Inr : forall I G p Phi Psi,
      WellFormed I Phi ->
      h_derivation I G p Psi ->
      HyperOneStepDerivation I G (tm_inr Phi p) (Ty_Sum Phi Psi)
  | HOS_Case : forall I G p p1 p2 Phi Psi Chi,
      h_derivation I G p (Ty_Sum Phi Psi) ->
      h_derivation I (Phi :: G) p1 Chi ->
      h_derivation I (Psi :: G) p2 Chi ->
      HyperOneStepDerivation I G (tm_case p p1 p2) Chi
  | HOS_Absurd : forall I G p Phi,
      WellFormed I Phi ->
      h_derivation I G p Ty_Void ->
      HyperOneStepDerivation I G (tm_absurd Phi p) Phi
  | HOS_All_Intro : forall I A G p Phi,
      h_derivation (b_Prod I A) (ctx_subst b_fst G) p Phi ->
      HyperOneStepDerivation I G (tm_all_intro p) (Ty_All A Phi)
  | HOS_All_Elim : forall I A G p Phi f,
      h_derivation I G p (Ty_All A Phi) ->
      base_typing I f A ->
      HyperOneStepDerivation I G (tm_all_elim p f)
        (form_subst (b_pair b_id f) Phi)
  | HOS_Ex_Intro : forall I A G p Phi f,
      base_typing I f A ->
      h_derivation I G p (form_subst (b_pair b_id f) Phi) ->
      HyperOneStepDerivation I G (tm_ex_intro f p) (Ty_Ex A Phi)
  | HOS_Ex_Elim : forall I A G p p2 Phi Chi,
      h_derivation I G p (Ty_Ex A Phi) ->
      h_derivation (b_Prod I A) (Phi :: ctx_subst b_fst G) p2
        (form_subst b_fst Chi) ->
      HyperOneStepDerivation I G (tm_ex_elim p p2) Chi
  | HOS_Eps_Intro : forall I A G p Phi f,
      base_typing I f A ->
      h_derivation I G p (form_subst (b_pair b_id f) Phi) ->
      HyperOneStepDerivation I G (tm_eps_intro f p)
        (form_subst (b_pair b_id (b_const A (skolem_index A Phi))) Phi)
  | HOS_Eps_Elim : forall I A G p p2 Phi Chi,
      h_derivation I G p
        (form_subst (b_pair b_id (b_const A (skolem_index A Phi))) Phi) ->
      h_derivation (b_Prod I A) (Phi :: ctx_subst b_fst G) p2
        (form_subst b_fst Chi) ->
      HyperOneStepDerivation I G (tm_eps_elim p p2) Chi.

Definition hyper_onestep_roll
  {I : b_ty} {G : @h_context Sign Func Pred}
  {p : @h_tm Sign Func Pred} {Phi : @h_ty Sign Func Pred}
  (s : HyperOneStepDerivation I G p Phi)
  : h_derivation I G p Phi :=
  match s with
  | HOS_Var0 i Phi G wfG =>
      HD_Var0 i Phi G wfG
  | HOS_VarS i Phi Psi G n wfPsi d =>
      HD_VarS i Phi Psi G n wfPsi d
  | HOS_Unit i G wfG =>
      HD_Unit i G wfG
  | HOS_Conv i G p Phi Psi d e =>
      HD_Conv i G p Phi Psi d e
  | HOS_Ctx_Conv i G1 G2 p Phi e d =>
      HD_Ctx_Conv i G1 G2 p Phi e d
  | HOS_Lam i G p Phi Psi d =>
      HD_Lam i G p Phi Psi d
  | HOS_App i G p1 p2 Phi Psi d1 d2 =>
      HD_App i G p1 p2 Phi Psi d1 d2
  | HOS_Pair i G p1 p2 Phi Psi d1 d2 =>
      HD_Pair i G p1 p2 Phi Psi d1 d2
  | HOS_Fst i G p Phi Psi d =>
      HD_Fst i G p Phi Psi d
  | HOS_Snd i G p Phi Psi d =>
      HD_Snd i G p Phi Psi d
  | HOS_Inl i G p Phi Psi wfPsi d =>
      HD_Inl wfPsi d
  | HOS_Inr i G p Phi Psi wfPhi d =>
      HD_Inr wfPhi d
  | HOS_Case i G p p1 p2 Phi Psi Chi d d1 d2 =>
      HD_Case i G p p1 p2 Phi Psi Chi d d1 d2
  | HOS_Absurd i G p Phi wfPhi d =>
      HD_Absurd wfPhi d
  | HOS_All_Intro i A G p Phi d =>
      HD_All_Intro i A G p Phi d
  | HOS_All_Elim i A G p Phi f d df =>
      HD_All_Elim i A G p Phi f d df
  | HOS_Ex_Intro i A G p Phi f df d =>
      HD_Ex_Intro i A G p Phi f df d
  | HOS_Ex_Elim i A G p p2 Phi Chi d d2 =>
      HD_Ex_Elim i A G p p2 Phi Chi d d2
  | HOS_Eps_Intro i A G p Phi f df d =>
      HD_Eps_Intro i A G p Phi f df d
  | HOS_Eps_Elim i A G p p2 Phi Chi d d2 =>
      HD_Eps_Elim i A G p p2 Phi Chi d d2
  end.

Definition hyper_onestep_unroll
  {I : b_ty} {G : @h_context Sign Func Pred}
  {p : @h_tm Sign Func Pred} {Phi : @h_ty Sign Func Pred}
  (d : h_derivation I G p Phi)
  : HyperOneStepDerivation I G p Phi.
Proof.
  dependent destruction d.
  - exact (HOS_Var0 I Phi G a).
  - exact (HOS_VarS I Phi Psi G n w d).
  - exact (HOS_Unit I G a).
  - exact (HOS_Conv I G p Phi Psi d f).
  - exact (HOS_Ctx_Conv I G1 G2 p Phi c d).
  - exact (HOS_Lam I G p Phi Psi d).
  - exact (HOS_App I G p1 p2 Phi Psi d1 d2).
  - exact (HOS_Pair I G p1 p2 Phi Psi d1 d2).
  - exact (HOS_Fst I G p Phi Psi d).
  - exact (HOS_Snd I G p Phi Psi d).
  - exact (HOS_Inl I G p Phi Psi w d).
  - exact (HOS_Inr I G p Phi Psi w d).
  - exact (HOS_Case I G p p1 p2 Phi Psi Chi d1 d2 d3).
  - exact (HOS_Absurd I G p Phi w d).
  - exact (HOS_All_Intro I A G p Phi d).
  - exact (HOS_All_Elim I A G p Phi f d b).
  - exact (HOS_Ex_Intro I A G p Phi f b d).
  - exact (HOS_Ex_Elim I A G p p2 Phi Chi d1 d2).
  - exact (HOS_Eps_Intro I A G p Phi f b d).
  - exact (HOS_Eps_Elim I A G p p2 Phi Chi d1 d2).
Defined.

Definition hyper_onestep_equiv
  {I : b_ty} {G : @h_context Sign Func Pred}
  {p : @h_tm Sign Func Pred} {Phi : @h_ty Sign Func Pred}
  (s t : HyperOneStepDerivation I G p Phi) : Prop :=
  hyper_onestep_roll s = hyper_onestep_roll t.

Global Instance hyper_onestep_equiv_equivalence
  {I : b_ty} {G : @h_context Sign Func Pred}
  {p : @h_tm Sign Func Pred} {Phi : @h_ty Sign Func Pred}
  : Equivalence (@hyper_onestep_equiv I G p Phi).
Proof.
  unfold hyper_onestep_equiv.
  constructor.
  - intro x. reflexivity.
  - intros x y Hxy. symmetry. exact Hxy.
  - intros x y z Hxy Hyz. transitivity (hyper_onestep_roll y); assumption.
Defined.

Lemma TermModel_hyper_roll_unroll
  {I : b_ty} {G : @h_context Sign Func Pred}
  {p : @h_tm Sign Func Pred} {Phi : @h_ty Sign Func Pred}
  (d : h_derivation I G p Phi)
  : hyper_onestep_roll (hyper_onestep_unroll d) = d.
Proof.
  dependent destruction d; reflexivity.
Defined.

Lemma TermModel_hyper_unroll_roll
  {I : b_ty} {G : @h_context Sign Func Pred}
  {p : @h_tm Sign Func Pred} {Phi : @h_ty Sign Func Pred}
  (s : HyperOneStepDerivation I G p Phi)
  : hyper_onestep_equiv (hyper_onestep_unroll (hyper_onestep_roll s)) s.
Proof.
  unfold hyper_onestep_equiv.
  apply TermModel_hyper_roll_unroll.
Defined.

Class HyperOneStepFixedPoint := mk_HyperOneStepFixedPoint {
  hyper_fixed_roll_unroll :
    forall {I : b_ty} {G : @h_context Sign Func Pred}
      {p : @h_tm Sign Func Pred} {Phi : @h_ty Sign Func Pred}
      (d : h_derivation I G p Phi),
      hyper_onestep_roll (hyper_onestep_unroll d) = d;
  hyper_fixed_unroll_roll :
    forall {I : b_ty} {G : @h_context Sign Func Pred}
      {p : @h_tm Sign Func Pred} {Phi : @h_ty Sign Func Pred}
      (s : HyperOneStepDerivation I G p Phi),
      hyper_onestep_equiv (hyper_onestep_unroll (hyper_onestep_roll s)) s
}.

Instance TermModel_HyperOneStepFixedPoint : HyperOneStepFixedPoint.
Proof.
  constructor.
  - intros I G p Phi d. apply TermModel_hyper_roll_unroll.
  - intros I G p Phi s. apply TermModel_hyper_unroll_roll.
Defined.

Class EpsilonFullOneStepFixedPoint := mk_EpsilonFullOneStepFixedPoint {
  #[global] epsilon_full_base_fixed_point ::
    @BaseOneStepFixedPoint Sign Func HFunc;
  #[global] epsilon_full_hyper_fixed_point ::
    HyperOneStepFixedPoint
}.

Instance TermModel_EpsilonFullOneStepFixedPoint
  : EpsilonFullOneStepFixedPoint.
Proof.
  constructor.
  - apply (@TermModel_BaseOneStepFixedPoint Sign Func HFunc).
  - apply TermModel_HyperOneStepFixedPoint.
Defined.

End EpsilonFullHyperFixedPoint.

Section EpsilonFullTermModelFixedPoint.

Context {Sign Func Pred : Type}.
Context `{HFunc : FunctionSignature Func}.
Context `{HPred : PredicateSignature Pred}.
Context {SM : SkolemMapping Sign Func Pred}.

Let TM : @EpsilonFullModel Sign Func Pred HFunc HPred SM :=
  @TermModel_EpsilonFullModel Sign Func Pred HFunc HPred SM.

Definition term_model_base_onestep_roll {I A : b_ty}
  (s : @BaseOneStepHom Sign Func HFunc I A)
  : @hom (@efm_cat Sign Func Pred HFunc HPred SM TM)
      (@efm_interp_ty Sign Func Pred HFunc HPred SM TM I)
      (@efm_interp_ty Sign Func Pred HFunc HPred SM TM A) :=
  @efm_interp_tm Sign Func Pred HFunc HPred SM TM I A
    (tm_of (base_onestep_roll s))
    (deriv_of (base_onestep_roll s)).

Definition term_model_base_onestep_unroll {I A : b_ty}
  (f : @hom (@efm_cat Sign Func Pred HFunc HPred SM TM)
      (@efm_interp_ty Sign Func Pred HFunc HPred SM TM I)
      (@efm_interp_ty Sign Func Pred HFunc HPred SM TM A))
  : @BaseOneStepHom Sign Func HFunc I A :=
  base_onestep_unroll (term_model_base_hom f).

Definition term_model_base_onestep_equiv {I A : b_ty}
  (s t : @BaseOneStepHom Sign Func HFunc I A) : Prop :=
  @hom_equiv (@efm_cat Sign Func Pred HFunc HPred SM TM)
    (@efm_interp_ty Sign Func Pred HFunc HPred SM TM I)
    (@efm_interp_ty Sign Func Pred HFunc HPred SM TM A)
    (term_model_base_onestep_roll s)
    (term_model_base_onestep_roll t).

Global Instance term_model_base_onestep_equiv_equivalence {I A : b_ty}
  : Equivalence (@term_model_base_onestep_equiv I A).
Proof.
  unfold term_model_base_onestep_equiv.
  constructor.
  - intro x. reflexivity.
  - intros x y Hxy. symmetry. exact Hxy.
  - intros x y z Hxy Hyz.
    transitivity (term_model_base_onestep_roll y); assumption.
Defined.

Lemma TermModel_semantic_base_roll_unroll
  {I A : b_ty}
  (f : @hom (@efm_cat Sign Func Pred HFunc HPred SM TM)
      (@efm_interp_ty Sign Func Pred HFunc HPred SM TM I)
      (@efm_interp_ty Sign Func Pred HFunc HPred SM TM A))
  : @hom_equiv (@efm_cat Sign Func Pred HFunc HPred SM TM)
      (@efm_interp_ty Sign Func Pred HFunc HPred SM TM I)
      (@efm_interp_ty Sign Func Pred HFunc HPred SM TM A)
      (term_model_base_onestep_roll (term_model_base_onestep_unroll f))
      f.
Proof.
  unfold term_model_base_onestep_roll, term_model_base_onestep_unroll.
  pose (h := term_model_base_hom f).
  transitivity (@efm_interp_tm Sign Func Pred HFunc HPred SM TM I A
    (tm_of h) (deriv_of h)).
  - eapply (@base_soundness_equational Sign Func HFunc
      (@efm_cat Sign Func Pred HFunc HPred SM TM)
      (@efm_cartesian Sign Func Pred HFunc HPred SM TM)
      (@efm_twosort Sign Func Pred HFunc HPred SM TM)
      (@efm_base_model Sign Func Pred HFunc HPred SM TM)
      (@efm_base_coherent Sign Func Pred HFunc HPred SM TM)).
    exists (deriv_of (base_onestep_roll (base_onestep_unroll h))).
    exists (deriv_of h).
    exact (TermModel_base_roll_unroll h).
  - symmetry.
    exact (term_model_base_hom_reinterp_equiv f).
Defined.

Lemma TermModel_semantic_base_unroll_roll
  {I A : b_ty} (s : @BaseOneStepHom Sign Func HFunc I A)
  : term_model_base_onestep_equiv
      (term_model_base_onestep_unroll (term_model_base_onestep_roll s)) s.
Proof.
  unfold term_model_base_onestep_equiv.
  apply TermModel_semantic_base_roll_unroll.
Defined.

Class TermModelSemanticBaseOneStepFixedPoint :=
  mk_TermModelSemanticBaseOneStepFixedPoint {
  semantic_base_fixed_roll_unroll :
    forall {I A : b_ty}
      (f : @hom (@efm_cat Sign Func Pred HFunc HPred SM TM)
        (@efm_interp_ty Sign Func Pred HFunc HPred SM TM I)
        (@efm_interp_ty Sign Func Pred HFunc HPred SM TM A)),
      @hom_equiv (@efm_cat Sign Func Pred HFunc HPred SM TM)
        (@efm_interp_ty Sign Func Pred HFunc HPred SM TM I)
        (@efm_interp_ty Sign Func Pred HFunc HPred SM TM A)
        (term_model_base_onestep_roll (term_model_base_onestep_unroll f)) f;
  semantic_base_fixed_unroll_roll :
    forall {I A : b_ty} (s : @BaseOneStepHom Sign Func HFunc I A),
      term_model_base_onestep_equiv
        (term_model_base_onestep_unroll (term_model_base_onestep_roll s)) s
}.

Instance TermModel_SemanticBaseOneStepFixedPoint
  : TermModelSemanticBaseOneStepFixedPoint.
Proof.
  constructor.
  - intros I A f. apply TermModel_semantic_base_roll_unroll.
  - intros I A s. apply TermModel_semantic_base_unroll_roll.
Defined.

Definition TermModelFiberOneStepHom
  (I : b_ty) (Phi Psi : @h_ty Sign Func Pred) : Type :=
  { p : @h_tm Sign Func Pred &
      @HyperOneStepDerivation Sign Func Pred HFunc HPred SM
        I [] p (Ty_Arrow Phi Psi) }.

Definition term_model_fiber_onestep_roll
  {I : b_ty} {Phi Psi : @h_ty Sign Func Pred}
  (s : TermModelFiberOneStepHom I Phi Psi)
  : @hom (@efm_fiber Sign Func Pred HFunc HPred SM TM I)
      (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Phi)
      (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Psi).
Proof.
  destruct s as [p step].
  exact (@closed_arrow_soundness_to_hom
    Sign Func Pred HFunc HPred SM TM I Phi Psi p
    (hyper_onestep_roll step)).
Defined.

Definition term_model_fiber_closed_derivation
  {I : b_ty} {Phi Psi : @h_ty Sign Func Pred}
  (wf_Phi : WellFormed I Phi) (wf_Psi : WellFormed I Psi)
  (f : @hom (@efm_fiber Sign Func Pred HFunc HPred SM TM I)
      (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Phi)
      (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Psi))
  : { p : @h_tm Sign Func Pred &
      @h_derivation Sign Func Pred HFunc HPred SM
        I [] p (Ty_Arrow Phi Psi) }.
Proof.
  unfold TM, efm_fiber, efm_interp_h_ty, efm_interp_ty in f.
  cbn in f.
  destruct f as [p d].
  pose proof (@term_model_interp_id
    Sign Func Pred HFunc HPred SM I Phi wf_Phi) as H_phi.
  pose proof (@term_model_interp_id
    Sign Func Pred HFunc HPred SM I Psi wf_Psi) as H_psi.
  cbn in H_phi, H_psi.
  rewrite H_phi in d.
  rewrite H_psi in d.
  rewrite (interp_ty_id Sign Func I) in d.
  exists p.
  exact d.
Defined.

Definition term_model_fiber_onestep_unroll
  {I : b_ty} {Phi Psi : @h_ty Sign Func Pred}
  (wf_Phi : WellFormed I Phi) (wf_Psi : WellFormed I Psi)
  (f : @hom (@efm_fiber Sign Func Pred HFunc HPred SM TM I)
      (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Phi)
      (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Psi))
  : TermModelFiberOneStepHom I Phi Psi.
Proof.
  destruct (term_model_fiber_closed_derivation wf_Phi wf_Psi f) as [p d].
  exists p.
  exact (hyper_onestep_unroll d).
Defined.

Definition term_model_fiber_onestep_equiv
  {I : b_ty} {Phi Psi : @h_ty Sign Func Pred}
  (s t : TermModelFiberOneStepHom I Phi Psi) : Prop :=
  @hom_equiv (@efm_fiber Sign Func Pred HFunc HPred SM TM I)
    (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Phi)
    (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Psi)
    (term_model_fiber_onestep_roll s)
    (term_model_fiber_onestep_roll t).

Global Instance term_model_fiber_onestep_equiv_equivalence
  {I : b_ty} {Phi Psi : @h_ty Sign Func Pred}
  : Equivalence (@term_model_fiber_onestep_equiv I Phi Psi).
Proof.
  unfold term_model_fiber_onestep_equiv.
  constructor.
  - intro x. reflexivity.
  - intros x y Hxy. symmetry. exact Hxy.
  - intros x y z Hxy Hyz.
    transitivity (term_model_fiber_onestep_roll y); assumption.
Defined.

Lemma TermModel_semantic_fiber_roll_unroll
  {I : b_ty} {Phi Psi : @h_ty Sign Func Pred}
  (wf_Phi : WellFormed I Phi) (wf_Psi : WellFormed I Psi)
  (f : @hom (@efm_fiber Sign Func Pred HFunc HPred SM TM I)
      (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Phi)
      (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Psi))
  : @hom_equiv (@efm_fiber Sign Func Pred HFunc HPred SM TM I)
      (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Phi)
      (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Psi)
      (term_model_fiber_onestep_roll
        (term_model_fiber_onestep_unroll wf_Phi wf_Psi f))
      f.
Proof.
  apply (fiber_is_thin
    (@efm_interp_ty Sign Func Pred HFunc HPred SM TM I)).
Defined.

Class TermModelSemanticFiberOneStepFixedPoint :=
  mk_TermModelSemanticFiberOneStepFixedPoint {
  semantic_fiber_fixed_roll_unroll :
    forall {I : b_ty} {Phi Psi : @h_ty Sign Func Pred}
      (wf_Phi : WellFormed I Phi) (wf_Psi : WellFormed I Psi)
      (f : @hom (@efm_fiber Sign Func Pred HFunc HPred SM TM I)
        (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Phi)
        (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Psi)),
      @hom_equiv (@efm_fiber Sign Func Pred HFunc HPred SM TM I)
        (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Phi)
        (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Psi)
        (term_model_fiber_onestep_roll
          (term_model_fiber_onestep_unroll wf_Phi wf_Psi f)) f;
  semantic_fiber_fixed_unroll_roll :
    forall {I : b_ty} {Phi Psi : @h_ty Sign Func Pred}
      (wf_Phi : WellFormed I Phi) (wf_Psi : WellFormed I Psi)
      (s : TermModelFiberOneStepHom I Phi Psi),
      term_model_fiber_onestep_equiv
        (term_model_fiber_onestep_unroll wf_Phi wf_Psi
          (term_model_fiber_onestep_roll s)) s
}.

Lemma TermModel_semantic_fiber_unroll_roll
  {I : b_ty} {Phi Psi : @h_ty Sign Func Pred}
  (wf_Phi : WellFormed I Phi) (wf_Psi : WellFormed I Psi)
  (s : TermModelFiberOneStepHom I Phi Psi)
  : term_model_fiber_onestep_equiv
      (term_model_fiber_onestep_unroll wf_Phi wf_Psi
        (term_model_fiber_onestep_roll s)) s.
Proof.
  unfold term_model_fiber_onestep_equiv.
  apply (fiber_is_thin
    (@efm_interp_ty Sign Func Pred HFunc HPred SM TM I)).
Defined.

Instance TermModel_SemanticFiberOneStepFixedPoint
  : TermModelSemanticFiberOneStepFixedPoint.
Proof.
  constructor.
  - intros I Phi Psi wf_Phi wf_Psi f.
    apply TermModel_semantic_fiber_roll_unroll.
  - intros I Phi Psi wf_Phi wf_Psi s.
    apply TermModel_semantic_fiber_unroll_roll.
Defined.

Definition TermModelSequentOneStepHom
  (I : b_ty) (G : @h_context Sign Func Pred)
  (Phi : @h_ty Sign Func Pred) : Type :=
  { p : @h_tm Sign Func Pred &
      @HyperOneStepDerivation Sign Func Pred HFunc HPred SM
        I [] p (Ty_Arrow (h_make_ctx_ty G) Phi) }.

Definition term_model_sequent_onestep_roll
  {I : b_ty} {G : @h_context Sign Func Pred}
  {Phi : @h_ty Sign Func Pred}
  (s : TermModelSequentOneStepHom I G Phi)
  : @hom (@efm_fiber Sign Func Pred HFunc HPred SM TM I)
      (@efm_interp_h_ctx Sign Func Pred HFunc HPred SM TM I G)
      (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Phi).
Proof.
  destruct s as [p step].
  exact (@closed_ctx_arrow_soundness_to_hom
    Sign Func Pred HFunc HPred SM TM I G Phi p
    (hyper_onestep_roll step)).
Defined.

Definition term_model_sequent_closed_derivation
  {I : b_ty} {G : @h_context Sign Func Pred}
  {Phi : @h_ty Sign Func Pred}
  (wf_G : All_WellFormed I G) (wf_Phi : WellFormed I Phi)
  (f : @hom (@efm_fiber Sign Func Pred HFunc HPred SM TM I)
      (@efm_interp_h_ctx Sign Func Pred HFunc HPred SM TM I G)
      (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Phi))
  : { p : @h_tm Sign Func Pred &
      @h_derivation Sign Func Pred HFunc HPred SM
        I [] p (Ty_Arrow (h_make_ctx_ty G) Phi) }.
Proof.
  unfold TM, efm_fiber, efm_interp_h_ctx, efm_interp_h_ty, efm_interp_ty in f.
  cbn in f.
  destruct f as [p d].
  pose proof (@term_model_interp_ctx_id
    Sign Func Pred HFunc HPred SM I G wf_G) as H_ctx.
  pose proof (@term_model_interp_id
    Sign Func Pred HFunc HPred SM I Phi wf_Phi) as H_phi.
  cbn in H_ctx, H_phi.
  rewrite H_ctx in d.
  rewrite H_phi in d.
  rewrite (interp_ty_id Sign Func I) in d.
  exists p.
  exact d.
Defined.

Definition term_model_sequent_onestep_unroll
  {I : b_ty} {G : @h_context Sign Func Pred}
  {Phi : @h_ty Sign Func Pred}
  (wf_G : All_WellFormed I G) (wf_Phi : WellFormed I Phi)
  (f : @hom (@efm_fiber Sign Func Pred HFunc HPred SM TM I)
      (@efm_interp_h_ctx Sign Func Pred HFunc HPred SM TM I G)
      (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Phi))
  : TermModelSequentOneStepHom I G Phi.
Proof.
  destruct (term_model_sequent_closed_derivation wf_G wf_Phi f) as [p d].
  exists p.
  exact (hyper_onestep_unroll d).
Defined.

Definition term_model_sequent_onestep_equiv
  {I : b_ty} {G : @h_context Sign Func Pred}
  {Phi : @h_ty Sign Func Pred}
  (s t : TermModelSequentOneStepHom I G Phi) : Prop :=
  @hom_equiv (@efm_fiber Sign Func Pred HFunc HPred SM TM I)
    (@efm_interp_h_ctx Sign Func Pred HFunc HPred SM TM I G)
    (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Phi)
    (term_model_sequent_onestep_roll s)
    (term_model_sequent_onestep_roll t).

Global Instance term_model_sequent_onestep_equiv_equivalence
  {I : b_ty} {G : @h_context Sign Func Pred}
  {Phi : @h_ty Sign Func Pred}
  : Equivalence (@term_model_sequent_onestep_equiv I G Phi).
Proof.
  unfold term_model_sequent_onestep_equiv.
  constructor.
  - intro x. reflexivity.
  - intros x y Hxy. symmetry. exact Hxy.
  - intros x y z Hxy Hyz.
    transitivity (term_model_sequent_onestep_roll y); assumption.
Defined.

Lemma TermModel_semantic_sequent_roll_unroll
  {I : b_ty} {G : @h_context Sign Func Pred}
  {Phi : @h_ty Sign Func Pred}
  (wf_G : All_WellFormed I G) (wf_Phi : WellFormed I Phi)
  (f : @hom (@efm_fiber Sign Func Pred HFunc HPred SM TM I)
      (@efm_interp_h_ctx Sign Func Pred HFunc HPred SM TM I G)
      (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Phi))
  : @hom_equiv (@efm_fiber Sign Func Pred HFunc HPred SM TM I)
      (@efm_interp_h_ctx Sign Func Pred HFunc HPred SM TM I G)
      (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Phi)
      (term_model_sequent_onestep_roll
        (term_model_sequent_onestep_unroll wf_G wf_Phi f))
      f.
Proof.
  apply (fiber_is_thin
    (@efm_interp_ty Sign Func Pred HFunc HPred SM TM I)).
Defined.

Lemma TermModel_semantic_sequent_unroll_roll
  {I : b_ty} {G : @h_context Sign Func Pred}
  {Phi : @h_ty Sign Func Pred}
  (wf_G : All_WellFormed I G) (wf_Phi : WellFormed I Phi)
  (s : TermModelSequentOneStepHom I G Phi)
  : term_model_sequent_onestep_equiv
      (term_model_sequent_onestep_unroll wf_G wf_Phi
        (term_model_sequent_onestep_roll s)) s.
Proof.
  unfold term_model_sequent_onestep_equiv.
  apply (fiber_is_thin
    (@efm_interp_ty Sign Func Pred HFunc HPred SM TM I)).
Defined.

Class TermModelSemanticSequentOneStepFixedPoint :=
  mk_TermModelSemanticSequentOneStepFixedPoint {
  semantic_sequent_fixed_roll_unroll :
    forall {I : b_ty} {G : @h_context Sign Func Pred}
      {Phi : @h_ty Sign Func Pred}
      (wf_G : All_WellFormed I G) (wf_Phi : WellFormed I Phi)
      (f : @hom (@efm_fiber Sign Func Pred HFunc HPred SM TM I)
        (@efm_interp_h_ctx Sign Func Pred HFunc HPred SM TM I G)
        (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Phi)),
      @hom_equiv (@efm_fiber Sign Func Pred HFunc HPred SM TM I)
        (@efm_interp_h_ctx Sign Func Pred HFunc HPred SM TM I G)
        (@efm_interp_h_ty Sign Func Pred HFunc HPred SM TM I Phi)
        (term_model_sequent_onestep_roll
          (term_model_sequent_onestep_unroll wf_G wf_Phi f)) f;
  semantic_sequent_fixed_unroll_roll :
    forall {I : b_ty} {G : @h_context Sign Func Pred}
      {Phi : @h_ty Sign Func Pred}
      (wf_G : All_WellFormed I G) (wf_Phi : WellFormed I Phi)
      (s : TermModelSequentOneStepHom I G Phi),
      term_model_sequent_onestep_equiv
        (term_model_sequent_onestep_unroll wf_G wf_Phi
          (term_model_sequent_onestep_roll s)) s
}.

Instance TermModel_SemanticSequentOneStepFixedPoint
  : TermModelSemanticSequentOneStepFixedPoint.
Proof.
  constructor.
  - intros I G Phi wf_G wf_Phi f.
    apply TermModel_semantic_sequent_roll_unroll.
  - intros I G Phi wf_G wf_Phi s.
    apply TermModel_semantic_sequent_unroll_roll.
Defined.

Class TermModelConcreteOneStepFixedPoint :=
  mk_TermModelConcreteOneStepFixedPoint {
  #[global] term_model_raw_onestep_fixed_point ::
    @EpsilonFullOneStepFixedPoint Sign Func Pred HFunc HPred SM;
  #[global] term_model_semantic_base_onestep_fixed_point ::
    TermModelSemanticBaseOneStepFixedPoint;
  #[global] term_model_semantic_fiber_onestep_fixed_point ::
    TermModelSemanticFiberOneStepFixedPoint;
  #[global] term_model_semantic_sequent_onestep_fixed_point ::
    TermModelSemanticSequentOneStepFixedPoint
}.

Instance TermModel_ConcreteOneStepFixedPoint
  : TermModelConcreteOneStepFixedPoint.
Proof.
  constructor.
  - apply (@TermModel_EpsilonFullOneStepFixedPoint
      Sign Func Pred HFunc HPred SM).
  - apply TermModel_SemanticBaseOneStepFixedPoint.
  - apply TermModel_SemanticFiberOneStepFixedPoint.
  - apply TermModel_SemanticSequentOneStepFixedPoint.
Defined.

End EpsilonFullTermModelFixedPoint.
