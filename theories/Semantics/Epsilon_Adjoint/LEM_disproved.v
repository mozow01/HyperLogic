(* theories/Semantics/Epsilon_Adjoint/LEM_disproved.v *)

Require Import Coq.Logic.Classical.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Classes.Morphisms.

(* Kategóriaelméleti alapok *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import HyperLogic.Cat.Fibration.

(* Szintaxis és Epsilon Szemantika *)
Require Import HyperLogic.Logic.Base.Epsilon_Adjoint.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon_Adjoint.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon_Adjoint.Hyper_Syntax_Lemmas.

Require Import HyperLogic.Semantics.Epsilon_Adjoint.Base_Epsilon_Completeness.
Require Import HyperLogic.Semantics.Epsilon_Adjoint.Epsilon_Adjoint_Fibration.

(* FONTOS: Ide be kell húznod az Epsilon Soundness fájlodat! *)
Require Import HyperLogic.Semantics.Epsilon_Adjoint.Epsilon_Adjoint_Soundness.

(* ================================================================= *)
(* 1. A 3-ELEMŰ HEYTING ALGEBRA (H3)                                 *)
(* ================================================================= *)

Inductive H3 : Type := HBot | HMid | HTop.

(* Részbenrendezés: Bot <= Mid <= Top *)
Definition H3_le (x y : H3) : Prop :=
  match x, y with
  | HBot, _ => True
  | _, HTop => True
  | HMid, HMid => True
  | _, _ => False
  end.

Lemma H3_le_refl : forall x, H3_le x x. 
Proof. destruct x; simpl; exact I. Defined.

Lemma H3_le_trans : forall x y z, H3_le y z -> H3_le x y -> H3_le x z.
Proof. destruct x, y, z; simpl; tauto. Defined.

(* Logikai művelet H3-on (inf)*)
Definition H3_meet (x y : H3) : H3 :=
  match x, y with
  | HBot, _ | _, HBot => HBot
  | HTop, a | a, HTop => a
  | HMid, HMid => HMid
  end.

(* Logikai művelet H3-on (sup)*)
Definition H3_join (x y : H3) : H3 :=
  match x, y with
  | HTop, _ | _, HTop => HTop
  | HBot, a | a, HBot => a
  | HMid, HMid => HMid
  end.

(* Logikai művelet H3-on (imp)*)
Definition H3_impl (x y : H3) : H3 :=
  match x, y with
  | HBot, _ => HTop
  | HMid, HBot => HBot
  | HMid, HMid => HTop
  | HMid, HTop => HTop
  | HTop, a => a
  end.

(* A Végleges Fázisos Favágó Taktika *)
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

(* ================================================================= *)
(* 2. A H3 KATEGÓRIA (BiCartesian Closed)                            *)
(* ================================================================= *)

Instance H3_Setoid : SetoidCategory.
Proof.
  refine (mk_SetoidCategory H3 H3_le
    H3_le_refl H3_le_trans (fun _ _ _ _ => True) _ _ _ _ _);
  h3_crush.
Defined.

Instance H3_Cartesian : CartesianCategory H3_Setoid.
Proof.
  refine (mk_CartesianCategory H3_Setoid
    HTop (fun x => _) _
    H3_meet (fun x y z f g => _) (fun x y => _) (fun x y => _)
    _ _ _ _);
    h3_crush.
    Unshelve. all: h3_crush.
Defined.

Instance H3_Closed : CartesianClosedCategory H3_Setoid.
Proof.
  refine (mk_CartesianClosedCategory H3_Setoid H3_Cartesian
    (fun a b => H3_impl b a) _ _   
    _ _ _).
  Unshelve.
  all: h3_crush.
Defined.

Instance H3_BiClosed : BiCartesianClosedCategory H3_Closed.
Proof.
  refine (mk_BiCartesianClosedCategory H3_Setoid H3_Cartesian H3_Closed
    HBot _ _
    H3_join _ _ _
    _ _ _ _).
  Unshelve.
  all: h3_crush.
Defined.

(* ================================================================= *)
(* 3. A KONSTANS H3 FIBRÁCIÓ                                         *)
(* ================================================================= *)

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

(* ÁLTALÁNOSÍTOTT JAVÍTÁS: A Bázis Kategória itt az Epsilon szintaxis bázisa *)
Instance H3_GoodFibration {Sign : Type} {SM : SkolemMapping Sign} : GoodFibration (Base_SetoidCategory Sign).
Proof.
  refine {|
    Fiber := fun _ => H3_Setoid;
    fiber_is_thin := fun _ x y f g => I;
    Fiber_is_Cartesian := fun _ => H3_Cartesian;
    Fiber_is_Closed := fun _ => H3_Closed;
    Fiber_is_BiClosed := fun _ => H3_BiClosed;
    Pullback := fun _ _ _ => H3_IdentityFunctor;
    pullback_has_left_adjoint  := fun _ _ => H3_AdjointR;
    pullback_has_right_adjoint := fun _ _ => H3_AdjointL
  |}.
  Unshelve.
  all: intros; h3_crush. all: reflexivity.
Defined.

Instance H3_StrictGoodFibration {Sign : Type} {SM : SkolemMapping Sign} : StrictGoodFibration (Base_SetoidCategory Sign) H3_GoodFibration.
Proof.
  econstructor. 
  intros X Y M1 M2 H.
  assert (H_sym : h_base M2 ≅ h_base M1). { symmetry. exact H. }
  exists H_sym.
  exact I.
Defined.

(* ================================================================= *)
(* 4. A H3 EPSZILON HIPERMODELL                                      *)
(* ================================================================= *)

Instance H3_EpsilonHyperModel {Sign : Type} {SM : SkolemMapping Sign}
  : EpsilonHyperModel H3_StrictGoodFibration.
Proof.
  unshelve econstructor.

  - (* i_atom *)
    exact (fun p t I => HMid).

  - (* i_atom_pb *)
    intros p t I A f df.
    simpl.
    reflexivity.

  - (* i_atom_cong_global *)
    intros p I A t1 t2 d1 d2 Heq.
    simpl.
    reflexivity.
Defined.

(* ================================================================= *)
(* 4.5 A KONSTANS H3 MODELL EPSILON-ADJUNKT FIBRÁCIÓJA               *)
(* ================================================================= *)

Lemma H3_interp_h_ty_subst_const :
  forall {Sign : Type} {SM : SkolemMapping Sign}
         (I J : b_ty) (Phi : @h_ty Sign) (f : @b_tm Sign),
  @interp_h_ty
    Sign
    (Base_SetoidCategory Sign)
    (Base_CartesianCategory Sign)
    (Base_TwoSortCategory Sign)
    (Base_SyntacticEpsilonModel Sign)
    H3_GoodFibration
    H3_StrictGoodFibration
    H3_EpsilonHyperModel
    I
    (form_subst f Phi)
  =
  @interp_h_ty
    Sign
    (Base_SetoidCategory Sign)
    (Base_CartesianCategory Sign)
    (Base_TwoSortCategory Sign)
    (Base_SyntacticEpsilonModel Sign)
    H3_GoodFibration
    H3_StrictGoodFibration
    H3_EpsilonHyperModel
    J
    Phi.
Proof.
  intros Sign SM I J Phi.
  revert I J.

  induction Phi; intros I J f; simpl.
  - reflexivity.
  - reflexivity.

  - (* Ty_Prod *)
    rewrite (IHPhi1 I J f).
    rewrite (IHPhi2 I J f).
    reflexivity.

  - (* Ty_Sum *)
    rewrite (IHPhi1 I J f).
    rewrite (IHPhi2 I J f).
    reflexivity.

  - (* Ty_Arrow *)
    rewrite (IHPhi1 I J f).
    rewrite (IHPhi2 I J f).
    reflexivity.

  - (* Ty_Atom *)
    reflexivity.

  - (* Ty_All *)
    rewrite (IHPhi (b_Prod I b) (b_Prod J b) (b_subst_ext f)).
    reflexivity.

  - (* Ty_Ex *)
    rewrite (IHPhi (b_Prod I b) (b_Prod J b) (b_subst_ext f)).
    reflexivity.
Defined.

Instance H3_AdjointEpsilonFibration {Sign : Type} {SM : SkolemMapping Sign}
  : @AdjointEpsilonFibration
      Sign SM
      (Base_SetoidCategory Sign)
      (Base_CartesianCategory Sign)
      (Base_TwoSortCategory Sign)
      (Base_SyntacticEpsilonModel Sign)
      H3_GoodFibration
      H3_StrictGoodFibration
      H3_EpsilonHyperModel.
Proof.
  constructor.

  - (* eps_is_left_adj_obj *)
    intros I A Phi Hwf_Phi.

    cbn [left_adj_obj
         pullback_has_left_adjoint
         H3_GoodFibration
         H3_AdjointR].

    rewrite
      (@H3_interp_h_ty_subst_const
         Sign SM
         I
         (b_Prod I A)
         Phi
         (b_pair b_id (b_const A (skolem_index A Phi)))).

    reflexivity.

  - (* eps_functorial *)
    intros I A Phi Psi Hwf_Phi Hwf_Psi H_iso.

    rewrite
      (@H3_interp_h_ty_subst_const
         Sign SM
         I
         (b_Prod I A)
         Phi
         (b_pair b_id (b_const A (skolem_index A Phi)))).

    rewrite
      (@H3_interp_h_ty_subst_const
         Sign SM
         I
         (b_Prod I A)
         Psi
         (b_pair b_id (b_const A (skolem_index A Psi)))).

    exact H_iso.
Defined.
(* ================================================================= *)
(* 5. A KIZÁRT HARMADIK CÁFOLATA                                     *)
(* ================================================================= *)

Definition P_atom {Sign : Type} (I : b_ty) : @h_ty Sign := 
  Ty_Atom 0 b_unit.

Definition LEM_Formula {Sign : Type} (I : b_ty) : @h_ty Sign := 
  Ty_Sum (P_atom I) (Ty_Arrow (P_atom I) Ty_Void).

Lemma LEM_WellFormed : forall {Sign : Type} (I : b_ty),
  @WellFormed Sign I (LEM_Formula I).
Proof.
  intros Sign I.
  apply WF_Sum.
  - eapply WF_Atom. apply BT_Unit.
  - apply WF_Arrow.
    + eapply WF_Atom. apply BT_Unit.
    + apply WF_Void.
Defined. 

(* Epsilon-specifikus Nil kontextus *)
Lemma wf_ctx_nil_valid : forall {Sign : Type} (I : b_ty), @All_WellFormed Sign I nil.
Proof.
  intro I.
  apply AWF_Nil.
Defined.

(* ================================================================= *)
(* 5. A KIZÁRT HARMADIK CÁFOLATA ÉS SZINTAKTIKUS NEM-LEVEZETHETŐSÉGE *)
(* ================================================================= *)

Theorem LEM_Refuted_WF : 
  forall {Sign : Type} {SM : SkolemMapping Sign},
  ~ (forall (C : SetoidCategory)
            (CC : CartesianCategory C)
            (TSC : TwoSortCategory C)
            (BEM : @BaseEpsilonModel Sign C CC TSC)
            (GF : GoodFibration C)
            (SGF : StrictGoodFibration C GF)
            (HM : @EpsilonHyperModel Sign C CC TSC BEM GF SGF)
            (AdEHM : @AdjointEpsilonFibration Sign SM C CC TSC BEM GF SGF HM)
            (I : b_ty),
       inhabited
         (@hom (Fiber (interp_ty I))
               (@interp_h_ctx Sign C CC TSC BEM GF SGF HM I nil)
               (@interp_h_ty  Sign C CC TSC BEM GF SGF HM I (LEM_Formula I)))).
Proof.
  intros Sign SM H_univ.

  specialize
    (H_univ
       (Base_SetoidCategory Sign)
       (Base_CartesianCategory Sign)
       (Base_TwoSortCategory Sign)
       (Base_SyntacticEpsilonModel Sign)
       H3_GoodFibration
       H3_StrictGoodFibration
       H3_EpsilonHyperModel
       H3_AdjointEpsilonFibration
       b_Unit).

  destruct H_univ as [f_lem].
  simpl in f_lem.
  exact f_lem.
Defined.


Theorem LEM_Underivable_WF : 
  forall {Sign : Type} {SM : SkolemMapping Sign},
  (forall (I : b_ty),
      { p : @h_tm Sign &
        h_derivation I nil p (LEM_Formula I) }) -> False.
Proof.
  intros Sign SM H_all_der.

  apply LEM_Refuted_WF.

  intros C CC TSC BEM GF SGF HM AdEHM I_any.

  destruct (H_all_der I_any) as [p H_der].

  constructor.

  exact (@soundness
           Sign SM
           C CC
           TSC BEM GF SGF HM AdEHM
           I_any nil p (LEM_Formula I_any)
           H_der).
Defined.
