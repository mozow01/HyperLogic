
Require Import Coq.Classes.Morphisms.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import HyperLogic.Cat.Fibration.

Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Lemmas.
Require Import HyperLogic.Semantics.Simple.Base_Simple_Soundness.
Require Import HyperLogic.Semantics.Simple.Simple_Soundness.

Require Import HyperLogic.Semantics.Simple.Simple_Completeness.

(** Three-element Heyting algebra used by the countermodel. *)

Inductive H3 : Type := HBot | HMid | HTop.

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

(* Parallel morphisms are equal because [H3] is a poset. *)
Instance H3_Setoid : SetoidCategory.
Proof.
  refine (mk_SetoidCategory H3 H3_le
    H3_le_refl H3_le_trans (fun _ _ _ _ => True) _ _ _ _ _); h3_crush.
Defined.

Instance H3_Cartesian : CartesianCategory H3_Setoid.
Proof.
  refine (mk_CartesianCategory H3_Setoid
    HTop (fun x => _) _
    H3_meet (fun x y z f g => _) (fun x y => _) (fun x y => _)
    _ _ _ _); h3_crush.
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



(* Reindexing is identity because the fibration is constant. *)
Instance H3_IdentityFunctor : Functor H3_Setoid H3_Setoid.
Proof.
  refine (mk_Functor H3_Setoid H3_Setoid (fun x => x) _ _ _ _).
  Unshelve.
  all: h3_crush.
Defined.

(* The identity functor is both its own left and right adjoint. *)
Instance H3_AdjointL : IsLeftAdjoint H3_IdentityFunctor.
Proof.
  refine (mk_IsLeftAdjoint _ _ _ (fun x => x) _ _ _ _ _).
  Unshelve.
  all: h3_crush.
Defined.

Instance H3_AdjointR : IsRightAdjoint H3_IdentityFunctor.
Proof.
  refine (mk_IsRightAdjoint _ _ _ (fun x => x) _ _ _ _ _).
  Unshelve.
  all: h3_crush.
Defined.

Instance H3_GoodFibration : GoodFibration (@Base_SetoidCategory nat).
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

Instance H3_StrictGoodFibration : StrictGoodFibration (@Base_SetoidCategory nat) H3_GoodFibration.
Proof.
  econstructor. 
  intros X Y M1 M2 H.
  
  assert (H_sym : h_base M2 ≅ h_base M1).
  { symmetry. exact H. }
  
  exists H_sym. 
  
  exact I.
Defined.


Instance H3_HyperModel : HyperModel H3_StrictGoodFibration.
Proof.
  unshelve econstructor.
  
  -
    exact (fun p t I A dt => HMid).
    
  -
    intros. reflexivity. 
    
  -
    intros I J f g df dg Heq. 
    apply base_soundness_equational. 
    exact Heq.
    
  -
    intros. reflexivity.
Defined.

(** Countermodel to excluded middle. *)

Definition P_atom (I : b_ty) : h_ty := 
  Ty_Atom 0 b_unit.

Definition LEM_Formula (I : b_ty) : h_ty := 
  Ty_Sum (P_atom I) (Ty_Arrow (P_atom I) Ty_Void).
  


Theorem LEM_Refuted : 
  ~ (forall (C : SetoidCategory) (CC : CartesianCategory C)
            (TSC : TwoSortCategory C) (GF : GoodFibration C) 
            (SGF : StrictGoodFibration C GF) (HM : HyperModel SGF)
            (I : b_ty) (wfc : wf_ctx I nil) (wf_Phi : WellFormed I (LEM_Formula I)),
       inhabited (hom (interp_h_ctx I nil wfc) (interp_h_ty I (LEM_Formula I) wf_Phi))).
Proof.
  intro H_univ.
  
  assert (wf_LEM : WellFormed b_Unit (LEM_Formula b_Unit)).
  { apply WF_Sum.
    - eapply WF_Atom. apply BT_Unit.
    - apply WF_Arrow. eapply WF_Atom. apply BT_Unit. apply WF_Void. }
    
  specialize (H_univ 
               (@Base_SetoidCategory nat) 
               (@Base_CartesianCategory nat)
               (@Base_TwoSortCategory nat)
               H3_GoodFibration 
               H3_StrictGoodFibration 
               H3_HyperModel 
               b_Unit
               (WFC_nil b_Unit)
               wf_LEM).
               
  destruct H_univ as [f_lem].
  
  simpl in f_lem.
  
  exact f_lem.
Defined.

Theorem LEM_Underivable : 
  (forall (I : b_ty) (wfc : wf_ctx I nil) (wf_Phi : WellFormed I (LEM_Formula I)),
       { p : h_tm & h_derivation I nil p (LEM_Formula I) }) -> False.
Proof.
  intro H_all_der.
  
  apply LEM_Refuted.
  
  intros C CC TSC GF SGF HM I_any wfc_any wf_Phi_any.
  
  destruct (H_all_der I_any wfc_any wf_Phi_any) as [p H_der].
  
  constructor.
  
  apply (hyper_soundness_inhabited H_der wfc_any wf_Phi_any).
Defined.


Lemma LEM_WellFormed : forall (I : b_ty), WellFormed I (LEM_Formula I).
Proof.
  intro I.
  apply WF_Sum.
  - eapply WF_Atom. apply BT_Unit.
  - apply WF_Arrow. eapply WF_Atom. apply BT_Unit. apply WF_Void.
Defined. (* [Defined] keeps the witness reducible for simplification. *)

Lemma wf_ctx_nil_valid : forall (I : b_ty), wf_ctx I nil.
Proof.
  intro I.
  constructor.
Defined.


Theorem LEM_Refuted_WF : 
  ~ (forall (C : SetoidCategory) (CC : CartesianCategory C)
            (TSC : TwoSortCategory C) (GF : GoodFibration C) 
            (SGF : StrictGoodFibration C GF) (HM : HyperModel SGF)
            (I : b_ty),
       inhabited (hom (interp_h_ctx I nil (wf_ctx_nil_valid I)) 
                      (interp_h_ty I (LEM_Formula I) (LEM_WellFormed I)))).
Proof.
  intro H_univ.
  
  specialize (H_univ 
               (@Base_SetoidCategory nat) 
               (@Base_CartesianCategory nat)
               (@Base_TwoSortCategory nat)
               H3_GoodFibration 
               H3_StrictGoodFibration 
               H3_HyperModel 
               b_Unit).
               
  destruct H_univ as [f_lem].
  simpl in f_lem.
  exact f_lem.
Defined.

(** Excluded middle is not derivable. *)

Theorem LEM_Underivable_WF : 
  (forall (I : b_ty), { p : h_tm & h_derivation I nil p (LEM_Formula I) }) -> False.
Proof.
  intro H_all_der.
  
  apply LEM_Refuted.
  intros C CC TSC GF SGF HM I_any.
  
  destruct (H_all_der I_any) as [p H_der].
  
  constructor.
  
  apply (hyper_soundness_inhabited H_der wfc wf_Phi).
Defined.
