

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

(** Five-element Heyting algebra used by the countermodel. *)

Inductive H5 : Type := HBot | H1 | H2 | H12 | HTop.

Definition H5_le (x y : H5) : Prop :=
  match x, y with
  | HBot, _ => True
  | _, HTop => True
  | H1, H1 | H1, H12 => True
  | H2, H2 | H2, H12 => True
  | H12, H12 => True
  | _, _ => False
  end.

Lemma H5_le_refl : forall x, H5_le x x. Proof. destruct x; exact I. Defined.
Lemma H5_le_trans : forall x y z, H5_le y z -> H5_le x y -> H5_le x z.
Proof. destruct x, y, z; simpl; tauto. Defined.

Definition H5_meet (x y : H5) : H5 :=
  match x, y with
  | HBot, _ | _, HBot => HBot
  | HTop, a | a, HTop => a
  | H1, H1 | H1, H12 | H12, H1 => H1
  | H2, H2 | H2, H12 | H12, H2 => H2
  | H12, H12 => H12
  | H1, H2 | H2, H1 => HBot
  end.

Definition H5_join (x y : H5) : H5 :=
  match x, y with
  | HTop, _ | _, HTop => HTop
  | HBot, a | a, HBot => a
  | H12, _ | _, H12 => H12
  | H1, H1 => H1
  | H2, H2 => H2
  | H1, H2 | H2, H1 => H12
  end.

Definition H5_impl (x y : H5) : H5 :=
  match x, y with
  | HBot, _ | _, HTop => HTop
  | HTop, a => a
  | H12, H1 => H1
  | H12, H2 => H2
  | H12, HBot => HBot
  | H1, H1 | H1, H12 => HTop
  | H1, H2 | H1, HBot => H2
  | H2, H2 | H2, H12 => HTop
  | H2, H1 | H2, HBot => H1
  | H12, H12 => HTop
  end.




Definition H5_Pred (X : Type) := X -> H5.
Definition H5_Pred_le {X : Type} (P Q : H5_Pred X) : Prop := forall x, H5_le (P x) (Q x).
Ltac h5_pred_crush :=
  repeat intro;
  
  repeat match goal with
  | |- Proper _ _ => red
  | |- respectful _ _ _ _ => red
  | |- RelationClasses.Equivalence _ => split; red
  end;
  
  cbn in *;
  try unfold hom in *;
  try unfold H5_Pred_le in *; 
  
  repeat match goal with
  | H : ?T |- _ => 
      let T' := eval hnf in T in
      lazymatch T with
      | forall _, _ => fail
      | _ => lazymatch T' with
             | forall _, _ => change T' in H
             | _ => fail
             end
      end
  end;
  
  match goal with
  | |- ?G => let G' := eval hnf in G in change G'
  end;
  
  repeat intro;
  
  repeat match goal with
  | H : forall w, H5_le (?P w) _ |- context [ ?P ?z ] => 
      specialize (H z)
  | H : forall w, H5_le _ (?Q w) |- context [ ?Q ?z ] => 
      specialize (H z)
  | H : forall w, H5_le (?P w) _, H2 : context [ ?P ?z ] |- _ => 
      specialize (H z)
  | H : forall w, H5_le _ (?Q w), H2 : context [ ?Q ?z ] |- _ => 
      specialize (H z)
  end;
  
  simpl in *;
  
  repeat match goal with
  | |- context [ ?P ?x ] =>
      is_var P;
      let T := type of P in
      lazymatch eval hnf in T with
      | _ -> H5 => destruct (P x); simpl in *
      end
      
  | H : context [ ?P ?x ] |- _ =>
      is_var P;
      let T := type of P in
      lazymatch eval hnf in T with
      | _ -> H5 => destruct (P x); simpl in *
      end
      
  | y : H5 |- _ => is_var y; destruct y; simpl in *
  end;
  
  intuition; auto; try exact I.

Instance H5_Pred_Setoid (X : Type) : SetoidCategory.
Proof. 
  refine (mk_SetoidCategory (H5_Pred X) H5_Pred_le _ _ (fun _ _ _ _ => True) _ _ _ _ _). 
  Unshelve. all: h5_pred_crush.  
Defined.

Instance H5_Pred_Cartesian (X : Type) : CartesianCategory (H5_Pred_Setoid X).
Proof. 
  refine (mk_CartesianCategory (H5_Pred_Setoid X) 
    (fun _ => HTop) (fun _ => _) _ 
    (fun P Q x => H5_meet (P x) (Q x)) 
    (fun P Q R f g => _) (fun P Q => _) (fun P Q => _) _ _ _ _). 
  Unshelve. all: h5_pred_crush. 
Defined.

Instance H5_Pred_Closed (X : Type) : CartesianClosedCategory (H5_Pred_Setoid X).
Proof. 
  refine (mk_CartesianClosedCategory _ (H5_Pred_Cartesian X) 
    (fun P Q x => H5_impl (Q x) (P x))
    _ _ _ _ _). 
  Unshelve. all: h5_pred_crush. 
Defined.

Instance H5_Pred_BiClosed (X : Type) : BiCartesianClosedCategory (H5_Pred_Closed X).
Proof. 
  refine (mk_BiCartesianClosedCategory _ _ (H5_Pred_Closed X) 
    (fun _ => HBot) _ _ 
    (fun P Q x => H5_join (P x) (Q x)) _ _ _ _ _ _ _). 
  Unshelve. all: h5_pred_crush. 
Defined.


Instance Subst_Functor {X Y : Type} (f : Y -> X) : Functor (H5_Pred_Setoid X) (H5_Pred_Setoid Y).
Proof. 
  refine (mk_Functor (H5_Pred_Setoid X) (H5_Pred_Setoid Y) 
          (fun (P : H5_Pred X) (y : Y) => P (f y)) 
          _ _ _ _). 
  Unshelve. all: h5_pred_crush. 
Defined.


(** Finite base category used for computation. *)

Inductive FinObj : Type :=
  | F_Unit : FinObj
  | F_Bool : FinObj
  | F_Prod : FinObj -> FinObj -> FinObj.

Fixpoint interp_F (A : FinObj) : Type :=
  match A with
  | F_Unit => Coq.Init.Datatypes.unit
  | F_Bool => bool
  | F_Prod A B => Coq.Init.Datatypes.prod (interp_F A) (interp_F B)
  end.

Definition FinHom (A B : FinObj) := interp_F A -> interp_F B.
Definition FinEquiv {A B : FinObj} (f g : FinHom A B) : Prop := forall x, f x = g x.

Ltac fin_crush :=
  repeat intro;
  repeat match goal with
  | |- Proper _ _ => red
  | |- respectful _ _ _ _ => red
  | |- RelationClasses.Equivalence _ => split; red
  end;
  repeat intro; simpl in *; auto; try congruence.

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
  unshelve econstructor.
  - exact F_Bool.
  -
    intro Heq. discriminate Heq.
Defined.

Require Import Coq.Bool.Bool.

(** Quantifiers are computed as finite joins and meets. *)

Fixpoint Fin_sup {Y : FinObj} : (interp_F Y -> H5) -> H5 :=
  match Y return (interp_F Y -> H5) -> H5 with
  | F_Unit => fun P => P tt
  | F_Bool => fun P => H5_join (P true) (P false)
  | F_Prod A B => fun P => Fin_sup (fun a => Fin_sup (fun b => P (a, b)))
  end.

Fixpoint Fin_inf {Y : FinObj} : (interp_F Y -> H5) -> H5 :=
  match Y return (interp_F Y -> H5) -> H5 with
  | F_Unit => fun P => P tt
  | F_Bool => fun P => H5_meet (P true) (P false)
  | F_Prod A B => fun P => Fin_inf (fun a => Fin_inf (fun b => P (a, b)))
  end.

Fixpoint eq_fin {X : FinObj} : interp_F X -> interp_F X -> bool :=
  match X return interp_F X -> interp_F X -> bool with
  | F_Unit => fun _ _ => true
  | F_Bool => fun b1 b2 => Bool.eqb b1 b2
  | F_Prod A B => fun p1 p2 => andb (eq_fin (fst p1) (fst p2)) (eq_fin (snd p1) (snd p2))
  end.


Definition Fin_Exists_val {X Y : FinObj} (f : FinHom Y X) (P : interp_F Y -> H5) (x : interp_F X) : H5 :=
  Fin_sup (fun y => if eq_fin x (f y) then P y else HBot).

Definition Fin_Forall_val {X Y : FinObj} (f : FinHom Y X) (P : interp_F Y -> H5) (x : interp_F X) : H5 :=
  Fin_inf (fun y => if eq_fin x (f y) then P y else HTop).

Require Import Coq.Bool.Bool.


Lemma eq_fin_refl : forall (X : FinObj) (x : interp_F X), eq_fin x x = true.
Proof.
  induction X; simpl; intros.
  - destruct x. reflexivity.
  - destruct x; reflexivity.
  - destruct x. rewrite IHX1, IHX2. reflexivity.
Qed.

Lemma eq_fin_eq : forall (X : FinObj) (x1 x2 : interp_F X), eq_fin x1 x2 = true -> x1 = x2.
Proof.
  induction X; simpl; intros.
  - destruct x1, x2. reflexivity.
  - destruct x1, x2; simpl in H; try discriminate H; reflexivity.
  - destruct x1 as [a1 b1], x2 as [a2 b2].
    apply Bool.andb_true_iff in H. destruct H.
    apply IHX1 in H. apply IHX2 in H0. subst. simpl in H. simpl in H0. subst. reflexivity.
Qed.

Lemma Fin_sup_upper_bound : forall (Y : FinObj) (F : interp_F Y -> H5) (y : interp_F Y), H5_le (F y) (@Fin_sup Y F).
Proof.
  induction Y; simpl; intros.
  - destruct y. destruct (F tt); exact I.
  - destruct y; destruct (F true); destruct (F false); exact I.
  - destruct y as [a b].
    assert (H1 := IHY2 (fun b' => F (a, b')) b).
    assert (H2 := IHY1 (fun a' => Fin_sup (fun b' => F (a', b'))) a).
    exact (H5_le_trans _ _ _ H2 H1).
Qed.

Lemma Fin_sup_least_bound : forall (Y : FinObj) (F : interp_F Y -> H5) (bound : H5),
  (forall y, H5_le (F y) bound) -> H5_le (@Fin_sup Y F) bound.
Proof.
  induction Y; simpl; intros.
  - apply H.
  - pose proof (H true). pose proof (H false).
    destruct bound; destruct (F true); destruct (F false); simpl in *; tauto || exact I.
  - apply IHY1. intros a. apply IHY2. intros b. apply H.
Qed.

Lemma Fin_inf_lower_bound : forall (Y : FinObj) (F : interp_F Y -> H5) (y : interp_F Y), H5_le (@Fin_inf Y F) (F y).
Proof.
  induction Y; simpl; intros.
  - destruct y. destruct (F tt); exact I.
  - destruct y; destruct (F true); destruct (F false); exact I.
  - destruct y as [a b].
    assert (H1 := IHY2 (fun b' => F (a, b')) b).
    assert (H2 := IHY1 (fun a' => Fin_inf (fun b' => F (a', b'))) a).
    exact (H5_le_trans _ _ _ H1 H2).
Qed.

Lemma Fin_inf_greatest_bound : forall (Y : FinObj) (F : interp_F Y -> H5) (bound : H5),
  (forall y, H5_le bound (F y)) -> H5_le bound (@Fin_inf Y F).
Proof.
  induction Y; simpl; intros.
  - apply H.
  - pose proof (H true). pose proof (H false).
    destruct bound; destruct (F true); destruct (F false); simpl in *; tauto || exact I.
  - apply IHY1. intros a. apply IHY2. intros b. apply H.
Qed.


Instance Fin_Subst_Functor {X Y : FinObj} (f : FinHom Y X) : Functor (H5_Pred_Setoid (interp_F X)) (H5_Pred_Setoid (interp_F Y)).
Proof. 
  refine (mk_Functor (H5_Pred_Setoid (interp_F X)) (H5_Pred_Setoid (interp_F Y)) 
          (fun (P : H5_Pred (interp_F X)) (y : interp_F Y) => P (f y)) 
          _ _ _ _). 
  Unshelve. all: h5_pred_crush. 
Defined.

Instance Fin_Subst_IsRightAdjoint {X Y : FinObj} (f : FinHom Y X) : IsRightAdjoint (Fin_Subst_Functor f).
Proof.
  refine (mk_IsRightAdjoint _ _ (Fin_Subst_Functor f)
    (fun P => Fin_Exists_val f P)
    
    ltac:(
      intros P y; unfold Fin_Exists_val;
      pose proof (Fin_sup_upper_bound Y (fun y' => if eq_fin (f y) (f y') then P y' else HBot) y) as Hsup;
      simpl in Hsup;
      rewrite eq_fin_refl in Hsup; 
      exact Hsup
    )
    
    ltac:(
      intros P Q Hle x; unfold Fin_Exists_val;
      apply Fin_sup_least_bound; intro y;
      simpl;
      destruct (eq_fin x (f y)) eqn:Heq;
      [ apply eq_fin_eq in Heq; subst; apply Hle | exact I ]
    )
    
    _ _ _).
  Unshelve.
  all: h5_pred_crush.
Defined.

Instance Fin_Subst_IsLeftAdjoint {X Y : FinObj} (f : FinHom Y X) : IsLeftAdjoint (Fin_Subst_Functor f).
Proof.
  refine (mk_IsLeftAdjoint _ _ (Fin_Subst_Functor f)
    (fun P => Fin_Forall_val f P)
    
    ltac:(
      intros P y; unfold Fin_Forall_val;
      pose proof (Fin_inf_lower_bound Y (fun y' => if eq_fin (f y) (f y') then P y' else HTop) y) as Hinf;
      simpl in Hinf;
      rewrite eq_fin_refl in Hinf; 
      exact Hinf
    )
    
    ltac:(
      intros Q P Hle x; unfold Fin_Forall_val;
      apply Fin_inf_greatest_bound; intro y;
      simpl;
      destruct (eq_fin x (f y)) eqn:Heq;
      [ apply eq_fin_eq in Heq; subst; apply Hle | destruct (Q x); exact I ]
    )
    
    _ _ _).
  Unshelve.
  all: h5_pred_crush.
Defined.

(** Finite hyperdoctrine countermodel. *)

Instance Fin_GoodFibration : GoodFibration Fin_Setoid.
Proof.
  refine {|
    Fiber := fun X => H5_Pred_Setoid (interp_F X);
    fiber_is_thin := fun _ _ _ _ _ => I;
    Fiber_is_Cartesian := fun X => H5_Pred_Cartesian (interp_F X);
    Fiber_is_Closed := fun X => H5_Pred_Closed (interp_F X);
    Fiber_is_BiClosed := fun X => H5_Pred_BiClosed (interp_F X);
    Pullback := fun X Y f => Fin_Subst_Functor f;
    pullback_has_left_adjoint := fun X Y => Fin_Subst_IsRightAdjoint _;
    pullback_has_right_adjoint := fun X Y => Fin_Subst_IsLeftAdjoint _
  |}.
  Unshelve.(interp_F Y -> H5)
  Ltac solve_trivial_iso :=
    intros; unshelve econstructor;
    [ intros x; simpl; try apply H5_le_refl; try exact Logic.I
    | intros x; simpl; try apply H5_le_refl; try exact Logic.I
    | unfold hom_equiv; compute; exact Logic.I
    | unfold hom_equiv; compute; exact Logic.I ].

  - solve_trivial_iso.
  - solve_trivial_iso.
  - solve_trivial_iso.
  - solve_trivial_iso.
  - solve_trivial_iso.
  - solve_trivial_iso.
  - solve_trivial_iso.
  - intros I J K f A.
    unshelve econstructor.
    +
      intros k. simpl. unfold Fin_Exists_val. simpl.
      apply Fin_sup_least_bound. intros i.
      apply Fin_sup_least_bound. intros j.
      destruct (eq_fin (f k) i) eqn:Heq.
      * apply eq_fin_eq in Heq. subst i.
        assert (H1 := Fin_sup_upper_bound K (fun a => Fin_sup (fun b : interp_F J => if eq_fin k a then A (f a, b) else HBot)) k).
        assert (H2 := Fin_sup_upper_bound J (fun b => if eq_fin k k then A (f k, b) else HBot) j).
        simpl in H1; rewrite eq_fin_refl in H1. 
        simpl in H2; rewrite eq_fin_refl in H2.
        exact (H5_le_trans _ _ _ H1 H2).
      * simpl. reflexivity.
    +
      intros k. simpl. unfold Fin_Exists_val. simpl.
      apply Fin_sup_least_bound. intros k'.
      apply Fin_sup_least_bound. intros j.
      destruct (eq_fin k k') eqn:Heq.
      * apply eq_fin_eq in Heq. subst k'.
        assert (H1 := Fin_sup_upper_bound I (fun a => Fin_sup (fun b : interp_F J => if eq_fin (f k) a then A (a, b) else HBot)) (f k)).
        assert (H2 := Fin_sup_upper_bound J (fun b => if eq_fin (f k) (f k) then A (f k, b) else HBot) j).
        simpl in H1; rewrite eq_fin_refl in H1.
        simpl in H2; rewrite eq_fin_refl in H2.
        exact (H5_le_trans _ _ _ H1 H2).
      * simpl. reflexivity.
    + unfold hom_equiv; compute; reflexivity.
    + unfold hom_equiv; compute; reflexivity.

  - intros I_obj J_obj K_obj f A.
    unshelve econstructor.
    +
      intros k. simpl. unfold Fin_Forall_val. simpl.
      apply Fin_inf_greatest_bound. intros k'.
      apply Fin_inf_greatest_bound. intros j.
      destruct (eq_fin k k') eqn:Heq.
      * apply eq_fin_eq in Heq. subst k'.
        assert (H1 := Fin_inf_lower_bound I_obj (fun a => Fin_inf (fun b : interp_F J_obj => if eq_fin (f k) a then A (a, b) else HTop)) (f k)).
        assert (H2 := Fin_inf_lower_bound J_obj (fun b => if eq_fin (f k) (f k) then A (f k, b) else HTop) j).
        simpl in H1; rewrite eq_fin_refl in H1.
        simpl in H2; rewrite eq_fin_refl in H2.
        exact (H5_le_trans _ _ _ H2 H1).
      * match goal with |- H5_le ?x _ => destruct x; exact Logic.I end.
    +
      intros k. simpl. unfold Fin_Forall_val. simpl.
      apply Fin_inf_greatest_bound. intros i.
      apply Fin_inf_greatest_bound. intros j.
      destruct (eq_fin (f k) i) eqn:Heq.
      * apply eq_fin_eq in Heq. subst i.
        assert (H1 := Fin_inf_lower_bound K_obj (fun a => Fin_inf (fun b : interp_F J_obj => if eq_fin k a then A (f a, b) else HTop)) k).
        assert (H2 := Fin_inf_lower_bound J_obj (fun b => if eq_fin k k then A (f k, b) else HTop) j).
        simpl in H1; rewrite eq_fin_refl in H1.
        simpl in H2; rewrite eq_fin_refl in H2.
        exact (H5_le_trans _ _ _ H2 H1).
      * match goal with |- H5_le ?x _ => destruct x; exact Logic.I end.
    + unfold hom_equiv; compute; reflexivity.
    + unfold hom_equiv; compute; reflexivity.

  - intros I_obj J_obj f g Heq A.
    unshelve econstructor.
    + intros x; simpl; rewrite (Heq x); apply H5_le_refl.
    + intros x; simpl; rewrite (Heq x); apply H5_le_refl.
    + unfold hom_equiv; compute; reflexivity.
    + unfold hom_equiv; compute; reflexivity.

  Unshelve.
  all: try (intros; econstructor; h5_pred_crush).
Defined.


Instance Fin_StrictGoodFibration : StrictGoodFibration Fin_Setoid Fin_GoodFibration.
Proof.
  econstructor.
  intros X Y M1 M2 H.
  exists (fun x => eq_sym (H x)).
  exact I.
Defined.


(* The predicate maps the booleans to the two incomparable values. *)
Definition Drinker_Pred (b : bool) : H5 :=
  if b then H1 else H2.

Instance Fin_HyperModel : HyperModel Fin_StrictGoodFibration.
Proof.
  unshelve econstructor.
  -
    intros p t I A dt env.
    exact (
      match interp_ty A as FA return interp_F FA -> H5 with
      | F_Bool => Drinker_Pred
      | _ => fun _ => HBot
      end (interp_tm dt env)
    ).
    
  -
    intros. unshelve econstructor.
    + intros env; simpl; apply H5_le_refl.
    + intros env; simpl; apply H5_le_refl.
    + exact Logic.I.
    + exact Logic.I.
    
  -
    intros I J f g df dg Heq.
    apply base_soundness_equational. exact Heq.
    
  -
    intros p t1 t2 I A d1 d2 H.
    unshelve econstructor.
    +
      intros env. simpl.
      assert (Heq : interp_tm d1 ≅ interp_tm d2).
      { apply base_soundness_equational. exact H. }
      
      pose proof (Heq env) as Heq_env.
      
      rewrite Heq_env. apply H5_le_refl.
      
    +
      intros env. simpl.
      assert (Heq : interp_tm d1 ≅ interp_tm d2).
      { apply base_soundness_equational. exact H. }
      pose proof (Heq env) as Heq_env.
      
      rewrite Heq_env. apply H5_le_refl.
      
    + exact Logic.I.
    + exact Logic.I.
Defined.

Lemma wf_ctx_nil_valid : forall (I : b_ty), wf_ctx I nil.
Proof. intro I; constructor. Defined.

Definition P_x (I D : b_ty) : h_ty := Ty_Atom 0 b_snd.
Definition Ex_P (I D : b_ty) : h_ty := Ty_Ex D (P_x I D).

Definition DualDrinkerFormula (I D : b_ty) : h_ty :=
  Ty_Ex D (Ty_Arrow (form_pullback b_fst (Ex_P I D)) (P_x I D)).

Lemma DualDrinker_WellFormed : forall I D, WellFormed I (DualDrinkerFormula I D).
Proof.
  intros I D.
  unfold DualDrinkerFormula, Ex_P, P_x.
  repeat econstructor.
Defined. (* [Defined] keeps the witness reducible for computation. *)

Theorem DualDrinker_Refuted : 
  ~ (forall (C : SetoidCategory) (CC : CartesianCategory C)
            (TSC : TwoSortCategory C) (GF : GoodFibration C) 
            (SGF : StrictGoodFibration C GF) (HM : HyperModel SGF)
            (I D : b_ty),
       inhabited (hom (interp_h_ctx I nil (wf_ctx_nil_valid I)) 
                      (interp_h_ty I (DualDrinkerFormula I D) (DualDrinker_WellFormed I D)))).
Proof.
  intro H_univ.
  
  specialize (H_univ 
               Fin_Setoid 
               Fin_Cartesian
               Fin_TwoSort
               Fin_GoodFibration 
               Fin_StrictGoodFibration 
               Fin_HyperModel 
               b_Unit
               b_S).
               
  destruct H_univ as [f_drinker].
  
  pose proof (f_drinker tt) as f_eval.
  
  (* Finiteness lets [compute] reduce the semantic claim to [False]. *)
  compute in f_eval.
  
  exact f_eval.
Defined.


(** The dual drinker formula is not derivable. *)
Theorem DualDrinker_Underivable : 
  (forall (I D : b_ty), { p : h_tm & h_derivation I nil p (DualDrinkerFormula I D) }) -> False.
Proof.
  intro H_all_der.
  
  apply DualDrinker_Refuted.
  intros C CC TSC GF SGF HM I_any D_any.
  
  destruct (H_all_der I_any D_any) as [p H_der].
  constructor.
  
  apply (hyper_soundness_inhabited H_der (wf_ctx_nil_valid I_any) (DualDrinker_WellFormed I_any D_any)).
Defined.
