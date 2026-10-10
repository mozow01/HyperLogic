(** Arbitrary-index predicate quantifiers require chosen Type-valued bounds. *)
Require Import HyperLogic.Semantics.EpsilonFull.FiniteHeytingPredicates.
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import HyperLogic.Cat.Fibration.
Require Import Coq.Classes.Morphisms.

Set Universe Polymorphism.

Class ChosenIndexedHeytingBounds (H : FiniteHeytingAlgebra) := {
  indexed_sup : forall (A : Type), (A -> fh_carrier) -> fh_carrier;
  indexed_inf : forall (A : Type), (A -> fh_carrier) -> fh_carrier;
  indexed_sup_upper : forall A (F : A -> fh_carrier) a,
    fh_le (F a) (indexed_sup A F);
  indexed_sup_least : forall A (F : A -> fh_carrier) b,
    (forall a, fh_le (F a) b) -> fh_le (indexed_sup A F) b;
  indexed_inf_lower : forall A (F : A -> fh_carrier) a,
    fh_le (indexed_inf A F) (F a);
  indexed_inf_greatest : forall A (F : A -> fh_carrier) b,
    (forall a, fh_le b (F a)) -> fh_le b (indexed_inf A F)
}.

Section ArbitraryBase.
Context {H : FiniteHeytingAlgebra} {B : ChosenIndexedHeytingBounds H}.
Variable S : Type.

Inductive GeneratedBase : Type :=
| base_one : GeneratedBase
| base_sort : GeneratedBase
| base_product : GeneratedBase -> GeneratedBase -> GeneratedBase.

Fixpoint base_carrier (X : GeneratedBase) : Type :=
  match X with
  | base_one => Datatypes.unit
  | base_sort => S
  | base_product X Y => (base_carrier X * base_carrier Y)%type
  end.

Definition Predicate (X : Type) : Type := X -> fh_carrier.
Definition predicate_le {X : Type} (P Q : Predicate X) : Prop :=
  forall x, fh_le (P x) (Q x).
Definition reindex {X Y : Type} (f : X -> Y) (Q : Predicate Y) : Predicate X :=
  fun x => Q (f x).
Definition sigma {X A : Type} (P : Predicate (X * A)) : Predicate X :=
  fun x => indexed_sup A (fun a => P (x,a)).
Definition pi {X A : Type} (P : Predicate (X * A)) : Predicate X :=
  fun x => indexed_inf A (fun a => P (x,a)).

Lemma sigma_projection_adjunction {X A : Type}
  (P : Predicate (X * A)) (Q : Predicate X) :
  predicate_le (sigma P) Q <->
  predicate_le P (reindex (@fst X A) Q).
Proof.
  split.
  - intros Hle [x a].
    eapply fh_le_trans with (y := sigma P x).
    + exact (indexed_sup_upper A (fun b : A => P (x,b)) a).
    + exact (Hle x).
  - intros Hle x.
    apply indexed_sup_least.
    intro a. exact (Hle (x,a)).
Defined.

Lemma pi_projection_adjunction {X A : Type}
  (P : Predicate (X * A)) (Q : Predicate X) :
  predicate_le (reindex (@fst X A) Q) P <->
  predicate_le Q (pi P).
Proof.
  split.
  - intros Hle x.
    apply indexed_inf_greatest.
    intro a. apply (Hle (x,a)).
  - intros Hle [x a].
    eapply fh_le_trans with (y := pi P x).
    + exact (Hle x).
    + exact (indexed_inf_lower A (fun b : A => P (x,b)) a).
Defined.

Lemma sigma_beck_chevalley {X Y A : Type}
  (f : X -> Y) (P : Predicate (Y * A)) (x : X) :
  sigma (reindex (fun xa : X * A => (f (fst xa), snd xa)) P) x =
  reindex f (sigma P) x.
Proof. reflexivity. Defined.

Lemma pi_beck_chevalley {X Y A : Type}
  (f : X -> Y) (P : Predicate (Y * A)) (x : X) :
  pi (reindex (fun xa : X * A => (f (fst xa), snd xa)) P) x =
  reindex f (pi P) x.
Proof. reflexivity. Defined.
End ArbitraryBase.

Section ArbitraryHyperdoctrine.
Context {H : FiniteHeytingAlgebra} {B : ChosenIndexedHeytingBounds H}.
Variable S : Type.

Definition AHBaseHom (X Y : GeneratedBase) : Type :=
  base_carrier S X -> base_carrier S Y.
Definition AHBaseHomEquiv {X Y : GeneratedBase}
  (f g : AHBaseHom X Y) : Prop := forall x, f x = g x.

Global Instance AHBaseCategory : SetoidCategory.
Proof.
  refine {|
    obj := GeneratedBase;
    hom := AHBaseHom;
    id := fun _ x => x;
    compose := fun _ _ _ g f x => g (f x);
    hom_equiv := @AHBaseHomEquiv
  |}.
  - intros X Y. constructor.
    + intros f x. reflexivity.
    + intros f g Hfg x. symmetry. apply Hfg.
    + intros f g h Hfg Hgh x. rewrite (Hfg x), (Hgh x). reflexivity.
  - intros; unfold AHBaseHomEquiv; intro point; reflexivity.
  - intros; unfold AHBaseHomEquiv; intro point; reflexivity.
  - intros; unfold AHBaseHomEquiv; intro point; reflexivity.
  - intros X Y Z f g h i Hfg Hhi x. rewrite (Hfg (h x)), (Hhi x). reflexivity.
Defined.

Global Instance AHBaseCartesian : CartesianCategory AHBaseCategory.
Proof.
  refine {|
    terminal := (base_one : @obj AHBaseCategory);
    terminal_map := fun _ _ => tt;
    prod := base_product;
    prod_map := fun _ _ _ f g x => (f x, g x);
    prod_fst := fun _ _ xy => fst xy;
    prod_snd := fun _ _ xy => snd xy
  |}.
  - intros X f x. destruct (f x). reflexivity.
  - intros; unfold AHBaseHomEquiv; intro point; reflexivity.
  - intros; unfold AHBaseHomEquiv; intro point; reflexivity.
  - intros X Y Z h x.
    change ((Datatypes.pair (Datatypes.fst (h x))
      (Datatypes.snd (h x))) = h x).
    destruct (h x). reflexivity.
  - intros X Y Z. red. intros f f' Hf g g' Hg x.
    rewrite (Hf x), (Hg x). reflexivity.
Defined.

Definition AHPredicate (X : GeneratedBase) : Type :=
  base_carrier S X -> fh_carrier.
Definition AHPredicateLe {X : GeneratedBase}
  (P Q : AHPredicate X) : Prop := forall x, fh_le (P x) (Q x).

Global Instance AHPredicateCategory (X : GeneratedBase) : SetoidCategory.
Proof.
  refine {|
    obj := AHPredicate X;
    hom := fun P Q => AHPredicateLe P Q;
    id := fun P x => fh_le_refl (P x);
    compose := fun P Q R g f x => fh_le_trans _ _ _ (f x) (g x);
    hom_equiv := fun _ _ _ _ => True
  |}.
  - intros. constructor; firstorder.
  - intros. exact I.
  - intros. exact I.
  - intros. exact I.
  - intros. exact I.
Defined.

Global Instance AHPredicateThin (X : GeneratedBase) : Thin (AHPredicateCategory X).
Proof. intros P Q f g. exact I. Defined.

Global Instance AHPredicateCartesian (X : GeneratedBase) :
  CartesianCategory (AHPredicateCategory X).
Proof.
  refine (@Build_Thin_CC (AHPredicateCategory X) (AHPredicateThin X)
    (fun _ => fh_top)
    (fun P x => fh_le_top (P x))
    (fun P Q x => fh_meet (P x) (Q x))
    (fun P Q R f g x => fh_le_meet _ _ _ (f x) (g x))
    (fun P Q x => fh_meet_le_l (P x) (Q x))
    (fun P Q x => fh_meet_le_r (P x) (Q x))).
Defined.

Global Instance AHPredicateClosed (X : GeneratedBase) :
  CartesianClosedCategory (AHPredicateCategory X).
Proof.
  refine (@Build_Thin_CCC (AHPredicateCategory X) (AHPredicateThin X)
    (AHPredicateCartesian X)
    (fun P Q x => fh_impl (Q x) (P x)) _ _).
  - intros P Q x. apply fh_impl_elim. apply fh_le_refl.
  - intros P Q R g x. apply fh_impl_intro. exact (g x).
Defined.

Global Instance AHPredicateBiClosed (X : GeneratedBase) :
  BiCartesianClosedCategory (AHPredicateClosed X).
Proof.
  refine (@Build_Thin_BiCCC (AHPredicateCategory X)
    (AHPredicateCartesian X) (AHPredicateClosed X) (AHPredicateThin X)
    (fun _ => fh_bot)
    (fun P x => fh_bot_le (P x))
    (fun P Q x => fh_join (P x) (Q x))
    (fun P Q x => fh_le_join_l (P x) (Q x))
    (fun P Q x => fh_le_join_r (P x) (Q x))
    (fun P Q R f g x => fh_join_le _ _ _ (f x) (g x))).
Defined.

Definition AHPullback {X Y : GeneratedBase} (f : AHBaseHom X Y) :
  Functor (AHPredicateCategory Y) (AHPredicateCategory X).
Proof.
  refine (mk_Functor (AHPredicateCategory Y) (AHPredicateCategory X)
    (fun (P : AHPredicate Y) (x : base_carrier S X) => P (f x))
    (fun (P Q : AHPredicate Y) (h : AHPredicateLe P Q)
      (x : base_carrier S X) => h (f x)) _ _ _).
  - repeat red. intros. exact I.
  - intros. exact I.
  - intros. exact I.
Defined.

Definition AHSigma {X A : GeneratedBase}
  (Q : AHPredicate (base_product X A)) : AHPredicate X :=
  fun x => indexed_sup (base_carrier S A) (fun a => Q (x,a)).
Definition AHPi {X A : GeneratedBase}
  (Q : AHPredicate (base_product X A)) : AHPredicate X :=
  fun x => indexed_inf (base_carrier S A) (fun a => Q (x,a)).

Definition AHSigmaUnit {X A : GeneratedBase}
  (Q : AHPredicate (base_product X A)) :
  AHPredicateLe Q (fun xa : base_carrier S (base_product X A) => AHSigma Q (fst xa)).
Proof.
  intros [x a].
  exact (indexed_sup_upper (base_carrier S A)
    (fun a0 => Q (x,a0)) a).
Defined.
Definition AHPiCounit {X A : GeneratedBase}
  (Q : AHPredicate (base_product X A)) :
  AHPredicateLe (fun xa : base_carrier S (base_product X A) => AHPi Q (fst xa)) Q.
Proof.
  intros [x a].
  exact (indexed_inf_lower (base_carrier S A)
    (fun a0 => Q (x,a0)) a).
Defined.

Definition AHProjectionPullbackRightAdjoint (X A : GeneratedBase) :
  IsRightAdjoint (AHPullback (fun xa : base_carrier S (base_product X A) => fst xa)).
Proof.
  refine (mk_IsRightAdjoint _ _
    (AHPullback (fun xa : base_carrier S (base_product X A) => fst xa))
    (fun Q : AHPredicate (base_product X A) => AHSigma Q)
    (@AHSigmaUnit X A)
    (fun (Q : AHPredicate (base_product X A)) (P : AHPredicate X) h x =>
      indexed_sup_least (base_carrier S A) (fun a => Q (x,a)) (P x)
        (fun a => h (x,a)))
    _ _ _).
  - repeat red. intros. exact I.
  - intros. exact I.
  - intros. exact I.
Defined.

Definition AHProjectionPullbackLeftAdjoint (X A : GeneratedBase) :
  IsLeftAdjoint (AHPullback (fun xa : base_carrier S (base_product X A) => fst xa)).
Proof.
  refine (mk_IsLeftAdjoint _ _
    (AHPullback (fun xa : base_carrier S (base_product X A) => fst xa))
    (fun Q : AHPredicate (base_product X A) => AHPi Q)
    (@AHPiCounit X A)
    (fun (P : AHPredicate X) (Q : AHPredicate (base_product X A)) h x =>
      indexed_inf_greatest (base_carrier S A) (fun a => Q (x,a)) (P x)
        (fun a => h (x,a)))
    _ _ _).
  - repeat red. intros. exact I.
  - intros. exact I.
  - intros. exact I.
Defined.

Definition AHPredicateIsoOfPointwiseEq {X : GeneratedBase}
  (P Q : AHPredicate X) (Heq : forall x, P x = Q x) :
  @Iso (AHPredicateCategory X) P Q.
Proof.
  unshelve econstructor.
  - cbn. intro x. rewrite Heq. apply fh_le_refl.
  - cbn. intro x. rewrite Heq. apply fh_le_refl.
  - exact I.
  - exact I.
Defined.

Definition AHGoodFibration : @GoodFibration AHBaseCategory AHBaseCartesian.
Proof.
  refine {|
    Fiber := AHPredicateCategory;
    fiber_is_thin := AHPredicateThin;
    Fiber_is_Cartesian := AHPredicateCartesian;
    Fiber_is_Closed := AHPredicateClosed;
    Fiber_is_BiClosed := AHPredicateBiClosed;
    Pullback := fun X Y f => AHPullback f;
    pullback_has_left_adjoint := AHProjectionPullbackRightAdjoint;
    pullback_has_right_adjoint := AHProjectionPullbackLeftAdjoint
  |}.
  - intros X P. apply AHPredicateIsoOfPointwiseEq. reflexivity.
  - intros X Y Z g f P. apply AHPredicateIsoOfPointwiseEq. reflexivity.
  - intros X Y f. apply AHPredicateIsoOfPointwiseEq. reflexivity.
  - intros X Y f P Q. apply AHPredicateIsoOfPointwiseEq. reflexivity.
  - intros X Y f. apply AHPredicateIsoOfPointwiseEq. reflexivity.
  - intros X Y f P Q. apply AHPredicateIsoOfPointwiseEq. reflexivity.
  - intros X Y f P Q. apply AHPredicateIsoOfPointwiseEq. reflexivity.
  - intros X Y K f A0. apply AHPredicateIsoOfPointwiseEq. reflexivity.
  - intros X Y K f A0. apply AHPredicateIsoOfPointwiseEq. reflexivity.
  - intros X Y f g Hfg P. apply AHPredicateIsoOfPointwiseEq.
    intro x. cbn. apply f_equal. apply Hfg.
Defined.
End ArbitraryHyperdoctrine.
