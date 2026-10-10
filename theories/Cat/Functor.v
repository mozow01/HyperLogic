Require Import List.  
Import ListNotations.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import HyperLogic.Cat.Core.

Class Functor (C D : SetoidCategory) := mk_Functor {
  fobj : @obj C -> @obj D;

  fmap : forall {x y : @obj C} (f : @hom C x y), @hom D (fobj x) (fobj y);

  fmap_proper : forall {x y : @obj C}, 
    Proper (@hom_equiv C x y ==> @hom_equiv D (fobj x) (fobj y)) (@fmap x y);

  fmap_id : forall (x : @obj C), 
    @hom_equiv D (fobj x) (fobj x) (fmap (@id C x)) (@id D (fobj x));

  fmap_comp : forall {x y z : @obj C} (f : @hom C x y) (g : @hom C y z),
    @hom_equiv D (fobj x) (fobj z) 
      (fmap (@compose C x y z g f)) 
      (@compose D (fobj x) (fobj y) (fobj z) (fmap g) (fmap f))
}.

Arguments fobj {C D} _ _.
Arguments fmap {C D} _ {x y} _.
Arguments fmap_proper {C D} _ {x y} _ _ _.
Arguments fmap_id {C D} _ _.
Arguments fmap_comp {C D} _ {x y z} _ _.

Existing Instance fmap_proper.

Definition ComposeFunctors {C D E : SetoidCategory} (G : Functor D E) (F : Functor C D) : Functor C E.
Proof.
  refine (mk_Functor C E
    (fun x => @fobj D E G (@fobj C D F x))
    
    (fun x y f => @fmap D E G _ _ (@fmap C D F x y f))
    _ _ _).

  -
    intros x y f g H.
    apply (@fmap_proper D E G).
    apply (@fmap_proper C D F).
    assumption.

  -
    intros x.
    rewrite (@fmap_id C D F x). 
    rewrite (@fmap_id D E G (@fobj C D F x)).
    reflexivity.

  -
    intros x y z f g.
    rewrite (@fmap_comp C D F x y z f g).
    rewrite (@fmap_comp D E G _ _ _ (@fmap C D F _ _ f) (@fmap C D F _ _ g)).
    reflexivity.
Defined.

Notation "F 'O' G" := (ComposeFunctors F G) (at level 40, left associativity).

Definition IdFunctor (C : SetoidCategory) : Functor C C.
Proof.
  refine (mk_Functor C C 
    (fun x => x) 
    (fun x y f => f) 
    _ _ _).
  -
    do 2 red. intros. assumption.
  -
    intros. reflexivity.
  -
    intros. reflexivity.
Defined.

Lemma functor_iso_cong {C D : SetoidCategory} (F : Functor C D) {X Y : @obj C} :
  X ≅O Y -> fobj F X ≅O fobj F Y.
Proof.
  intros H.
  destruct H as [to from to_from from_to].

  refine {|
    iso_to := @fmap C D F X Y to;
    iso_from := @fmap C D F Y X from
  |}.
  - eapply (@RelationClasses.Equivalence_Transitive
              _ _
              (@hom_equiv_equivalence D (@fobj C D F Y) (@fobj C D F Y)))
      with (y := @fmap C D F Y Y (@compose C Y X Y to from)).
    + eapply (@RelationClasses.Equivalence_Symmetric
                _ _
                (@hom_equiv_equivalence D (@fobj C D F Y) (@fobj C D F Y))).
      apply (@fmap_comp C D F Y X Y from to).
    + eapply (@RelationClasses.Equivalence_Transitive
                _ _
                (@hom_equiv_equivalence D (@fobj C D F Y) (@fobj C D F Y)))
        with (y := @fmap C D F Y Y (@id C Y)).
      * apply (@fmap_proper C D F Y Y).
        exact to_from.
      * apply (@fmap_id C D F Y).

  - eapply (@RelationClasses.Equivalence_Transitive
              _ _
              (@hom_equiv_equivalence D (@fobj C D F X) (@fobj C D F X)))
      with (y := @fmap C D F X X (@compose C X Y X from to)).
    + eapply (@RelationClasses.Equivalence_Symmetric
                _ _
                (@hom_equiv_equivalence D (@fobj C D F X) (@fobj C D F X))).
      apply (@fmap_comp C D F X Y X to from).
    + eapply (@RelationClasses.Equivalence_Transitive
                _ _
                (@hom_equiv_equivalence D (@fobj C D F X) (@fobj C D F X)))
        with (y := @fmap C D F X X (@id C X)).
      * apply (@fmap_proper C D F X X).
        exact from_to.
      * apply (@fmap_id C D F X).
Defined.
