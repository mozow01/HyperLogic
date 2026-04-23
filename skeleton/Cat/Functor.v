Require Import List.
Import ListNotations.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import HyperLogic.Cat.Core.

Class Functor (C D : SetoidCategory) := mk_Functor {
  (* Object: *)
  fobj : @obj C -> @obj D;

  (* Morphism: (x -> y) -> (F x -> F y) *)
  fmap : forall {x y : @obj C} (f : @hom C x y), @hom D (fobj x) (fobj y);

  (* Proper: *)
  fmap_proper : forall {x y : @obj C},
    Proper (@hom_equiv C x y ==> @hom_equiv D (fobj x) (fobj y)) (@fmap x y);

  (* Identity: F(id) ~ id *)
  fmap_id : forall (x : @obj C),
    @hom_equiv D (fobj x) (fobj x) (fmap (@id C x)) (@id D (fobj x));

  (* Composition: F(g ∘ f) ~ F(g) ∘ F(f) *)
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

(* Proper instance for setoid_rewrite *)
Existing Instance fmap_proper.

Definition ComposeFunctors {C D E : SetoidCategory} (G : Functor D E) (F : Functor C D) : Functor C E.
Proof. Admitted.

Notation "F 'O' G" := (ComposeFunctors F G) (at level 40, left associativity).

Definition IdFunctor (C : SetoidCategory) : Functor C C.
Proof. Admitted.

Lemma functor_iso_cong {C D : SetoidCategory} (F : Functor C D) {X Y : @obj C} :
  X ≅O Y -> fobj F X ≅O fobj F Y.
Proof. Admitted.