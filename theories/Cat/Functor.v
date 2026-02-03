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

(* Proper instance for setoid_rewrite *)
Existing Instance fmap_proper.

Definition ComposeFunctors {C D E : SetoidCategory} (G : Functor D E) (F : Functor C D) : Functor C E.
Proof.
  refine (mk_Functor C E
    (* Object: x |-> G(F(x)) *)
    (fun x => @fobj D E G (@fobj C D F x))
    
    (* Morphism: f |-> G(F(f)) *)
    (fun x y f => @fmap D E G _ _ (@fmap C D F x y f))
    _ _ _).

  - (* Proper: f ~ g => G(F(f)) ~ G(F(g)) *)
    intros x y f g H.
    apply (@fmap_proper D E G). (* G proper *)
    apply (@fmap_proper C D F). (* F proper *)
    assumption.

  - (* Identity: G(F(id)) ~ id *)
    intros x.
    (* 1. F(id) ~ id *)
    rewrite (@fmap_id C D F x). 
    (* 2. G(id) ~ id *)
    rewrite (@fmap_id D E G (@fobj C D F x)).
    reflexivity.

  - (* Composition: G(F(g o f)) ~ G(F(g)) o G(F(f)) *)
    intros x y z f g.
    (* 1. F(g o f) ~ F g o F f *)
    rewrite (@fmap_comp C D F x y z f g).
    (* 2. G(F g o F f) ~ G(F g) o G(F f) *)
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
  - (* Proper *)
    do 2 red. intros. assumption.
  - (* Id *)
    intros. reflexivity.
  - (* Comp *)
    intros. reflexivity.
Defined.