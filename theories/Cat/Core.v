Require Import List.
Import ListNotations.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

Class SetoidCategory := mk_SetoidCategory {
  obj : Type;
  hom : obj -> obj -> Type;

  id : forall x, hom x x;
  compose : forall {x y z}, hom y z -> hom x y -> hom x z;

  hom_equiv : forall {x y}, hom x y -> hom x y -> Prop;
  
  hom_equiv_equivalence : forall {x y}, Equivalence (@hom_equiv x y);

  comp_assoc : forall x y z w (f : hom z w) (g : hom y z) (h : hom x y),
        hom_equiv (compose f (compose g h)) (compose (compose f g) h);

  id_right : forall x y (f : hom x y), hom_equiv (compose f (id x)) f;
  id_left  : forall x y (f : hom x y), hom_equiv (compose (id y) f) f;

  comp_proper : forall {x y z} (f g: hom y z) (h i : hom x y), 
        hom_equiv f g -> hom_equiv h i -> hom_equiv (compose f h) (compose g i);
}.

Notation "x → y" := (hom x y) (at level 90, right associativity) : type_scope.
Notation "f ∘ g" := (compose f g) (at level 40, left associativity) : type_scope.
Notation "f ≅ g" := (hom_equiv f g) (at level 40, no associativity) : type_scope.

Add Parametric Relation (C : SetoidCategory) (x y : @obj C) : (@hom C x y) (@hom_equiv C x y)
  reflexivity proved by (@Equivalence_Reflexive _ _ (@hom_equiv_equivalence C x y))
  symmetry proved by (@Equivalence_Symmetric _ _ (@hom_equiv_equivalence C x y))
  transitivity proved by (@Equivalence_Transitive _ _ (@hom_equiv_equivalence C x y))
  as hom_equiv_rel.

Instance compose_proper_instance (C : SetoidCategory) (x y z : @obj C) : 
  Proper (@hom_equiv C y z ==> @hom_equiv C x y ==> @hom_equiv C x z) (@compose C x y z).
Proof.
  do 2 red. intros f g Hfg h i Hhi.
  apply comp_proper; assumption.
Defined.

(* Thin Category  *)
Class Thin (C : SetoidCategory) :=
  thin_unique : forall {x y} (f g : hom x y), f ≅ g.