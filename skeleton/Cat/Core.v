Require Import List.
Import ListNotations.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.

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

Global Instance compose_proper_instance {C : SetoidCategory} {x y z : @obj C} :
  Proper (@hom_equiv C y z ==> @hom_equiv C x y ==> @hom_equiv C x z) (@compose C x y z).
Proof. Admitted.

(* Thin Category  *)
Class Thin (C : SetoidCategory) :=
  thin_unique : forall {x y} (f g : hom x y), f ≅ g.

(* Isomorphisms *)
Class Iso {C : SetoidCategory} (A B : @obj C) := {
  iso_to : A → B;
  iso_from : B → A;

  iso_to_from : iso_to ∘ iso_from ≅ id B;

  iso_from_to : iso_from ∘ iso_to ≅ id A
}.

Notation "A ≅O B" := (Iso A B) (at level 40, no associativity) : type_scope.

Require Import Coq.Classes.CMorphisms.
Require Import Coq.Classes.CRelationClasses.

(* ========================================================================= *)
(* 1. ALAP LEMMÁK (A reláció matematikai tulajdonságai)                      *)
(* ========================================================================= *)

(* Szimmetria (A ≅O B -> B ≅O A) *)
Definition iso_sym {C : SetoidCategory} {A B : obj} (H : A ≅O B) : B ≅O A.
Proof. Admitted.

(* Reflexivitás (A ≅O A) *)
Definition iso_refl {C : SetoidCategory} (A : obj) : A ≅O A.
Proof. Admitted.

(* Tranzitivitás (A ≅O B és B ≅O X -> A ≅O X) *)
(* Tranzitivitás (A ≅O B és B ≅O X -> A ≅O X) *)
Definition iso_trans {C : SetoidCategory} {A B X : obj}
  (H1 : A ≅O B) (H2 : B ≅O X) : A ≅O X.
Proof. Admitted.

(* ========================================================================= *)
(* TYPECLASS REGISZTRÁCIÓ (Ez helyettesíti az Add Parametric Relation-t)     *)
(* ========================================================================= *)

Global Instance iso_refl_inst {C : SetoidCategory} : Reflexive (@Iso C) := @iso_refl C.
Global Instance iso_sym_inst {C : SetoidCategory} : Symmetric (@Iso C) := @iso_sym C.
Global Instance iso_trans_inst {C : SetoidCategory} : Transitive (@Iso C) := @iso_trans C.

(* Összefoglaljuk őket egy Ekvivalencia relációba *)
Global Instance iso_equiv_inst {C : SetoidCategory} : Equivalence (@Iso C) := {
  Equivalence_Reflexive := iso_refl_inst;
  Equivalence_Symmetric := iso_sym_inst;
  Equivalence_Transitive := iso_trans_inst
}.

(* Engedélyezzük a 'rewrite' és 'setoid_rewrite' taktikákat erre a relációra! *)
Global Instance RewriteRelation_Iso {C : SetoidCategory} : RewriteRelation (@Iso C) := {}.

