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
Proof.
  do 2 red. intros f g Hfg h i Hhi.
  apply comp_proper; assumption.
Defined.

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
Proof.
  (* Szétszedjük az eredeti izomorfizmust a nyers elemeire *)
  destruct H as [to from to_from from_to].
  
  (* Direktben felépítjük a rekordot, megkerülve a Typeclass motort *)
  exact {|
    iso_to := from;
    iso_from := to;
    iso_to_from := from_to;
    iso_from_to := to_from
  |}.
Defined.

(* Reflexivitás (A ≅O A) *)
Definition iso_refl {C : SetoidCategory} (A : obj) : A ≅O A.
Proof.
  refine {|
    iso_to := id A;
    iso_from := id A
  |}.
  - (* Bizonyítás: id ∘ id ≅ id *)
    apply id_left. (* Cseréld le, ha nálad pl. comp_id_l vagy cat_id_l a neve! *)
  - (* Bizonyítás: id ∘ id ≅ id *)
    apply id_left. 
Defined.

(* Tranzitivitás (A ≅O B és B ≅O X -> A ≅O X) *)
(* Tranzitivitás (A ≅O B és B ≅O X -> A ≅O X) *)
Definition iso_trans {C : SetoidCategory} {A B X : obj}
  (H1 : A ≅O B) (H2 : B ≅O X) : A ≅O X.
Proof.
  destruct H1 as [to1 from1 to_from1 from_to1].
  destruct H2 as [to2 from2 to_from2 from_to2].

  refine {|
    iso_to := to2 ∘ to1;
    iso_from := from1 ∘ from2
  |}.

  - (* 1. Ág: (to2 ∘ to1) ∘ (from1 ∘ from2) ≅ id X *)
    (* 1) asszociálás kívül *)
    eapply (@RelationClasses.Equivalence_Transitive _ _ (@hom_equiv_equivalence C X X))
      with (y := to2 ∘ (to1 ∘ (from1 ∘ from2))).
    + (* (to2 ∘ to1) ∘ (from1 ∘ from2) ≅ to2 ∘ (to1 ∘ (from1 ∘ from2)) *)
      eapply (@RelationClasses.Equivalence_Symmetric _ _ (@hom_equiv_equivalence C X X)).
      exact (comp_assoc X A B X to2 to1 (from1 ∘ from2)).
    + (* 2) asszociálás belül: to1 ∘ (from1 ∘ from2) -> (to1 ∘ from1) ∘ from2 *)
      eapply (@RelationClasses.Equivalence_Transitive _ _ (@hom_equiv_equivalence C X X))
        with (y := to2 ∘ ((to1 ∘ from1) ∘ from2)).
      * eapply comp_proper; [reflexivity |].
        exact (comp_assoc X B A B to1 from1 from2).
      * (* 3) cseréld le (to1 ∘ from1)-et id B-re, majd id_left *)
        eapply (@RelationClasses.Equivalence_Transitive _ _ (@hom_equiv_equivalence C X X))
          with (y := to2 ∘ (id B ∘ from2)).
        -- eapply comp_proper; [reflexivity |].
           eapply comp_proper; [exact to_from1 | reflexivity].
        -- eapply (@RelationClasses.Equivalence_Transitive _ _ (@hom_equiv_equivalence C X X))
             with (y := to2 ∘ from2).
           ++ eapply comp_proper; [reflexivity |].
              apply id_left.
           ++ exact to_from2.

  - (* 2. Ág: (from1 ∘ from2) ∘ (to2 ∘ to1) ≅ id A *)
    eapply (@RelationClasses.Equivalence_Transitive _ _ (@hom_equiv_equivalence C A A))
      with (y := from1 ∘ (from2 ∘ (to2 ∘ to1))).
    + eapply (@RelationClasses.Equivalence_Symmetric _ _ (@hom_equiv_equivalence C A A)).
      exact (comp_assoc A X B A from1 from2 (to2 ∘ to1)).
    + eapply (@RelationClasses.Equivalence_Transitive _ _ (@hom_equiv_equivalence C A A))
        with (y := from1 ∘ ((from2 ∘ to2) ∘ to1)).
      * eapply comp_proper; [reflexivity |].
        exact (comp_assoc A B X B from2 to2 to1).
      * eapply (@RelationClasses.Equivalence_Transitive _ _ (@hom_equiv_equivalence C A A))
          with (y := from1 ∘ (id B ∘ to1)).
        -- eapply comp_proper; [reflexivity |].
           eapply comp_proper; [exact from_to2 | reflexivity].
        -- eapply (@RelationClasses.Equivalence_Transitive _ _ (@hom_equiv_equivalence C A A))
             with (y := from1 ∘ to1).
           ++ eapply comp_proper; [reflexivity |].
              apply id_left.
           ++ exact from_to1.
Defined.

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

