Require Import HyperLogic.Cat.Core.
Require Import Coq.Classes.Morphisms.

(* ================================================================= *)
(* CARTESIAN CATEGORY (Terminal + Product)                           *)
(* ================================================================= *)

Class CartesianCategory (C : SetoidCategory) := mk_CartesianCategory {

  (* --- TERMINAL --- *)
  terminal : @obj C;
  terminal_map : forall {x}, hom x terminal;
  terminal_map_unique : forall {x} (f : hom x terminal), f ≅ terminal_map;

  (* --- PRODUCT --- *)
  prod : @obj C -> @obj C -> @obj C;
  prod_map : forall {x y z} (f : hom x y) (g : hom x z), hom x (prod y z);
  prod_fst : forall {x y}, hom (prod x y) x;
  prod_snd : forall {x y}, hom (prod x y) y;

  (* Equations *)
  prod_map_fst : forall {x y z} (f : hom x y) (g : hom x z),
    compose prod_fst (prod_map f g) ≅ f;
  prod_map_snd : forall {x y z} (f : hom x y) (g : hom x z),
    compose prod_snd (prod_map f g) ≅ g;
  prod_eta : forall {x y z} (h : hom x (prod y z)),
    prod_map (compose prod_fst h) (compose prod_snd h) ≅ h;

  (* Proper *)
  prod_map_proper_ax : forall {x y z},
    Proper (hom_equiv ==> hom_equiv ==> hom_equiv) (@prod_map x y z)
}.

Arguments terminal {C} {_}.
Arguments terminal_map {C} {_} {x}.
Arguments terminal_map_unique {C} {_} {x} _.

Arguments prod {C} {_} _ _.
Arguments prod_map {C} {_} {x y z} _ _.
Arguments prod_fst {C} {_} {x y}.
Arguments prod_snd {C} {_} {x y}.

Arguments prod_map_fst {C} {_} {x y z} _ _.
Arguments prod_map_snd {C} {_} {x y z} _ _.
Arguments prod_eta {C} {_} {x y z} _.
Arguments prod_map_proper_ax {C} {_} {x y z}.

Existing Instance prod_map_proper_ax.

(* Notations *)
Notation "1" := (terminal) : type_scope.
Notation "⊤" := (terminal) (at level 0, no associativity) : type_scope.
Notation "x × y" := (prod x y) (at level 40, left associativity) : type_scope.
Notation "f '∏' g" := (prod_map f g) (at level 30, no associativity) : type_scope.
Notation "f 'Π' g" := (prod_map (compose f prod_fst) (compose g prod_snd)) (at level 30, no associativity) : type_scope.

(* --- Theorems --- *)

Lemma prod_unique {C : SetoidCategory} {CC : CartesianCategory C} :
  forall {x y z} (f : hom x y) (g : hom x z) (h : hom x (prod y z)),
    (compose prod_fst h ≅ f) /\ (compose prod_snd h ≅ g) -> h ≅ (prod_map f g).
Proof. Admitted.

Theorem unique_prod {C : SetoidCategory} {CC : CartesianCategory C} :
  forall (x y z : @obj C) (f1 : x → y) (f2 : x → z) (g : x → y × z),
    ((prod_fst ∘ g) ≅ f1) /\ ((prod_snd ∘ g) ≅ f2) -> f1 ∏ f2 ≅ g.
Proof. Admitted.

(* Composition distributes over product map *)
Theorem compos_prod {C : SetoidCategory} {CC : CartesianCategory C} :
  forall x y z w (f : w → y) (g : w → z) (h : x → w),
  (f ∘ h) ∏ (g ∘ h) ≅ ((f ∏ g) ∘ h).
Proof. Admitted.

Lemma pr_and_id {C : SetoidCategory} {CC : CartesianCategory C} :
  forall (A B : @obj C), id (A × B) ≅ prod_fst ∏ prod_snd.
Proof. Admitted.

(* EZ HIÁNYZOTT: Functoriality of Product *)
Lemma prod_id {C : SetoidCategory} {CC : CartesianCategory C} (X Y Z A : @obj C) :
  forall (f : X → Y) (g : Y → Z),
    (g Π (id A)) ∘ (f Π (id A)) ≅ (g ∘ f) Π (id A).
Proof. Admitted.

(* Builder for Thin Categories *)
Definition Build_Thin_CC (C : SetoidCategory) (HThin : Thin C)
  (terminal_item : @obj C) (terminal_map_item : forall {x}, hom x terminal_item)
  (prod_item : @obj C -> @obj C -> @obj C) (prod_map_item : forall {x y z} (f : hom x y) (g : hom x z), hom x (prod_item y z))
  (prod_fst_item : forall {x y}, hom (prod_item x y) x) (prod_snd_item : forall {x y}, hom (prod_item x y) y)
  : CartesianCategory C.
Proof. Admitted.

Lemma prod_iso_cong {C : SetoidCategory} {CC : CartesianCategory C} {A B A' B' : @obj C} :
  A ≅O A' -> B ≅O B' -> prod A B ≅O prod A' B'.
Proof. Admitted.