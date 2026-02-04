Require Import Core.
Require Import Coq.Classes.Morphisms.
Require Import CCC.

Class BiCartesianClosedCategory {C : SetoidCategory} (CC : CartesianClosedCategory C) := mk_BiCartesianClosedCategory {

  (* ========================== *)
  (* 1. INITIAL OBJECT          *)
  (* ========================== *)
  initial : @obj C;
  initial_map : forall {x}, hom initial x;

  (* Eta rule for Initial Object *)
  initial_map_unique : forall {x} (f : hom initial x), 
        f ≅ initial_map;

  (* ========================== *)
  (* 2. COPRODUCT               *)
  (* ========================== *)
  coprod : @obj C -> @obj C -> @obj C;

  (* Constructors (Injections) *)
  coprod_inl : forall {x y}, hom x (coprod x y);
  coprod_inr : forall {x y}, hom y (coprod x y);

  (* Destructor (Case Analysis / Co-Pairing): [f, g] *)
  coprod_map : forall {x y z} (f : hom x z) (g : hom y z), hom (coprod x y) z;

  (* Equations *)

  (* Beta rule: [f, g] o inl = f *)
  coprod_map_inl : forall {x y z} (f : hom x z) (g : hom y z), 
        compose (coprod_map f g) coprod_inl ≅ f;

  (* Beta rule: [f, g] o inr = g *)
  coprod_map_inr : forall {x y z} (f : hom x z) (g : hom y z), 
        compose (coprod_map f g) coprod_inr ≅ g;

  (* Eta rule: [h o inl, h o inr] = h *)
  coprod_eta : forall {x y z} (h : hom (coprod x y) z), 
        coprod_map (compose h coprod_inl) (compose h coprod_inr) ≅ h;

  (* Proper instance required for rewriting *)
  coprod_map_proper_ax : forall {x y z},
        Proper (hom_equiv ==> hom_equiv ==> hom_equiv) (@coprod_map x y z)
}.

(* Register the Proper instance for usage in setoid_rewrite *)
Existing Instance coprod_map_proper_ax.

(* --- Notations --- *)

Notation "⊥" := (initial) (at level 0, no associativity) : type_scope.
Notation "x '⊕' y" := (coprod x y) (at level 50, left associativity) : type_scope.

(* Case analysis notation [f, g] *)
Notation "f '∐' g" := (coprod_map f g) (at level 30, no associativity) : type_scope.

(* Functorial map f + g (Torii dual) *)
Notation "f '⊔' g" := (coprod_map (compose coprod_inl f) (compose coprod_inr g)) 
                      (at level 30, no associativity) : type_scope.

(* --- Theorems --- *)

(* Uniqueness derived from Eta (mirroring prod_unique) *)
Theorem coprod_unique {C : SetoidCategory} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC} : 
  forall {x y z} (f : hom x z) (g : hom y z) (h : hom (coprod x y) z), 
    (compose h coprod_inl ≅ f) /\ (compose h coprod_inr ≅ g) -> h ≅ (coprod_map f g).
Proof.
  intros x y z f g h [Hinl Hinr].
  rewrite <- coprod_eta. (* Replace h with [h o inl, h o inr] *)
  apply coprod_map_proper_ax.
  - exact Hinl.
  - exact Hinr.
Qed.

(* --- Thin BiCCC Constructor --- *)

Definition Build_Thin_BiCCC 
  (C : SetoidCategory) 
  (CC : CartesianClosedCategory C)
  (HThin : Thin C) 
  (initial_item : @obj C)
  (initial_map_item : forall {x}, hom initial_item x)
  (coprod_item : @obj C -> @obj C -> @obj C)
  (coprod_inl_item : forall {x y}, hom x (coprod_item x y))
  (coprod_inr_item : forall {x y}, hom y (coprod_item x y))
  (coprod_map_item : forall {x y z} (f : hom x z) (g : hom y z), hom (coprod_item x y) z)
  : BiCartesianClosedCategory CC.
Proof.
  apply mk_BiCartesianClosedCategory with
    (initial := initial_item)
    (initial_map := @initial_map_item)
    (coprod := coprod_item)
    (coprod_inl := @coprod_inl_item)
    (coprod_inr := @coprod_inr_item)
    (coprod_map := @coprod_map_item).
  
  all: intros.
  all: try (unfold Proper, respectful; intros).
  all: apply thin_unique.
Defined.