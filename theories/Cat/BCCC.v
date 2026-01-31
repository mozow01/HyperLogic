Require Import Core.
Require Import Coq.Classes.Morphisms.
Require Import CCC.

Class BiCartesianClosedCategory {C : SetoidCategory} (CC : CartesianClosedCategory C)  := mk_BiCartesianClosedCategory {

  (* 1. Initial Object *)
  initial : @obj C;
  initial_map : forall {x}, hom initial x;

  (* 2. Coproduct (Sum) *)
  coprod : @obj C -> @obj C -> @obj C;

  (* The universal map [f, g] (case analysis) *)
  (* x -> z, y -> z ===> x + y -> z *)
  coprod_map : forall {x y z} (f : hom x z) (g : hom y z), hom (coprod x y) z;
  
  (* Injections *)
  coprod_inl : forall {x y}, hom x (coprod x y);
  coprod_inr : forall {x y}, hom y (coprod x y);

  (* Laws *)
  
  (* Unique map from initial object *)
  initial_map_unique : forall {x} (f : hom initial x), 
        f ≅ initial_map;

  (* Injection Commutativity *)
  (* [f, g] o inl ~ f *)
  coprod_map_inl : forall {x y z} (f : hom x z) (g : hom y z), 
        compose (coprod_map f g) coprod_inl ≅ f;
        
  (* [f, g] o inr ~ g *)
  coprod_map_inr : forall {x y z} (f : hom x z) (g : hom y z), 
        compose (coprod_map f g) coprod_inr ≅ g;
        
  (* Uniqueness of the coproduct map *)
  coprod_unique : forall {x y z} (f : hom x z) (g : hom y z) (h : hom (coprod x y) z), 
        (compose h coprod_inl ≅ f) /\ (compose h coprod_inr ≅ g) -> h ≅ (coprod_map f g)
}.

(* --- Notations --- *)

Notation "⊥" := (initial) (at level 0, no associativity) : type_scope.

(* f ∐ g : Case Analysis *)
(* x -> z, y -> z ===> x + y -> z *)
Notation "f '∐' g" := (coprod_map f g) (at level 30, no associativity) : type_scope.

(* f ⊔ g : Functorial Coproduct *)
(* x -> y , z -> w ===> x + z -> y + w *)
Notation "f '⊔' g" := (coprod_map (compose coprod_inl f) (compose coprod_inr g)) 
                      (at level 30, no associativity) : type_scope.

(* x + y *)
Notation "x # y" := (coprod x y) (at level 50, left associativity) : type_scope.


(* --- Theorems & Instances --- *)

Instance coprod_map_proper {C : SetoidCategory} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC} {x y z : @obj C} :
  Proper (hom_equiv ==> hom_equiv ==> hom_equiv) (@coprod_map C CC BCC x y z).
Proof.
  (* f ≅ f' , g ≅ g' ->  [f, g] ≅ [f', g'] *)
  intros f f' Hf g g' Hg.
  
  (* coprod_unique (h = [f', g']) *)
  symmetry.
  apply coprod_unique.
  split.
  
  (* LHS: [f', g'] o inl ≅ f *)
  - rewrite coprod_map_inl. (* [f', g'] o inl --> f' *)
    symmetry. assumption.   (* f' ≅ f *)
    
  (* RHS: [f', g'] o inr ≅ g *)
  - rewrite coprod_map_inr. (* [f', g'] o inr --> g' *)
    symmetry. assumption.   (* g' ≅ g *)
Qed.

Theorem unique_coprod {C : SetoidCategory} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC} : 
  forall (x y z : @obj C) (f1 : x → z) (f2 : y → z) (g : x # y → z), 
    ((g ∘ coprod_inl) ≅ f1) /\ ((g ∘ coprod_inr) ≅ f2) -> f1 ∐ f2 ≅ g.
Proof.
  intros x y z f1 f2 g H.
  symmetry.
  apply coprod_unique. 
  destruct H as [H1 H2].
  split.
  - rewrite H1. reflexivity.
  - rewrite H2. reflexivity.
Qed.

Theorem coprod_eta {C : SetoidCategory} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC} : 
  forall {x y z : @obj C} (h : x # y → z),
    coprod_map (compose h coprod_inl) (compose h coprod_inr) ≅ h.
Proof.
  intros x y z h.
  symmetry.
  apply coprod_unique. 
  split.
  all: reflexivity.
Qed.

(* Distributivity of composition over coproduct case analysis *)
(* h ∘ [f, g] ≅ [h ∘ f, h ∘ g] *)
Theorem compos_coprod {C : SetoidCategory} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC} : 
  forall (x y z w : @obj C) (f : x → y) (g : z → y) (h : y → w),
 (h ∘ (coprod_map f g)) ≅ (coprod_map (h ∘ f) (h ∘ g)).
Proof.
  intros x y z w f g h.
  symmetry.
  apply unique_coprod.
  split.
  (* LHS: ([h ∘ f, h ∘ g] ∘ inl) *)
  - rewrite <- comp_assoc.      
    rewrite coprod_map_inl.   
    reflexivity.             

  (* RHS: ([h ∘ f, h ∘ g] ∘ inr) *)
  - rewrite <- comp_assoc.      
    rewrite coprod_map_inr.   
    reflexivity.             
Qed.

Lemma in_and_id {C : SetoidCategory} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC} : 
  forall (A B : @obj C), id (A # B) ≅ coprod_inl ∐ coprod_inr.
Proof.
  intros A B.
  (* inl ≅ (id ∘ inl) *)
  assert (H1: coprod_inl ≅ compose (id (A # B)) coprod_inl).
  { rewrite id_left. reflexivity. }
  
  assert (H2: coprod_inr ≅ compose (id (A # B)) coprod_inr).
  { rewrite id_left. reflexivity. }

  rewrite H1 at 1.
  rewrite H2 at 1.
  symmetry.
  
  apply unique_coprod.
  split; rewrite id_left; reflexivity.
Qed.