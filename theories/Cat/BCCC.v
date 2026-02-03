Require Import Core.
Require Import Coq.Classes.Morphisms.
Require Import CCC.

Class BiCartesianClosedCategory {C : SetoidCategory} (CC : CartesianClosedCategory C) := mk_BiCartesianClosedCategory {

  (* 1. Initial Object *)
  initial : @obj C;
  
  (* Initiality: unique map from initial to any x *)
  initial_map : forall {x}, hom initial x;
  initial_map_unique : forall {x} (f : hom initial x), f ≅ initial_map;

  (* 2. Coproduct (Sum) *)
  coprod : @obj C -> @obj C -> @obj C;

  (* The universal map *)
  coprod_map : forall {x y z} (f : hom x z) (g : hom y z), hom (coprod x y) z;
  
  (* Injections *)
  coprod_inl : forall {x y}, hom x (coprod x y);
  coprod_inr : forall {x y}, hom y (coprod x y);

  (* --- The Single Axiom (Lambek Style) --- *)
  (* h ≅ [f, g] <-> h o inl ≅ f /\ h o inr ≅ g *)
  coprod_def : forall {x y z} (f : hom x z) (g : hom y z) (h : hom (coprod x y) z),
        h ≅ coprod_map f g <-> (compose h coprod_inl ≅ f) /\ (compose h coprod_inr ≅ g)
}.

(* --- Notations --- *)

Notation "⊥" := (initial) (at level 0, no associativity) : type_scope.

(* f ∐ g : Case Analysis (Unicode \amalg) *)
(* x -> z, y -> z ===> x + y -> z *)
Notation "f '∐' g" := (coprod_map f g) (at level 30, no associativity) : type_scope.

(* f ⊔ g : Functorial Coproduct (Unicode \sqcup) *)
(* x -> y , z -> w ===> x + z -> y + w *)
Notation "f '⊔' g" := (coprod_map (compose coprod_inl f) (compose coprod_inr g)) 
                      (at level 30, no associativity) : type_scope.

(* x + y *)
Notation "x # y" := (coprod x y) (at level 50, left associativity) : type_scope.


(* --- Derived Laws from the Lambek Axiom --- *)

Theorem coprod_map_inl {C : SetoidCategory} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC} : 
  forall {x y z} (f : hom x z) (g : hom y z), 
    compose (coprod_map f g) coprod_inl ≅ f.
Proof.
  intros.
  (* Instantiate the axiom with h = [f,g] *)
  pose proof (coprod_def f g (coprod_map f g)) as H.
  assert (Refl : coprod_map f g ≅ coprod_map f g) by reflexivity.
  apply H in Refl.
  destruct Refl as [Goal _].
  exact Goal.
Qed.

Theorem coprod_map_inr {C : SetoidCategory} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC} : 
  forall {x y z} (f : hom x z) (g : hom y z), 
    compose (coprod_map f g) coprod_inr ≅ g.
Proof.
  intros.
  pose proof (coprod_def f g (coprod_map f g)) as H.
  assert (Refl : coprod_map f g ≅ coprod_map f g) by reflexivity.
  apply H in Refl.
  destruct Refl as [_ Goal].
  exact Goal.
Qed.

Theorem coprod_unique {C : SetoidCategory} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC} : 
  forall {x y z} (f : hom x z) (g : hom y z) (h : hom (coprod x y) z), 
    (compose h coprod_inl ≅ f) /\ (compose h coprod_inr ≅ g) -> h ≅ (coprod_map f g).
Proof.
  intros x y z f g h H.
  (* Direction <- of the axiom *)
  apply coprod_def.
  exact H.
Qed.

(* --- Instances & Theorems --- *)

Instance coprod_map_proper {C : SetoidCategory} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC} {x y z : @obj C} :
  Proper (hom_equiv ==> hom_equiv ==> hom_equiv) (@coprod_map C CC BCC x y z).
Proof.
  intros f f' Hf g g' Hg.
  apply coprod_unique.
  split.
  - rewrite coprod_map_inl. assumption.
  - rewrite coprod_map_inr. assumption.
Qed.

Theorem compos_coprod {C : SetoidCategory} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC} : 
  forall (x y z w : @obj C) (f : x → y) (g : z → y) (h : y → w),
 (h ∘ (f ∐ g)) ≅ ((h ∘ f) ∐ (h ∘ g)).
Proof.
  intros x y z w f g h.
  apply coprod_unique.
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

Theorem coprod_eta {C : SetoidCategory} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC} : 
  forall {x y z : @obj C} (h : x # y → z),
    (h ∘ coprod_inl) ∐ (h ∘ coprod_inr) ≅ h.
Proof.
  intros x y z h.
  symmetry.
  apply coprod_unique. 
  split.
  all: reflexivity.
Qed.

Lemma in_and_id {C : SetoidCategory} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC} : 
  forall (A B : @obj C), id (A # B) ≅ coprod_inl ∐ coprod_inr.
Proof.
  intros A B.
  apply coprod_unique.
  split.
  - rewrite id_left. reflexivity.
  - rewrite id_left. reflexivity.
Qed.