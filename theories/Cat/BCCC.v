Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.  
Require Import HyperLogic.Cat.CCC.
Require Import Coq.Classes.Morphisms.

(* Itt a változás: {Ct : CartesianCategory C} hozzáadása *)
Class BiCartesianClosedCategory {C : SetoidCategory} {Ct : CartesianCategory C} (CC : CartesianClosedCategory C) := mk_BiCartesianClosedCategory {

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

Arguments initial {C} {Ct} {CC} {_}.
Arguments initial_map {C} {Ct} {CC} {_} {x}.
Arguments initial_map_unique {C} {Ct} {CC} {_} {x} _.

Arguments coprod {C} {Ct} {CC} {_} _ _.
Arguments coprod_inl {C} {Ct} {CC} {_} {x y}.
Arguments coprod_inr {C} {Ct} {CC} {_} {x y}.
Arguments coprod_map {C} {Ct} {CC} {_} {x y z} _ _.

Arguments coprod_map_inl {C} {Ct} {CC} {_} {x y z} _ _.
Arguments coprod_map_inr {C} {Ct} {CC} {_} {x y z} _ _.
Arguments coprod_eta {C} {Ct} {CC} {_} {x y z} _.
Arguments coprod_map_proper_ax {C} {Ct} {CC} {_} {x y z}.

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
Theorem coprod_unique {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC} : 
  forall {x y z} (f : hom x z) (g : hom y z) (h : hom (coprod x y) z), 
    (compose h coprod_inl ≅ f) /\ (compose h coprod_inr ≅ g) -> h ≅ (coprod_map f g).
Proof.
  intros x y z f g h [Hinl Hinr].
  rewrite <- coprod_eta.
  (* Replace h with [h o inl, h o inr] *)
  apply coprod_map_proper_ax.
  - exact Hinl.
  - exact Hinr.
Qed.

(* --- Thin BiCCC Constructor --- *)

Definition Build_Thin_BiCCC 
  (C : SetoidCategory) 
  {Ct : CartesianCategory C} (* Explicitly require Base CC *)
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

(** * Derived Theorems *)

(* Directional version of coprod_unique *)
Theorem unique_coprod {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC} : 
  forall (x y z : @obj C) (f1 : x → z) (f2 : y → z) (g : x ⊕ y → z), 
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

(* Pre-composition distributes over coproduct map *)
(* Dual to compos_prod *)
Theorem compos_coprod {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC} : 
  forall (x y z w : @obj C) (f : x → y) (g : z → y) (h : y → w),
 (h ∘ f) ∐ (h ∘ g) ≅ (h ∘ (f ∐ g)).
Proof.
  intros x y z w f g h.
  apply unique_coprod.
  split.
  (* Check 1st component (inl) *)
  - rewrite <- comp_assoc.
    rewrite coprod_map_inl.
    reflexivity.
  (* Check 2nd component (inr) *)
  - rewrite <- comp_assoc.
    rewrite coprod_map_inr.
    reflexivity.
Qed.

(* Identity expanded as a coproduct of injections *)
(* Dual to pr_and_id *)
Lemma in_and_id {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC} : 
  forall (A B : @obj C), id (A ⊕ B) ≅ coprod_inl ∐ coprod_inr.
Proof.
  intros A B.
  symmetry.
  apply unique_coprod.
  split.
  - rewrite id_left. reflexivity.
  - rewrite id_left. reflexivity.
Qed.

(* Functoriality of Coproduct (Composition of Parallel Maps) *)
(* Dual to prod_id *)
(* (g ⊔ id) ∘ (f ⊔ id) ≅ (g ∘ f) ⊔ id *)
Lemma coprod_id {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC} 
  (X Y Z A : @obj C) : 
  forall (f : X → Y) (g : Y → Z),
    (g ⊔ (id A)) ∘ (f ⊔ (id A)) ≅ (g ∘ f) ⊔ (id A).
Proof.
  intros f g.
  symmetry.
  apply unique_coprod.
  split.

  (* --- 1. First Component (inl) --- *)
  - rewrite <- comp_assoc.
    (* 1. Apply to the first term (Rightmost in composition) *)
    (* (g ⊔ id) ∘ ( (f ⊔ id) ∘ inl ) *)
    rewrite  coprod_map_inl.
    (* (f ⊔ id) ∘ inl -> inl ∘ f *)

    (* 2. Re-associate to expose the second term *)
    (* ( (g ⊔ id) ∘ inl ) ∘ f *)
    rewrite comp_assoc.
    (* 3. Apply to the second term *)
    rewrite coprod_map_inl.
    (* (g ⊔ id) ∘ inl -> inl ∘ g *)
    
    (* 4. Restore association and finish *)
    rewrite comp_assoc.
    (* inl ∘ (g ∘ f) *)
    reflexivity.

  (* --- 2. Second Component (inr) --- *)
  - rewrite <- comp_assoc.
    (* Strategy: The second component handles the Identity part *)
    
    rewrite coprod_map_inr.
    repeat rewrite id_right.
    rewrite coprod_map_inr.
    reflexivity.
Qed.

Lemma coprod_iso_cong {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC} {A B A' B' : @obj C} :
  A ≅O A' -> B ≅O B' -> coprod A B ≅O coprod A' B'.
Proof.
  intros HA HB.
  destruct HA as [toA fromA toA_fromA fromA_toA].
  destruct HB as [toB fromB toB_fromB fromB_toB].

  refine {|
    iso_to := (coprod_inl ∘ toA) ∐ (coprod_inr ∘ toB);
    iso_from := (coprod_inl ∘ fromA) ∐ (coprod_inr ∘ fromB)
  |}.
  - etransitivity.
    + symmetry.
      apply unique_coprod.
      split.
      * rewrite <- comp_assoc.
        rewrite coprod_map_inl.
        rewrite comp_assoc.
        rewrite coprod_map_inl.
        rewrite <- comp_assoc.
        rewrite toA_fromA.
        apply id_right.
      * rewrite <- comp_assoc.
        rewrite coprod_map_inr.
        rewrite comp_assoc.
        rewrite coprod_map_inr.
        rewrite <- comp_assoc.
        rewrite toB_fromB.
        apply id_right.
    + symmetry.
      apply in_and_id.

  - etransitivity.
    + symmetry.
      apply unique_coprod.
      split.
      * rewrite <- comp_assoc.
        rewrite coprod_map_inl.
        rewrite comp_assoc.
        rewrite coprod_map_inl.
        rewrite <- comp_assoc.
        rewrite fromA_toA.
        apply id_right.
      * rewrite <- comp_assoc.
        rewrite coprod_map_inr.
        rewrite comp_assoc.
        rewrite coprod_map_inr.
        rewrite <- comp_assoc.
        rewrite fromB_toB.
        apply id_right.
    + symmetry.
      apply in_and_id.
Qed.