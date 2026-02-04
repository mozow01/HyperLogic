Require Import Core.
Require Import Coq.Classes.Morphisms.

(** * Cartesian Closed Category Definition *) 

Class CartesianClosedCategory (C : SetoidCategory) := mk_CartesianClosedCategory {
  
  (* ========================== *)
  (* 1. TERMINAL OBJECT         *)
  (* ========================== *)
  terminal : @obj C;
  terminal_map : forall {x}, hom x terminal;
  
  terminal_map_unique : forall {x} (f : hom x terminal), 
    f ≅ terminal_map;

  (* ========================== *)
  (* 2. PRODUCT OBJECT          *)
  (* ========================== *)
  prod : @obj C -> @obj C -> @obj C;
  
  (* Constructors: <f, g> *)
  prod_map : forall {x y z} (f : hom x y) (g : hom x z), hom x (prod y z);
  
  (* Destructors: Projections *)
  prod_fst : forall {x y}, hom (prod x y) x;
  prod_snd : forall {x y}, hom (prod x y) y;

  (* Equations *)
  
  (* Projection rules *)
  prod_map_fst : forall {x y z} (f : hom x y) (g : hom x z), 
    compose prod_fst (prod_map f g) ≅ f;
        
  prod_map_snd : forall {x y z} (f : hom x y) (g : hom x z), 
    compose prod_snd (prod_map f g) ≅ g;
  
  (* Eta rule: <fst o h, snd o h> ~ h *)
  prod_eta : forall {x y z} (h : hom x (prod y z)),
    prod_map (compose prod_fst h) (compose prod_snd h) ≅ h;

  (* Proper instance required for rewriting inside prod_map *)
  prod_map_proper_ax : forall {x y z},
    Proper (hom_equiv ==> hom_equiv ==> hom_equiv) (@prod_map x y z);


  (* ========================== *)
  (* 3. EXPONENTIAL OBJECT      *)
  (* ========================== *)
  exp : @obj C -> @obj C -> @obj C;
  
  (* Constructor: Lambda g / curry g *)
  (* Renamed to exp_map for symmetry with prod_map *)
  exp_map : forall {x y z} (g : hom (prod x y) z), hom x (exp z y);

  (* Destructor: eval / apply *)
  eval : forall {y z}, hom (prod (exp z y) y) z;
  
  (* Equations *)

  (* Beta rule: eval( (λg) x id ) ~ g *)
  exp_beta : forall {x y z} (g : hom (prod x y) z),
    compose eval 
            (prod_map (compose (exp_map g) prod_fst) 
                      (compose (id y) prod_snd)) ≅ g;

  (* Eta rule: λ( eval( h x id ) ) ~ h *)
  exp_eta : forall {x y z} (h : hom x (exp z y)),
    exp_map (compose eval 
                     (prod_map (compose h prod_fst) 
                               (compose (id y) prod_snd))) ≅ h;

  (* Proper instance required for rewriting inside exp_map *)
  exp_map_proper_ax : forall {x y z},
    Proper (hom_equiv ==> hom_equiv) (@exp_map x y z)
}.

(* Register instances for Setoid rewriting *)
Existing Instance prod_map_proper_ax.
Existing Instance exp_map_proper_ax.

(* --- Notations --- *)

Notation "⊤" := (terminal) (at level 0, no associativity) : type_scope.
Notation "x × y" := (prod x y) (at level 40, left associativity) : type_scope.

(* Standard Product Map: <f, g> *)
Notation "f '∏' g" := (prod_map f g) (at level 30, no associativity) : type_scope.

(* Parallel Product Map: f x g *)
Notation "f 'Π' g" := (prod_map (compose f prod_fst) (compose g prod_snd)) 
                      (at level 30, no associativity) : type_scope.


(** * Core Lemmas *)

(* Uniqueness of the product map derived from Eta *)
Lemma prod_unique {C : SetoidCategory} {CC : CartesianClosedCategory C} : 
  forall {x y z} (f : hom x y) (g : hom x z) (h : hom x (prod y z)), 
    (compose prod_fst h ≅ f) /\ (compose prod_snd h ≅ g) -> h ≅ (prod_map f g).
Proof.
  intros x y z f g h [Hfst Hsnd].
  rewrite <- prod_eta. (* Replace h with <fst h, snd h> *)
  apply prod_map_proper_ax.
  - exact Hfst. 
  - exact Hsnd. 
Qed.

(* Uniqueness of the exponential map derived from Eta *)
Theorem exp_unique {C : SetoidCategory} {CC : CartesianClosedCategory C} : 
  forall {x y z} (g : hom (prod x y) z) (h : hom x (exp z y)),
  compose eval (prod_map (compose h prod_fst) (compose (id y) prod_snd)) ≅ g
  -> h ≅ exp_map g.
Proof.
  intros x y z g h H_eq.
  rewrite <- exp_eta. (* Replace h with exp_map(eval(h x id)) *)
  apply exp_map_proper_ax.
  exact H_eq.
Qed.

(* --- Thin CCC Constructor --- *)
(* Automates the construction of a CCC if the category is Thin *)
Definition Build_Thin_CCC 
  (C : SetoidCategory)          
  (HThin : Thin C)              
  (terminal_item : @obj C)
  (terminal_map_item : forall {x}, hom x terminal_item)
  (prod_item : @obj C -> @obj C -> @obj C)
  (prod_map_item : forall {x y z} (f : hom x y) (g : hom x z), hom x (prod_item y z))
  (prod_fst_item : forall {x y}, hom (prod_item x y) x)
  (prod_snd_item : forall {x y}, hom (prod_item x y) y)
  (exp_item : @obj C -> @obj C -> @obj C)
  (eval_item : forall {y z}, hom (prod_item (exp_item z y) y) z)
  (exp_map_item : forall {x y z} (g : hom (prod_item x y) z), hom x (exp_item z y))
  : CartesianClosedCategory C.
Proof.
  apply mk_CartesianClosedCategory with
    (terminal := terminal_item)
    (terminal_map := @terminal_map_item)
    (prod := prod_item)
    (prod_map := @prod_map_item)
    (prod_fst := @prod_fst_item)
    (prod_snd := @prod_snd_item)
    (exp := exp_item)
    (eval := @eval_item)
    (exp_map := @exp_map_item).
  
  (* Introduce variables for all goals *)
  all: intros.
  (* Unfold Proper definitions to expose the underlying equality *)
  all: try (unfold Proper, respectful; intros).
  (* Thin categories satisfy all equality constraints automatically *)
  all: apply thin_unique.
Defined.


(** * Derived Theorems *)

(* Directional version of prod_unique for easier application *)
Theorem unique_prod {C : SetoidCategory} {CC : CartesianClosedCategory C} : 
  forall (x y z : @obj C) (f1 : x → y) (f2 : x → z) (g : x → y × z), 
    ((prod_fst ∘ g) ≅ f1) /\ ((prod_snd ∘ g) ≅ f2) -> f1 ∏ f2 ≅ g.
Proof.
  intros x y z f1 f2 g H.
  symmetry.
  apply prod_unique.
  destruct H as [H1 H2].
  split.
  - rewrite H1. reflexivity.
  - rewrite H2. reflexivity.
Qed.

(* Composition of product maps *)
Theorem compos_prod {C : SetoidCategory} {CC : CartesianClosedCategory C} : 
  forall x y z w (f : w → y) (g : w → z) (h : x → w),
  (f ∘ h) ∏ (g ∘ h) ≅ ((f ∏ g) ∘ h). 
Proof.
  intros.
  apply unique_prod.
  split.
  (* Check 1st component *)
  - rewrite comp_assoc. 
    rewrite prod_map_fst. 
    reflexivity.
  (* Check 2nd component *)
  - rewrite comp_assoc. 
    rewrite prod_map_snd. 
    reflexivity.
Qed.

(* Identity expanded as a product of projections *)
Lemma pr_and_id {C : SetoidCategory} {CC : CartesianClosedCategory C} : 
  forall (A B : @obj C), id (A × B) ≅ prod_fst ∏ prod_snd.
Proof.
  intros A B.
  symmetry.
  apply unique_prod.
  split.
  - rewrite id_right. reflexivity.
  - rewrite id_right. reflexivity.
Qed.

(* Functoriality of Product (Composition of Parallel Maps) *)
Lemma prod_id {C : SetoidCategory} {CC : CartesianClosedCategory C} (X Y Z A : @obj C) : 
  forall (f : X → Y) (g : Y → Z),
    (g Π (id A)) ∘ (f Π (id A)) ≅ (g ∘ f) Π (id A).
Proof.
  intros f g.
  symmetry. 
  apply unique_prod.
  split.
  
  (* --- 1. First Component (fst) --- *)
  - rewrite comp_assoc. 
    
    (* Strategy: Move prod_fst to the right through the composition chain.
       We need to re-associate (<- comp_assoc) to expose the inner prod_map 
       to prod_fst. *)

    (* 1. Apply to the first term *)
    rewrite prod_map_fst. (* prod_fst ∘ (g Π id) -> g ∘ prod_fst *)

    (* 2. Re-associate to expose the second term *)
    rewrite <- comp_assoc. (* g ∘ (prod_fst ∘ (f Π id)) *)

    (* 3. Apply to the second term *)
    rewrite prod_map_fst. (* g ∘ (f ∘ prod_fst) *)
    
    (* 4. Restore association *)
    rewrite comp_assoc.
    reflexivity.

  (* --- 2. Second Component (snd) --- *)
  - rewrite comp_assoc.
    
    (* Strategy: Peel off layers. Since the second component of (X Π id) is identity,
       it simplifies quickly. *)
    
    rewrite prod_map_snd. (* prod_snd ∘ (g Π id) -> id ∘ prod_snd *)
    rewrite id_left.      

    rewrite prod_map_snd. (* prod_snd ∘ (f Π id) -> id ∘ prod_snd *)
    rewrite id_left. 
    reflexivity.
Qed.

(* Naturality of Currying *)
Theorem compos_exp {C : SetoidCategory} {CC : CartesianClosedCategory C} : 
  forall x y z w (g : y × w → z) (h : x → y),
  exp_map g ∘ h ≅ exp_map (g ∘ (h Π (id w))).
Proof.
  intros x y z w g h.
  apply exp_unique.
  
  (* Goal: eval ∘ ((exp_map g ∘ h) Π id) ≅ g ∘ (h Π id) *)

  (* Use transitivity to introduce a middle term that helps apply exp_beta *)
  transitivity (eval ∘ ((exp_map g Π (id w)) ∘ (h Π (id w)))).
  
  (* Subgoal 1: Left side rearrangement *)
  - apply comp_proper; [reflexivity | ].
    (* Use prod_id in reverse: (u Π id) ∘ (v Π id) ≅ (u ∘ v) Π id *)
    symmetry.
    apply prod_id.

  (* Subgoal 2: Right side simplification using Beta rule *)
  - rewrite comp_assoc.
    (* Now the head matches exp_beta: eval ∘ (exp_map g Π id) ... *)
    rewrite exp_beta.
    reflexivity. 
Qed.

(* Identity on Exponentials *)
Lemma eval_and_id {C : SetoidCategory} {CC : CartesianClosedCategory C} : 
  forall (A B : @obj C), id (exp B A) ≅ exp_map eval.
Proof.
  intros A B.
  apply exp_unique.
  
  (* We need to prove: eval ∘ (id Π id) ≅ eval *)
  
  (* Local assertion: (id Π id) is just id *)
  assert (H_simpl: prod_map (compose (id (exp B A)) prod_fst) 
                            (compose (id A) prod_snd)
                   ≅ id (prod (exp B A) A)).
  {
    (* Simplify the product map internals *)
    rewrite id_left. 
    rewrite id_left.
    
    (* prod_map fst snd ≅ id (via pr_and_id) *)
    symmetry.
    apply pr_and_id.
  }

  (* Apply the simplification *)
  rewrite H_simpl.
  apply id_right.
Qed. 
