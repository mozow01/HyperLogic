Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import Coq.Classes.Morphisms.

(* ================================================================= *)
(* CARTESIAN CLOSED CATEGORY (Extends CartesianCategory)             *)
(* ================================================================= *)

(* A Ct : CartesianCategory C paraméter jelzi, hogy erre épülünk *)
Class CartesianClosedCategory (C : SetoidCategory) {Ct : CartesianCategory C} := mk_CartesianClosedCategory {
  
  (* --- EXPONENTIAL OBJECT --- *)
  exp : @obj C -> @obj C -> @obj C;
  
  (* Constructor: Lambda g / curry g *)
  (* prod_map a CC-ből jön! *)
  exp_map : forall {x y z} (g : hom (prod x y) z), hom x (exp z y);
  
  (* Destructor: eval / apply *)
  eval : forall {y z}, hom (prod (exp z y) y) z;
  
  (* Equations *)
  
  (* Beta rule *)
  exp_beta : forall {x y z} (g : hom (prod x y) z),
    compose eval (prod_map (compose (exp_map g) prod_fst) (compose (id y) prod_snd)) ≅ g;
                      
  (* Eta rule *)
  exp_eta : forall {x y z} (h : hom x (exp z y)),
    exp_map (compose eval (prod_map (compose h prod_fst) (compose (id y) prod_snd))) ≅ h;

  (* Proper instance *)
  exp_map_proper_ax : forall {x y z},
    Proper (hom_equiv ==> hom_equiv) (@exp_map x y z)
}. 

Existing Instance exp_map_proper_ax.

(* --- Notations --- *)
Notation "z ^ y" := (exp z y) (at level 30, right associativity) : type_scope.

(* --- Theorems --- *)

Theorem exp_unique {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} : 
  forall {x y z} (g : hom (prod x y) z) (h : hom x (exp z y)),
  compose eval (prod_map (compose h prod_fst) (compose (id y) prod_snd)) ≅ g
  -> h ≅ exp_map g.
Proof.
  intros x y z g h H_eq.
  rewrite <- exp_eta.
  apply exp_map_proper_ax; exact H_eq.
Qed.

(* Naturality of Currying *)
Theorem compos_exp {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} : 
  forall x y z w (g : y × w → z) (h : x → y),
  exp_map g ∘ h ≅ exp_map (g ∘ (h Π (id w))).
Proof.
  intros x y z w g h.
  apply exp_unique.
  transitivity (eval ∘ ((exp_map g Π (id w)) ∘ (h Π (id w)))).
  - apply comp_proper; [reflexivity | ].
    symmetry. apply prod_id.
  - rewrite comp_assoc.
    rewrite exp_beta.
    reflexivity.
Qed.

Lemma eval_and_id {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} : 
  forall (A B : @obj C), id (exp B A) ≅ exp_map eval.
Proof.
  intros A B.
  apply exp_unique.
  assert (H_simpl: prod_map (compose (id (exp B A)) prod_fst) 
                            (compose (id A) prod_snd)
                   ≅ id (prod (exp B A) A)).
  {
    rewrite id_left, id_left.
    symmetry. apply pr_and_id.
  }
  rewrite H_simpl.
  apply id_right.
Qed.

(* --- Thin CCC Constructor --- *)
(* Ez most már csak az Exponenciális részt építi fel! *)
(* A felhasználónak előbb fel kell építenie a CC-t a Build_Thin_CC-vel. *)
Definition Build_Thin_CCC 
  (C : SetoidCategory)          
  (HThin : Thin C)              
  {Ct : CartesianCategory C} (* Elvárjuk, hogy ez már meglegyen *)
  (exp_item : @obj C -> @obj C -> @obj C)
  (eval_item : forall {y z}, hom (prod (exp_item z y) y) z)
  (exp_map_item : forall {x y z} (g : hom (prod x y) z), hom x (exp_item z y))
  : CartesianClosedCategory C.
Proof.
  apply mk_CartesianClosedCategory with
    (exp := exp_item)
    (eval := @eval_item)
    (exp_map := @exp_map_item).
  all: intros; try (unfold Proper, respectful; intros); apply thin_unique.
Defined.