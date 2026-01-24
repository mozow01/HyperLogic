Require Import Core.
Require Import Coq.Classes.Morphisms.

Class CartesianClosedCategory (C : SetoidCategory) := mk_CartesianClosedCategory {
  
  (* 1. Terminal Object *)
  terminal : @obj C;
  terminal_map : forall {x}, hom x terminal;

  (* 2. Product *)
  prod : @obj C -> @obj C -> @obj C;
  
  prod_map : forall {x y z} (f : hom x y) (g : hom x z), hom x (prod y z);
  prod_fst : forall {x y}, hom (prod x y) x;
  prod_snd : forall {x y}, hom (prod x y) y;

  (* 3. Exponential *)
  exp : @obj C -> @obj C -> @obj C;
  
  eval : forall {y z}, hom (prod (exp z y) y) z;
  curry : forall {x y z} (g : hom (prod x y) z), hom x (exp z y);
  
  terminal_map_unique : forall {x} (f : hom x terminal), 
        f ≅ terminal_map;

  prod_map_fst : forall {x y z} (f : hom x y) (g : hom x z), 
        compose prod_fst (prod_map f g) ≅ f;
        
  prod_map_snd : forall {x y z} (f : hom x y) (g : hom x z), 
        compose prod_snd (prod_map f g) ≅ g;
        
  prod_unique : forall {x y z} (f : hom x y) (g : hom x z) (h : hom x (prod y z)), 
        (compose prod_fst h ≅ f) /\ (compose prod_snd h ≅ g) -> h ≅ (prod_map f g);

  curry_eval : forall {x y z} (g : hom (prod x y) z),
        compose eval 
                (prod_map (compose (curry g) prod_fst) 
                          (compose (id y) prod_snd)) ≅ g;

  curry_unique : forall {x y z} (h : hom x (exp z y)),
        curry (compose eval 
                       (prod_map (compose h prod_fst) 
                                 (compose (id y) prod_snd))) ≅ h
}.

Notation "⊤" := (terminal) (at level 0, no associativity) : type_scope.

(* f ∏ g : *)
(* x -> y, x -> z  ===> x -> y × z *)
Notation "f '∏' g" := (prod_map f g) (at level 30, no associativity) : type_scope.

(* f Π g : "Torii" *)
(* x -> y , z -> w ===> x × z -> y × w *)
Notation "f 'Π' g" := (prod_map (compose f prod_fst) (compose g prod_snd)) 
                      (at level 30, no associativity) : type_scope.
(* x × y  *)
Notation "x × y" := (prod x y) (at level 40, left associativity) : type_scope.

Instance prod_map_proper {C : SetoidCategory} {CC : CartesianClosedCategory C} {x y z : @obj C} :
  Proper (hom_equiv ==> hom_equiv ==> hom_equiv) (@prod_map C CC x y z).
Proof.
  (* f ≅ f' , g ≅ g' ->  <f,g> ≅ <f',g'> *)
  intros f f' Hf g g' Hg.
  
  (*  prod_unique  (h = <f', g'>) *)
  symmetry.
  apply prod_unique.
  split.
  
  (* LHS: fst o <f', g'> ≅ f *)
  - rewrite prod_map_fst. (* fst o <f', g'> --> f' *)
    symmetry. assumption. (* f' ≅ f *)
    
  (* RHS: snd o <f', g'> ≅ g *)
  - rewrite prod_map_snd. (* snd o <f', g'> --> g' *)
    symmetry. assumption. (* g' ≅ g *)
Qed.

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

Theorem prod_eta {C : SetoidCategory} {CC : CartesianClosedCategory C} : 
  forall {x y z : @obj C} (h : x → y × z),
    prod_map (compose prod_fst h) (compose prod_snd h) ≅ h.
Proof.
  intros x y z h.
  symmetry.
  apply prod_unique. 
  split.
  all: reflexivity.
Qed.

Theorem compos_prod {C : SetoidCategory} {CC : CartesianClosedCategory C} : 
  forall (x y z w : @obj C) (f : w → y) (g : w → z) (h : x → w),
 (prod_map (f ∘ h) (g ∘ h)) ≅ ((prod_map f g) ∘ h).
Proof.
  intros x y z w f g h.
  apply unique_prod.
  split.
  all: rewrite comp_assoc; try rewrite prod_map_fst; try rewrite prod_map_snd; reflexivity.
  (*
  (* LHS: fst ∘ ((f ∏ g) ∘ h) *)
  - rewrite comp_assoc.      (* (fst ∘ (f ∏ g)) ∘ h ≅ fst ∘ (f ∏ g) ∘ h *)
    rewrite prod_map_fst.    (* fst ∘ (f ∏ g) ≅ f *)
    reflexivity.             (* f ∘ h ≅ f ∘ h *)

  (* RHS: snd ∘ ((f ∏ g) ∘ h) *)
  - rewrite comp_assoc.      (* prod_snd ∘ (f ∏ g ∘ h) ≅ prod_snd ∘ f ∏ g ∘ h *)
    rewrite prod_map_snd.    (* snd ∘ (f ∏ g) ≅ g *)
    reflexivity.             (* g ∘ h ≅ g ∘ h *)
   *)
Qed.

Lemma pr_and_id {C : SetoidCategory} {CC : CartesianClosedCategory C} : 
  forall (A B : @obj C), id (A × B) ≅ prod_fst ∏ prod_snd.
Proof.
  intros A B.
  (* prod_fst ≅ (prod_fst ∘ id) *)
  assert (H1: prod_fst ≅ compose prod_fst (id (A × B))).
  { rewrite id_right. reflexivity. }
  
  assert (H2: prod_snd ≅ compose prod_snd (id (A × B))).
  { rewrite id_right. reflexivity. }

  rewrite H1 at 1. 
  rewrite H2 at 1.

  symmetry.
  apply unique_prod.
  split.
  all: reflexivity.
Qed.

(* --- Thin CCC Constructor --- *)

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
  (curry_item : forall {x y z} (g : hom (prod_item x y) z), hom x (exp_item z y))
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
    (curry := @curry_item).
  all: intros; apply thin_unique.
Defined.