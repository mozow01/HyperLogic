Require Import Core.
Require Import Coq.Classes.Morphisms.

Class CartesianClosedCategory (C : SetoidCategory) := mk_CartesianClosedCategory {
  
  (* ========================== *)
  (* 1. TERMINAL                *)
  (* ========================== *)
  terminal : @obj C;
  terminal_map : forall {x}, hom x terminal;
  
  terminal_map_unique : forall {x} (f : hom x terminal), 
        f ≅ terminal_map;

  (* ========================== *)
  (* 2. PRODUCT                 *)
  (* ========================== *)
  prod : @obj C -> @obj C -> @obj C;
  
  (* Constructors: <f, g> *)
  prod_map : forall {x y z} (f : hom x y) (g : hom x z), hom x (prod y z);
  
  (* Destructors: *)
  prod_fst : forall {x y}, hom (prod x y) x;
  prod_snd : forall {x y}, hom (prod x y) y;

  (* Equations *)
  
  prod_map_fst : forall {x y z} (f : hom x y) (g : hom x z), 
        compose prod_fst (prod_map f g) ≅ f;
        
  prod_map_snd : forall {x y z} (f : hom x y) (g : hom x z), 
        compose prod_snd (prod_map f g) ≅ g;
  
  prod_eta : forall {x y z} (h : hom x (prod y z)),
        prod_map (compose prod_fst h) (compose prod_snd h) ≅ h;

  prod_map_proper_ax : forall {x y z},
        Proper (hom_equiv ==> hom_equiv ==> hom_equiv) (@prod_map x y z);


  (* ========================== *)
  (* 3. EXPONENTIAL             *)
  (* ========================== *)
  exp : @obj C -> @obj C -> @obj C;
  
  (*Constructor: Lambda g / curry g *)
  exp_map : forall {x y z} (g : hom (prod x y) z), hom x (exp z y);

  (* Destructor: eval / apply *)
  eval : forall {y z}, hom (prod (exp z y) y) z;
  
  (* Equations *)

  (* Beta rule: eval( (λg) x id ) = g *)
  exp_beta : forall {x y z} (g : hom (prod x y) z),
        compose eval 
                (prod_map (compose (exp_map g) prod_fst) 
                          (compose (id y) prod_snd)) ≅ g;

  (* Eta rule: λ( eval( h x id ) ) = h *)
  exp_eta : forall {x y z} (h : hom x (exp z y)),
        exp_map (compose eval 
                       (prod_map (compose h prod_fst) 
                                 (compose (id y) prod_snd))) ≅ h;

  exp_map_proper_ax : forall {x y z},
        Proper (hom_equiv ==> hom_equiv) (@exp_map x y z)
}.

Existing Instance prod_map_proper_ax.
Existing Instance exp_map_proper_ax.

Notation "⊤" := (terminal) (at level 0, no associativity) : type_scope.
Notation "x × y" := (prod x y) (at level 40, left associativity) : type_scope.

Notation "f '∏' g" := (prod_map f g) (at level 30, no associativity) : type_scope.
Notation "f 'Π' g" := (prod_map (compose f prod_fst) (compose g prod_snd)) 
                      (at level 30, no associativity) : type_scope.


Lemma prod_unique {C : SetoidCategory} {CC : CartesianClosedCategory C} : 
  forall {x y z} (f : hom x y) (g : hom x z) (h : hom x (prod y z)), 
    (compose prod_fst h ≅ f) /\ (compose prod_snd h ≅ g) -> h ≅ (prod_map f g).
Proof.
  intros x y z f g h [Hfst Hsnd].
  rewrite <- prod_eta. (* h helyett <fst h, snd h> *)
  apply prod_map_proper_ax.
  - exact Hfst. 
  - exact Hsnd. 
Qed.

(* Az exp_unique (curry_unique) lemma átnevezve, exp_map-et használva *)
Theorem exp_unique {C : SetoidCategory} {CC : CartesianClosedCategory C} : 
  forall {x y z} (g : hom (prod x y) z) (h : hom x (exp z y)),
  compose eval (prod_map (compose h prod_fst) (compose (id y) prod_snd)) ≅ g
  -> h ≅ exp_map g.
Proof.
  intros x y z g h H_eq.
  rewrite <- exp_eta. (* h helyett exp_map(eval(h x id)) *)
  apply exp_map_proper_ax.
  exact H_eq.
Qed.

(* --- Thin CCC Constructor (Frissített nevekkel) --- *)

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
  (exp_map_item : forall {x y z} (g : hom (prod_item x y) z), hom x (exp_item z y)) (* Renamed *)
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
    (exp_map := @exp_map_item). (* Renamed *)
  
  all: intros.

   all: try (unfold Proper, respectful; intros).
   all: apply thin_unique.
Defined.