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

Arguments exp {C} {Ct} {_} _ _.
Arguments exp_map {C} {Ct} {_} {x y z} _.
Arguments eval {C} {Ct} {_} {y z}.

Arguments exp_beta {C} {Ct} {_} {x y z} _.
Arguments exp_eta {C} {Ct} {_} {x y z} _.
Arguments exp_map_proper_ax {C} {Ct} {_} {x y z}.

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
Defined.

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
Defined.
 
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
Defined.

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

Lemma exp_iso_cong {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} {A B A' B' : @obj C} :
  A ≅O A' -> B ≅O B' -> exp A B ≅O exp A' B'.
Proof.
  intros HA HB.
  destruct HA as [toA fromA toA_fromA fromA_toA].
  destruct HB as [toB fromB toB_fromB fromB_toB].

  (* ========================================================= *)
  (* ALAP LEMMÁK (Szigorú zárójelezéssel!)                     *)
  (* ========================================================= *)
  
  assert (H_swap_gen : forall (X Y Z W : @obj C) (E : hom X Z) (f : hom W Y),
    ((prod_fst ∏ (f ∘ prod_snd)) ∘ (E Π id W)) ≅ ((E ∘ prod_fst) ∏ (f ∘ prod_snd))).
  { intros X Y Z W E f. symmetry. apply unique_prod. split.
    - repeat rewrite comp_assoc. rewrite prod_map_fst. unfold "Π". rewrite prod_map_fst. reflexivity.
    - repeat rewrite comp_assoc. rewrite prod_map_snd. rewrite <- comp_assoc. unfold "Π". rewrite prod_map_snd. rewrite comp_assoc. rewrite id_right. reflexivity. }
  
  assert (H_swap2_gen : forall (X Y Z W : @obj C) (E : hom X Z) (f : hom W Y),
    ((E Π id Y) ∘ (prod_fst ∏ (f ∘ prod_snd))) ≅ ((E ∘ prod_fst) ∏ (f ∘ prod_snd))).
  { intros X Y Z W E f. symmetry. apply unique_prod. split.
    - repeat rewrite comp_assoc. unfold "Π". rewrite prod_map_fst. rewrite <- comp_assoc. rewrite prod_map_fst. reflexivity.
    - repeat rewrite comp_assoc. unfold "Π". rewrite prod_map_snd. rewrite <- comp_assoc. rewrite prod_map_snd. rewrite id_left. reflexivity. }
  
  assert (H_beta_P : forall (X Y Z W : @obj C) (f : hom (prod X Y) Z) (P : hom W (prod X Y)),
    (eval ∘ ((exp_map f Π id Y) ∘ P)) ≅ (f ∘ P)).
  { intros X Y Z W f P.
    assert (H1 : (eval ∘ ((exp_map f Π id Y) ∘ P)) ≅ ((eval ∘ (exp_map f Π id Y)) ∘ P)).
    { apply comp_assoc || (symmetry; apply comp_assoc). }
    rewrite H1. unfold "Π". rewrite exp_beta. reflexivity. }

  assert (H_id_gen : forall (X Y Z : @obj C) (f : hom Y Z) (g : hom Z Y),
    (f ∘ g) ≅ id _ ->
    (((prod_fst ∏ (f ∘ prod_snd) : hom (prod X Y) (prod X Z)) ∘ 
    (prod_fst ∏ (g ∘ prod_snd) : hom (prod X Z) (prod X Y)))) ≅ id _).
  { intros X Y Z f g Hfg.
    assert (Hid : id (prod X Z) ≅ (prod_fst ∏ prod_snd)).
    { apply pr_and_id || (symmetry; apply pr_and_id). }
    rewrite Hid. symmetry. apply unique_prod. split.
    - repeat rewrite comp_assoc. rewrite prod_map_fst. rewrite prod_map_fst. reflexivity.
    - repeat rewrite comp_assoc. rewrite prod_map_snd. rewrite <- comp_assoc. rewrite prod_map_snd. rewrite comp_assoc. rewrite Hfg. rewrite id_left. reflexivity. }

  (* ========================================================= *)
  (* MAKRÓ LEMMÁK (Gyökérszintű cserék a Coq helyett!)         *)
  (* ========================================================= *)
  
  assert (H_step1 : forall (X Y Z W V U : @obj C) (g : hom V U) (h : hom (prod Z Y) V) (E : hom X Z) (f : hom W Y),
    (g ∘ (h ∘ ((prod_fst ∏ (f ∘ prod_snd)) ∘ (E Π id W)))) ≅ 
    (g ∘ (h ∘ ((E ∘ prod_fst) ∏ (f ∘ prod_snd))))).
  { intros. assert (H : ((prod_fst ∏ (f ∘ prod_snd)) ∘ (E Π id W)) ≅ ((E ∘ prod_fst) ∏ (f ∘ prod_snd))) by apply H_swap_gen. rewrite H. reflexivity. }

  assert (H_step2 : forall (X Y Z W V U : @obj C) (g : hom V U) (h : hom (prod Z Y) V) (E : hom X Z) (f : hom W Y),
    (g ∘ (h ∘ ((E ∘ prod_fst) ∏ (f ∘ prod_snd)))) ≅ 
    (g ∘ (h ∘ ((E Π id Y) ∘ (prod_fst ∏ (f ∘ prod_snd)))))).
  { intros. assert (H : ((E ∘ prod_fst) ∏ (f ∘ prod_snd)) ≅ ((E Π id Y) ∘ (prod_fst ∏ (f ∘ prod_snd)))) by (symmetry; apply H_swap2_gen). rewrite H. reflexivity. }

  assert (H_step3 : forall (X Y Z W U : @obj C) (g : hom Z U) (f : hom (prod X Y) Z) (P : hom W (prod X Y)),
    (g ∘ (eval ∘ ((exp_map f Π id Y) ∘ P))) ≅ 
    (g ∘ (f ∘ P))).
  { intros. assert (H : (eval ∘ ((exp_map f Π id Y) ∘ P)) ≅ (f ∘ P)) by apply H_beta_P. rewrite H. reflexivity. }

  assert (H_step4 : forall (X Y Z W : @obj C) (h : hom (prod X Z) W) (f : hom Y Z) (g : hom Z Y),
    (f ∘ g) ≅ id _ ->
    (h ∘ (((prod_fst ∏ (f ∘ prod_snd) : hom (prod X Y) (prod X Z))) ∘ (prod_fst ∏ (g ∘ prod_snd)))) ≅ h).
  { intros. assert (K : (((prod_fst ∏ (f ∘ prod_snd) : hom (prod X Y) (prod X Z))) ∘ (prod_fst ∏ (g ∘ prod_snd))) ≅ id _).
    { apply H_id_gen. exact H. }
    rewrite K. apply id_right. }

  (* ÚJ: Törlő makrók, amik PONTOSAN a Coq balra-zárójelező (AST) formátumát várják! *)
  assert (H_cancel_toA_AST : forall (X1 X2 X3 : @obj C) (h1 : hom X3 A') (h2 : hom X2 X3) (h3 : hom X1 X2),
    (toA ∘ (((fromA ∘ h1) ∘ h2) ∘ h3)) ≅ (h1 ∘ (h2 ∘ h3))).
  { intros.
    assert (Step1 : (((fromA ∘ h1) ∘ h2) ∘ h3) ≅ ((fromA ∘ h1) ∘ (h2 ∘ h3))). { apply comp_assoc || (symmetry; apply comp_assoc). } rewrite Step1.
    assert (Step2 : ((fromA ∘ h1) ∘ (h2 ∘ h3)) ≅ (fromA ∘ (h1 ∘ (h2 ∘ h3)))). { apply comp_assoc || (symmetry; apply comp_assoc). } rewrite Step2.
    assert (Step3 : (toA ∘ (fromA ∘ (h1 ∘ (h2 ∘ h3)))) ≅ ((toA ∘ fromA) ∘ (h1 ∘ (h2 ∘ h3)))). { apply comp_assoc || (symmetry; apply comp_assoc). } rewrite Step3.
    rewrite toA_fromA. apply id_left. }

  assert (H_cancel_fromA_AST : forall (X1 X2 X3 : @obj C) (h1 : hom X3 A) (h2 : hom X2 X3) (h3 : hom X1 X2),
    (fromA ∘ (((toA ∘ h1) ∘ h2) ∘ h3)) ≅ (h1 ∘ (h2 ∘ h3))).
  { intros.
    assert (Step1 : (((toA ∘ h1) ∘ h2) ∘ h3) ≅ ((toA ∘ h1) ∘ (h2 ∘ h3))). { apply comp_assoc || (symmetry; apply comp_assoc). } rewrite Step1.
    assert (Step2 : ((toA ∘ h1) ∘ (h2 ∘ h3)) ≅ (toA ∘ (h1 ∘ (h2 ∘ h3)))). { apply comp_assoc || (symmetry; apply comp_assoc). } rewrite Step2.
    assert (Step3 : (fromA ∘ (toA ∘ (h1 ∘ (h2 ∘ h3)))) ≅ ((fromA ∘ toA) ∘ (h1 ∘ (h2 ∘ h3)))). { apply comp_assoc || (symmetry; apply comp_assoc). } rewrite Step3.
    rewrite fromA_toA. apply id_left. }

  refine {|
    iso_to := exp_map (toA ∘ eval ∘ (prod_fst ∏ (fromB ∘ prod_snd)));
    iso_from := exp_map (fromA ∘ eval ∘ (prod_fst ∏ (toB ∘ prod_snd)))
  |}.
  
  - (* ========================================================= *)
    (* 1. Irány: iso_to ∘ iso_from ≅ id                          *)
    (* ========================================================= *)
    etransitivity. { apply compos_exp. }
    
    assert (H_arg : ((toA ∘ eval ∘ (prod_fst ∏ (fromB ∘ prod_snd))) ∘ (exp_map (fromA ∘ eval ∘ (prod_fst ∏ (toB ∘ prod_snd))) Π id B')) ≅ eval).
    {
      assert (H_ready : (toA ∘ (eval ∘ ((prod_fst ∏ (fromB ∘ prod_snd)) ∘ (exp_map (fromA ∘ eval ∘ (prod_fst ∏ (toB ∘ prod_snd))) Π id B')))) ≅ eval).
      {
        rewrite H_step1.
        rewrite H_step2.
        rewrite H_step3.
        
        (* A varázslat: A Coq balra-zárójelező fája PONTOSAN illeszkedik a makróra! *)
        rewrite H_cancel_toA_AST.
        
        (* És a H_step4 pedig pontosan azt a h1 ∘ (h2 ∘ h3) fát várja, amit a makró kiad! *)
        apply H_step4. exact toB_fromB.
      }
      assert (H_assoc : ((toA ∘ eval ∘ (prod_fst ∏ (fromB ∘ prod_snd))) ∘ (exp_map (fromA ∘ eval ∘ (prod_fst ∏ (toB ∘ prod_snd))) Π id B')) ≅ 
                        (toA ∘ (eval ∘ ((prod_fst ∏ (fromB ∘ prod_snd)) ∘ (exp_map (fromA ∘ eval ∘ (prod_fst ∏ (toB ∘ prod_snd))) Π id B'))))).
      { repeat rewrite comp_assoc. reflexivity. }
      rewrite H_assoc. exact H_ready.
    }
    rewrite H_arg.
    symmetry. apply eval_and_id.

  - (* ========================================================= *)
    (* 2. Irány: iso_from ∘ iso_to ≅ id                          *)
    (* ========================================================= *)
    etransitivity. { apply compos_exp. }
    
    assert (H_arg : ((fromA ∘ eval ∘ (prod_fst ∏ (toB ∘ prod_snd))) ∘ (exp_map (toA ∘ eval ∘ (prod_fst ∏ (fromB ∘ prod_snd))) Π id B)) ≅ eval).
    {
      assert (H_ready : (fromA ∘ (eval ∘ ((prod_fst ∏ (toB ∘ prod_snd)) ∘ (exp_map (toA ∘ eval ∘ (prod_fst ∏ (fromB ∘ prod_snd))) Π id B)))) ≅ eval).
      {
        rewrite H_step1.
        rewrite H_step2.
        rewrite H_step3.
        
        (* Ugyanez a csoda a második iránynál! *)
        rewrite H_cancel_fromA_AST.
        
        apply H_step4. exact fromB_toB.
      }
      assert (H_assoc : ((fromA ∘ eval ∘ (prod_fst ∏ (toB ∘ prod_snd))) ∘ (exp_map (toA ∘ eval ∘ (prod_fst ∏ (fromB ∘ prod_snd))) Π id B)) ≅ 
                        (fromA ∘ (eval ∘ ((prod_fst ∏ (toB ∘ prod_snd)) ∘ (exp_map (toA ∘ eval ∘ (prod_fst ∏ (fromB ∘ prod_snd))) Π id B))))).
      { repeat rewrite comp_assoc. reflexivity. }
      rewrite H_assoc. exact H_ready.
    }
    rewrite H_arg.
    symmetry. apply eval_and_id.
Defined.