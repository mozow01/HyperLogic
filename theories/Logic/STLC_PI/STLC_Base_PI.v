Require Import List PeanoNat Arith Lia.
Import ListNotations.
Require Import Coq.Classes.Morphisms.

(* ================================================================= *)
(*                    TYPES AND TERMS                                *)
(* ================================================================= *)

Inductive ty : Set :=
  | Ty_Atomic : nat -> ty
  | Ty_Unit   : ty               
  | Ty_Arrow  : ty -> ty -> ty   
  | Ty_Prod   : ty -> ty -> ty. 

Inductive tm : Set :=
  | tm_unit : tm                 
  | tm_var  : nat -> tm          
  | tm_lam  : ty -> tm -> tm     
  | tm_app  : tm -> tm -> tm     
  | tm_pair : tm -> tm -> tm    
  | tm_fst  : tm -> tm           
  | tm_snd  : tm -> tm.         

Definition context := list ty.

(* ================================================================= *)
(*                    TYPING SYSTEM                                  *)
(* ================================================================= *)

Inductive typeability : context -> tm -> ty -> Prop :=
  | T_Unit : forall Gamma, 
      typeability Gamma tm_unit Ty_Unit

  | T_Var0 : forall Gamma A, 
      typeability (A :: Gamma) (tm_var 0) A

  | T_VarS : forall Gamma A B i, 
      typeability Gamma (tm_var i) A -> 
      typeability (B :: Gamma) (tm_var (S i)) A

  | T_Lam : forall Gamma t A B, 
      typeability (A :: Gamma) t B -> 
      typeability Gamma (tm_lam A t) (Ty_Arrow A B)

  | T_App : forall Gamma t s A B, 
      typeability Gamma t (Ty_Arrow A B) -> 
      typeability Gamma s A -> 
      typeability Gamma (tm_app t s) B

  | T_Pair : forall Gamma t s A B, 
      typeability Gamma t A -> 
      typeability Gamma s B -> 
      typeability Gamma (tm_pair t s) (Ty_Prod A B)

  | T_Fst : forall Gamma t A B, 
      typeability Gamma t (Ty_Prod A B) -> 
      typeability Gamma (tm_fst t) A

  | T_Snd : forall Gamma t A B, 
      typeability Gamma t (Ty_Prod A B) -> 
      typeability Gamma (tm_snd t) B.

Notation "Gamma '⊢' t '[:]' A" := (typeability Gamma t A) (at level 70, no associativity) : type_scope.
Notation "'⊢' t '[:]' A" := (typeability nil t A) (at level 70, no associativity) : type_scope.
Notation "A ⊃ B" := (Ty_Arrow A B) (at level 70, right associativity) : type_scope.

(* ================================================================= *)
(*                  PROOF IRRELEVANCE LOGIC                          *)
(* ================================================================= *)

Inductive tm_equiv_rel : tm -> tm -> Prop :=
  | PI_rule : forall Gamma A t s,
      (Gamma ⊢ t [:] A) -> (Gamma ⊢ s [:] A) -> tm_equiv_rel t s.

Definition obj_stlc := ty.

Definition hom_stlc (x y : obj_stlc) := { t : tm | ⊢ t [:] (x ⊃ y)}.

Definition hom_equiv_stlc {x y : obj_stlc} (f g : hom_stlc x y) :=
  tm_equiv_rel (proj1_sig f) (proj1_sig g).

Lemma generic_axiom_proof : forall {x y} (f g : hom_stlc x y), hom_equiv_stlc f g.
Proof.
  intros x y f g.
  unfold hom_equiv_stlc.
  apply (PI_rule nil (x ⊃ y)).
  - exact (proj2_sig f).
  - exact (proj2_sig g).
Defined.

Lemma hom_equiv_stlc_refl : forall {x y} (f : hom_stlc x y), hom_equiv_stlc f f.
Proof. intros; apply generic_axiom_proof. Defined.

Lemma hom_equiv_stlc_sym : forall {x y} (f g : hom_stlc x y), hom_equiv_stlc f g -> hom_equiv_stlc g f.
Proof. intros; apply generic_axiom_proof. Defined.

Lemma hom_equiv_stlc_trans : forall {x y} (f g h : hom_stlc x y), hom_equiv_stlc f g -> hom_equiv_stlc g h -> hom_equiv_stlc f h.
Proof. intros; apply generic_axiom_proof. Defined.  