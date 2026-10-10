
Require Import List PeanoNat Arith Lia.
Import ListNotations.
Require Import Coq.Classes.Morphisms.

(** Simply typed lambda calculus with products, sums, and void. *)

Inductive ty : Set :=
  | Ty_Atomic : nat -> ty
  | Ty_Unit   : ty
  | Ty_Void   : ty
  | Ty_Arrow  : ty -> ty -> ty
  | Ty_Prod   : ty -> ty -> ty
  | Ty_Sum    : ty -> ty -> ty.

Inductive tm : Set :=
  | tm_unit   : tm                 
  | tm_var    : nat -> tm          
  | tm_lam    : ty -> tm -> tm     
  | tm_app    : tm -> tm -> tm     
  | tm_pair   : tm -> tm -> tm     
  | tm_fst    : tm -> tm           
  | tm_snd    : tm -> tm           
  (* Sum injections carry the other summand to make typing unique. *)
  | tm_inl    : ty -> tm -> tm
  | tm_inr    : ty -> tm -> tm
  | tm_case   : tm -> tm -> tm -> tm
  | tm_absurd : ty -> tm -> tm.

Definition context := list ty.


Declare Scope stlc_scope_sum.
Delimit Scope stlc_scope_sum with stlc_sum.


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

  | T_App : forall Gamma t1 t2 A B, 
      typeability Gamma t1 (Ty_Arrow A B) -> 
      typeability Gamma t2 A -> 
      typeability Gamma (tm_app t1 t2) B

  | T_Pair : forall Gamma t1 t2 A B,
      typeability Gamma t1 A ->
      typeability Gamma t2 B ->
      typeability Gamma (tm_pair t1 t2) (Ty_Prod A B)

  | T_Fst : forall Gamma t A B,
      typeability Gamma t (Ty_Prod A B) ->
      typeability Gamma (tm_fst t) A

  | T_Snd : forall Gamma t A B,
      typeability Gamma t (Ty_Prod A B) ->
      typeability Gamma (tm_snd t) B


  | T_Inl : forall Gamma t A B,
      typeability Gamma t A ->
      typeability Gamma (tm_inl B t) (Ty_Sum A B)

  | T_Inr : forall Gamma t A B,
      typeability Gamma t B ->
      typeability Gamma (tm_inr A t) (Ty_Sum A B)

  | T_Case : forall Gamma t t1 t2 A B C,
      typeability Gamma t (Ty_Sum A B) ->
      typeability (A :: Gamma) t1 C ->
      typeability (B :: Gamma) t2 C ->
      typeability Gamma (tm_case t t1 t2) C

  
  | T_Absurd : forall Gamma t A,
      typeability Gamma t Ty_Void ->
      typeability Gamma (tm_absurd A t) A.


Notation "Gamma '⊢' t '[:]' A" := (typeability Gamma t A) (at level 70, no associativity) : stlc_scope_sum.
Notation "'⊢' t '[:]' A" := (typeability nil t A) (at level 70, no associativity) : stlc_scope_sum.

Notation "A ⊃ B" := (Ty_Arrow A B) (at level 70, right associativity) : stlc_scope_sum.
Notation "A ⊕ B" := (Ty_Sum A B) (at level 50, left associativity) : stlc_scope_sum.
Notation "∅" := (Ty_Void) (at level 0) : stlc_scope_sum.

Open Scope stlc_scope_sum.


Inductive derivation : context -> tm -> ty -> Set :=
  | D_Unit : forall Gamma, 
      derivation Gamma tm_unit Ty_Unit

  | D_Var0 : forall Gamma A, 
      derivation (A :: Gamma) (tm_var 0) A

  | D_VarS : forall Gamma A B i, 
      derivation Gamma (tm_var i) A -> 
      derivation (B :: Gamma) (tm_var (S i)) A

  | D_Lam : forall Gamma t A B, 
      derivation (A :: Gamma) t B -> 
      derivation Gamma (tm_lam A t) (Ty_Arrow A B)

  | D_App : forall Gamma t1 t2 A B, 
      derivation Gamma t1 (Ty_Arrow A B) -> 
      derivation Gamma t2 A -> 
      derivation Gamma (tm_app t1 t2) B

  | D_Pair : forall Gamma t1 t2 A B,
      derivation Gamma t1 A -> 
      derivation Gamma t2 B -> 
      derivation Gamma (tm_pair t1 t2) (Ty_Prod A B)

  | D_Fst : forall Gamma t A B, 
      derivation Gamma t (Ty_Prod A B) -> 
      derivation Gamma (tm_fst t) A

  | D_Snd : forall Gamma t A B, 
      derivation Gamma t (Ty_Prod A B) -> 
      derivation Gamma (tm_snd t) B


  | D_Inl : forall Gamma t A B,
      derivation Gamma t A ->
      derivation Gamma (tm_inl B t) (Ty_Sum A B)

  | D_Inr : forall Gamma t A B,
      derivation Gamma t B ->
      derivation Gamma (tm_inr A t) (Ty_Sum A B)

  | D_Case : forall Gamma t t1 t2 A B C,
      derivation Gamma t (Ty_Sum A B) ->
      derivation (A :: Gamma) t1 C ->
      derivation (B :: Gamma) t2 C ->
      derivation Gamma (tm_case t t1 t2) C


  | D_Absurd : forall Gamma t A,
      derivation Gamma t Ty_Void ->
      derivation Gamma (tm_absurd A t) A.

(** Forgets a derivation tree to Prop-valued typeability. *)
Fixpoint forget_derivation {Gamma t A} (d : derivation Gamma t A) : typeability Gamma t A.
Proof.
  induction d.
  - apply T_Unit.
  - apply T_Var0.
  - apply T_VarS; assumption.
  - apply T_Lam; assumption.
  - eapply T_App; eassumption.
  - apply T_Pair; assumption.
  - eapply T_Fst; eassumption.
  - eapply T_Snd; eassumption.
  - apply T_Inl; assumption.
  - apply T_Inr; assumption.
  - eapply T_Case; eassumption.
  - apply T_Absurd; assumption.
Defined.


Inductive tm_equiv_rel : tm -> tm -> Prop :=
  | PI_rule : forall Gamma A t s,
      (Gamma ⊢ t [:] A) -> (Gamma ⊢ s [:] A) -> tm_equiv_rel t s.

Definition obj_stlc := ty.

Definition hom_stlc (x y : obj_stlc) := { t : tm | ⊢ t [:] (x ⊃ y)}.

Definition hom_equiv_stlc {x y : obj_stlc} (f g : hom_stlc x y) :=
  tm_equiv_rel (proj1_sig f) (proj1_sig g).

Lemma hom_equiv_stlc_refl : forall {x y} (f : hom_stlc x y), hom_equiv_stlc f f.
Proof.
  intros x y f. destruct f as [t H].
  unfold hom_equiv_stlc; simpl.
  apply (PI_rule nil (x ⊃ y)). all: exact H.
Defined.

Lemma hom_equiv_stlc_sym : forall {x y} (f g : hom_stlc x y), hom_equiv_stlc f g -> hom_equiv_stlc g f.
Proof.
  intros x y f g H.
  destruct f as [t_f Hf].
  destruct g as [t_g Hg].
  unfold hom_equiv_stlc; simpl.
  apply (PI_rule nil (x ⊃ y)).
  - exact Hg.
  - exact Hf.
Qed.

Lemma hom_equiv_stlc_trans : forall {x y} (f g h : hom_stlc x y), 
  hom_equiv_stlc f g -> hom_equiv_stlc g h -> hom_equiv_stlc f h.
Proof.
  intros x y f g h H1 H2.
  destruct f as [t_f Hf]. 
  destruct h as [t_h Hh].
  unfold hom_equiv_stlc; simpl.
  apply (PI_rule nil (x ⊃ y)).
  - exact Hf.
  - exact Hh.
Qed.

Lemma generic_axiom_proof : forall {x y} (f g : hom_stlc x y), hom_equiv_stlc f g.
Proof.
  intros x y f g.
  unfold hom_equiv_stlc.
  apply (PI_rule nil (x ⊃ y)).
  - exact (proj2_sig f).
  - exact (proj2_sig g).
Defined.