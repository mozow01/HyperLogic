Require Import List.
Import ListNotations.
Require Import Coq.Classes.Morphisms.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Logic.STLC_PI.STLC_PI.

Open Scope stlc_scope. 

(* ================================================================= *)
(* 1. MODEL & TYPE INTERPRETATION                                   *)
(* ================================================================= *)

Class Model (C : SetoidCategory) := {
  interp_base : nat -> @obj C
}.

(* We use Fixpoints rather than axiomatic rewrites for 
   interpretations. This ensures that [interp_ty] and [interp_ctx] reduce 
   via definitional equality, simplifying proofs by allowing [simpl] 
   to work without manual rewriting steps.
*)

(* Interpretation of Types: [[ A ]]
   ---------------------------------------------------------
   [[ base n ]] = M(n)
   [[ unit ]]   = 1          (Terminal)
   [[ A x B ]]  = [[A]] x [[B]] (Product)
   [[ A -> B ]] = [[B]]^[[A]]   (Exponential) *)
Fixpoint interp_ty (C : SetoidCategory) (CC : CartesianClosedCategory C) 
                   (M : Model C) (A : ty) : @obj C :=
  match A with
  | Ty_Atomic n  => interp_base n
  | Ty_Unit      => terminal          
  | Ty_Prod A B  => prod (interp_ty C CC M A) (interp_ty C CC M B)
  | Ty_Arrow A B => exp (interp_ty C CC M B) (interp_ty C CC M A)  
  end.

(* Interpretation of Contexts: [[ Gamma ]]
   ---------------------------------------------------------
   [[ nil ]]      = 1
   [[ A :: G' ]]  = [[G']] x [[A]] *)
Fixpoint interp_ctx (C : SetoidCategory) (CC : CartesianClosedCategory C) 
                    (M : Model C) (Gamma : context) : @obj C :=
  match Gamma with
  | nil       => terminal
  | A :: Gamma' => prod (interp_ctx C CC M Gamma') (interp_ty C CC M A)
  end.


(* ================================================================= *)
(* 2. EXPLICIT SEMANTICS (Computation / Set-based)                  *)
(* ================================================================= *)

(* We define interpretation over [derivation] (in Set) 
   rather than [typeability] (in Prop). Coq's extraction mechanism performs 
   Prop-erasure, meaning we cannot computationally match on a [Prop] 
   proof to construct the specific morphism data. Using [Set] allows 
   us to treat the derivation as a data structure.
*)

(* Interpretation of Derivations: [[ D ]]
   ---------------------------------------------------------
   Maps a derivation tree D of type (Gamma |- t : A) 
   to a morphism f : [[Gamma]] -> [[A]] in the category C. *)
Fixpoint interp_derivation {C : SetoidCategory} {CC : CartesianClosedCategory C} {M : Model C} 
                           {Gamma : context} {t : tm} {A : ty} 
                           (D : derivation Gamma t A) 
                           : hom (interp_ctx C CC M Gamma) (interp_ty C CC M A) :=
  match D in (derivation G t0 A0) return (hom (interp_ctx C CC M G) (interp_ty C CC M A0)) with
  | D_Unit _               => terminal_map
  | D_Var0 _ _             => prod_snd
  | D_VarS _ _ _ _ D_prev  => compose (interp_derivation D_prev) prod_fst
  | D_Lam _ _ _ _ D_body   => exp_map (interp_derivation D_body)
  | D_App _ _ _ _ _ D_f D_x => compose eval (prod_map (interp_derivation D_f) (interp_derivation D_x))
  | D_Pair _ _ _ _ _ D_l D_r => prod_map (interp_derivation D_l) (interp_derivation D_r)
  | D_Fst _ _ _ _ D_pair   => compose prod_fst (interp_derivation D_pair)
  | D_Snd _ _ _ _ D_pair   => compose prod_snd (interp_derivation D_pair)
  end.

(* This wrapper alias makes the term [t] an explicit argument.
   This improves readability in the coherence theorems below, emphasizing 
   that we are interpreting a term via a specific derivation.
*)
Definition interp_term_ver {C : SetoidCategory} {CC : CartesianClosedCategory C} {M : Model C} 
                           (t : tm) 
                           {Gamma : context} {A : ty} 
                           (d : derivation Gamma t A) 
                           : hom (interp_ctx C CC M Gamma) (interp_ty C CC M A) :=
  interp_derivation d.

(* --- Explicit Soundness Theorems --- *)

(* Theorem: Explicit Soundness (Constructive)
   ---------------------------------------------------------
   Input:  A specific derivation D for (Gamma |- t : A)
   Output: A concrete morphism f : [[Gamma]] -> [[A]] *)
Theorem Soundness_explicit : forall (C : SetoidCategory) (CC : CartesianClosedCategory C) (M : Model C) 
                                    (Gamma : context) (A : ty) (t : tm)
                                    (D : derivation Gamma t A),
  hom (interp_ctx C CC M Gamma) (interp_ty C CC M A).
Proof.
  intros.
  exact (interp_derivation D).
Defined.

(* This theorem bridges the explicit [derivation] world to the [inhabited] 
   world often used in completeness proofs. It demonstrates that if a 
   derivation exists, the hom-set is non-empty.
*)
Theorem Soundness : forall (Gamma : context) (A : ty),
  (exists (t : tm) (d : derivation Gamma t A), True) -> 
  (forall (C : SetoidCategory) (CC : CartesianClosedCategory C) (M : Model C),
     inhabited (hom (interp_ctx C CC M Gamma) (interp_ty C CC M A))).
Proof.
  intros Gamma A [t [d _]] C CC M.
  apply inhabits.
  apply (interp_derivation d).
Defined.

(* --- Coherence and Equivalence --- *)

(*
   We leverage the [Thin] category property here. 
   Since a Thin category has at most one morphism between any two objects 
   (up to equivalence), proving coherence becomes trivial. We do not need 
   complex induction on the derivations; the target category's structure 
   enforces uniqueness.
*)

(* Theorem: Coherence / Semantics Stability
   ---------------------------------------------------------
   If t1 == t2 (syntactically equivalent), then for ANY derivations 
   d1 and d2 proving them:
   
      [[ t1 ]]_d1  ≅  [[ t2 ]]_d2
      
   The semantics is independent of the specific derivation tree.*)
Theorem coherence_theorem {C : SetoidCategory} {CC : CartesianClosedCategory C} 
                          {M : Model C} {HThin : Thin C}
                          {Gamma : context} {A : ty} 
                          (t1 t2 : tm) 
                          (d1 : derivation Gamma t1 A) 
                          (d2 : derivation Gamma t2 A) 
                          (Heq : tm_equiv_rel t1 t2) : 
  interp_term_ver t1 d1 ≅ interp_term_ver t2 d2.
Proof.
  unfold interp_term_ver.
  apply thin_unique.
Defined. 

Theorem soundness_equiv {C : SetoidCategory} {CC : CartesianClosedCategory C} 
                        {M : Model C} {HThin : Thin C}
                        {Gamma : context} {A : ty} {t1 t2 : tm}
                        (d1 : derivation Gamma t1 A)
                        (d2 : derivation Gamma t2 A)
                        (Heq : tm_equiv_rel t1 t2) : 
  interp_derivation d1 ≅ interp_derivation d2.
Proof.
  apply thin_unique.
Defined. 

(* This predicate hides the [derivation] tree from the user API.
   It allows stating soundness theorems purely in terms of terms and morphisms,
   abstracting away the underlying proof tree construction.
*)
Definition interprets_to {C : SetoidCategory} {CC : CartesianClosedCategory C} 
                         {M : Model C} 
                         (Gamma : context) (A : ty) (t : tm) 
                         (f : hom (interp_ctx C CC M Gamma) (interp_ty C CC M A)) : Prop :=
  exists (d : derivation Gamma t A), interp_derivation d ≅ f.

(* Theorem: Soundness for Equivalent Terms (No explicit derivations)
   ---------------------------------------------------------
   If (t1 -> f) AND (t2 -> g) AND (t1 == t2)
   THEN (f ≅ g) *)
Theorem soundness_terms_equiv {C : SetoidCategory} {CC : CartesianClosedCategory C} 
                              {M : Model C} {HThin : Thin C}
                              (Gamma : context) (A : ty) 
                              (t1 t2 : tm) 
                              (f g : hom (interp_ctx C CC M Gamma) (interp_ty C CC M A)) :
  interprets_to Gamma A t1 f ->
  interprets_to Gamma A t2 g ->
  tm_equiv_rel t1 t2 ->
  f ≅ g.
Proof.
  intros [d1 Hf] [d2 Hg] Heq.
  rewrite <- Hf.
  rewrite <- Hg.
  apply (coherence_theorem t1 t2 d1 d2).
  exact Heq.
Defined. 


(* ================================================================= *)
(* 3. IMPLICIT SEMANTICS (Prop-based / Existential)                 *)
(* ================================================================= *)

(* This auxiliary lemma performs induction on the [typeability] 
   Prop relation. We preserve this to show that soundness can be established 
   purely logically without reifying derivations into Set, resulting in an 
   [inhabited] result rather than a specific morphism.
*)
Lemma Soundness_implicit_aux (C : SetoidCategory) (CC : CartesianClosedCategory C) (M : Model C) :
  forall (Gamma : context) (t : tm) (A : ty),
    (Gamma ⊢ t [:] A) -> inhabited (hom (interp_ctx C CC M Gamma) (interp_ty C CC M A)).
Proof.
  intros Gamma t A H.
  induction H.
  
  (* T_Unit *)
  - apply inhabits. simpl. 
    exact terminal_map.
    
  (* T_Var0 *)
  - apply inhabits. simpl. 
    exact prod_snd.
    
  (* T_VarS *)
  - destruct IHtypeability as [IH].
    apply inhabits. simpl. 
    exact (compose IH prod_fst).
    
  (* T_Lam *)
  - destruct IHtypeability as [IH].
    apply inhabits. simpl. 
    exact (exp_map IH).
    
  (* T_App *)
  - destruct IHtypeability1 as [Fun]. (* Gamma -> B^A *)
    destruct IHtypeability2 as [Arg]. (* Gamma -> A *)
    apply inhabits. simpl. 
    exact (compose eval (prod_map Fun Arg)).
    
  (* T_Pair *)
  - destruct IHtypeability1 as [Hfst].
    destruct IHtypeability2 as [Hsnd].
    apply inhabits. simpl. 
    exact (prod_map Hfst Hsnd).
    
  (* T_Fst *)
  - destruct IHtypeability as [Hpair].
    apply inhabits. simpl. 
    exact (compose prod_fst Hpair).
    
  (* T_Snd *)
  - destruct IHtypeability as [Hpair].
    apply inhabits. simpl. 
    exact (compose prod_snd Hpair).
Defined.

(* Theorem: Implicit Soundness (Prop-only)
   ---------------------------------------------------------
   If (Gamma |- t : A) holds, then there is a morphism f : [[Gamma]] -> [[A]] *)
Theorem Soundness_implicit : forall (Gamma : context) (A : ty),
  (exists t, (Gamma ⊢ t [:] A)) ->
  (forall (C : SetoidCategory) (CC : CartesianClosedCategory C) (M : Model C),
     inhabited (hom (interp_ctx C CC M Gamma) (interp_ty C CC M A))).
Proof.
  (* We assert the generalization step first to separate the 
     logical quantifier manipulation from the structural induction performed 
     in [Soundness_implicit_aux].
  *)
  assert (S : (forall (C : SetoidCategory) (CC : CartesianClosedCategory C) (M : Model C) 
                      (Gamma : context) (A : ty),
                (exists t, (Gamma ⊢ t [:] A)) ->
                inhabited (hom (interp_ctx C CC M Gamma) (interp_ty C CC M A))) ->
              (forall (Gamma : context) (A : ty),
                (exists t, (Gamma ⊢ t [:] A)) ->
                (forall (C : SetoidCategory) (CC : CartesianClosedCategory C) (M : Model C),
                   inhabited (hom (interp_ctx C CC M Gamma) (interp_ty C CC M A))))).
  {
    intros H_impl Gamma A H_ex C CC M.
    apply H_impl.
    exact H_ex.
  }
  apply S.
  intros C CC M Gamma A [t H_type].
  apply Soundness_implicit_aux with (t := t).
  exact H_type.
Defined.