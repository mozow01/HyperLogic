Require Import List.
Import ListNotations.
Require Import Coq.Classes.Morphisms.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.   
Require Import HyperLogic.Cat.CCC.

Require Import HyperLogic.Logic.STLC_PI.STLC_PI.
Require Import HyperLogic.Logic.STLC_PI.STLC_PI_Lemmas.

Open Scope stlc_scope. 

(** Categorical semantics for STLC with products. *)

Class Model (C : SetoidCategory) := {
  interp_base : nat -> @obj C
}.

Fixpoint interp_ty (C : SetoidCategory) {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} 
                   (M : Model C) (A : ty) : @obj C :=
  match A with
  | Ty_Atomic n  => interp_base n
  | Ty_Unit      => terminal          
  | Ty_Prod A B  => prod (interp_ty C M A) (interp_ty C M B)
  | Ty_Arrow A B => exp (interp_ty C M B) (interp_ty C M A)  
  end.

Fixpoint interp_ctx (C : SetoidCategory) {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} 
                    (M : Model C) (Gamma : context) : @obj C :=
  match Gamma with
  | nil       => terminal
  | A :: Gamma' => prod (interp_ctx C M Gamma') (interp_ty C M A)
  end.

(** Explicit interpretation of Set-valued derivation trees. *)

Fixpoint interp_derivation {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} 
                           {M : Model C} 
                           {Gamma : context} {t : tm} {A : ty} 
                           (D : derivation Gamma t A) 
                           : hom (interp_ctx C M Gamma) (interp_ty C M A) :=
  match D in (derivation G t0 A0) return (hom (interp_ctx C M G) (interp_ty C M A0)) with
  | D_Unit _               => terminal_map
  | D_Var0 _ _             => prod_snd
  | D_VarS _ _ _ _ D_prev  => compose (interp_derivation D_prev) prod_fst
  | D_Lam _ _ _ _ D_body   => exp_map (interp_derivation D_body)
  | D_App _ _ _ _ _ D_f D_x => compose eval (prod_map (interp_derivation D_f) (interp_derivation D_x))
  | D_Pair _ _ _ _ _ D_l D_r => prod_map (interp_derivation D_l) (interp_derivation D_r)
  | D_Fst _ _ _ _ D_pair   => compose prod_fst (interp_derivation D_pair)
  | D_Snd _ _ _ _ D_pair   => compose prod_snd (interp_derivation D_pair)
  end.

Definition interp_term_ver {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} 
                           {M : Model C} (t : tm) 
                           {Gamma : context} {A : ty} 
                           (d : derivation Gamma t A) 
                           : hom (interp_ctx C M Gamma) (interp_ty C M A) :=
  interp_derivation d.


Theorem Soundness_explicit : forall (C : SetoidCategory) (Ct : CartesianCategory C) (CC : CartesianClosedCategory C) (M : Model C) 
                                    (Gamma : context) (A : ty) (t : tm)
                                    (D : derivation Gamma t A),
  hom (interp_ctx C M Gamma) (interp_ty C M A).
Proof.
  intros.
  exact (interp_derivation D).
Defined.

Theorem Soundness : forall (Gamma : context) (A : ty),
  (exists (t : tm) (d : derivation Gamma t A), True) -> 
  (forall (C : SetoidCategory) (Ct : CartesianCategory C) (CC : CartesianClosedCategory C) (M : Model C),
     inhabited (hom (interp_ctx C M Gamma) (interp_ty C M A))).
Proof.
  intros Gamma A [t [d _]] C Ct CC M.
  apply inhabits.
  apply (interp_derivation d).
Defined.


Theorem coherence_theorem {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} 
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

Theorem soundness_equiv {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} 
                        {M : Model C} {HThin : Thin C}
                        {Gamma : context} {A : ty} {t1 t2 : tm}
                        (d1 : derivation Gamma t1 A)
                        (d2 : derivation Gamma t2 A)
                        (Heq : tm_equiv_rel t1 t2) : 
  interp_derivation d1 ≅ interp_derivation d2.
Proof.
  apply thin_unique.
Defined. 

Definition interprets_to {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} 
                         {M : Model C} 
                         (Gamma : context) (A : ty) (t : tm) 
                         (f : hom (interp_ctx C M Gamma) (interp_ty C M A)) : Prop :=
  exists (d : derivation Gamma t A), interp_derivation d ≅ f.

Theorem soundness_terms_equiv {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} 
                              {M : Model C} {HThin : Thin C}
                              (Gamma : context) (A : ty) 
                              (t1 t2 : tm) 
                              (f g : hom (interp_ctx C M Gamma) (interp_ty C M A)) :
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


(** Inhabitational interpretation of Prop-valued typeability. *)

Lemma Soundness_implicit_aux (C : SetoidCategory) (Ct : CartesianCategory C) (CC : CartesianClosedCategory C) (M : Model C) :
  forall (Gamma : context) (t : tm) (A : ty),
  (Gamma ⊢ t [:] A) -> inhabited (hom (interp_ctx C M Gamma) (interp_ty C M A)).
Proof.
  intros Gamma t A H.
  induction H.
  
  - apply inhabits. simpl.
    exact terminal_map.
    
  - apply inhabits. simpl. 
    exact prod_snd.
  - destruct IHtypeability as [IH].
    apply inhabits. simpl. 
    exact (compose IH prod_fst).
  - destruct IHtypeability as [IH].
    apply inhabits. simpl. 
    exact (exp_map IH).
  - destruct IHtypeability1 as [Fun].
    destruct IHtypeability2 as [Arg].
    apply inhabits. simpl. 
    exact (compose eval (prod_map Fun Arg)).
  - destruct IHtypeability1 as [Hfst].
    destruct IHtypeability2 as [Hsnd].
    apply inhabits. simpl. 
    exact (prod_map Hfst Hsnd).
  - destruct IHtypeability as [Hpair].
    apply inhabits. simpl. 
    exact (compose prod_fst Hpair).
  - destruct IHtypeability as [Hpair].
    apply inhabits. simpl. 
    exact (compose prod_snd Hpair).
Defined.

Theorem Soundness_implicit : forall (Gamma : context) (A : ty),
  (exists t, (Gamma ⊢ t [:] A)) ->
  (forall (C : SetoidCategory) (Ct : CartesianCategory C) (CC : CartesianClosedCategory C) (M : Model C),
     inhabited (hom (interp_ctx C M Gamma) (interp_ty C M A))).
Proof.
  assert (S : (forall (C : SetoidCategory) (Ct : CartesianCategory C) (CC : CartesianClosedCategory C) (M : Model C) 
                      (Gamma : context) (A : ty),
                (exists t, (Gamma ⊢ t [:] A)) ->
                inhabited (hom (interp_ctx C M Gamma) (interp_ty C M A))) ->
              (forall (Gamma : context) (A : ty),
                (exists t, (Gamma ⊢ t [:] A)) ->
                (forall (C : SetoidCategory) (Ct : CartesianCategory C) (CC : CartesianClosedCategory C) (M : Model C),
                 inhabited (hom (interp_ctx C M Gamma) (interp_ty C M A))))).
  {
    intros H_impl Gamma A H_ex C Ct CC M.
    apply H_impl.
    exact H_ex.
  }
  apply S.
  intros C Ct CC M Gamma A [t H_type].
  apply Soundness_implicit_aux with (t := t).
  exact H_type.
Defined.