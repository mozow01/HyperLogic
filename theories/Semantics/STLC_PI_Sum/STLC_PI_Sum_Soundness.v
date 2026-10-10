Require Import List. 
Import ListNotations.
Require Import Coq.Classes.Morphisms.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.

Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum.
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum_Lemmas.

Open Scope stlc_scope_sum. 

(** Categorical semantics for STLC with sums and void. *)

Class Model (C : SetoidCategory) := {
  interp_base : nat -> @obj C
}.

Fixpoint interp_ty (C : SetoidCategory) {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC}
                   (M : Model C) (A : ty) : @obj C :=
  match A with
  | Ty_Atomic n  => interp_base n
  | Ty_Unit      => terminal
  | Ty_Void      => initial
  | Ty_Prod A B  => prod (interp_ty C M A) (interp_ty C M B)
  | Ty_Arrow A B => exp (interp_ty C M B) (interp_ty C M A)
  | Ty_Sum A B   => coprod (interp_ty C M A) (interp_ty C M B)
  end.

Fixpoint interp_ctx (C : SetoidCategory) {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC}
                    (M : Model C) (Gamma : context) : @obj C :=
  match Gamma with
  | nil       => terminal
  | A :: Gamma' => prod (interp_ctx C M Gamma') (interp_ty C M A)
  end.

(** Explicit interpretation of Set-valued derivation trees. *)

(* Currying swaps [Gamma x A] to [A x Gamma] using [prod_map]. *)
Definition swap_map {C : SetoidCategory} {Ct : CartesianCategory C} 
  {x y : @obj C} : hom (prod x y) (prod y x) :=
  prod_map prod_snd prod_fst.

Fixpoint interp_derivation {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC}
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

  
  | D_Inl _ _ _ _ D_t => 
      compose coprod_inl (interp_derivation D_t)
      
  | D_Inr _ _ _ _ D_t => 
      compose coprod_inr (interp_derivation D_t)

  | D_Case Gamma0 _ _ _ A0 B t3 D_t D_l D_r => 
      compose eval 
        (prod_map 
           (compose 
              (coprod_map 
                 (exp_map (compose (interp_derivation D_l) swap_map)) 
                 (exp_map (compose (interp_derivation D_r) swap_map)))
              (interp_derivation D_t)) 
           (id _))

  | D_Absurd _ _ _ D_t =>
      compose initial_map (interp_derivation D_t)

  end.

Definition interp_term_ver {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC}
                           {M : Model C} (t : tm) {Gamma : context} {A : ty} (d : derivation Gamma t A) 
                           : hom (interp_ctx C M Gamma) (interp_ty C M A) :=
  interp_derivation d.


Theorem Soundness_explicit : forall (C : SetoidCategory) (Ct : CartesianCategory C) (CC : CartesianClosedCategory C) (BCC : BiCartesianClosedCategory CC)
                                    (M : Model C) (Gamma : context) (A : ty) (t : tm)
                                    (D : derivation Gamma t A),
  hom (interp_ctx C M Gamma) (interp_ty C M A).
Proof.
  intros. exact (interp_derivation D).
Defined.

Theorem Soundness : forall (Gamma : context) (A : ty),
  (exists (t : tm) (d : derivation Gamma t A), True) -> 
  (forall (C : SetoidCategory) (Ct : CartesianCategory C) (CC : CartesianClosedCategory C) (BCC : BiCartesianClosedCategory CC) (M : Model C),
      inhabited (hom (interp_ctx C M Gamma) (interp_ty C M A))).
Proof.
  intros Gamma A [t [d _]] C Ct CC BCC M.
  apply inhabits.
  apply (interp_derivation d).
Defined.

(** Equational soundness and interpretation relations. *)

Theorem soundness_equiv {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC}
                        {M : Model C} {HThin : Thin C}
                        {Gamma : context} {A : ty} {t1 t2 : tm}
                        (d1 : derivation Gamma t1 A)
                        (d2 : derivation Gamma t2 A)
                        (Heq : tm_equiv_rel t1 t2) : 
  interp_derivation d1 ≅ interp_derivation d2.
Proof.
  apply thin_unique.
Defined.

Definition interprets_to {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC}
                         {M : Model C} 
                         (Gamma : context) (A : ty) (t : tm) 
                         (f : hom (interp_ctx C M Gamma) (interp_ty C M A)) : Prop :=
  exists (d : derivation Gamma t A), interp_derivation d ≅ f.

Theorem soundness_terms_equiv {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC}
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
  apply (soundness_equiv d1 d2).
  exact Heq.
Defined.

(** Inhabitational interpretation of Prop-valued typeability. *)

Lemma Soundness_implicit_aux (C : SetoidCategory) (Ct : CartesianCategory C) (CC : CartesianClosedCategory C) (BCC : BiCartesianClosedCategory CC) (M : Model C) :
  forall (Gamma : context) (t : tm) (A : ty),
    (Gamma ⊢ t [:] A) -> inhabited (hom (interp_ctx C M Gamma) (interp_ty C M A)).
Proof.
  intros Gamma t A H.
  induction H.
  
  - apply inhabits; simpl. exact terminal_map.
  - apply inhabits; simpl. exact prod_snd.
  - destruct IHtypeability as [IH]. apply inhabits; simpl. exact (compose IH prod_fst).
  - destruct IHtypeability as [IH]. apply inhabits; simpl. exact (exp_map IH).
  - destruct IHtypeability1 as [Fun]. destruct IHtypeability2 as [Arg]. 
    apply inhabits; simpl. exact (compose eval (prod_map Fun Arg)).
  - destruct IHtypeability1 as [Hfst]. destruct IHtypeability2 as [Hsnd].
    apply inhabits; simpl. exact (prod_map Hfst Hsnd).
  - destruct IHtypeability as [Hpair]. apply inhabits; simpl. exact (compose prod_fst Hpair).
  - destruct IHtypeability as [Hpair]. apply inhabits; simpl. exact (compose prod_snd Hpair).

  - destruct IHtypeability as [IH]. apply inhabits; simpl. exact (compose coprod_inl IH).
  - destruct IHtypeability as [IH]. apply inhabits; simpl. exact (compose coprod_inr IH).
  
  - destruct IHtypeability1 as [Hsum].
    destruct IHtypeability2 as [Hleft].
    destruct IHtypeability3 as [Hright].
    apply inhabits; simpl.
    assert (CurriedLeft : hom (interp_ty C M A) (exp (interp_ty C M C0) (interp_ctx C M Gamma))).
    { apply exp_map. apply (compose Hleft). apply swap_map. }
    assert (CurriedRight : hom (interp_ty C M B) (exp (interp_ty C M C0) (interp_ctx C M Gamma))).
    { apply exp_map. apply (compose Hright). apply swap_map. }

    assert (CaseMap : hom (interp_ty C M (Ty_Sum A B)) (exp (interp_ty C M C0) (interp_ctx C M Gamma))).
    { apply coprod_map; assumption. }

    exact (compose eval (prod_map (compose CaseMap Hsum) (id _))).

  - destruct IHtypeability as [Hvoid]. apply inhabits; simpl. exact (compose initial_map Hvoid).
Defined.

Theorem Soundness_implicit : forall (Gamma : context) (A : ty),
  (exists t, (Gamma ⊢ t [:] A)) ->
  (forall (C : SetoidCategory) (Ct : CartesianCategory C) (CC : CartesianClosedCategory C) (BCC : BiCartesianClosedCategory CC) (M : Model C),
     inhabited (hom (interp_ctx C M Gamma) (interp_ty C M A))).
Proof.
  intros Gamma A [t H_type] C Ct CC BCC M.
  apply Soundness_implicit_aux with (t := t).
  exact H_type.
Defined.