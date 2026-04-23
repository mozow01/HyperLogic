Require Import List.
Import ListNotations.
Require Import Coq.Classes.Morphisms.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.   (* ÚJ: Alap kategória *)
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.

Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum.
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum_Lemmas.

Open Scope stlc_scope_sum.

(* ================================================================= *)
(* 1. MODEL & TYPE INTERPRETATION                                    *)
(* ================================================================= *)

Class Model (C : SetoidCategory) := {
  interp_base : nat -> @obj C
}.

(* Interpretation of Types: [[ A ]] *)
(* VÁLTOZÁS: Ct, CC, BCC implicitek lettek {} *)
Fixpoint interp_ty (C : SetoidCategory) {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC}
                   (M : Model C) (A : ty) : @obj C :=
  match A with
  | Ty_Atomic n  => interp_base n
  | Ty_Unit      => terminal
  | Ty_Void      => initial
  (* Itt már nem kell átadni a kategória instance-okat explicit módon *)
  | Ty_Prod A B  => prod (interp_ty C M A) (interp_ty C M B)
  | Ty_Arrow A B => exp (interp_ty C M B) (interp_ty C M A)
  | Ty_Sum A B   => coprod (interp_ty C M A) (interp_ty C M B)
  end.

(* Interpretation of Contexts: [[ Gamma ]] *)
Fixpoint interp_ctx (C : SetoidCategory) {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC}
                    (M : Model C) (Gamma : context) : @obj C :=
  match Gamma with
  | nil       => terminal
  | A :: Gamma' => prod (interp_ctx C M Gamma') (interp_ty C M A)
  end.

(* ================================================================= *)
(* 2. EXPLICIT SEMANTICS                                             *)
(* ================================================================= *)

(* Helper: Swap context for Currying
   <snd, fst> : Gamma x A -> A x Gamma
   Ez most a Ct-ből jön (prod_map)
*)
Definition swap_map {C : SetoidCategory} {Ct : CartesianCategory C}
  {x y : @obj C} : hom (prod x y) (prod y x) :=
  prod_map prod_snd prod_fst.

Fixpoint interp_derivation {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC}
                           {M : Model C}
                           {Gamma : context} {t : tm} {A : ty}
                           (D : derivation Gamma t A)
                           : hom (interp_ctx C M Gamma) (interp_ty C M A) :=
  match D in (derivation G t0 A0) return (hom (interp_ctx C M G) (interp_ty C M A0)) with

  (* --- Standard STLC (Uses Ct & CC) --- *)
  | D_Unit _               => terminal_map
  | D_Var0 _ _             => prod_snd
  | D_VarS _ _ _ _ D_prev  => compose (interp_derivation D_prev) prod_fst
  | D_Lam _ _ _ _ D_body   => exp_map (interp_derivation D_body)
  | D_App _ _ _ _ _ D_f D_x => compose eval (prod_map (interp_derivation D_f) (interp_derivation D_x))
  | D_Pair _ _ _ _ _ D_l D_r => prod_map (interp_derivation D_l) (interp_derivation D_r)
  | D_Fst _ _ _ _ D_pair   => compose prod_fst (interp_derivation D_pair)
  | D_Snd _ _ _ _ D_pair   => compose prod_snd (interp_derivation D_pair)

  (* --- BiSTLC Extensions (Uses BCC) --- *)

  (* [[ inl t ]] = inl o [[ t ]] *)
  | D_Inl _ _ _ _ D_t =>
      compose coprod_inl (interp_derivation D_t)

  (* [[ inr t ]] = inr o [[ t ]] *)
  | D_Inr _ _ _ _ D_t =>
      compose coprod_inr (interp_derivation D_t)

  (* [[ case t of x.t1 | y.t2 ]] *)
  | D_Case Gamma0 _ _ _ A0 B t3 D_t D_l D_r =>
      compose eval
        (prod_map
           (compose
              (coprod_map
                 (exp_map (compose (interp_derivation D_l) swap_map))
                 (exp_map (compose (interp_derivation D_r) swap_map)))
              (interp_derivation D_t))
           (id _))

  (* [[ absurd t ]] = initial_map o [[ t ]] *)
  | D_Absurd _ _ _ D_t =>
      compose initial_map (interp_derivation D_t)

  end.

Definition interp_term_ver {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC}
                           {M : Model C} (t : tm) {Gamma : context} {A : ty} (d : derivation Gamma t A)
                           : hom (interp_ctx C M Gamma) (interp_ty C M A) :=
  interp_derivation d.

(* ================================================================= *)
(* 3. THEOREMS                                                       *)
(* ================================================================= *)

Theorem Soundness_explicit : forall (C : SetoidCategory) (Ct : CartesianCategory C) (CC : CartesianClosedCategory C) (BCC : BiCartesianClosedCategory CC)
                                    (M : Model C) (Gamma : context) (A : ty) (t : tm)
                                    (D : derivation Gamma t A),
  hom (interp_ctx C M Gamma) (interp_ty C M A).
Proof. Admitted.

Theorem Soundness : forall (Gamma : context) (A : ty),
  (exists (t : tm) (d : derivation Gamma t A), True) ->
  (forall (C : SetoidCategory) (Ct : CartesianCategory C) (CC : CartesianClosedCategory C) (BCC : BiCartesianClosedCategory CC) (M : Model C),
      inhabited (hom (interp_ctx C M Gamma) (interp_ty C M A))).
Proof. Admitted.

(* ================================================================= *)
(* KIEGÉSZÍTÉS: Soundness Equivalence & Interpretation Relations     *)
(* ================================================================= *)

Theorem soundness_equiv {C : SetoidCategory} {Ct : CartesianCategory C} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC}
                        {M : Model C} {HThin : Thin C}
                        {Gamma : context} {A : ty} {t1 t2 : tm}
                        (d1 : derivation Gamma t1 A)
                        (d2 : derivation Gamma t2 A)
                        (Heq : tm_equiv_rel t1 t2) :
  interp_derivation d1 ≅ interp_derivation d2.
Proof. Admitted.

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
Proof. Admitted.

(* ================================================================= *)
(* 4. IMPLICIT SEMANTICS                                             *)
(* ================================================================= *)

Lemma Soundness_implicit_aux (C : SetoidCategory) (Ct : CartesianCategory C) (CC : CartesianClosedCategory C) (BCC : BiCartesianClosedCategory CC) (M : Model C) :
  forall (Gamma : context) (t : tm) (A : ty),
    (Gamma ⊢ t [:] A) -> inhabited (hom (interp_ctx C M Gamma) (interp_ty C M A)).
Proof. Admitted.

Theorem Soundness_implicit : forall (Gamma : context) (A : ty),
  (exists t, (Gamma ⊢ t [:] A)) ->
  (forall (C : SetoidCategory) (Ct : CartesianCategory C) (CC : CartesianClosedCategory C) (BCC : BiCartesianClosedCategory CC) (M : Model C),
     inhabited (hom (interp_ctx C M Gamma) (interp_ty C M A))).
Proof. Admitted.