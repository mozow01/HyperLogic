Require Import List.
Import ListNotations.
Require Import Coq.Classes.Morphisms.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.

Require Import HyperLogic.Logic.STLC_PI.STLC_PI_Sum.
Require Import HyperLogic.Logic.STLC_PI.STLC_PI_Sum_Lemmas.

Open Scope stlc_scope_sum. 

(* ================================================================= *)
(* 1. MODEL & TYPE INTERPRETATION                                    *)
(* ================================================================= *)

Class Model (C : SetoidCategory) := {
  interp_base : nat -> @obj C
}.

(* Interpretation of Types: [[ A ]]
   Adds Coproduct (Sum) and Initial (Void)
*)
Fixpoint interp_ty (C : SetoidCategory) (CC : CartesianClosedCategory C) (BCC : BiCartesianClosedCategory CC)
                   (M : Model C) (A : ty) : @obj C :=
  match A with
  | Ty_Atomic n  => interp_base n
  | Ty_Unit      => terminal
  | Ty_Void      => initial
  | Ty_Prod A B  => prod (interp_ty C CC BCC M A) (interp_ty C CC BCC M B)
  | Ty_Arrow A B => exp (interp_ty C CC BCC M B) (interp_ty C CC BCC M A)
  | Ty_Sum A B   => coprod (interp_ty C CC BCC M A) (interp_ty C CC BCC M B)
  end.

(* Interpretation of Contexts: [[ Gamma ]] *)
Fixpoint interp_ctx (C : SetoidCategory) (CC : CartesianClosedCategory C) (BCC : BiCartesianClosedCategory CC)
                    (M : Model C) (Gamma : context) : @obj C :=
  match Gamma with
  | nil         => terminal
  | A :: Gamma' => prod (interp_ctx C CC BCC M Gamma') (interp_ty C CC BCC M A)
  end.

(* ================================================================= *)
(* 2. EXPLICIT SEMANTICS                                           *)
(* ================================================================= *)

(* Helper: Swap context for Currying 
   Converts (Gamma x A) -> (A x Gamma) so we can Curry to (A -> C^Gamma)
   swap = <snd, fst>
*)
Definition swap_map {C : SetoidCategory} {CC : CartesianClosedCategory C} 
  {x y : @obj C} : hom (prod x y) (prod y x) :=
  prod_map prod_snd prod_fst.


Fixpoint interp_derivation {C : SetoidCategory} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC}
                           {M : Model C} 
                           {Gamma : context} {t : tm} {A : ty} 
                           (D : derivation Gamma t A) 
                           : hom (interp_ctx C CC BCC M Gamma) (interp_ty C CC BCC M A) :=
  match D in (derivation G t0 A0) return (hom (interp_ctx C CC BCC M G) (interp_ty C CC BCC M A0)) with
  
  (* --- Standard STLC --- *)
  | D_Unit _               => terminal_map
  | D_Var0 _ _             => prod_snd
  | D_VarS _ _ _ _ D_prev  => compose (interp_derivation D_prev) prod_fst
  | D_Lam _ _ _ _ D_body   => exp_map (interp_derivation D_body)
  | D_App _ _ _ _ _ D_f D_x => compose eval (prod_map (interp_derivation D_f) (interp_derivation D_x))
  | D_Pair _ _ _ _ _ D_l D_r => prod_map (interp_derivation D_l) (interp_derivation D_r)
  | D_Fst _ _ _ _ D_pair   => compose prod_fst (interp_derivation D_pair)
  | D_Snd _ _ _ _ D_pair   => compose prod_snd (interp_derivation D_pair)

  (* --- BiSTLC Extensions --- *)
  
  (* [[ inl t ]] = inl o [[ t ]] *)
  | D_Inl _ _ _ _ D_t => 
      compose coprod_inl (interp_derivation D_t)
      
  (* [[ inr t ]] = inr o [[ t ]] *)
  | D_Inr _ _ _ _ D_t => 
      compose coprod_inr (interp_derivation D_t)

  (* [[ case t of x.t1 | y.t2 ]]
     Strategy: Use Exponentials to distribute context.
     t1 : Gamma x A -> C  ==>  f1 : A -> C^Gamma
     t2 : Gamma x B -> C  ==>  f2 : B -> C^Gamma
     case : A + B -> C^Gamma
     final : Gamma -> C
  *)
  | D_Case Gamma0 _ _ _ A0 B t3 D_t D_l D_r => 
      let f1 := interp_derivation D_l in (* Gamma0 x A0 -> C *)
      let f2 := interp_derivation D_r in (* Gamma0 x B -> C *)
      let f_sum := interp_derivation D_t in (* Gamma0 -> A0 + B *)
      
      (* Define types locally to make explicit application cleaner *)
      let ty_G := interp_ctx C CC BCC M Gamma0 in
      let ty_A := interp_ty C CC BCC M A0 in
      let ty_B := interp_ty C CC BCC M B in
      let ty_C := interp_ty C CC BCC M t3 in (* The result type *)

      (* 1. Instantiate swap maps with explicit types *)
      (* sw_l : ty_A x ty_G -> ty_G x ty_A *)
      let sw_l := @swap_map C CC ty_A ty_G in
      let sw_r := @swap_map C CC ty_B ty_G in

      (* 2. Curry the branches with explicit compose and curry *)
      
      (* Left Branch: (A x G -> C) *)
      (* We use @compose to explicitly state: X->Y->Z *)
      (* X = ty_A x ty_G *)
      (* Y = ty_G x ty_A *)
      (* Z = ty_C *)
      let f1_swapped := @compose C (prod ty_A ty_G) (prod ty_G ty_A) ty_C f1 sw_l in
      
      (* Curry Left: A -> C^G *)
      (* Use @exp_map C CC [Context] [Domain] [Codomain] *)
      let curried_l := @exp_map C CC ty_A ty_G ty_C f1_swapped in 
      
      (* Right Branch: B x G -> C  ==>  B -> C^G *)
      let f2_swapped := @compose C (prod ty_B ty_G) (prod ty_G ty_B) ty_C f2 sw_r in
      (* Use @exp_map C CC [Context] [Domain] [Codomain] *)
      let curried_r := @exp_map C CC ty_B ty_G ty_C f2_swapped in 
      
      (* 3. Combine via coproduct map: A + B -> C^G *)
      let case_fn := coprod_map curried_l curried_r in 
      
      (* 4. Compose with subject term to get G -> C^G *)
      let applied := compose case_fn f_sum in
      
      (* 5. Evaluate: eval o <applied, id> : G -> C *)
      compose eval (prod_map applied (id _))

  (* [[ absurd t ]] = initial_map o [[ t ]] *)
  | D_Absurd _ _ _ D_t =>
      compose initial_map (interp_derivation D_t)

  end.

Definition interp_term_ver {C : SetoidCategory} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC}
                           {M : Model C} (t : tm) {Gamma : context} {A : ty} (d : derivation Gamma t A) 
                           : hom (interp_ctx C CC BCC M Gamma) (interp_ty C CC BCC M A) :=
  interp_derivation d.

(* ================================================================= *)
(* 3. THEOREMS                                                     *)
(* ================================================================= *)

Theorem Soundness_explicit : forall (C : SetoidCategory) (CC : CartesianClosedCategory C) (BCC : BiCartesianClosedCategory CC)
                                    (M : Model C) (Gamma : context) (A : ty) (t : tm)
                                    (D : derivation Gamma t A),
  hom (interp_ctx C CC BCC M Gamma) (interp_ty C CC BCC M A).
Proof.
  intros. exact (interp_derivation D).
Defined.

Theorem Soundness : forall (Gamma : context) (A : ty),
  (exists (t : tm) (d : derivation Gamma t A), True) -> 
  (forall (C : SetoidCategory) (CC : CartesianClosedCategory C) (BCC : BiCartesianClosedCategory CC) (M : Model C),
      inhabited (hom (interp_ctx C CC BCC M Gamma) (interp_ty C CC BCC M A))).
Proof.
  intros Gamma A [t [d _]] C CC BCC M.
  apply inhabits.
  apply (interp_derivation d).
Defined.

(* Coherence holds simply because the category is Thin *)
Theorem coherence_theorem {C : SetoidCategory} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC}
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

Definition interprets_to {C : SetoidCategory} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC}
                         {M : Model C} 
                         (Gamma : context) (A : ty) (t : tm) 
                         (f : hom (interp_ctx C CC BCC M Gamma) (interp_ty C CC BCC M A)) : Prop :=
  exists (d : derivation Gamma t A), interp_derivation d ≅ f.

Theorem soundness_terms_equiv {C : SetoidCategory} {CC : CartesianClosedCategory C} {BCC : BiCartesianClosedCategory CC}
                              {M : Model C} {HThin : Thin C}
                              (Gamma : context) (A : ty) 
                              (t1 t2 : tm) 
                              (f g : hom (interp_ctx C CC BCC M Gamma) (interp_ty C CC BCC M A)) :
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
(* 4. IMPLICIT SEMANTICS                                           *)
(* ================================================================= *)

Lemma Soundness_implicit_aux (C : SetoidCategory) (CC : CartesianClosedCategory C) (BCC : BiCartesianClosedCategory CC) (M : Model C) :
  forall (Gamma : context) (t : tm) (A : ty),
    (Gamma ⊢ t [:] A) -> inhabited (hom (interp_ctx C CC BCC M Gamma) (interp_ty C CC BCC M A)).
Proof.
  intros Gamma t A H.
  induction H.
  
  (* Standard STLC Cases *)
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

  (* --- BiSTLC Cases --- *)

  (* T_Inl *)
  - destruct IHtypeability as [IH].
    apply inhabits; simpl.
    exact (compose coprod_inl IH).

  (* T_Inr *)
  - destruct IHtypeability as [IH].
    apply inhabits; simpl.
    exact (compose coprod_inr IH).

  (* T_Case *)
  - destruct IHtypeability1 as [Hsum].
    destruct IHtypeability2 as [Hleft].
    destruct IHtypeability3 as [Hright].
    apply inhabits; simpl.

    (* 1. Define types explicitly for clarity *)
    pose (ty_G := interp_ctx C CC BCC M Gamma).
    pose (ty_A := interp_ty C CC BCC M A).
    pose (ty_B := interp_ty C CC BCC M B).
    pose (ty_C := interp_ty C CC BCC M C0). (* C0 is the result type from your error msg *)

    (* 2. Instantiate swap maps: ty_A x ty_G -> ty_G x ty_A *)
    pose (sw_l := @swap_map C CC ty_A ty_G).
    pose (sw_r := @swap_map C CC ty_B ty_G).

    (* 3. Curry Left Branch: A x G -> C  ==>  A -> C^G *)
    (* Hleft : G x A -> C.   sw_l : A x G -> G x A. *)
    pose (f1_swapped := @compose C (prod ty_A ty_G) (prod ty_G ty_A) ty_C Hleft sw_l).
    pose (curried_l := @exp_map C CC ty_A ty_G ty_C f1_swapped).

    (* 4. Curry Right Branch: B x G -> C  ==>  B -> C^G *)
    pose (f2_swapped := @compose C (prod ty_B ty_G) (prod ty_G ty_B) ty_C Hright sw_r).
    pose (curried_r := @exp_map C CC ty_B ty_G ty_C f2_swapped).

    (* 5. Combine and Evaluate *)
    pose (case_fn := coprod_map curried_l curried_r).
    pose (applied := compose case_fn Hsum).
    
    (* Result: G -> C *)
    exact (compose eval (prod_map applied (id _))).
  (* T_Absurd *)
  - destruct IHtypeability as [Hvoid].
    apply inhabits; simpl.
    exact (compose initial_map Hvoid).
Defined.

Theorem Soundness_implicit : forall (Gamma : context) (A : ty),
  (exists t, (Gamma ⊢ t [:] A)) ->
  (forall (C : SetoidCategory) (CC : CartesianClosedCategory C) (BCC : BiCartesianClosedCategory CC) (M : Model C),
     inhabited (hom (interp_ctx C CC BCC M Gamma) (interp_ty C CC BCC M A))).
Proof.
  assert (S : (forall (C : SetoidCategory) (CC : CartesianClosedCategory C) (BCC : BiCartesianClosedCategory CC) (M : Model C) 
                      (Gamma : context) (A : ty),
                (exists t, (Gamma ⊢ t [:] A)) ->
                inhabited (hom (interp_ctx C CC BCC M Gamma) (interp_ty C CC BCC M A))) ->
              (forall (Gamma : context) (A : ty),
                (exists t, (Gamma ⊢ t [:] A)) ->
                (forall (C : SetoidCategory) (CC : CartesianClosedCategory C) (BCC : BiCartesianClosedCategory CC) (M : Model C),
                   inhabited (hom (interp_ctx C CC BCC M Gamma) (interp_ty C CC BCC M A))))).
  {
    intros H_impl Gamma A H_ex C CC BCC M.
    apply H_impl.
    exact H_ex.
  }
  apply S.
  intros C CC BCC M Gamma A [t H_type].
  apply Soundness_implicit_aux with (t := t).
  exact H_type.
Defined.