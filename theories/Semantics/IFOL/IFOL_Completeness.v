(** Standalone syntactic completeness model for iFOL. *)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Eqdep_dec.
Require Import List.
Import ListNotations.
 
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Fibration.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.

Require Import HyperLogic.Logic.Base.IFOL.Base_Syntax.
Require Import HyperLogic.Logic.Base.IFOL.Base_Syntax_Lemmas.
Require Import HyperLogic.Logic.Hyper.IFOL.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.IFOL.Hyper_Syntax_Lemmas.


Require Import HyperLogic.Semantics.IFOL.Base_IFOL_Completeness.
Require Import HyperLogic.Semantics.IFOL.IFOL_Fibration.


(** Fiber objects pair formulas with well-formedness derivations. *)
Definition wf_ty {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I : b_ty) := 
  { Phi : @h_ty Func Pred & WellFormed I Phi }.

(** Fiber arrows are closed implication derivations between the underlying formulas. *)
Class hom_fiber {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  {I : b_ty} (A B : wf_ty I) : Type := mk_hom_fiber {
  h_tm_of : @h_tm Func Pred;
  h_deriv_of : h_derivation I [] h_tm_of (Ty_Arrow (projT1 A) (projT1 B))
}.

Arguments hom_fiber {Func Pred _ _  I} A B.
Arguments mk_hom_fiber {Func Pred _ _  I A B} h_tm_of h_deriv_of.
Arguments h_tm_of {Func Pred _ _  I A B} _.
Arguments h_deriv_of {Func Pred _ _  I A B} _.

(* Proof terms are identified, making every fiber thin. *)
Definition fiber_equiv {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  {I : b_ty} {A B : wf_ty I} 
  (f g : hom_fiber A B) : Prop := True.

Global Instance fiber_equiv_equivalence
  {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}
   {I : b_ty} {A B : wf_ty I}
  : Equivalence (@fiber_equiv Func Pred _ _  I A B).
Proof. constructor; red; intros; unfold fiber_equiv; constructor. Defined.


Definition id_fiber {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I : b_ty) (A : wf_ty I) : hom_fiber A A.
Proof.
  refine (@mk_hom_fiber Func Pred _ _  I A A (tm_lam (projT1 A) (tm_var 0)) _).
  apply HD_Lam. 
  apply HD_Var0.
  
  apply AWF_Cons.
  - exact (projT2 A).
  - apply AWF_Nil.
Defined.

Definition comp_fiber {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I : b_ty) {A B C : wf_ty I} 
  (f : hom_fiber B C) (g : hom_fiber A B) : hom_fiber A C.
Proof.
  refine (@mk_hom_fiber Func Pred _ _  I A C 
    (tm_app (tm_app 
       (tm_lam (Ty_Arrow (projT1 B) (projT1 C)) 
         (tm_lam (Ty_Arrow (projT1 A) (projT1 B)) 
           (tm_lam (projT1 A) 
             (tm_app (tm_var 2) (tm_app (tm_var 1) (tm_var 0))))))
       (h_tm_of f)) 
    (h_tm_of g)) _).
  
  apply HD_App with (Phi := Ty_Arrow (projT1 A) (projT1 B)).
  - apply HD_App with (Phi := Ty_Arrow (projT1 B) (projT1 C)).
    +
      apply HD_Lam. apply HD_Lam. apply HD_Lam.
      apply HD_App with (Phi := projT1 B).
      
      *
        apply HD_VarS. 
        -- exact (projT2 A).
        -- apply HD_VarS.
           ++ apply WF_Arrow; [exact (projT2 A) | exact (projT2 B)].
           ++ apply HD_Var0.
              apply AWF_Cons.
              ** apply WF_Arrow; [exact (projT2 B) | exact (projT2 C)].
              ** apply AWF_Nil.
              
      *
        apply HD_App with (Phi := projT1 A).
        --
           apply HD_VarS.
           ++ exact (projT2 A).
           ++ apply HD_Var0.
              apply AWF_Cons.
              ** apply WF_Arrow; [exact (projT2 A) | exact (projT2 B)].
              ** apply AWF_Cons.
                 --- apply WF_Arrow; [exact (projT2 B) | exact (projT2 C)].
                 --- apply AWF_Nil.
                 
        --
           apply HD_Var0.
           apply AWF_Cons.
           ++ exact (projT2 A).
           ++ apply AWF_Cons.
              ** apply WF_Arrow; [exact (projT2 A) | exact (projT2 B)].
              ** apply AWF_Cons.
                 --- apply WF_Arrow; [exact (projT2 B) | exact (projT2 C)].
                 --- apply AWF_Nil.
                 
    +
      exact (h_deriv_of f).
  -
    exact (h_deriv_of g).
Defined.


Instance Fiber_SetoidCategory {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I : b_ty) : SetoidCategory.
Proof.
  refine (mk_SetoidCategory 
    (wf_ty I)
    (@hom_fiber Func Pred _ _  I) 
    (fun X => @id_fiber Func Pred _ _  I X)
    (fun X Y Z f g => @comp_fiber Func Pred _ _  I X Y Z f g)
    (fun X Y f g => @fiber_equiv Func Pred _ _  I X Y f g)
    _ _ _ _ _).
  
  Unshelve.
  all: intros; unfold fiber_equiv; constructor.
Defined.

Instance Fiber_Thin {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I : b_ty) : Thin (Fiber_SetoidCategory I).
Proof.
  intros x y f g. unfold fiber_equiv; constructor.
Defined.


Definition fiber_unit {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I : b_ty) : wf_ty I :=
  existT _ Ty_Unit (WF_Unit I).

Definition fiber_prod {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  {I : b_ty} (Y Z : wf_ty I) : wf_ty I :=
  existT _ (Ty_Prod (projT1 Y) (projT1 Z)) (WF_Prod I (projT1 Y) (projT1 Z) (projT2 Y) (projT2 Z)).

Definition term_fiber {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I : b_ty) (X : wf_ty I) : @hom_fiber Func Pred _ _  I X (fiber_unit I).
Proof.
  refine (@mk_hom_fiber Func Pred _ _  I X (fiber_unit I) (tm_lam (projT1 X) tm_unit) _).
  apply HD_Lam. 
  apply HD_Unit.
  apply AWF_Cons.
  - exact (projT2 X).
  - apply AWF_Nil.
Defined.

Definition prod_map_fiber {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I : b_ty) {X Y Z : wf_ty I} 
  (f : @hom_fiber Func Pred _ _  I X Y) (g : @hom_fiber Func Pred _ _  I X Z) : @hom_fiber Func Pred _ _  I X (fiber_prod Y Z).
Proof.
  refine (@mk_hom_fiber Func Pred _ _  I X (fiber_prod Y Z)
    (tm_app (tm_app
      (tm_lam (Ty_Arrow (projT1 X) (projT1 Y))
        (tm_lam (Ty_Arrow (projT1 X) (projT1 Z))
          (tm_lam (projT1 X)
            (tm_pair (tm_app (tm_var 2) (tm_var 0)) (tm_app (tm_var 1) (tm_var 0))))))
      (h_tm_of f)) (h_tm_of g)) _).
      
  apply HD_App with (Phi := Ty_Arrow (projT1 X) (projT1 Z)).
  - apply HD_App with (Phi := Ty_Arrow (projT1 X) (projT1 Y)).
    + apply HD_Lam. apply HD_Lam. apply HD_Lam. apply HD_Pair.
      * apply HD_App with (Phi := projT1 X).
        --
           apply HD_VarS. 
           ++ exact (projT2 X).
           ++ apply HD_VarS.
              ** apply WF_Arrow; [exact (projT2 X) | exact (projT2 Z)].
              ** apply HD_Var0.
                 apply AWF_Cons.
                 --- apply WF_Arrow; [exact (projT2 X) | exact (projT2 Y)].
                 --- apply AWF_Nil.
        --
           apply HD_Var0.
           apply AWF_Cons. exact (projT2 X).
           apply AWF_Cons. apply WF_Arrow; [exact (projT2 X) | exact (projT2 Z)].
           apply AWF_Cons. apply WF_Arrow; [exact (projT2 X) | exact (projT2 Y)].
           apply AWF_Nil.
           
      * apply HD_App with (Phi := projT1 X).
        --
           apply HD_VarS.
           ++ exact (projT2 X).
           ++ apply HD_Var0.
              apply AWF_Cons.
              ** apply WF_Arrow; [exact (projT2 X) | exact (projT2 Z)].
              ** apply AWF_Cons.
                 --- apply WF_Arrow; [exact (projT2 X) | exact (projT2 Y)].
                 --- apply AWF_Nil.
        --
           apply HD_Var0.
           apply AWF_Cons. exact (projT2 X).
           apply AWF_Cons. apply WF_Arrow; [exact (projT2 X) | exact (projT2 Z)].
           apply AWF_Cons. apply WF_Arrow; [exact (projT2 X) | exact (projT2 Y)].
           apply AWF_Nil.
           
    + exact (h_deriv_of f).
  - exact (h_deriv_of g).
Defined.

Definition fst_fiber {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I : b_ty) {X Y : wf_ty I} : @hom_fiber Func Pred _ _  I (fiber_prod X Y) X.
Proof.
  refine (@mk_hom_fiber Func Pred _ _  I (fiber_prod X Y) X (tm_lam (projT1 (fiber_prod X Y)) (tm_fst (tm_var 0))) _).
  apply HD_Lam. 
  eapply HD_Fst. 
  apply HD_Var0.
  apply AWF_Cons.
  - apply WF_Prod; [exact (projT2 X) | exact (projT2 Y)].
  - apply AWF_Nil.
Defined.

Definition snd_fiber {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I : b_ty) {X Y : wf_ty I} : @hom_fiber Func Pred _ _  I (fiber_prod X Y) Y.
Proof.
  refine (@mk_hom_fiber Func Pred _ _  I (fiber_prod X Y) Y (tm_lam (projT1 (fiber_prod X Y)) (tm_snd (tm_var 0))) _).
  apply HD_Lam. 
  eapply HD_Snd. 
  apply HD_Var0.
  apply AWF_Cons.
  - apply WF_Prod; [exact (projT2 X) | exact (projT2 Y)].
  - apply AWF_Nil.
Defined.

Instance Fiber_CartesianCategory {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I : b_ty) : CartesianCategory (Fiber_SetoidCategory I).
Proof.
  apply (Build_Thin_CC _ (Fiber_Thin I)
    (fiber_unit I) (fun X => @term_fiber Func Pred _ _  I X)
    (fun X Y => fiber_prod X Y) (fun X Y Z f g => @prod_map_fiber Func Pred _ _  I X Y Z f g)
    (fun X Y => @fst_fiber Func Pred _ _  I X Y)
    (fun X Y => @snd_fiber Func Pred _ _  I X Y)
  ).
Defined.


Definition fiber_arrow {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  {I : b_ty} (Y Z : wf_ty I) : wf_ty I :=
  existT _ (Ty_Arrow (projT1 Y) (projT1 Z)) (WF_Arrow I (projT1 Y) (projT1 Z) (projT2 Y) (projT2 Z)).

Definition eval_fiber {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I : b_ty) {Y Z : wf_ty I} : @hom_fiber Func Pred _ _  I (fiber_prod (fiber_arrow Y Z) Y) Z.
Proof.
  refine (@mk_hom_fiber Func Pred _ _  I _ _
    (tm_lam (projT1 (fiber_prod (fiber_arrow Y Z) Y)) (tm_app (tm_fst (tm_var 0)) (tm_snd (tm_var 0)))) _).
  apply HD_Lam. 
  apply HD_App with (Phi := projT1 Y).
  - eapply HD_Fst. apply HD_Var0.
    apply AWF_Cons.
    + apply (WF_Prod I). 
      * apply (WF_Arrow I); [exact (projT2 Y) | exact (projT2 Z)].
      * exact (projT2 Y).
    + apply AWF_Nil.
  - eapply HD_Snd. apply HD_Var0.
    apply AWF_Cons.
    + apply (WF_Prod I). 
      * apply (WF_Arrow I); [exact (projT2 Y) | exact (projT2 Z)].
      * exact (projT2 Y).
    + apply AWF_Nil.
Defined.

Definition curry_fiber {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I : b_ty) {X Y Z : wf_ty I} (g : @hom_fiber Func Pred _ _  I (fiber_prod X Y) Z) : @hom_fiber Func Pred _ _  I X (fiber_arrow Y Z).
Proof.
  refine (@mk_hom_fiber Func Pred _ _  I X (fiber_arrow Y Z)
    (tm_app
      (tm_lam (Ty_Arrow (projT1 (fiber_prod X Y)) (projT1 Z))
        (tm_lam (projT1 X)
          (tm_lam (projT1 Y)
            (tm_app (tm_var 2) (tm_pair (tm_var 1) (tm_var 0))))))
      (h_tm_of g)) _).
      
  apply HD_App with (Phi := Ty_Arrow (projT1 (fiber_prod X Y)) (projT1 Z)).
  - apply HD_Lam. apply HD_Lam. apply HD_Lam.
    apply HD_App with (Phi := projT1 (fiber_prod X Y)).
    +
      apply HD_VarS. exact (projT2 Y).
      apply HD_VarS. exact (projT2 X).
      apply HD_Var0.
      apply AWF_Cons.
      * apply (WF_Arrow I).
        -- apply (WF_Prod I); [exact (projT2 X) | exact (projT2 Y)].
        -- exact (projT2 Z).
      * apply AWF_Nil.
      
    + eapply HD_Pair.
      *
        apply HD_VarS. exact (projT2 Y).
        apply HD_Var0.
        apply AWF_Cons. exact (projT2 X).
        apply AWF_Cons. 
        -- apply (WF_Arrow I).
           ++ apply (WF_Prod I); [exact (projT2 X) | exact (projT2 Y)].
           ++ exact (projT2 Z).
        -- apply AWF_Nil.
        
      *
        apply HD_Var0.
        apply AWF_Cons. exact (projT2 Y).
        apply AWF_Cons. exact (projT2 X).
        apply AWF_Cons. 
        -- apply (WF_Arrow I).
           ++ apply (WF_Prod I); [exact (projT2 X) | exact (projT2 Y)].
           ++ exact (projT2 Z).
        -- apply AWF_Nil.
        
  - exact (h_deriv_of g).
Defined.

Instance Fiber_CartesianClosedCategory {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I : b_ty) : CartesianClosedCategory (Fiber_SetoidCategory I).
Proof.
  refine (Build_Thin_CCC _ (Fiber_Thin I)
    (fun Z Y => fiber_arrow Y Z)
    (fun Y Z => @eval_fiber Func Pred _ _  I Y Z)
    (fun X Y Z g => @curry_fiber Func Pred _ _  I X Y Z g)
  ).
Defined.


Definition fiber_void {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I : b_ty) : wf_ty I :=
  existT _ Ty_Void (WF_Void I). 

Definition fiber_sum {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  {I : b_ty} (X Y : wf_ty I) : wf_ty I :=
  existT _ (Ty_Sum (projT1 X) (projT1 Y)) (WF_Sum I (projT1 X) (projT1 Y) (projT2 X) (projT2 Y)).

Definition init_fiber {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I : b_ty) {X : wf_ty I} : @hom_fiber Func Pred _ _  I (fiber_void I) X.
Proof.
  refine (@mk_hom_fiber Func Pred _ _  I (fiber_void I) X (tm_lam Ty_Void (tm_absurd (projT1 X) (tm_var 0))) _).
  apply HD_Lam. 
  apply HD_Absurd. 
  -
    exact (projT2 X).
  -
    apply HD_Var0.
    apply AWF_Cons.
    + apply WF_Void.
    + apply AWF_Nil.
Defined.

Definition inl_fiber {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I : b_ty) {X Y : wf_ty I} : @hom_fiber Func Pred _ _  I X (fiber_sum X Y).
Proof.
  refine (@mk_hom_fiber Func Pred _ _  I X (fiber_sum X Y) (tm_lam (projT1 X) (tm_inl (projT1 Y) (tm_var 0))) _).
  apply HD_Lam. 
  apply HD_Inl. 
  -
    exact (projT2 Y).
  -
    apply HD_Var0.
    apply AWF_Cons. exact (projT2 X). apply AWF_Nil.
Defined.

Definition inr_fiber {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I : b_ty) {X Y : wf_ty I} : @hom_fiber Func Pred _ _  I Y (fiber_sum X Y).
Proof.
  refine (@mk_hom_fiber Func Pred _ _  I Y (fiber_sum X Y) (tm_lam (projT1 Y) (tm_inr (projT1 X) (tm_var 0))) _).
  apply HD_Lam. 
  apply HD_Inr. 
  -
    exact (projT2 X).
  -
    apply HD_Var0.
    apply AWF_Cons. exact (projT2 Y). apply AWF_Nil.
Defined.

Definition coprod_map_fiber {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I : b_ty) {X Y Z : wf_ty I} 
  (f : @hom_fiber Func Pred _ _  I X Z) (g : @hom_fiber Func Pred _ _  I Y Z) : @hom_fiber Func Pred _ _  I (fiber_sum X Y) Z.
Proof.
  refine (@mk_hom_fiber Func Pred _ _  I (fiber_sum X Y) Z
    (tm_app (tm_app
      (tm_lam (Ty_Arrow (projT1 X) (projT1 Z))
        (tm_lam (Ty_Arrow (projT1 Y) (projT1 Z))
          (tm_lam (Ty_Sum (projT1 X) (projT1 Y))
            (tm_case (tm_var 0)
              (tm_app (tm_var 3) (tm_var 0))
              (tm_app (tm_var 2) (tm_var 0))))))
      (h_tm_of f)) (h_tm_of g)) _).
      
  apply HD_App with (Phi := Ty_Arrow (projT1 Y) (projT1 Z)).
  - apply HD_App with (Phi := Ty_Arrow (projT1 X) (projT1 Z)).
    + apply HD_Lam. apply HD_Lam. apply HD_Lam.
      apply HD_Case with (Phi := projT1 X) (Psi := projT1 Y).
      *
        apply HD_Var0.
        apply AWF_Cons. apply (WF_Sum I); [exact (projT2 X) | exact (projT2 Y)].
        apply AWF_Cons. apply (WF_Arrow I); [exact (projT2 Y) | exact (projT2 Z)].
        apply AWF_Cons. apply (WF_Arrow I); [exact (projT2 X) | exact (projT2 Z)].
        apply AWF_Nil.
        
      *
        apply HD_App with (Phi := projT1 X).
        --
           apply HD_VarS. exact (projT2 X).
           apply HD_VarS. apply (WF_Sum I); [exact (projT2 X) | exact (projT2 Y)].
           apply HD_VarS. apply (WF_Arrow I); [exact (projT2 Y) | exact (projT2 Z)].
           apply HD_Var0.
           apply AWF_Cons. apply (WF_Arrow I); [exact (projT2 X) | exact (projT2 Z)].
           apply AWF_Nil.
        --
           apply HD_Var0.
           apply AWF_Cons. exact (projT2 X).
           apply AWF_Cons. apply (WF_Sum I); [exact (projT2 X) | exact (projT2 Y)].
           apply AWF_Cons. apply (WF_Arrow I); [exact (projT2 Y) | exact (projT2 Z)].
           apply AWF_Cons. apply (WF_Arrow I); [exact (projT2 X) | exact (projT2 Z)].
           apply AWF_Nil.
           
      *
        apply HD_App with (Phi := projT1 Y).
        --
           apply HD_VarS. exact (projT2 Y).
           apply HD_VarS. apply (WF_Sum I); [exact (projT2 X) | exact (projT2 Y)].
           apply HD_Var0.
           apply AWF_Cons. apply (WF_Arrow I); [exact (projT2 Y) | exact (projT2 Z)].
           apply AWF_Cons. apply (WF_Arrow I); [exact (projT2 X) | exact (projT2 Z)].
           apply AWF_Nil.
        --
           apply HD_Var0.
           apply AWF_Cons. exact (projT2 Y).
           apply AWF_Cons. apply (WF_Sum I); [exact (projT2 X) | exact (projT2 Y)].
           apply AWF_Cons. apply (WF_Arrow I); [exact (projT2 Y) | exact (projT2 Z)].
           apply AWF_Cons. apply (WF_Arrow I); [exact (projT2 X) | exact (projT2 Z)].
           apply AWF_Nil.
           
    + exact (h_deriv_of f).
  - exact (h_deriv_of g).
Defined. 

Instance Fiber_BiCartesianClosedCategory {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I : b_ty) : BiCartesianClosedCategory (Fiber_CartesianClosedCategory I).
Proof.
  apply (Build_Thin_BiCCC (Fiber_SetoidCategory I) (Fiber_CartesianClosedCategory I) (Fiber_Thin I)
    (fiber_void I) (fun X => @init_fiber Func Pred _ _  I X)
    (fun X Y => fiber_sum X Y) (fun X Y => @inl_fiber Func Pred _ _  I X Y) (fun X Y => @inr_fiber Func Pred _ _  I X Y)
    (fun X Y Z f g => @coprod_map_fiber Func Pred _ _  I X Y Z f g)
  ).
Defined.

Require Import Coq.Lists.List.

(** Substitution conversion used by universal elimination and existential introduction. *)
Lemma form_equiv_subst_comm_elim : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} 
  {I J A : b_ty} (t : @b_tm Func) (f : @b_tm Func) (Phi : @h_ty Func Pred)
  (dt : base_typing I t J) (df : base_typing J f A),
  WellFormed (b_Prod J A) Phi ->
  form_equiv I
    (form_subst (b_pair b_id (b_comp f t)) (form_subst (b_subst_ext t) Phi))
    (form_subst t (form_subst (b_pair b_id f) Phi)).
Proof.
intros Func Pred HFunc HPred  I J A t f Phi dt df Hwf.
  eapply FE_Trans.
  -
    eapply FE_Pullback_Comp.
    +
      eapply typing_subst_ext. exact dt.
    +
      eapply BT_Pair.
      * apply BT_Id.
      * eapply BT_Comp; eassumption.
    + exact Hwf.
  - eapply FE_Trans.
    +
      eapply FE_Pullback_Cong.
      * unfold b_subst_ext.
        eapply BE_Trans. 
        
        --
           eapply BE_Trans.
           ++
              apply BE_CompPair. 
           ++
              eapply BE_CongPair.
              **
                 eapply BE_Trans.
                 --- eapply BE_Sym. apply BE_Assoc.
                 --- eapply BE_Trans.
                     +++ eapply BE_CongComp. 
                         *** apply BE_BetaFst.
                         *** apply BE_Refl.
                     +++ apply BE_IdR.         
              **
                 apply BE_BetaSnd.
                 
        --
           eapply BE_Sym. 
           eapply BE_Trans.
           ++
              apply BE_CompPair.
           ++
              eapply BE_CongPair.
              **
                 apply BE_IdL.
              **
                 apply BE_Refl.
                 
      * exact Hwf.
  +
      eapply FE_Sym. eapply FE_Pullback_Comp.
      *
        eapply BT_Pair.
        -- apply BT_Id.
        -- exact df.
      *
        exact dt.
      * exact Hwf.

  Unshelve.
  all: repeat match goal with
  | |- base_typing _ _ _ => eapply BT_Comp || eapply BT_Pair || apply BT_Id || eapply BT_Fst || eapply BT_Snd || apply typing_subst_ext || eassumption
  end.
Defined.   


Lemma form_equiv_subst_comm_fst : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} 
  {I J A : b_ty} (t : @b_tm Func) (Chi : @h_ty Func Pred)
  (dt : base_typing I t J),
  WellFormed J Chi ->
  form_equiv (b_Prod I A)
    (form_subst (b_subst_ext t) (form_subst b_fst Chi))
    (form_subst b_fst (form_subst t Chi)).
Proof.
  intros Func Pred HFunc HPred  I J A t Chi dt Hwf.
  eapply FE_Trans.
  -
    eapply FE_Pullback_Comp.
    + eapply BT_Fst.
    + apply typing_subst_ext. exact dt.
    + exact Hwf.
  - eapply FE_Trans.
    +
      eapply FE_Pullback_Cong.
      * unfold b_subst_ext. apply BE_BetaFst.
      * exact Hwf.
    +
      eapply FE_Sym. eapply FE_Pullback_Comp.
      * exact dt.
      * apply BT_Fst.
      * exact Hwf.

  Unshelve.
  all: repeat match goal with
  | |- base_typing _ _ _ => eapply BT_Comp || apply BT_Fst || apply BT_Snd || apply typing_subst_ext || eassumption
  end.
Defined.

Lemma ctx_subst_ext_comm : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  
  {I J A : b_ty} (t : @b_tm Func) (dt : base_typing I t J) (G : @h_context Func Pred),
  All_WellFormed J G ->
  ctx_equiv (b_Prod I A) 
            (ctx_subst (b_subst_ext t) (ctx_subst b_fst G)) 
            (ctx_subst b_fst (ctx_subst t G)).
Proof.
  intros Func Pred HFunc HPred  I J A t dt G Hwf.
  induction Hwf.
  -
    simpl. apply CEq_Nil.
  -
    simpl. apply CEq_Cons.
    + eapply FE_Trans.
      *
        eapply FE_Pullback_Comp.
        -- eapply BT_Fst.
        -- apply typing_subst_ext. exact dt.
        -- assumption.
      * eapply FE_Trans.
        --
           eapply FE_Pullback_Cong.
           ++ unfold b_subst_ext. apply BE_BetaFst.
           ++ eapply w.
        --
           eapply FE_Sym. eapply FE_Pullback_Comp.
           ++ exact dt.
           ++ apply BT_Fst.
           ++ assumption.
    + exact IHHwf.
    Unshelve.
  all: repeat match goal with
  | |- base_typing _ _ _ => eapply BT_Comp || apply BT_Fst || apply BT_Snd || apply typing_subst_ext || eassumption || typeclasses eauto
  end.
Defined.



(** Typed substitution reflects formula well-formedness. *)
Lemma form_wf_subst_inv : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  {I J : b_ty} 
  (f : @b_tm Func) (df : base_typing I f J) (Phi : @h_ty Func Pred),
  WellFormed I (form_subst f Phi) -> WellFormed J Phi.
Proof.
  intros Func Pred HFunc HPred  I J f df Phi.
  generalize dependent J. generalize dependent I. generalize dependent f.
  
  induction Phi; intros f I J df Hwf; simpl in Hwf; inversion Hwf; subst.
  
  -   apply WF_Unit.
  -   apply WF_Void.
  -   apply WF_Prod; [eapply IHPhi1 | eapply IHPhi2]; eassumption.
  -   apply WF_Sum;  [eapply IHPhi1 | eapply IHPhi2]; eassumption.
  -   apply WF_Arrow;[eapply IHPhi1 | eapply IHPhi2]; eassumption.
  
  -
    match goal with
    | [ H_typ : base_typing _ (b_comp _ _) _ |- _ ] => inversion H_typ; subst
    end.
    assert (H_eq : J = B). { eapply base_typing_unique. exact df. eassumption. }
    subst B.
    eapply WF_Atom. eassumption.
    
  -
    apply WF_All.
    eapply IHPhi. 2: eassumption.
    unfold b_subst_ext.
    eapply BT_Pair.
    + eapply BT_Comp. exact df. apply BT_Fst.
    + apply BT_Snd.
    
  -
    apply WF_Ex.
    eapply IHPhi. 2: eassumption.
    unfold b_subst_ext.
    eapply BT_Pair.
    + eapply BT_Comp. exact df. apply BT_Fst.
    + apply BT_Snd.
Defined.



(** Well-formedness reflects along the first projection. *)
Lemma form_wf_fst_inv : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  {I A : b_ty} {Phi : @h_ty Func Pred},
  WellFormed (b_Prod I A) (form_subst b_fst Phi) -> WellFormed I Phi.
Proof.
  intros Func Pred HFunc HPred  I A Phi Hwf.
  eapply form_wf_subst_inv.
  - eapply BT_Fst.
  - exact Hwf.
Defined.
(** Context well-formedness reflects along the first projection. *)
Lemma ctx_wf_fst_inv : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  {I A : b_ty} {G : @h_context Func Pred},
  All_WellFormed (b_Prod I A) (ctx_subst b_fst G) -> All_WellFormed I G.
Proof.
  intros Func Pred HFunc HPred  I A G H.
  induction G.
  -
    simpl in H. inversion H. apply AWF_Nil.
  -
    simpl in H. 
    inversion H as [| ? ? H_head H_tail]; subst.
    apply AWF_Cons.
    +
      eapply form_wf_fst_inv. exact H_head.
    +
      apply IHG. exact H_tail.
Defined.

Lemma meta_ctx_wf : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  {I : b_ty} 
  {G : @h_context Func Pred} {p : @h_tm Func Pred} {Phi : @h_ty Func Pred},
  h_derivation I G p Phi -> @All_WellFormed Func Pred _ _ I G.
Proof.
intros Func Pred HFunc HPred  I G p Phi Hderiv.
  induction Hderiv.
  -
    exact a.
  -
    apply AWF_Cons; assumption.
  -
    exact a.
  -
    exact IHHderiv.
  -
    eapply ctx_equiv_wf_right.
    + exact c.
    + exact IHHderiv.
    
  -
    inversion IHHderiv; subst; assumption.
  -
    exact IHHderiv1.
  -
    exact IHHderiv1.
  -
    exact IHHderiv.
  -
    exact IHHderiv.
  -
    exact IHHderiv.
  -
    exact IHHderiv.
  -
    exact IHHderiv1.
  -
    exact IHHderiv.
  -
    apply ctx_wf_fst_inv in IHHderiv. 
    exact IHHderiv.
  -
    exact IHHderiv.
  -
    exact IHHderiv.
  -
     exact IHHderiv1.
Defined.



(** Every derivation has a well-formed context. *)
Lemma meta_ctx_wf_base : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  {I A : b_ty} 
  {G : @h_context Func Pred} {p : @h_tm Func Pred} {Phi : @h_ty Func Pred},
  h_derivation (b_Prod I A) (ctx_subst b_fst G) p Phi -> All_WellFormed I G.
Proof.
  intros Func Pred HFunc HPred  I A G p Phi H.
  apply meta_ctx_wf in H.
  apply ctx_wf_fst_inv in H.
  exact H.
Defined.

Lemma meta_type_wf : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  {I : b_ty} 
  {G : @h_context Func Pred} {p : @h_tm Func Pred} {Phi : @h_ty Func Pred},
  h_derivation I G p Phi -> WellFormed I Phi.
Proof.
  intros Func Pred HFunc HPred  I G p Phi Hderiv.
  induction Hderiv; simpl.
  -   inversion a; subst; assumption.
  -   assumption.
  -   apply WF_Unit.
  -
    destruct (form_equiv_wf I Phi Psi f) as [_ Hwf_Psi].
    exact Hwf_Psi.
  -   assumption.
  -
    apply WF_Arrow.
    +
      apply meta_ctx_wf in Hderiv. inversion Hderiv; subst. assumption.
    + assumption.
  -   inversion IHHderiv1; subst; assumption.
  -   apply WF_Prod; assumption.
  -   inversion IHHderiv; subst; assumption.
  -   inversion IHHderiv; subst; assumption.
  -   apply WF_Sum; assumption.
  -   apply WF_Sum; assumption.
  -   assumption.
  -
    exact w. 
  -   apply WF_All. apply IHHderiv.
  -
    eapply wf_subst.
    +
      eapply BT_Pair.
      * apply BT_Id.
      * exact b.
    +
      inversion IHHderiv; subst; assumption.
  -
    apply WF_Ex.
    eapply form_wf_subst_inv.
    +
      eapply BT_Pair.
      * apply BT_Id.
      * exact b.
    +
      exact IHHderiv.
  -
    apply form_wf_fst_inv in IHHderiv2.
    exact IHHderiv2.
Defined.

Lemma meta_all_body_wf : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  {I A : b_ty} 
  {G : @h_context Func Pred} {p : @h_tm Func Pred} {Phi : @h_ty Func Pred},
  h_derivation I G p (Ty_All A Phi) -> WellFormed (b_Prod I A) Phi.
Proof.
intros Func Pred HFunc HPred  I A G p Phi Hderiv.
  apply meta_type_wf in Hderiv.
  inversion Hderiv; subst.
  assumption.
Defined.

Lemma meta_subst_wf : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  {I J : b_ty} 
  (t : @b_tm Func) (dt : base_typing I t J) (Phi : @h_ty Func Pred),
  @WellFormed Func Pred _ _ J Phi -> @WellFormed Func Pred _ _ I (form_subst t Phi).
Proof.
intros Func Pred HFunc HPred  I J t dt Phi Hwf.
  eapply wf_subst.
  - exact dt.
  - exact Hwf.
Defined.

Lemma meta_ex_body_wf : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  {I A : b_ty} 
  {G : @h_context Func Pred} {p : @h_tm Func Pred} {Phi : @h_ty Func Pred} {f : @b_tm Func},
  base_typing I f A -> h_derivation I G p (form_subst (b_pair b_id f) Phi) -> @WellFormed Func Pred _ _ (b_Prod I A) Phi.
Proof.
intros Func Pred HFunc HPred  I A G p Phi f dt Hderiv.
  apply meta_type_wf in Hderiv.
  
  eapply form_wf_subst_inv.
  -
    eapply BT_Pair.
    + apply BT_Id.
    + exact dt.
  -
    exact Hderiv.
Defined.

Lemma meta_ex_body_wf_base : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  {I A : b_ty} 
  {G : @h_context Func Pred} {p : @h_tm Func Pred} {Phi : @h_ty Func Pred},
  h_derivation I G p (Ty_Ex A Phi) -> @WellFormed Func Pred _ _ (b_Prod I A) Phi.
Proof.
intros Func Pred HFunc HPred  I A G p Phi Hderiv.
  apply meta_type_wf in Hderiv.
  inversion Hderiv; subst.
  assumption.
Defined.

Lemma meta_ex_elim_chi_wf : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  {I A : b_ty} 
  {G : @h_context Func Pred} {p1 p2 : h_tm} {Phi Chi : @h_ty Func Pred},
  h_derivation I G p1 (Ty_Ex A Phi) ->
  h_derivation (b_Prod I A) (Phi :: ctx_subst b_fst G) p2 (form_subst b_fst Chi) ->
  @WellFormed Func Pred _ _ I Chi.
Proof.
intros Func Pred HFunc HPred  I A G p1 p2 Phi Chi H1 H2.
  apply meta_type_wf in H2.
  
  eapply form_wf_fst_inv.
  exact H2.
Defined.


Lemma ctx_wf_subst : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  {I J : b_ty} 
  (t : @b_tm Func) (dt : base_typing I t J) (G : @h_context Func Pred),
  All_WellFormed J G -> All_WellFormed I (ctx_subst t G).
Proof.
  intros Func Pred HFunc HPred  I J t dt G Hwf.
  induction Hwf.
  -
    simpl. apply AWF_Nil.
  -
    simpl. apply AWF_Cons.
    + eapply wf_subst; eassumption.
    + exact IHHwf.
Defined.

Lemma h_derivation_subst_general : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  
  {I J : b_ty} (t : @b_tm Func) (dt : base_typing I t J) (G : @h_context Func Pred) (Phi : @h_ty Func Pred) (p : @h_tm Func Pred),
  h_derivation J G p Phi -> 
  h_derivation I (ctx_subst t G) (tm_subst t p) (form_subst t Phi).
Proof.
  intros Func Pred HFunc HPred  I J t dt G Phi p Hderiv.
  revert I t dt.
  induction Hderiv; intros I0 t0 dt0.
  -
    simpl. apply HD_Var0.
    inversion a; subst.
    apply AWF_Cons.
    +
      eapply wf_subst. eassumption. exact X.
    +
      eapply ctx_wf_subst. eassumption. exact X0.
  -
    simpl. apply HD_VarS.
    + eapply wf_subst. exact dt0. exact w.
    +
      apply IHHderiv. exact dt0. 
  -
    simpl.
    apply HD_Unit.
    eapply ctx_wf_subst.
    + exact dt0.
    + exact a.
  -
    eapply HD_Conv.
    +
      apply IHHderiv. exact dt0.
    +
      eapply form_equiv_subst.
      * exact dt0.  
      * exact f.
  -
    eapply HD_Ctx_Conv.
    + eapply ctx_equiv_subst. exact dt0. exact c.
    + apply IHHderiv. exact dt0.
  -
    simpl. apply HD_Lam. apply IHHderiv. exact dt0.
  -
    simpl. eapply HD_App.
    + apply IHHderiv1. exact dt0.
    + apply IHHderiv2. exact dt0.
  -
    simpl. apply HD_Pair.
    + apply IHHderiv1. exact dt0.
    + apply IHHderiv2. exact dt0.
  -
    simpl. eapply HD_Fst. apply IHHderiv. exact dt0.
  -
    simpl. eapply HD_Snd. apply IHHderiv. exact dt0.
  -
    simpl. apply HD_Inl.
    +
      eapply wf_subst.
      * exact dt0.
      * exact w.
    +
      apply IHHderiv.
      exact dt0.
  -
    simpl. apply HD_Inr.
    +
      eapply wf_subst.
      * exact dt0.
      * exact w.
    +
      apply IHHderiv.
      exact dt0.
  -
    simpl. eapply HD_Case.
    + apply IHHderiv1. exact dt0.
    + apply IHHderiv2. exact dt0.
    + apply IHHderiv3. exact dt0.
  -
    simpl. apply HD_Absurd.
    +
      eapply wf_subst.
      * exact dt0.
      * exact w.
    +
      apply IHHderiv.
      exact dt0.
  
  -
    simpl. apply HD_All_Intro.
    eapply HD_Ctx_Conv.
    +
      eapply ctx_subst_ext_comm. 
      * exact dt0.
      * eapply meta_ctx_wf_base. exact Hderiv.
    +
      apply IHHderiv. 
      apply typing_subst_ext. exact dt0.

  -
    simpl. eapply HD_Conv.
    + eapply HD_All_Elim.
      * apply IHHderiv. exact dt0.
      * eapply BT_Comp. eassumption. exact dt0.
    +
      eapply form_equiv_subst_comm_elim.
      * exact dt0.
      * exact b.
      * eapply meta_all_body_wf. exact Hderiv.

  -
    simpl. eapply HD_Ex_Intro.
    + eapply BT_Comp. eassumption. exact dt0.
    + eapply HD_Conv.
      * apply IHHderiv. exact dt0.
      *
        eapply FE_Sym. 
        eapply form_equiv_subst_comm_elim.
        -- exact dt0.
        -- exact b.
        -- eapply meta_ex_body_wf. exact b. exact Hderiv.

  -
    simpl. eapply HD_Ex_Elim.
    + apply IHHderiv1. exact dt0.
    + eapply HD_Conv. 
      * eapply HD_Ctx_Conv.
        -- apply CEq_Cons. 
           ++
              apply FE_Refl. 
              eapply meta_subst_wf. 
              ** eapply typing_subst_ext. exact dt0.
              ** eapply meta_ex_body_wf_base. exact Hderiv1.
           ++
              eapply ctx_subst_ext_comm. 
              ** exact dt0.
              ** eapply meta_ctx_wf. exact Hderiv1. 
        -- apply IHHderiv2. apply typing_subst_ext. exact dt0.
      *
        eapply form_equiv_subst_comm_fst. 
        -- exact dt0.
        -- eapply meta_ex_elim_chi_wf. exact Hderiv1. exact Hderiv2.

Defined.


Definition subst_functor_obj {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  
  {I J : b_ty} (t : @b_tm Func) (dt : base_typing I t J)
  (Phi : wf_ty J) : wf_ty I.
Proof.
  destruct Phi as [phi Hwf].
  
  exists (form_subst t phi).
  
  eapply meta_subst_wf.
  - exact dt.
  - exact Hwf.
Defined.

Definition subst_functor_hom {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  
  {I J : b_ty} (t : @b_tm Func) (dt : base_typing I t J)
  (Phi Psi : wf_ty J)
  (f : hom_fiber Phi Psi) : hom_fiber (subst_functor_obj t dt Phi) (subst_functor_obj t dt Psi).
Proof.
  (* Destruct sigma objects so [subst_functor_obj] can reduce. *)
  destruct Phi as [phi Hwf_phi].
  destruct Psi as [psi Hwf_psi].
  
  destruct f as [p Hderiv].
  
  exists (tm_subst t p).
  
  change (h_derivation I (ctx_subst t []) (tm_subst t p) 
         (form_subst t (Ty_Arrow phi psi))).
         
  eapply h_derivation_subst_general.
  - exact dt.
  - exact Hderiv.
Defined.


Instance subst_functor {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  
  {I J : b_ty} (t : @b_tm Func) (dt : base_typing I t J) :
  Functor (Fiber_SetoidCategory J) (Fiber_SetoidCategory I).
Proof.
  refine (mk_Functor 
    (Fiber_SetoidCategory J) 
    (Fiber_SetoidCategory I)
    (fun Phi => subst_functor_obj t dt Phi)
    (fun Phi Psi f => subst_functor_hom t dt Phi Psi f)
    _ _ _).
Unshelve.
  (* Functor laws follow from thinness. *)
  all: intros; unfold fiber_equiv; constructor.
Defined.


Definition ex_functor_obj {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  
  (I A : b_ty) (Phi : wf_ty (b_Prod I A)) : wf_ty I.
Proof. 
  destruct Phi as [phi Hwf].
  exists (Ty_Ex A phi).
  apply WF_Ex. exact Hwf.
Defined.

Definition ex_subst_unit {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I A : b_ty) (Y : wf_ty (b_Prod I A)) :
  hom_fiber Y (subst_functor_obj b_fst BT_Fst (ex_functor_obj I A Y)).
Proof.
  destruct Y as [y Hy].
  exists (tm_lam y (tm_ex_intro b_snd (tm_var 0))).
  apply HD_Lam.
  simpl.
  eapply HD_Ex_Intro.
  - apply BT_Snd.
  - eapply HD_Conv.
    + apply HD_Var0. apply AWF_Cons; auto. apply AWF_Nil.
    + eapply FE_Trans.
      { eapply FE_Sym. eapply FE_Pullback_Id. exact Hy. }
      eapply FE_Trans.
      { eapply FE_Pullback_Cong.
        - eapply BE_Trans. { eapply BE_Sym. apply BE_EtaPair. }
          eapply BE_Sym. eapply BE_Trans. { apply BE_CompPair. }
          eapply BE_CongPair.
          + eapply BE_Trans. { eapply BE_Sym. apply BE_Assoc. }
            eapply BE_CongComp. apply BE_BetaFst. apply BE_Refl.
          + eapply BE_Trans. { apply BE_BetaSnd. } eapply BE_Sym. apply BE_IdR.
        - exact Hy.
      }
      { apply FE_Sym. eapply FE_Pullback_Comp.
        - eapply typing_subst_ext. eapply BT_Fst.
        - apply BT_Pair. apply BT_Id. apply BT_Snd.
        - exact Hy.
      }
Unshelve.
  all: repeat match goal with
  | |- base_typing _ _ _ => eapply BT_Comp || eapply BT_Pair || apply BT_Id || eapply BT_Fst || eapply BT_Snd || apply typing_subst_ext || eassumption
  | |- _ => auto
  end.
Defined.

Definition ex_subst_left_adj_mor {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I A : b_ty) 
  (Y : wf_ty (b_Prod I A)) (X : wf_ty I)
  (g : hom_fiber Y (subst_functor_obj b_fst BT_Fst X)) : 
  hom_fiber (ex_functor_obj I A Y) X.
Proof.
  destruct Y as [y Hy]. destruct X as [x Hx].
  destruct g as [p Hderiv].
  
  exists (tm_lam (Ty_Ex A y) (tm_ex_elim (tm_var 0) (tm_app p (tm_var 0)))).
  
  apply HD_Lam.
  eapply HD_Ex_Elim.
  - apply HD_Var0. apply AWF_Cons. apply WF_Ex. exact Hy. apply AWF_Nil.
  - simpl.
    eapply (HD_App _ _ _ _ y (form_subst b_fst x)).
    + change (h_derivation (b_Prod I A) ([] ++ [y; Ty_Ex A (form_subst (b_subst_ext b_fst) y)]) p (Ty_Arrow y (form_subst b_fst x))).
      eapply h_derivation_append.
      * exact Hderiv.
      * apply AWF_Cons; try assumption.
        apply AWF_Cons; try assumption.
        apply WF_Ex. eapply wf_subst; try assumption.
        eapply typing_subst_ext. apply BT_Fst.
        exact Hy.
        apply AWF_Nil.
    + apply HD_Var0. 
      apply AWF_Cons; try assumption.
      apply AWF_Cons; try assumption.
      apply WF_Ex. eapply wf_subst; try assumption.
      eapply typing_subst_ext. apply BT_Fst.
      exact Hy.
      apply AWF_Nil.
Defined.

Instance TermModel_Pullback_IsRightAdjoint {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I A : b_ty) :
  IsRightAdjoint (subst_functor b_fst BT_Fst (I:=b_Prod I A) (J:=I)).
Proof.
  refine (mk_IsRightAdjoint 
    (Fiber_SetoidCategory I)
    (Fiber_SetoidCategory (b_Prod I A))
    (subst_functor b_fst BT_Fst (I:=b_Prod I A) (J:=I))
    (fun Y => ex_functor_obj I A Y)
    (fun Y => ex_subst_unit I A Y)
    (fun Y X g => ex_subst_left_adj_mor I A Y X g)
    _ _ _).
Unshelve.
  all: intros; unfold fiber_equiv; constructor.
Defined.


Definition all_functor_obj {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I A : b_ty) 
  (Phi : wf_ty (b_Prod I A)) : wf_ty I.
Proof. 
  destruct Phi as [phi Hwf].
  exists (Ty_All A phi).
  apply WF_All. exact Hwf.
Defined.

Definition all_subst_counit {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I A : b_ty) 
  (X : wf_ty (b_Prod I A)) :
  hom_fiber (subst_functor_obj b_fst BT_Fst (all_functor_obj I A X)) X.
Proof.
  destruct X as [x Hx].
  exists (tm_lam (form_subst b_fst (Ty_All A x)) (tm_all_elim (tm_var 0) b_snd)).
  
  apply HD_Lam.
  eapply HD_Conv.
  - eapply HD_All_Elim.
    + apply HD_Var0. apply AWF_Cons. 
      change (WellFormed (b_Prod I A) (form_subst b_fst (Ty_All A x))).
      eapply wf_subst. 
      * apply BT_Fst. 
      * apply WF_All. exact Hx. 
      * apply AWF_Nil.
    + apply BT_Snd.
  -
    eapply FE_Sym.
    eapply FE_Trans.
    { eapply FE_Sym. eapply FE_Pullback_Id. exact Hx. }
    eapply FE_Trans.
    { eapply FE_Pullback_Cong.
      - eapply BE_Trans. { eapply BE_Sym. apply BE_EtaPair. }
        eapply BE_Sym. eapply BE_Trans. { apply BE_CompPair. }
        eapply BE_CongPair.
        + eapply BE_Trans. { eapply BE_Sym. apply BE_Assoc. }
          eapply BE_CongComp. apply BE_BetaFst. apply BE_Refl.
        + eapply BE_Trans. { apply BE_BetaSnd. } eapply BE_Sym. apply BE_IdR.
      - exact Hx.
    }
    { apply FE_Sym. eapply FE_Pullback_Comp.
      - eapply typing_subst_ext. eapply BT_Fst.
      - apply BT_Pair. apply BT_Id. apply BT_Snd.
      - exact Hx.
    }
Unshelve.
  all: repeat match goal with
  | |- base_typing _ _ _ => eapply BT_Comp || eapply BT_Pair || apply BT_Id || eapply BT_Fst || eapply BT_Snd || apply typing_subst_ext || eassumption
  end.
Defined.

Definition all_subst_right_adj_mor {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I A : b_ty) 
  (Y : wf_ty I) (X : wf_ty (b_Prod I A))
  (f : hom_fiber (subst_functor_obj b_fst BT_Fst Y) X) : 
  hom_fiber Y (all_functor_obj I A X).
Proof.
  destruct Y as [y Hy]. destruct X as [x Hx].
  destruct f as [p Hderiv].
  
  exists (tm_lam y (tm_all_intro (tm_app p (tm_var 0)))).
  
  apply HD_Lam.
  apply HD_All_Intro.
  
  simpl.
  
  (* Explicit formula arguments avoid an unresolved [Phi] evar. *)
  eapply (HD_App _ _ _ _ (form_subst b_fst y) x).
  -
    change (h_derivation (b_Prod I A) ([] ++ [form_subst b_fst y]) p (Ty_Arrow (form_subst b_fst y) x)).
    
    eapply h_derivation_append.
    + exact Hderiv.
    + apply AWF_Cons. eapply wf_subst. apply BT_Fst. exact Hy. apply AWF_Nil.
  -
    apply HD_Var0. 
    apply AWF_Cons. eapply wf_subst. apply BT_Fst. exact Hy. apply AWF_Nil.
Defined.
 

Instance TermModel_Pullback_IsLeftAdjoint {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I A : b_ty) :
  IsLeftAdjoint (subst_functor b_fst BT_Fst (I:=b_Prod I A) (J:=I)).
Proof.
  refine (mk_IsLeftAdjoint 
    (Fiber_SetoidCategory (b_Prod I A))
    (Fiber_SetoidCategory I)
    (subst_functor b_fst BT_Fst (I:=b_Prod I A) (J:=I))
    (fun X => all_functor_obj I A X)
    (fun X => all_subst_counit I A X)
    (fun Y X f => all_subst_right_adj_mor I A Y X f)
    _ _ _).
Unshelve.
  all: intros; unfold fiber_equiv; constructor.
Defined.



Lemma form_equiv_to_iso {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I : b_ty) 
  (X Y : wf_ty I) :
  form_equiv I (projT1 X) (projT1 Y) -> @Iso (Fiber_SetoidCategory I) X Y.
Proof.
  intros Heq.
  destruct X as [x Hx]. destruct Y as [y Hy]. simpl in Heq.
  
  econstructor.
  - unfold fiber_equiv; constructor.
  - unfold fiber_equiv; constructor.
    
  Unshelve.
  *
    exists (tm_lam x (tm_var 0)).
    apply HD_Lam. eapply HD_Conv.
    + apply HD_Var0. apply AWF_Cons; auto. apply AWF_Nil.
    + exact Heq.
    
  *
    exists (tm_lam y (tm_var 0)).
    apply HD_Lam. eapply HD_Conv.
    + apply HD_Var0. apply AWF_Cons; auto. apply AWF_Nil.
    + apply FE_Sym. exact Heq.
Defined.



Instance TermModel_GoodFibration {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  : 
  GoodFibration (Base_SetoidCategory Func).
Proof.
  refine (@mk_GoodFibration 
    (Base_SetoidCategory Func) 
    (Base_CartesianCategory Func)
    (fun I => Fiber_SetoidCategory I)
    (fun I => Fiber_Thin I)
    (fun I => Fiber_CartesianCategory I)
    (fun I => Fiber_CartesianClosedCategory I)
    (fun I => Fiber_BiCartesianClosedCategory I)
    
    (fun I J f => subst_functor (tm_of f) (deriv_of f))
    
    _ _ _ _ _ _ _ 
    
    (fun I A => TermModel_Pullback_IsRightAdjoint I A)
    (fun I A => TermModel_Pullback_IsLeftAdjoint I A)
    
    _ _ _
  ).
  
  -
    intros I A. destruct A as [phi Hwf]. apply form_equiv_to_iso. simpl.
    eapply FE_Pullback_Id. exact Hwf.
    
  -
    intros I J K g f A. destruct A as [phi Hwf]. apply form_equiv_to_iso. simpl.
    eapply FE_Sym. 
    eapply FE_Pullback_Comp.
    + exact (deriv_of g).
    + exact (deriv_of f).
    + exact Hwf.
    
  -
    intros I J f. apply form_equiv_to_iso. simpl. apply FE_Refl. apply WF_Unit.
    
  -
    intros I J f A B. destruct A as [phiA HwfA]. destruct B as [phiB HwfB]. 
    apply form_equiv_to_iso. simpl. apply FE_Refl.
    apply WF_Prod.
    + eapply meta_subst_wf. exact (deriv_of f). exact HwfA.
    + eapply meta_subst_wf. exact (deriv_of f). exact HwfB.
    
  -
    intros I J f. apply form_equiv_to_iso. simpl. apply FE_Refl.
    apply WF_Void.
    
  -
    intros I J f A B. destruct A as [phiA HwfA]. destruct B as [phiB HwfB]. 
    apply form_equiv_to_iso. simpl. apply FE_Refl.
    apply WF_Sum.
    + eapply meta_subst_wf. exact (deriv_of f). exact HwfA.
    + eapply meta_subst_wf. exact (deriv_of f). exact HwfB.
    
  -
    intros I J f A B. destruct A as [phiA HwfA]. destruct B as [phiB HwfB]. 
    apply form_equiv_to_iso. simpl. apply FE_Refl.
    apply WF_Arrow.
    + eapply meta_subst_wf. exact (deriv_of f). exact HwfB.
    + eapply meta_subst_wf. exact (deriv_of f). exact HwfA.
    
  -
    intros I J K f A. destruct A as [phi Hwf]. apply form_equiv_to_iso. simpl. apply FE_Refl.
    apply WF_Ex.
    eapply meta_subst_wf. exact (deriv_of ((f ∘ prod_fst) ∏ prod_snd)). exact Hwf.
    
  -
    intros I J K f A. destruct A as [phi Hwf]. apply form_equiv_to_iso. simpl. apply FE_Refl.
    apply WF_All.
    eapply meta_subst_wf. exact (deriv_of ((f ∘ prod_fst) ∏ prod_snd)). exact Hwf.
  -
    intros I J f g Heq A. destruct A as [phi Hwf]. apply form_equiv_to_iso. simpl.
    eapply FE_Pullback_Cong.
    + exact Heq.
    + exact Hwf.
Defined.

(** Atomic predicate interpretation in the syntactic model. *)

  
Definition term_model_i_atom {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  
  (p : Pred) (t : @b_tm Func) (I : b_ty) : 
  wf_ty (@interp_ty (Base_SetoidCategory Func)
                    (Base_CartesianCategory Func)
                    (Base_TwoSortCategory Func) I).
Proof.
  rewrite (interp_ty_id Func I).
  
  destruct (decide_base_typing I t) as [[A dt] | Hbad].
  -
    destruct (b_ty_eq_dec A (pred_dom p)) as [HA | Hneq].
    + subst A.
      exists (Ty_Atom p t).
      eapply WF_Atom.
      exact dt.
    + exists Ty_Unit.
      apply WF_Unit.
  -
    exists Ty_Unit.
    apply WF_Unit.
Defined.

(** Helpers for dependent transports in the syntactic model. *)

(* Reindexing commutes with projection to the underlying formula. *)
Lemma projT1_pullback : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  {I J : @obj (Base_SetoidCategory Func)} 
  (f : @hom (Base_SetoidCategory Func) I J) (Phi : wf_ty J),
  projT1 (@fobj _ _ (Pullback f) Phi) = form_subst (tm_of f) (projT1 Phi).
Proof.
  intros. destruct Phi. reflexivity.
Defined.

(* Dependent transport does not change the underlying formula. *)
Lemma projT1_eq_rect_r_wf : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  {I J : @obj (Base_SetoidCategory Func)} 
  (e : I = J) (Phi : wf_ty J),
  projT1 (eq_rect_r (fun o : @obj (Base_SetoidCategory Func) => wf_ty o) Phi e) = projT1 Phi.
Proof.
  intros. destruct e. reflexivity.
Defined.

(** The syntactic iFOL hyperdoctrine. *)

Instance TermModel_IFOLHyperModel {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  : 
  @IFOLHyperModel Func Pred H H0
    (Base_SetoidCategory Func)
    (Base_CartesianCategory Func)
    (Base_TwoSortCategory Func)
    (Base_SyntacticIFOLModel Func)
    TermModel_GoodFibration.
Proof.
  refine (@Build_IFOLHyperModel Func Pred H H0
    (Base_SetoidCategory Func) 
    (Base_CartesianCategory Func) 
    (Base_TwoSortCategory Func) 
    (Base_SyntacticIFOLModel Func)
    TermModel_GoodFibration 
    term_model_i_atom
    _ 
    _).

  -
    intros p t I A f df.
    apply form_equiv_to_iso. 
    unfold term_model_i_atom.
    
    rewrite projT1_pullback.
    rewrite projT1_eq_rect_r_wf.
    rewrite projT1_eq_rect_r_wf.
    
    rewrite (interp_tm_term I A f df).
    
    cbn [projT1].
    
    destruct (decide_base_typing A t) as [[B dt_t] | Hbad_t].
    + destruct (b_ty_eq_dec B (pred_dom p)) as [HB | HB].
      * subst B.
        destruct (decide_base_typing I (b_comp t f)) as [[B' dcomp] | Hbad_comp].
        -- assert (HB' : B' = pred_dom p).
           { eapply base_typing_unique.
             - exact dcomp.
             - exact (BT_Comp dt_t df).
           }
           subst B'.
           destruct (b_ty_eq_dec (pred_dom p) (pred_dom p)) as [Heq_dom | Hcontra].
           2: exfalso; apply Hcontra; reflexivity.
           assert (HHeq_dom : Heq_dom = eq_refl) by
             exact (@UIP_dec b_ty b_ty_eq_dec _ _ Heq_dom eq_refl).
           try rewrite HHeq_dom in *.
           repeat rewrite projT1_eq_rect_r_wf.
           cbn [projT1 form_subst].
           rewrite (interp_ty_id Func I).
           apply FE_Refl.
           eapply WF_Atom.
           exact dcomp.
        -- destruct (Hbad_comp (pred_dom p) (BT_Comp dt_t df)).
      * destruct (decide_base_typing I (b_comp t f)) as [[B' dcomp] | Hbad_comp].
        -- assert (HB' : B' = B).
           { inversion dcomp; subst.
             match goal with
             | [ Ht : base_typing ?Mid t B', Hf : base_typing I f ?Mid |- _ ] =>
                 assert (HM : Mid = A) by (eapply base_typing_unique; [exact Hf | exact df]);
                 subst Mid;
                 eapply base_typing_unique; [exact Ht | exact dt_t]
             end.
           }
           subst B'.
           destruct (b_ty_eq_dec B (pred_dom p)) as [Hcontra | _].
           { contradiction. }
           rewrite (interp_ty_id Func I).
           apply FE_Refl.
           apply WF_Unit.
        -- rewrite (interp_ty_id Func I).
           apply FE_Refl.
           apply WF_Unit.
    + destruct (decide_base_typing I (b_comp t f)) as [[B' dcomp] | Hbad_comp].
      * inversion dcomp; subst.
        match goal with
        | [ Ht : base_typing ?Mid t _, Hf : base_typing I f ?Mid |- _ ] =>
            assert (HM : Mid = A) by (eapply base_typing_unique; [exact Hf | exact df]);
            subst Mid;
            destruct (Hbad_t B' Ht)
        end.
      * rewrite (interp_ty_id Func I).
        apply FE_Refl.
        apply WF_Unit.

  -
    intros p I A t1 t2 d1 d2 Heq.
    apply form_equiv_to_iso.
    unfold term_model_i_atom.
    
    rewrite projT1_eq_rect_r_wf.
    rewrite projT1_eq_rect_r_wf.
    
    cbn [projT1].
    
    destruct (decide_base_typing I t1) as [[B1 dt1] | Hbad1].
    + destruct (decide_base_typing I t2) as [[B2 dt2] | Hbad2].
      * assert (HB1 : B1 = A) by (eapply base_typing_unique; [exact dt1 | exact d1]).
        assert (HB2 : B2 = A) by (eapply base_typing_unique; [exact dt2 | exact d2]).
        subst B1 B2.
        destruct (b_ty_eq_dec A (pred_dom p)) as [HA | HA].
        -- subst A.
           destruct (b_ty_eq_dec (pred_dom p) (pred_dom p)) as [Heq_dom | Hcontra].
           2: exfalso; apply Hcontra; reflexivity.
           assert (HHeq_dom : Heq_dom = eq_refl) by
             exact (@UIP_dec b_ty b_ty_eq_dec _ _ Heq_dom eq_refl).
           try rewrite HHeq_dom in *.
           repeat rewrite projT1_eq_rect_r_wf.
           cbn [projT1].
           rewrite (interp_ty_id Func I).
           eapply FE_Atom.
           exact Heq.
        -- rewrite (interp_ty_id Func I).
           apply FE_Refl.
           apply WF_Unit.
      * destruct (Hbad2 A d2).
    + destruct (Hbad1 A d1).
Defined.

(** Interpretation identity. *)

Lemma projT1_ex_functor_obj : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}  (I A : b_ty) (Y : wf_ty (b_Prod I A)),
  projT1 (ex_functor_obj I A Y) = Ty_Ex A (projT1 Y).
Proof. intros. destruct Y. reflexivity. Defined.

(** Well-formed formulas interpret to their own syntactic representatives. *)

Lemma term_model_interp_id : forall {Func Pred : Type} `{HFunc : FunctionSignature Func} `{HPred : PredicateSignature Pred}  (ctx : b_ty) (X : @h_ty Func Pred), 
  WellFormed ctx X -> (* Excludes the ill-typed atom fallback. *)
  projT1 (@interp_h_ty Func Pred HFunc HPred
            (Base_SetoidCategory Func)
            (Base_CartesianCategory Func)
            (Base_TwoSortCategory Func)
            (Base_SyntacticIFOLModel Func)
            TermModel_GoodFibration
            (@TermModel_IFOLHyperModel Func Pred HFunc HPred )
            ctx X) = X.
Proof. 
  intros Func Pred HFunc HPred  ctx X Hwf.
  generalize dependent ctx.
  
  induction X; intros ctx Hwf; simpl.

  -
    reflexivity.
    
  -
    reflexivity.
    
  -
    inversion Hwf; subst. 
    simpl. rewrite IHX1, IHX2; auto.
    
  -
    inversion Hwf; subst. 
    simpl. rewrite IHX1, IHX2; auto.
    
  -
    inversion Hwf; subst. 
    simpl. rewrite IHX1, IHX2; auto.
    
  -
    inversion Hwf; subst.
    
    (* Unfold the atom interpretation to expose its dependent transport. *)
    unfold term_model_i_atom.
    
    rewrite projT1_eq_rect_r_wf.
    
    destruct (decide_base_typing ctx b) as [[A0 b0] | Hbad].
    +
      assert (HA0 : A0 = pred_dom p).
      { eapply base_typing_unique; [exact b0 | exact X]. }
      subst A0.
      destruct (b_ty_eq_dec (pred_dom p) (pred_dom p)) as [Heq_dom | Hcontra].
      2: exfalso; apply Hcontra; reflexivity.
      assert (HHeq_dom : Heq_dom = eq_refl) by
        exact (@UIP_dec b_ty b_ty_eq_dec _ _ Heq_dom eq_refl).
      try rewrite HHeq_dom in *.
      repeat rewrite projT1_eq_rect_r_wf.
      simpl.
      reflexivity.
    +
      match goal with
      | [ H_bt : base_typing ctx b ?A_mid |- _ ] => destruct (Hbad A_mid H_bt)
      end.
    
 -
    inversion Hwf; subst. 
    match goal with
    | [ H : WellFormed (b_Prod ctx b) X |- _ ] => specialize (IHX (b_Prod ctx b) H)
    end.
    destruct (interp_h_ty (b_Prod ctx b) X) as [phi Hwf_phi] in *.
    simpl in IHX. subst phi.
    
    cbn [all_functor_obj projT1].
    
    f_equal.
    apply (interp_ty_id Func b).
    
  -
    inversion Hwf; subst.
    match goal with
    | [ H : WellFormed (b_Prod ctx b) X |- _ ] => specialize (IHX (b_Prod ctx b) H)
    end.
    destruct (interp_h_ty (b_Prod ctx b) X) as [phi Hwf_phi] in *.
    simpl in IHX. subst phi.
    
    cbn [ex_functor_obj projT1].
    
    f_equal.
    apply (interp_ty_id Func b).
Defined.






Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

Fixpoint h_lift {Func Pred : Type} (shift cutoff : nat) (p : @h_tm Func Pred) : @h_tm Func Pred :=
  match p with
  | tm_unit => tm_unit

  | tm_var i =>
      if cutoff <=? i then tm_var (shift + i) else tm_var i

  | tm_lam Phi p' =>
      tm_lam Phi (h_lift shift (Datatypes.S cutoff) p')

  | tm_app p1 p2 =>
      tm_app (h_lift shift cutoff p1) (h_lift shift cutoff p2)

  | tm_pair p1 p2 =>
      tm_pair (h_lift shift cutoff p1) (h_lift shift cutoff p2)

  | tm_fst p' =>
      tm_fst (h_lift shift cutoff p')

  | tm_snd p' =>
      tm_snd (h_lift shift cutoff p')

  | tm_inl Psi p' =>
      tm_inl Psi (h_lift shift cutoff p')

  | tm_inr Phi p' =>
      tm_inr Phi (h_lift shift cutoff p')

  | tm_case p0 p1 p2 =>
      tm_case
        (h_lift shift cutoff p0)
        (h_lift shift (Datatypes.S cutoff) p1)
        (h_lift shift (Datatypes.S cutoff) p2)

  | tm_absurd Phi p' =>
      tm_absurd Phi (h_lift shift cutoff p')

  | tm_all_intro p' =>
      tm_all_intro (h_lift shift cutoff p')

  | tm_all_elim p' t =>
      tm_all_elim (h_lift shift cutoff p') t

  | tm_ex_intro t p' =>
      tm_ex_intro t (h_lift shift cutoff p')

  | tm_ex_elim p1 p2 =>
      tm_ex_elim
        (h_lift shift cutoff p1)
        (h_lift shift (Datatypes.S cutoff) p2)

  end.
  
Fixpoint h_insert_at {Func Pred : Type}
  (n : nat) (Psi : @h_ty Func Pred) (G : @h_context Func Pred) : @h_context Func Pred :=
  match n, G with
  | Datatypes.O, _ => Psi :: G
  | Datatypes.S n', nil => Psi :: nil
  | Datatypes.S n', Phi :: G' => Phi :: h_insert_at n' Psi G'
  end.
  
Lemma All_WellFormed_insert : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} 
  (I : b_ty) (G : @h_context Func Pred) (Psi : @h_ty Func Pred) (n : nat),
  WellFormed I Psi ->
  All_WellFormed I G ->
  All_WellFormed I (h_insert_at n Psi G).
Proof.
  intros Func Pred HFunc HPred  I G Psi n HwfPsi HwfG.
  revert n.
  induction HwfG; intros n; destruct n; simpl.
  -
    apply AWF_Cons.
    + exact HwfPsi.
    + apply AWF_Nil.

  -
    apply AWF_Cons.
    + exact HwfPsi.
    + apply AWF_Nil.

  -
    apply AWF_Cons.
    + exact HwfPsi.
    + apply AWF_Cons; assumption.

  -
    apply AWF_Cons.
    + assumption.
    + apply IHHwfG.
Defined.

Lemma ctx_subst_insert : forall {Func Pred : Type}
  (f : @b_tm Func) (n : nat) (Psi : @h_ty Func Pred) (G : @h_context Func Pred),
  ctx_subst f (h_insert_at n Psi G)
  =
  h_insert_at n (form_subst f Psi) (ctx_subst f G).
Proof.
  intros Func Pred f n Psi G.
  revert n.
  induction G as [|Phi G IH]; intros n; destruct n; simpl; auto.
  rewrite IH.
  reflexivity.
Defined.

Lemma ctx_equiv_insert : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} 
  (I : b_ty) (G1 G2 : @h_context Func Pred) (Psi : @h_ty Func Pred) (n : nat),
  WellFormed I Psi ->
  ctx_equiv I G1 G2 ->
  ctx_equiv I (h_insert_at n Psi G1) (h_insert_at n Psi G2).
Proof.
  intros Func Pred HFunc HPred  I G1 G2 Psi n HwfPsi Heq.
  revert n.
  induction Heq; intros n; destruct n; simpl.
  - apply CEq_Cons.
    + apply FE_Refl. exact HwfPsi.
    + apply CEq_Nil.
  - apply CEq_Cons.
    + apply FE_Refl. exact HwfPsi.
    + apply CEq_Nil.
  - apply CEq_Cons.
    + apply FE_Refl. exact HwfPsi.
    + apply CEq_Cons; assumption.
  - apply CEq_Cons.
    + exact f.
    + apply IHHeq.
Defined.

Theorem hd_weakening_general : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} 
  (I : b_ty) (G : @h_context Func Pred) (p : @h_tm Func Pred) (Phi Psi : @h_ty Func Pred) (n : nat),
  WellFormed I Psi ->
  h_derivation I G p Phi ->
  h_derivation I (h_insert_at n Psi G) (h_lift 1 n p) Phi.
Proof.
  intros Func Pred HFunc HPred  I G p Phi Psi n HwfPsi d.
  revert n Psi HwfPsi.
  induction d; intros n0 Psi0 Hwf0; simpl.

    -
    destruct n0; simpl.
    + apply HD_VarS.
      * exact Hwf0.
      * apply HD_Var0. exact a.

    + inversion a; subst.
      apply HD_Var0.
      apply AWF_Cons.
      * assumption.
      * apply All_WellFormed_insert; assumption.

    -
    destruct n0; simpl.
    + apply HD_VarS.
      * exact Hwf0.
      * apply HD_VarS; assumption.

    + destruct (n0 <=? n) eqn:Heq.
      * apply HD_VarS.
        -- exact w.
        -- replace (@tm_var Func Pred (Datatypes.S n))
             with (@h_lift Func Pred 1 n0 (@tm_var Func Pred n)).
           ++ apply IHd. exact Hwf0.
           ++ simpl. rewrite Heq. reflexivity.

      * apply HD_VarS.
        -- exact w.
        -- replace (@tm_var Func Pred n)
             with (@h_lift Func Pred 1 n0 (@tm_var Func Pred n)).
           ++ apply IHd. exact Hwf0.
           ++ simpl. rewrite Heq. reflexivity.
           
  -
    apply HD_Unit.
    apply All_WellFormed_insert; assumption.

  -
    eapply HD_Conv.
    + apply IHd. exact Hwf0.
    + exact f.

  -
    eapply HD_Ctx_Conv.
    + eapply ctx_equiv_insert. exact Hwf0. exact c.
    + apply IHd. exact Hwf0.

    -
    apply HD_Lam.
    exact (IHd (Datatypes.S n0) Psi0 Hwf0).

  -
    eapply HD_App.
    + apply IHd1. exact Hwf0.
    + apply IHd2. exact Hwf0.

  -
    apply HD_Pair.
    + apply IHd1. exact Hwf0.
    + apply IHd2. exact Hwf0.

  -
    eapply HD_Fst.
    apply IHd.
    exact Hwf0.

  -
    eapply HD_Snd.
    apply IHd.
    exact Hwf0.

  -
    apply HD_Inl.
    + exact w.
    + apply IHd. exact Hwf0.

  -
    apply HD_Inr.
    + exact w.
    + apply IHd. exact Hwf0.

    -
    eapply HD_Case.
    + apply IHd1.
      exact Hwf0.

    + change (h_derivation I
                (h_insert_at (Datatypes.S n0) Psi0 (Phi :: G))
                (@h_lift Func Pred 1 (Datatypes.S n0) p1)
                Chi).
      apply IHd2.
      exact Hwf0.

    + change (h_derivation I
                (h_insert_at (Datatypes.S n0) Psi0 (Psi :: G))
                (@h_lift Func Pred 1 (Datatypes.S n0) p2)
                Chi).
      apply IHd3.
      exact Hwf0.

  -
    apply HD_Absurd.
    + exact w.
    + apply IHd. exact Hwf0.

  -
    apply HD_All_Intro.
    rewrite ctx_subst_insert.
    apply IHd.
    eapply wf_subst.
    + apply BT_Fst.
    + exact Hwf0.

  -
    eapply HD_All_Elim.
    + apply IHd. exact Hwf0.
    + exact b.

  -
    eapply HD_Ex_Intro.
    + exact b.
    + apply IHd. exact Hwf0.

   -
    eapply HD_Ex_Elim.
    + apply IHd1.
      exact Hwf0.

    + simpl.
      rewrite ctx_subst_insert.

      change (h_derivation (b_Prod I A)
                (h_insert_at
                   (Datatypes.S n0)
                   (form_subst b_fst Psi0)
                   (Phi :: ctx_subst b_fst G))
                (@h_lift Func Pred 1 (Datatypes.S n0) p2)
                (form_subst b_fst Chi)).

      apply IHd2.

      eapply wf_subst.
      * apply BT_Fst.
      * exact Hwf0.

Defined.

Lemma hd_weakening : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} 
  (I : b_ty) (G : @h_context Func Pred) (A : @h_ty Func Pred) (p : @h_tm Func Pred) (Phi : @h_ty Func Pred),
  All_WellFormed I (A :: G) ->
  h_derivation I G p Phi ->
  h_derivation I (A :: G) (h_lift 1 0 p) Phi.
Proof.
  intros Func Pred HFunc HPred  I G A p Phi HwfCtx d.
  assert (HwfA : WellFormed I A).
  {
    inversion HwfCtx; subst.
    assumption.
  }
  exact (hd_weakening_general I G p Phi A 0 HwfA d).
Defined.

Fixpoint h_make_ctx_ty {Func Pred : Type} (G : @h_context Func Pred) : @h_ty Func Pred :=
  match G with
  | nil => Ty_Unit
  | A :: G' => Ty_Prod (h_make_ctx_ty G') A
  end.

Fixpoint h_reify_ctx {Func Pred : Type} (G : @h_context Func Pred) : @h_tm Func Pred :=
  match G with
  | nil => tm_unit
  | A :: G' => tm_pair (h_lift 1 0 (h_reify_ctx G')) (tm_var 0)
  end.
  
Lemma h_reify_ctx_typing : forall {Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} 
  (I : b_ty) (G : @h_context Func Pred),
  All_WellFormed I G ->
  h_derivation I G (h_reify_ctx G) (h_make_ctx_ty G).
Proof.
  intros Func Pred HFunc HPred  I G HwfG.
  induction HwfG as [|A G HwfA HwfG IH]; simpl.
  - apply HD_Unit.
    apply AWF_Nil.
  - apply HD_Pair.
    + eapply hd_weakening.
      * apply AWF_Cons; assumption.
      * exact IH.
    + apply HD_Var0.
      apply AWF_Cons; assumption.
Defined.

Lemma term_model_interp_ctx_id : forall {Func Pred : Type} `{HFunc : FunctionSignature Func} `{HPred : PredicateSignature Pred} 
  (I : b_ty) (G : @h_context Func Pred),
  All_WellFormed I G ->
  projT1
    (@interp_h_ctx Func Pred HFunc HPred
       (Base_SetoidCategory Func)
       (Base_CartesianCategory Func)
       (Base_TwoSortCategory Func)
       (Base_SyntacticIFOLModel Func)
       TermModel_GoodFibration
       (@TermModel_IFOLHyperModel Func Pred HFunc HPred )
       I G)
  = h_make_ctx_ty G.
Proof.
  intros Func Pred HFunc HPred  I G HwfG.
  induction HwfG as [|Phi G HwfPhi HwfG IH]; simpl.
  - reflexivity.
  - cbn [projT1].
    f_equal.
    + exact IH.
    + apply term_model_interp_id.
      exact HwfPhi.
Defined.

Theorem ifol_completeness_inhabitational_gen :
  forall {Func Pred : Type} `{HFunc : FunctionSignature Func} `{HPred : PredicateSignature Pred} 
         {I : b_ty} {G : @h_context Func Pred} {Phi : @h_ty Func Pred}
         (wfc : All_WellFormed I G)
         (wf_Phi : WellFormed I Phi),
  (forall (C : SetoidCategory) (CC : CartesianCategory C)
          (TSC : TwoSortCategory C)
          (BEM : @BaseIFOLModel Func HFunc C CC TSC)
          (GF : GoodFibration C)
          (EHM : @IFOLHyperModel Func Pred HFunc HPred C CC TSC BEM GF),
     inhabited
       (@hom (Fiber (interp_ty I))
             (@interp_h_ctx Func Pred HFunc HPred C CC TSC BEM GF EHM I G)
             (@interp_h_ty  Func Pred HFunc HPred C CC TSC BEM GF EHM I Phi))) ->
  exists (p : @h_tm Func Pred),
    inhabited (h_derivation I G p Phi).
Proof.
  intros Func Pred HFunc HPred  I G Phi wfc wf_Phi H_univ.

  pose proof
    (H_univ
       (Base_SetoidCategory Func)
       (Base_CartesianCategory Func)
       (Base_TwoSortCategory Func)
       (Base_SyntacticIFOLModel Func)
       TermModel_GoodFibration
       TermModel_IFOLHyperModel) as H_term.

  destruct H_term as [m_syn].
  destruct m_syn as [p_syn dp_syn].

  assert (H_ctx :
    projT1
      (@interp_h_ctx Func Pred HFunc HPred
         (Base_SetoidCategory Func)
         (Base_CartesianCategory Func)
         (Base_TwoSortCategory Func)
         (Base_SyntacticIFOLModel Func)
         TermModel_GoodFibration
         (@TermModel_IFOLHyperModel Func Pred HFunc HPred )
         I G)
    = h_make_ctx_ty G).
  {
    apply term_model_interp_ctx_id.
    exact wfc.
  }

  assert (H_phi :
    projT1
      (@interp_h_ty Func Pred HFunc HPred
         (Base_SetoidCategory Func)
         (Base_CartesianCategory Func)
         (Base_TwoSortCategory Func)
         (Base_SyntacticIFOLModel Func)
         TermModel_GoodFibration
         (@TermModel_IFOLHyperModel Func Pred HFunc HPred )
         I Phi)
    = Phi).
  {
    apply term_model_interp_id.
    exact wf_Phi.
  }

  rewrite H_ctx in dp_syn.
  rewrite H_phi in dp_syn.

  (* Rewrite [interp_ty] only after eliminating the dependent projections. *)
  rewrite (interp_ty_id Func I) in dp_syn.

  assert (H_fun :
    h_derivation I G p_syn (Ty_Arrow (h_make_ctx_ty G) Phi)).
  {
    change (h_derivation I (nil ++ G) p_syn (Ty_Arrow (h_make_ctx_ty G) Phi)).
    eapply (@h_derivation_append Func Pred HFunc HPred 
              I
              nil
              G
              p_syn
              (Ty_Arrow (h_make_ctx_ty G) Phi)).
    - exact dp_syn.
    - exact wfc.
  }

  exists (tm_app p_syn (h_reify_ctx G)).
  constructor.

  eapply HD_App.
  - exact H_fun.
  - apply h_reify_ctx_typing.
    exact wfc.
Defined.   
