
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Equality.
Require Import List.
Import ListNotations.
 
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Fibration.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.

Require Import HyperLogic.Logic.Base.Epsilon_Adjoint.Base_Syntax.
Require Import HyperLogic.Logic.Base.Epsilon_Adjoint.Base_Syntax_Lemmas.
Require Import HyperLogic.Logic.Hyper.Epsilon_Adjoint.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon_Adjoint.Hyper_Syntax_Lemmas.


Require Import HyperLogic.Semantics.Epsilon_Adjoint.Base_Epsilon_Completeness.
Require Import HyperLogic.Semantics.Epsilon_Adjoint.Epsilon_Adjoint_Fibration.
Require Import HyperLogic.Semantics.Epsilon_Adjoint.Base_Epsilon_Completeness.


(** Fiber objects pair formulas with well-formedness derivations. *)
Definition wf_ty {Sign : Type} `{SkolemMapping Sign} (I : b_ty) := 
  { Phi : @h_ty Sign & WellFormed I Phi }.

(** Fiber arrows are closed implication derivations between the underlying formulas. *)
Class hom_fiber {Sign : Type} {SM : SkolemMapping Sign} {I : b_ty} (A B : wf_ty I) : Type := mk_hom_fiber {
  h_tm_of : @h_tm Sign;
  h_deriv_of : h_derivation I [] h_tm_of (Ty_Arrow (projT1 A) (projT1 B))
}.

Arguments h_tm_of {Sign SM I A B} _.
Arguments h_deriv_of {Sign SM I A B} _.

(* Proof terms are identified, making every fiber thin. *)
Definition fiber_equiv {Sign : Type} {SM : SkolemMapping Sign} {I : b_ty} {A B : wf_ty I} 
  (f g : @hom_fiber Sign SM I A B) : Prop := True.

Global Instance fiber_equiv_equivalence {Sign SM I A B} : Equivalence (@fiber_equiv Sign SM I A B).
Proof. constructor; red; intros; unfold fiber_equiv; constructor. Defined.


Definition id_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) (A : wf_ty I) : @hom_fiber Sign SM I A A.
Proof.
  refine (@mk_hom_fiber Sign SM I A A (tm_lam (projT1 A) (tm_var 0)) _).
  apply HD_Lam. 
  apply HD_Var0.
  
  apply AWF_Cons.
  - exact (projT2 A).
  - apply AWF_Nil.
Defined.

Definition comp_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {A B C : wf_ty I} 
  (f : @hom_fiber Sign SM I B C) (g : @hom_fiber Sign SM I A B) : @hom_fiber Sign SM I A C.
Proof.
  refine (@mk_hom_fiber Sign SM I A C 
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


Instance Fiber_SetoidCategory {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) : SetoidCategory.
Proof.
  refine (mk_SetoidCategory 
    (wf_ty I)
    (@hom_fiber Sign SM I) 
    (fun X => @id_fiber Sign SM I X)
    (fun X Y Z f g => @comp_fiber Sign SM I X Y Z f g)
    (fun X Y f g => @fiber_equiv Sign SM I X Y f g)
    _ _ _ _ _).
  
  Unshelve.
  all: intros; unfold fiber_equiv; constructor.
Defined.

Instance Fiber_Thin {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) : Thin (Fiber_SetoidCategory I).
Proof.
  intros x y f g. unfold fiber_equiv; constructor.
Defined.


Definition fiber_unit {Sign : Type} `{SkolemMapping Sign} (I : b_ty) : wf_ty I :=
  existT _ Ty_Unit (WF_Unit I).

Definition fiber_prod {Sign : Type} `{SkolemMapping Sign} {I : b_ty} (Y Z : wf_ty I) : wf_ty I :=
  existT _ (Ty_Prod (projT1 Y) (projT1 Z)) (WF_Prod I (projT1 Y) (projT1 Z) (projT2 Y) (projT2 Z)).

Definition term_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) (X : wf_ty I) : @hom_fiber Sign SM I X (fiber_unit I).
Proof.
  refine (@mk_hom_fiber Sign SM I X (fiber_unit I) (tm_lam (projT1 X) tm_unit) _).
  apply HD_Lam. 
  apply HD_Unit.
  apply AWF_Cons.
  - exact (projT2 X).
  - apply AWF_Nil.
Defined.

Definition prod_map_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X Y Z : wf_ty I} 
  (f : @hom_fiber Sign SM I X Y) (g : @hom_fiber Sign SM I X Z) : @hom_fiber Sign SM I X (fiber_prod Y Z).
Proof.
  refine (@mk_hom_fiber Sign SM I X (fiber_prod Y Z)
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

Definition fst_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X Y : wf_ty I} : @hom_fiber Sign SM I (fiber_prod X Y) X.
Proof.
  refine (@mk_hom_fiber Sign SM I (fiber_prod X Y) X (tm_lam (projT1 (fiber_prod X Y)) (tm_fst (tm_var 0))) _).
  apply HD_Lam. 
  eapply HD_Fst. 
  apply HD_Var0.
  apply AWF_Cons.
  - apply WF_Prod; [exact (projT2 X) | exact (projT2 Y)].
  - apply AWF_Nil.
Defined.

Definition snd_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X Y : wf_ty I} : @hom_fiber Sign SM I (fiber_prod X Y) Y.
Proof.
  refine (@mk_hom_fiber Sign SM I (fiber_prod X Y) Y (tm_lam (projT1 (fiber_prod X Y)) (tm_snd (tm_var 0))) _).
  apply HD_Lam. 
  eapply HD_Snd. 
  apply HD_Var0.
  apply AWF_Cons.
  - apply WF_Prod; [exact (projT2 X) | exact (projT2 Y)].
  - apply AWF_Nil.
Defined.

Instance Fiber_CartesianCategory {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) : CartesianCategory (Fiber_SetoidCategory I).
Proof.
  apply (Build_Thin_CC _ (Fiber_Thin I)
    (fiber_unit I) (fun X => @term_fiber Sign SM I X)
    (fun X Y => fiber_prod X Y) (fun X Y Z f g => @prod_map_fiber Sign SM I X Y Z f g)
    (fun X Y => @fst_fiber Sign SM I X Y)
    (fun X Y => @snd_fiber Sign SM I X Y)
  ).
Defined.


Definition fiber_arrow {Sign : Type} `{SkolemMapping Sign} {I : b_ty} (Y Z : wf_ty I) : wf_ty I :=
  existT _ (Ty_Arrow (projT1 Y) (projT1 Z)) (WF_Arrow I (projT1 Y) (projT1 Z) (projT2 Y) (projT2 Z)).

Definition eval_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {Y Z : wf_ty I} : @hom_fiber Sign SM I (fiber_prod (fiber_arrow Y Z) Y) Z.
Proof.
  refine (@mk_hom_fiber Sign SM I _ _
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

Definition curry_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X Y Z : wf_ty I} (g : @hom_fiber Sign SM I (fiber_prod X Y) Z) : @hom_fiber Sign SM I X (fiber_arrow Y Z).
Proof.
  refine (@mk_hom_fiber Sign SM I X (fiber_arrow Y Z)
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

Instance Fiber_CartesianClosedCategory {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) : CartesianClosedCategory (Fiber_SetoidCategory I).
Proof.
  refine (Build_Thin_CCC _ (Fiber_Thin I)
    (fun Z Y => fiber_arrow Y Z)
    (fun Y Z => @eval_fiber Sign SM I Y Z)
    (fun X Y Z g => @curry_fiber Sign SM I X Y Z g)
  ).
Defined.


Definition fiber_void {Sign : Type} `{SkolemMapping Sign} (I : b_ty) : wf_ty I :=
  existT _ Ty_Void (WF_Void I). 

Definition fiber_sum {Sign : Type} `{SkolemMapping Sign} {I : b_ty} (X Y : wf_ty I) : wf_ty I :=
  existT _ (Ty_Sum (projT1 X) (projT1 Y)) (WF_Sum I (projT1 X) (projT1 Y) (projT2 X) (projT2 Y)).

Definition init_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X : wf_ty I} : @hom_fiber Sign SM I (fiber_void I) X.
Proof.
  refine (@mk_hom_fiber Sign SM I (fiber_void I) X (tm_lam Ty_Void (tm_absurd (projT1 X) (tm_var 0))) _).
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

Definition inl_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X Y : wf_ty I} : @hom_fiber Sign SM I X (fiber_sum X Y).
Proof.
  refine (@mk_hom_fiber Sign SM I X (fiber_sum X Y) (tm_lam (projT1 X) (tm_inl (projT1 Y) (tm_var 0))) _).
  apply HD_Lam. 
  apply HD_Inl. 
  -
    exact (projT2 Y).
  -
    apply HD_Var0.
    apply AWF_Cons. exact (projT2 X). apply AWF_Nil.
Defined.

Definition inr_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X Y : wf_ty I} : @hom_fiber Sign SM I Y (fiber_sum X Y).
Proof.
  refine (@mk_hom_fiber Sign SM I Y (fiber_sum X Y) (tm_lam (projT1 Y) (tm_inr (projT1 X) (tm_var 0))) _).
  apply HD_Lam. 
  apply HD_Inr. 
  -
    exact (projT2 X).
  -
    apply HD_Var0.
    apply AWF_Cons. exact (projT2 Y). apply AWF_Nil.
Defined.

Definition coprod_map_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X Y Z : wf_ty I} 
  (f : @hom_fiber Sign SM I X Z) (g : @hom_fiber Sign SM I Y Z) : @hom_fiber Sign SM I (fiber_sum X Y) Z.
Proof.
  refine (@mk_hom_fiber Sign SM I (fiber_sum X Y) Z
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

Instance Fiber_BiCartesianClosedCategory {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) : BiCartesianClosedCategory (Fiber_CartesianClosedCategory I).
Proof.
  apply (Build_Thin_BiCCC (Fiber_SetoidCategory I) (Fiber_CartesianClosedCategory I) (Fiber_Thin I)
    (fiber_void I) (fun X => @init_fiber Sign SM I X)
    (fun X Y => fiber_sum X Y) (fun X Y => @inl_fiber Sign SM I X Y) (fun X Y => @inr_fiber Sign SM I X Y)
    (fun X Y Z f g => @coprod_map_fiber Sign SM I X Y Z f g)
  ).
Defined.

Require Import Coq.Lists.List.

(** Substitution conversion used by universal elimination and existential introduction. *)
Lemma form_equiv_subst_comm_elim : forall {Sign : Type} `{SkolemMapping Sign}
  {I J A : b_ty} (t : @b_tm Sign) (f : @b_tm Sign) (Phi : @h_ty Sign)
  (dt : base_typing I t J) (df : base_typing J f A),
  WellFormed (b_Prod J A) Phi ->
  form_equiv I
    (form_subst (b_pair b_id (b_comp f t)) (form_subst (b_subst_ext t) Phi))
    (form_subst t (form_subst (b_pair b_id f) Phi)).
Proof.
intros Sign SM I J A t f Phi dt df Hwf.
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


(** Projection substitution conversion used by existential and epsilon elimination. *)
Lemma form_equiv_subst_comm_fst : forall {Sign : Type} `{SkolemMapping Sign}
  {I J A : b_ty} (t : @b_tm Sign) (Chi : @h_ty Sign)
  (dt : base_typing I t J),
  WellFormed J Chi ->
  form_equiv (b_Prod I A)
    (form_subst (b_subst_ext t) (form_subst b_fst Chi))
    (form_subst b_fst (form_subst t Chi)).
Proof.
  intros Sign SM I J A t Chi dt Hwf.
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

Lemma ctx_subst_ext_comm : forall {Sign : Type} `{SkolemMapping Sign} 
  {I J A : b_ty} (t : @b_tm Sign) (dt : base_typing I t J) (G : @h_context Sign),
  All_WellFormed J G ->
  ctx_equiv (b_Prod I A) 
            (ctx_subst (b_subst_ext t) (ctx_subst b_fst G)) 
            (ctx_subst b_fst (ctx_subst t G)).
Proof.
  intros Sign SM I J A t dt G Hwf.
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
Lemma form_wf_subst_inv : forall {Sign : Type} {SM : SkolemMapping Sign} {I J : b_ty} 
  (f : @b_tm Sign) (df : base_typing I f J) (Phi : @h_ty Sign),
  WellFormed I (form_subst f Phi) -> WellFormed J Phi.
Proof.
  intros Sign SM I J f df Phi.
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
Lemma form_wf_fst_inv : forall {Sign : Type} {SM : SkolemMapping Sign} {I A : b_ty} {Phi : @h_ty Sign},
  WellFormed (b_Prod I A) (form_subst b_fst Phi) -> WellFormed I Phi.
Proof.
  intros Sign SM I A Phi Hwf.
  eapply form_wf_subst_inv.
  - eapply BT_Fst.
  - exact Hwf.
Defined.
(** Context well-formedness reflects along the first projection. *)
Lemma ctx_wf_fst_inv : forall {Sign : Type} {SM : SkolemMapping Sign} {I A : b_ty} {G : @h_context Sign},
  All_WellFormed (b_Prod I A) (ctx_subst b_fst G) -> All_WellFormed I G.
Proof.
  intros Sign SM I A G H.
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

Lemma meta_ctx_wf : forall {Sign : Type} {SM : SkolemMapping Sign} {I : b_ty} 
  {G : @h_context Sign} {p : h_tm} {Phi : @h_ty Sign},
  h_derivation I G p Phi -> @All_WellFormed Sign I G.
Proof.
intros Sign SM I G p Phi Hderiv.
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
  -
    exact IHHderiv.
  -
    exact IHHderiv1.
Defined.



(** Every derivation has a well-formed context. *)
Lemma meta_ctx_wf_base : forall {Sign : Type} {SM : SkolemMapping Sign} {I A : b_ty} 
  {G : @h_context Sign} {p : h_tm} {Phi : h_ty},
  h_derivation (b_Prod I A) (ctx_subst b_fst G) p Phi -> All_WellFormed I G.
Proof.
  intros Sign SM I A G p Phi H.
  apply meta_ctx_wf in H.
  apply ctx_wf_fst_inv in H.
  exact H.
Defined.

Lemma meta_type_wf : forall {Sign : Type} {SM : SkolemMapping Sign} {I : b_ty} 
  {G : @h_context Sign} {p : h_tm} {Phi : @h_ty Sign},
  h_derivation I G p Phi -> WellFormed I Phi.
Proof.
  intros Sign SM I G p Phi Hderiv.
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
  -
    eapply wf_subst.
    + eapply BT_Pair. apply BT_Id. apply BT_Const.
    +
      eapply form_wf_subst_inv.
      * eapply BT_Pair.
        -- apply BT_Id.
        -- exact b.
      * exact IHHderiv.
  -
    apply form_wf_fst_inv in IHHderiv2.
    exact IHHderiv2.
Defined.

Lemma meta_all_body_wf : forall {Sign : Type} {SM : SkolemMapping Sign} {I A : b_ty} 
  {G : @h_context Sign} {p : h_tm} {Phi : h_ty},
  h_derivation I G p (Ty_All A Phi) -> WellFormed (b_Prod I A) Phi.
Proof.
intros Sign SM I A G p Phi Hderiv.
  apply meta_type_wf in Hderiv.
  inversion Hderiv; subst.
  assumption.
Defined.

Lemma meta_subst_wf : forall {Sign : Type} {SM : SkolemMapping Sign} {I J : b_ty} 
  (t : @b_tm Sign) (dt : base_typing I t J) (Phi : @h_ty Sign),
  @WellFormed Sign J Phi -> @WellFormed Sign I (form_subst t Phi).
Proof.
intros Sign SM I J t dt Phi Hwf.
  eapply wf_subst.
  - exact dt.
  - exact Hwf.
Defined.

Lemma meta_ex_body_wf : forall {Sign : Type} {SM : SkolemMapping Sign} {I A : b_ty} 
  {G : @h_context Sign} {p : h_tm} {Phi : @h_ty Sign} {f : @b_tm Sign},
  base_typing I f A -> h_derivation I G p (form_subst (b_pair b_id f) Phi) -> @WellFormed Sign (b_Prod I A) Phi.
Proof.
intros Sign SM I A G p Phi f dt Hderiv.
  apply meta_type_wf in Hderiv.
  
  eapply form_wf_subst_inv.
  -
    eapply BT_Pair.
    + apply BT_Id.
    + exact dt.
  -
    exact Hderiv.
Defined.

Lemma meta_ex_body_wf_base : forall {Sign : Type} {SM : SkolemMapping Sign} {I A : b_ty} 
  {G : @h_context Sign} {p : h_tm} {Phi : @h_ty Sign},
  h_derivation I G p (Ty_Ex A Phi) -> @WellFormed Sign (b_Prod I A) Phi.
Proof.
intros Sign SM I A G p Phi Hderiv.
  apply meta_type_wf in Hderiv.
  inversion Hderiv; subst.
  assumption.
Defined.

Lemma meta_ex_elim_chi_wf : forall {Sign : Type} {SM : SkolemMapping Sign} {I A : b_ty} 
  {G : @h_context Sign} {p1 p2 : h_tm} {Phi Chi : @h_ty Sign},
  h_derivation I G p1 (Ty_Ex A Phi) ->
  h_derivation (b_Prod I A) (Phi :: ctx_subst b_fst G) p2 (form_subst b_fst Chi) ->
  @WellFormed Sign I Chi.
Proof.
intros Sign SM I A G p1 p2 Phi Chi H1 H2.
  apply meta_type_wf in H2.
  
  eapply form_wf_fst_inv.
  exact H2.
Defined.


Lemma meta_eps_body_wf : forall {Sign : Type} {SM : SkolemMapping Sign} {I A : b_ty} 
  {G : @h_context Sign} {p : h_tm} {Phi : @h_ty Sign} {f : @b_tm Sign},
  base_typing I f A -> h_derivation I G p (Phi .[ f ]) -> @WellFormed Sign (b_Prod I A) Phi.
Proof.
intros Sign SM I A G p Phi f dt Hderiv.
  apply meta_type_wf in Hderiv.
  
  eapply form_wf_subst_inv.
  - eapply BT_Pair.
    + apply BT_Id.
    + exact dt.
  - exact Hderiv.
Defined.

(** Syntactic Beck-Chevalley conversion for epsilon instances. *)
Lemma meta_eps_bc : forall {Sign : Type} {SM : SkolemMapping Sign} {I J A : b_ty} 
  (t : @b_tm Sign) (dt : base_typing I t J) (Phi : @h_ty Sign),
  @WellFormed Sign (b_Prod J A) Phi ->
  form_equiv I 
    ((form_subst (b_subst_ext t) Phi) .[ ε A, form_subst (b_subst_ext t) Phi ])
    (form_subst t (Phi .[ ε A, Phi ])).
Proof.
  intros Sign SM I J A t dt Phi wf.
  eapply FE_Eps_BC.
  - exact dt.
  - exact wf.
Defined.

Lemma meta_eps_elim_body_wf : forall {Sign : Type} {SM : SkolemMapping Sign} {I A : b_ty} 
  {G : @h_context Sign} {p : h_tm} {Phi : @h_ty Sign},
  h_derivation I G p (Phi .[ ε A, Phi ]) -> @WellFormed Sign (b_Prod I A) Phi.
Proof.
intros Sign SM I A G p Phi Hderiv.
  apply meta_type_wf in Hderiv.
  
  eapply form_wf_subst_inv.
  -
    eapply BT_Pair.
    + apply BT_Id.
    + eapply BT_Const.
  -
    exact Hderiv.
Defined.

Lemma meta_eps_elim_chi_wf : forall {Sign : Type} {SM : SkolemMapping Sign} {I A : b_ty} 
  {G : @h_context Sign} {p1 p2 : h_tm} {Phi Chi : @h_ty Sign},
  h_derivation I G p1 (Phi .[ ε A, Phi ]) ->
  h_derivation (b_Prod I A) (Phi :: ctx_subst b_fst G) p2 (form_subst b_fst Chi) ->
  @WellFormed Sign I Chi.
Proof.
intros Sign SM I A G p1 p2 Phi Chi H1 H2.
  apply meta_type_wf in H2.
  
  eapply form_wf_fst_inv.
  exact H2.
Defined.

Lemma ctx_wf_subst : forall {Sign : Type} {SM : SkolemMapping Sign} {I J : b_ty} 
  (t : @b_tm Sign) (dt : base_typing I t J) (G : h_context),
  All_WellFormed J G -> All_WellFormed I (ctx_subst t G).
Proof.
  intros Sign SM I J t dt G Hwf.
  induction Hwf.
  -
    simpl. apply AWF_Nil.
  -
    simpl. apply AWF_Cons.
    + eapply wf_subst; eassumption.
    + exact IHHwf.
Defined.

Lemma h_derivation_subst_general : forall {Sign : Type} {SM : SkolemMapping Sign} 
  {I J : b_ty} (t : @b_tm Sign) (dt : base_typing I t J) (G : h_context) (Phi : h_ty) (p : h_tm),
  h_derivation J G p Phi -> 
  h_derivation I (ctx_subst t G) (tm_subst t p) (form_subst t Phi).
Proof.
  intros Sign SM I J t dt G Phi p Hderiv.
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


  -
    simpl. eapply HD_Conv.
    + eapply HD_Eps_Intro.
      * eapply BT_Comp. eassumption. exact dt0.
      * eapply HD_Conv. 
        -- apply IHHderiv. exact dt0.
        --
           eapply FE_Sym. 
           eapply form_equiv_subst_comm_elim.
           ++ exact dt0.
           ++ exact b.
           ++ eapply meta_eps_body_wf. exact b. exact Hderiv.
    +
      eapply meta_eps_bc.
      * exact dt0.
      * eapply meta_eps_body_wf. exact b. exact Hderiv.

  -
    simpl. eapply HD_Eps_Elim.
    + eapply HD_Conv.
      * apply IHHderiv1. exact dt0.
      *
        eapply FE_Sym. 
        eapply meta_eps_bc.
        -- exact dt0.
        -- eapply meta_eps_elim_body_wf. exact Hderiv1.
    + eapply HD_Conv.
      * eapply HD_Ctx_Conv.
        -- apply CEq_Cons.
           ++ apply FE_Refl. 
              eapply meta_subst_wf. 
              ** eapply typing_subst_ext. exact dt0.
              ** eapply meta_eps_elim_body_wf. exact Hderiv1.
           ++
              eapply ctx_subst_ext_comm. 
              ** exact dt0.
              ** eapply meta_ctx_wf. exact Hderiv1.
        -- apply IHHderiv2. apply typing_subst_ext. exact dt0.
      *
        eapply form_equiv_subst_comm_fst. 
        -- exact dt0.
        -- eapply meta_eps_elim_chi_wf. exact Hderiv1. exact Hderiv2.
Defined.


Definition subst_functor_obj {Sign : Type} {SM : SkolemMapping Sign} 
  {I J : b_ty} (t : @b_tm Sign) (dt : @base_typing Sign I t J) 
  (Phi : @wf_ty Sign SM J) : @wf_ty Sign SM I.
Proof.
  destruct Phi as [phi Hwf].
  
  exists (form_subst t phi).
  
  eapply meta_subst_wf.
  - exact dt.
  - exact Hwf.
Defined.

Definition subst_functor_hom {Sign : Type} {SM : SkolemMapping Sign} 
  {I J : b_ty} (t : @b_tm Sign) (dt : @base_typing Sign I t J) 
  (Phi Psi : @wf_ty Sign SM J) 
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


Instance subst_functor {Sign : Type} {SM : SkolemMapping Sign} 
  {I J : b_ty} (t : @b_tm Sign) (dt : @base_typing Sign I t J) : 
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


Definition ex_functor_obj {Sign : Type} {SM : SkolemMapping Sign} 
  (I A : b_ty) (Phi : @wf_ty Sign SM (b_Prod I A)) : @wf_ty Sign SM I.
Proof. 
  destruct Phi as [phi Hwf].
  exists (Ty_Ex A phi).
  apply WF_Ex. exact Hwf.
Defined.

Definition ex_subst_unit {Sign : Type} `{SkolemMapping Sign} (I A : b_ty) (Y : @wf_ty Sign _ (b_Prod I A)) : 
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

Definition ex_subst_left_adj_mor {Sign : Type} `{SkolemMapping Sign} (I A : b_ty) 
  (Y : @wf_ty Sign _ (b_Prod I A)) (X : @wf_ty Sign _ I)
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

Instance TermModel_Pullback_IsRightAdjoint {Sign : Type} `{SkolemMapping Sign} (I A : b_ty) :
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


Definition all_functor_obj {Sign : Type} `{SkolemMapping Sign} (I A : b_ty) 
  (Phi : @wf_ty Sign _ (b_Prod I A)) : @wf_ty Sign _ I.
Proof. 
  destruct Phi as [phi Hwf].
  exists (Ty_All A phi).
  apply WF_All. exact Hwf.
Defined.

Definition all_subst_counit {Sign : Type} `{SkolemMapping Sign} (I A : b_ty) 
  (X : @wf_ty Sign _ (b_Prod I A)) : 
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

Definition all_subst_right_adj_mor {Sign : Type} `{SkolemMapping Sign} (I A : b_ty) 
  (Y : @wf_ty Sign _ I) (X : @wf_ty Sign _ (b_Prod I A))
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
 

Instance TermModel_Pullback_IsLeftAdjoint {Sign : Type} `{SkolemMapping Sign} (I A : b_ty) :
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



Lemma form_equiv_to_iso {Sign : Type} `{SkolemMapping Sign} (I : b_ty) 
  (X Y : @wf_ty Sign _ I) :
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



Instance TermModel_GoodFibration {Sign : Type} {SM : SkolemMapping Sign} : 
  GoodFibration (Base_SetoidCategory Sign).
Proof.
  refine (@mk_GoodFibration 
    (Base_SetoidCategory Sign) 
    (Base_CartesianCategory Sign)
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


  
Definition term_model_i_atom {Sign : Type} {SM : SkolemMapping Sign} 
  (p : nat) (t : @b_tm Sign) (I : b_ty) : 
  wf_ty (@interp_ty (Base_SetoidCategory Sign) 
                    (Base_CartesianCategory Sign) 
                    (Base_TwoSortCategory Sign) I).
Proof.
  rewrite (@interp_ty_id Sign I).
  
  destruct (@decide_base_typing Sign I t) as [[A dt] | Hbad].
  -
    exact (@existT (@h_ty Sign) 
                  (fun Phi => @WellFormed Sign I Phi) 
                  (@Ty_Atom Sign p t) 
                  (@WF_Atom Sign I p t A dt)).
  -
    exact (@existT (@h_ty Sign) 
                  (fun Phi => @WellFormed Sign I Phi) 
                  (@Ty_Unit Sign) 
                  (@WF_Unit Sign I)).
Defined.

(** Helpers for dependent transports in the syntactic model. *)

(* Reindexing commutes with projection to the underlying formula. *)
Lemma projT1_pullback : forall {Sign : Type} {SM : SkolemMapping Sign} {I J : @obj (Base_SetoidCategory Sign)} 
  (f : @hom (Base_SetoidCategory Sign) I J) (Phi : wf_ty J),
  projT1 (@fobj _ _ (Pullback f) Phi) = form_subst (tm_of f) (projT1 Phi).
Proof.
  intros. destruct Phi. reflexivity.
Defined.

(* Dependent transport does not change the underlying formula. *)
Lemma projT1_eq_rect_r_wf : forall {Sign : Type} {SM : SkolemMapping Sign} {I J : @obj (Base_SetoidCategory Sign)} 
  (e : I = J) (Phi : wf_ty J),
  projT1 (eq_rect_r (fun o : @obj (Base_SetoidCategory Sign) => wf_ty o) Phi e) = projT1 Phi.
Proof.
  intros. destruct e. reflexivity.
Defined.


Instance TermModel_EpsilonHyperModel {Sign : Type} {SM : SkolemMapping Sign} : 
  @EpsilonHyperModel Sign
    (Base_SetoidCategory Sign)
    (Base_CartesianCategory Sign)
    (Base_TwoSortCategory Sign)
    (Base_SyntacticEpsilonModel Sign)
    TermModel_GoodFibration.
Proof.
  refine (@Build_EpsilonHyperModel Sign 
    (Base_SetoidCategory Sign) 
    (Base_CartesianCategory Sign) 
    (Base_TwoSortCategory Sign) 
    (Base_SyntacticEpsilonModel Sign)
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
    
    rewrite (@interp_tm_term Sign I A f df).
    
    cbn [projT1].
    
    destruct (decide_base_typing A t) as [[B dt_t] | Hbad_t].
    + destruct (decide_base_typing I (b_comp t f)) as [[B' dcomp] | Hbad_comp].
      *
        rewrite (@interp_ty_id Sign I).
        apply FE_Refl. eapply WF_Atom. exact dcomp.
      * destruct (Hbad_comp B (BT_Comp dt_t df)).
    + destruct (decide_base_typing I (b_comp t f)) as [[B' dcomp] | Hbad_comp].
      *
        inversion dcomp; subst.
        match goal with
        | [ Ht : base_typing ?Mid t _, Hf : base_typing _ f ?Mid |- _ ] =>
          assert (H_eq : Mid = A) by (eapply base_typing_unique; [exact Hf | exact df]);
          subst Mid;
          destruct (Hbad_t B' Ht)
        end.
      *
        rewrite (@interp_ty_id Sign I).
        apply FE_Refl. apply WF_Unit.

  -
    intros p I A t1 t2 d1 d2 Heq.
    apply form_equiv_to_iso.
    unfold term_model_i_atom.
    
    rewrite projT1_eq_rect_r_wf.
    rewrite projT1_eq_rect_r_wf.
    
    cbn [projT1].
    
    destruct (decide_base_typing I t1) as [[B1 dt1] | Hbad1].
    + destruct (decide_base_typing I t2) as [[B2 dt2] | Hbad2].
      * rewrite (@interp_ty_id Sign I).
        eapply FE_Atom. exact Heq.
      * destruct (Hbad2 A d2).
    + destruct (Hbad1 A d1).
Defined.


Lemma projT1_ex_functor_obj : forall {Sign : Type} `{SkolemMapping Sign} (I A : b_ty) (Y : wf_ty (b_Prod I A)),
  projT1 (ex_functor_obj I A Y) = Ty_Ex A (projT1 Y).
Proof. intros. destruct Y. reflexivity. Defined.

(** Well-formed formulas interpret to their own syntactic representatives. *)

Lemma term_model_interp_id : forall {Sign : Type} {SM : SkolemMapping Sign} (ctx : b_ty) (X : @h_ty Sign), 
  WellFormed ctx X -> (* Excludes the ill-typed atom fallback. *)
  projT1 (@interp_h_ty Sign 
            (Base_SetoidCategory Sign) 
            (Base_CartesianCategory Sign) 
            (Base_TwoSortCategory Sign) 
            (Base_SyntacticEpsilonModel Sign) 
            TermModel_GoodFibration 
            TermModel_EpsilonHyperModel 
            ctx X) = X.
Proof. 
  intros Sign SM ctx X Hwf.
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
      simpl. reflexivity.
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
    apply (@interp_ty_id Sign b).
    
  -
    inversion Hwf; subst.
    match goal with
    | [ H : WellFormed (b_Prod ctx b) X |- _ ] => specialize (IHX (b_Prod ctx b) H)
    end.
    destruct (interp_h_ty (b_Prod ctx b) X) as [phi Hwf_phi] in *.
    simpl in IHX. subst phi.
    
    cbn [ex_functor_obj projT1].
    
    f_equal.
    apply (@interp_ty_id Sign b).
Defined.



Instance TermModel_AdjointEpsilonFibration {Sign : Type} {SM : SkolemMapping Sign} : 
  @AdjointEpsilonFibration Sign SM 
    (Base_SetoidCategory Sign) 
    (Base_CartesianCategory Sign) 
    (Base_TwoSortCategory Sign) 
    (Base_SyntacticEpsilonModel Sign) 
    TermModel_GoodFibration 
    TermModel_EpsilonHyperModel.
Proof.
  constructor.

-
    intros I A Phi Hwf_Phi.
    
    apply form_equiv_to_iso.
    
    cbn [left_adj_obj pullback_has_left_adjoint TermModel_GoodFibration TermModel_Pullback_IsRightAdjoint].
    
    (* Destruct both sigma interpretations to expose their underlying formulas. *)
    destruct (interp_h_ty (b_Prod I A) Phi) as [phi Hwf_phi] eqn:Heq_phi.
    destruct (interp_h_ty I (Phi .[ ε A, Phi ])) as [psi Hwf_psi] eqn:Heq_psi.
    cbn [ex_functor_obj projT1].
    
    change (_ (Base_SetoidCategory Sign) (Base_CartesianCategory Sign) (Base_TwoSortCategory Sign) I) 
      with (@interp_ty (Base_SetoidCategory Sign) (Base_CartesianCategory Sign) (Base_TwoSortCategory Sign) I).
    change (_ (Base_SetoidCategory Sign) (Base_CartesianCategory Sign) (Base_TwoSortCategory Sign) A) 
      with (@interp_ty (Base_SetoidCategory Sign) (Base_CartesianCategory Sign) (Base_TwoSortCategory Sign) A).
      
    assert (H_phi : phi = Phi).
    {
      generalize (term_model_interp_id (b_Prod I A) Phi Hwf_Phi).
      rewrite Heq_phi. cbn [projT1]. auto.
    }
    subst phi.
    
    assert (H_psi : psi = Phi .[ ε A, Phi ]).
    {
      assert (Hwf_Psi : WellFormed I (Phi .[ ε A, Phi ])).
      {
        eapply wf_subst.
        - eapply BT_Pair. apply BT_Id. apply BT_Const.
        - exact Hwf_Phi.
      }
      generalize (term_model_interp_id I (Phi .[ ε A, Phi ]) Hwf_Psi).
      rewrite Heq_psi. cbn [projT1]. auto.
    }
    subst psi.
    
    rewrite (@interp_ty_id Sign I).
    rewrite (@interp_ty_id Sign A).
     
    apply FE_Eps_Adjoint_Iso.  
    exact Hwf_Phi.  
-
    intros I A Phi Psi Hwf_Phi Hwf_Psi H_iso.
    destruct H_iso as [f g Hfg Hgf].
    
    pose (L := LeftAdjointFunctor 
                 (Pullback (@interp_tm Sign _ _ _
                              (Base_SyntacticEpsilonModel Sign)
                              _ _ _
                              (BT_Fst (Sign:=Sign) (A:=I) (B:=A)))) 
                 pullback_has_left_adjoint).

    match type of f with
    | hom ?dPhi ?dPsi =>
        pose (DomPhi := dPhi);
        pose (DomPsi := dPsi)
    end.
    
    match goal with
    | |- ?cPhi ≅O ?cPsi =>
        pose (CodPhi := cPhi);
        pose (CodPsi := cPsi)
    end.

    assert (Iso_Phi : fobj L DomPhi ≅O CodPhi). 
    {
      apply form_equiv_to_iso.

      unfold L.
      destruct DomPhi as [phi Hwf_phi] eqn:Heq_phi.
      destruct CodPhi as [psi Hwf_psi] eqn:Heq_psi.
      
      unfold fobj, LeftAdjointFunctor.

      cbn [left_adj_obj
           pullback_has_left_adjoint
           TermModel_GoodFibration
           TermModel_Pullback_IsRightAdjoint].

      cbn [ex_functor_obj projT1].

      change (_ (Base_SetoidCategory Sign)
                (Base_CartesianCategory Sign)
                (Base_TwoSortCategory Sign)
                I)
        with (@interp_ty
                (Base_SetoidCategory Sign)
                (Base_CartesianCategory Sign)
                (Base_TwoSortCategory Sign)
                I).

      change (_ (Base_SetoidCategory Sign)
                (Base_CartesianCategory Sign)
                (Base_TwoSortCategory Sign)
                A)
        with (@interp_ty
                (Base_SetoidCategory Sign)
                (Base_CartesianCategory Sign)
                (Base_TwoSortCategory Sign)
                A).

           assert (H_phi : phi = Phi).
      {
        pose proof (term_model_interp_id (b_Prod I A) Phi Hwf_Phi) as H.
        unfold DomPhi in Heq_phi.
        rewrite Heq_phi in H.
        cbn [projT1] in H.
        exact H.
      }
      subst phi.
      
      assert (H_psi : psi = Phi .[ ε A, Phi ]).
      {
        assert (Hwf_EpsPhi : WellFormed I (Phi .[ ε A, Phi ])).
        {
          eapply wf_subst.
          - eapply BT_Pair.
            + apply BT_Id.
            + apply BT_Const.
          - exact Hwf_Phi.
        }

        pose proof (term_model_interp_id I (Phi .[ ε A, Phi ]) Hwf_EpsPhi) as H.
        unfold CodPhi in Heq_psi.
        rewrite Heq_psi in H.
        cbn [projT1] in H.
        exact H.
      }
      subst psi.

      rewrite (@interp_ty_id Sign I).
      rewrite (@interp_ty_id Sign A).

      apply FE_Eps_Adjoint_Iso.
      exact Hwf_Phi.
    }

    assert (Iso_Psi : fobj L DomPsi ≅O CodPsi).
    {
      apply form_equiv_to_iso.

      unfold L.
      destruct DomPsi as [psi_in Hwf_psi_in] eqn:Heq_psi_in.
      destruct CodPsi as [psi_out Hwf_psi_out] eqn:Heq_psi_out.
      
      unfold fobj, LeftAdjointFunctor.

      cbn [left_adj_obj
           pullback_has_left_adjoint
           TermModel_GoodFibration
           TermModel_Pullback_IsRightAdjoint].

      cbn [ex_functor_obj projT1].

      change (_ (Base_SetoidCategory Sign)
                (Base_CartesianCategory Sign)
                (Base_TwoSortCategory Sign)
                I)
        with (@interp_ty
                (Base_SetoidCategory Sign)
                (Base_CartesianCategory Sign)
                (Base_TwoSortCategory Sign)
                I).

      change (_ (Base_SetoidCategory Sign)
                (Base_CartesianCategory Sign)
                (Base_TwoSortCategory Sign)
                A)
        with (@interp_ty
                (Base_SetoidCategory Sign)
                (Base_CartesianCategory Sign)
                (Base_TwoSortCategory Sign)
                A).

           assert (H_psi_in : psi_in = Psi).
      {
        pose proof (term_model_interp_id (b_Prod I A) Psi Hwf_Psi) as H.
        unfold DomPsi in Heq_psi_in.
        rewrite Heq_psi_in in H.
        cbn [projT1] in H.
        exact H.
      }
      subst psi_in.
      
      assert (H_psi_out : psi_out = Psi .[ ε A, Psi ]).
      {
        assert (Hwf_EpsPsi : WellFormed I (Psi .[ ε A, Psi ])).
        {
          eapply wf_subst.
          - eapply BT_Pair.
            + apply BT_Id.
            + apply BT_Const.
          - exact Hwf_Psi.
        }

        pose proof (term_model_interp_id I (Psi .[ ε A, Psi ]) Hwf_EpsPsi) as H.
        unfold CodPsi in Heq_psi_out.
        rewrite Heq_psi_out in H.
        cbn [projT1] in H.
        exact H.
      }
      subst psi_out.

      rewrite (@interp_ty_id Sign I).
      rewrite (@interp_ty_id Sign A).

      apply FE_Eps_Adjoint_Iso.
      exact Hwf_Psi.
    }

    destruct Iso_Phi as [to_Phi from_Phi _ _].
    destruct Iso_Psi as [to_Psi from_Psi _ _].

    change (CodPhi ≅O CodPsi).

    refine {|
      iso_to :=
        @compose (Fiber (interp_ty I))
          CodPhi
          (fobj L DomPsi)
          CodPsi
          to_Psi
          (@compose (Fiber (interp_ty I))
             CodPhi
             (fobj L DomPhi)
             (fobj L DomPsi)
             (@fmap _ _ L DomPhi DomPsi f)
             from_Phi);

      iso_from :=
        @compose (Fiber (interp_ty I))
          CodPsi
          (fobj L DomPhi)
          CodPhi
          to_Phi
          (@compose (Fiber (interp_ty I))
             CodPsi
             (fobj L DomPsi)
             (fobj L DomPhi)
             (@fmap _ _ L DomPsi DomPhi g)
             from_Psi)
    |}.
    + unfold fiber_equiv; constructor.
    + unfold fiber_equiv; constructor.
Defined.

(** Completeness theorems. *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

Fixpoint h_lift {Sign : Type} (shift cutoff : nat) (p : @h_tm Sign) : @h_tm Sign :=
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

  | tm_eps_intro t p' =>
      tm_eps_intro t (h_lift shift cutoff p')

  | tm_eps_elim p1 p2 =>
      tm_eps_elim
        (h_lift shift cutoff p1)
        (h_lift shift (Datatypes.S cutoff) p2)
  end.
  
Fixpoint h_insert_at {Sign : Type}
  (n : nat) (Psi : @h_ty Sign) (G : @h_context Sign) : @h_context Sign :=
  match n, G with
  | Datatypes.O, _ => Psi :: G
  | Datatypes.S n', nil => Psi :: nil
  | Datatypes.S n', Phi :: G' => Phi :: h_insert_at n' Psi G'
  end.
  
Lemma All_WellFormed_insert : forall {Sign : Type} {SM : SkolemMapping Sign}
  (I : b_ty) (G : @h_context Sign) (Psi : @h_ty Sign) (n : nat),
  WellFormed I Psi ->
  All_WellFormed I G ->
  All_WellFormed I (h_insert_at n Psi G).
Proof.
  intros Sign SM I G Psi n HwfPsi HwfG.
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

Lemma ctx_subst_insert : forall {Sign : Type}
  (f : @b_tm Sign) (n : nat) (Psi : @h_ty Sign) (G : @h_context Sign),
  ctx_subst f (h_insert_at n Psi G)
  =
  h_insert_at n (form_subst f Psi) (ctx_subst f G).
Proof.
  intros Sign f n Psi G.
  revert n.
  induction G as [|Phi G IH]; intros n; destruct n; simpl; auto.
  rewrite IH.
  reflexivity.
Defined.

Lemma ctx_equiv_insert : forall {Sign : Type} {SM : SkolemMapping Sign}
  (I : b_ty) (G1 G2 : @h_context Sign) (Psi : @h_ty Sign) (n : nat),
  WellFormed I Psi ->
  ctx_equiv I G1 G2 ->
  ctx_equiv I (h_insert_at n Psi G1) (h_insert_at n Psi G2).
Proof.
  intros Sign SM I G1 G2 Psi n HwfPsi Heq.
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

Theorem hd_weakening_general : forall {Sign : Type} {SM : SkolemMapping Sign}
  (I : b_ty) (G : @h_context Sign) (p : @h_tm Sign) (Phi Psi : @h_ty Sign) (n : nat),
  WellFormed I Psi ->
  h_derivation I G p Phi ->
  h_derivation I (h_insert_at n Psi G) (h_lift 1 n p) Phi.
Proof.
  intros Sign SM I G p Phi Psi n HwfPsi d.
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
        -- replace (@tm_var Sign (Datatypes.S n))
             with (@h_lift Sign 1 n0 (@tm_var Sign n)).
           ++ apply IHd. exact Hwf0.
           ++ simpl. rewrite Heq. reflexivity.

      * apply HD_VarS.
        -- exact w.
        -- replace (@tm_var Sign n)
             with (@h_lift Sign 1 n0 (@tm_var Sign n)).
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
                (@h_lift Sign 1 (Datatypes.S n0) p1)
                Chi).
      apply IHd2.
      exact Hwf0.

    + change (h_derivation I
                (h_insert_at (Datatypes.S n0) Psi0 (Psi :: G))
                (@h_lift Sign 1 (Datatypes.S n0) p2)
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
                (@h_lift Sign 1 (Datatypes.S n0) p2)
                (form_subst b_fst Chi)).

      apply IHd2.

      eapply wf_subst.
      * apply BT_Fst.
      * exact Hwf0.

  -
    eapply HD_Eps_Intro.
    + exact b.
    + apply IHd. exact Hwf0.

   -
    eapply HD_Eps_Elim.
    + apply IHd1.
      exact Hwf0.

    + simpl.
      rewrite ctx_subst_insert.

      change (h_derivation (b_Prod I A)
                (h_insert_at
                   (Datatypes.S n0)
                   (form_subst b_fst Psi0)
                   (Phi :: ctx_subst b_fst G))
                (@h_lift Sign 1 (Datatypes.S n0) p2)
                (form_subst b_fst Chi)).

      apply IHd2.

      eapply wf_subst.
      * apply BT_Fst.
      * exact Hwf0.
Defined.

Lemma hd_weakening : forall {Sign : Type} {SM : SkolemMapping Sign}
  (I : b_ty) (G : @h_context Sign) (A : @h_ty Sign) (p : @h_tm Sign) (Phi : @h_ty Sign),
  All_WellFormed I (A :: G) ->
  h_derivation I G p Phi ->
  h_derivation I (A :: G) (h_lift 1 0 p) Phi.
Proof.
  intros Sign SM I G A p Phi HwfCtx d.
  assert (HwfA : WellFormed I A).
  {
    inversion HwfCtx; subst.
    assumption.
  }
  exact (hd_weakening_general I G p Phi A 0 HwfA d).
Defined.

Fixpoint h_make_ctx_ty {Sign : Type} (G : @h_context Sign) : @h_ty Sign :=
  match G with
  | nil => Ty_Unit
  | A :: G' => Ty_Prod (h_make_ctx_ty G') A
  end.

Fixpoint h_reify_ctx {Sign : Type} (G : @h_context Sign) : @h_tm Sign :=
  match G with
  | nil => tm_unit
  | A :: G' => tm_pair (h_lift 1 0 (h_reify_ctx G')) (tm_var 0)
  end.
  
Lemma h_reify_ctx_typing : forall {Sign : Type} {SM : SkolemMapping Sign}
  (I : b_ty) (G : @h_context Sign),
  All_WellFormed I G ->
  h_derivation I G (h_reify_ctx G) (h_make_ctx_ty G).
Proof.
  intros Sign SM I G HwfG.
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

Lemma term_model_interp_ctx_id : forall {Sign : Type} {SM : SkolemMapping Sign}
  (I : b_ty) (G : @h_context Sign),
  All_WellFormed I G ->
  projT1
    (@interp_h_ctx Sign
       (Base_SetoidCategory Sign)
       (Base_CartesianCategory Sign)
       (Base_TwoSortCategory Sign)
       (Base_SyntacticEpsilonModel Sign)
       TermModel_GoodFibration
       TermModel_EpsilonHyperModel
       I G)
  = h_make_ctx_ty G.
Proof.
  intros Sign SM I G HwfG.
  induction HwfG as [|Phi G HwfPhi HwfG IH]; simpl.
  - reflexivity.
  - cbn [projT1].
    f_equal.
    + exact IH.
    + apply term_model_interp_id.
      exact HwfPhi.
Defined.

Theorem epsilon_adjoint_completeness_inhabitational_gen :
  forall {Sign : Type} {SM : SkolemMapping Sign}
         {I : b_ty} {G : @h_context Sign} {Phi : @h_ty Sign}
         (wfc : All_WellFormed I G)
         (wf_Phi : WellFormed I Phi),
  (forall (C : SetoidCategory) (CC : CartesianCategory C)
          (TSC : TwoSortCategory C)
          (BEM : @BaseEpsilonModel Sign C CC TSC)
          (GF : GoodFibration C)
          (EHM : @EpsilonHyperModel Sign C CC TSC BEM GF)
          (AEF : @AdjointEpsilonFibration Sign SM C CC TSC BEM GF EHM),
     inhabited
       (@hom (Fiber (interp_ty I))
             (@interp_h_ctx Sign C CC TSC BEM GF EHM I G)
             (@interp_h_ty  Sign C CC TSC BEM GF EHM I Phi))) ->
  exists (p : @h_tm Sign),
    inhabited (h_derivation I G p Phi).
Proof.
  intros Sign SM I G Phi wfc wf_Phi H_univ.

  pose proof
    (H_univ
       (Base_SetoidCategory Sign)
       (Base_CartesianCategory Sign)
       (Base_TwoSortCategory Sign)
       (Base_SyntacticEpsilonModel Sign)
       TermModel_GoodFibration
       TermModel_EpsilonHyperModel
       TermModel_AdjointEpsilonFibration) as H_term.

  destruct H_term as [m_syn].
  destruct m_syn as [p_syn dp_syn].

  assert (H_ctx :
    projT1
      (@interp_h_ctx Sign
         (Base_SetoidCategory Sign)
         (Base_CartesianCategory Sign)
         (Base_TwoSortCategory Sign)
         (Base_SyntacticEpsilonModel Sign)
         TermModel_GoodFibration
         TermModel_EpsilonHyperModel
         I G)
    = h_make_ctx_ty G).
  {
    apply term_model_interp_ctx_id.
    exact wfc.
  }

  assert (H_phi :
    projT1
      (@interp_h_ty Sign
         (Base_SetoidCategory Sign)
         (Base_CartesianCategory Sign)
         (Base_TwoSortCategory Sign)
         (Base_SyntacticEpsilonModel Sign)
         TermModel_GoodFibration
         TermModel_EpsilonHyperModel
         I Phi)
    = Phi).
  {
    apply term_model_interp_id.
    exact wf_Phi.
  }

  rewrite H_ctx in dp_syn.
  rewrite H_phi in dp_syn.

  (* Rewrite [interp_ty] only after eliminating the dependent projections. *)
  rewrite (@interp_ty_id Sign I) in dp_syn.

  assert (H_fun :
    h_derivation I G p_syn (Ty_Arrow (h_make_ctx_ty G) Phi)).
  {
    change (h_derivation I (nil ++ G) p_syn (Ty_Arrow (h_make_ctx_ty G) Phi)).
    eapply (@h_derivation_append Sign SM
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
