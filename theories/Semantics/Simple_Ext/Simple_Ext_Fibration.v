
Require Import Coq.Classes.Morphisms.
Require Import List. 
Import ListNotations.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import HyperLogic.Cat.Fibration.

Require Import HyperLogic.Logic.Base.Simple_Ext.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple_Ext.Hyper_Syntax.


Fixpoint interp_ty {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
  (A : b_ty) : @obj C :=
  match A with
  | b_Unit => terminal
  | b_S => @S C CC TSC
  | b_Prod A B => prod (interp_ty A) (interp_ty B)
  end.

Class BaseSignatureModel {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} := {
  i_const : forall (I A : b_ty) (s : Sign), @hom C (interp_ty I) (interp_ty A)
}.

Fixpoint interp_tm {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} 
  {TSC : TwoSortCategory C} {BEM : BaseSignatureModel} 
  {I A : b_ty} {f : @b_tm Sign} (d : @base_typing Sign I f A) 
  : @hom C (interp_ty I) (interp_ty A) :=
  match d in (base_typing I' f' A') return (@hom C (interp_ty I') (interp_ty A')) with
  | @BT_Id _ A' => @id C (interp_ty A')
  | @BT_Comp _ A' B' C' g' f' dg df => @compose C (interp_ty A') (interp_ty B') (interp_ty C') (interp_tm dg) (interp_tm df)
  | @BT_Unit _ A' => @terminal_map C CC (interp_ty A')
  | @BT_Pair _ A' B' C' f' g' df dg => @prod_map C CC (interp_ty A') (interp_ty B') (interp_ty C') (interp_tm df) (interp_tm dg)
  | @BT_Fst _ A' B' => @prod_fst C CC (interp_ty A') (interp_ty B')
  | @BT_Snd _ A' B' => @prod_snd C CC (interp_ty A') (interp_ty B')
  | @BT_Const _ I' A' s => i_const I' A' s
  end.
  
Class CoherentBaseModel 
  {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} 
  {TSC : TwoSortCategory C} {BEM : @BaseSignatureModel Sign C CC TSC} := {
  
  interp_coh : forall {A B : b_ty} {f : @b_tm Sign} (d1 d2 : base_typing A f B), 
    interp_tm d1 ≅ interp_tm d2
}.


Class HyperModel 
  {Sign : Type} 
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
  {BSM : BaseSignatureModel} 
  {GF : GoodFibration C} (SGF : StrictGoodFibration C GF) := {
  
  i_atom : forall (p : nat) (t : @b_tm Sign) (I A : b_ty) (dt : base_typing I t A), @obj (Fiber (interp_ty I)) ;
  
  i_atom_pb : forall (p : nat) (t : @b_tm Sign) (I J A : b_ty) (f : @b_tm Sign) 
                     (df : base_typing I f A) (dt : base_typing A t J),
      @fobj _ _ (Pullback (interp_tm df)) (i_atom p t A J dt) ≅O i_atom p (b_comp t f) I J (BT_Comp dt df);
      
  base_model_sound : forall (I J : b_ty) (f g : @b_tm Sign) 
                            (df : base_typing I f J) (dg : base_typing I g J),
      base_equiv df dg -> hom_equiv (interp_tm df) (interp_tm dg);

  i_atom_cong_global : forall (p : nat) (t1 t2 : @b_tm Sign) (I A : b_ty) 
                              (d1 : base_typing I t1 A) (d2 : base_typing I t2 A),
                       base_equiv d1 d2 -> i_atom p t1 I A d1 ≅O i_atom p t2 I A d2
}.


Fixpoint interp_h_ty 
  {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {BSM : BaseSignatureModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} 
  {HM : HyperModel SGF}
  {I : b_ty} {Phi : @h_ty Sign} (wf : WellFormed I Phi) : @obj (Fiber (interp_ty I)) :=
  
  (* Dependent matching replaces [Phi] by the formula recovered from the derivation. *)
  match wf in (WellFormed I' Phi') return (@obj (Fiber (interp_ty I'))) with
  | WF_Unit I' => terminal
  | WF_Void I' => initial
  | WF_Prod I' A B wfA wfB => prod (interp_h_ty wfA) (interp_h_ty wfB)
  | WF_Sum I' A B wfA wfB => coprod (interp_h_ty wfA) (interp_h_ty wfB)
  | WF_Arrow I' A B wfA wfB => exp (interp_h_ty wfA) (interp_h_ty wfB)
  
  (* Atom well-formedness supplies the codomain and typing derivation. *)
  | WF_Atom I' p t A' dt => i_atom p t I' A' dt
  
  | WF_All I' A' Body wfBody => 
      @right_adj_obj _ _ _ pullback_has_right_adjoint (interp_h_ty wfBody)
  | WF_Ex I' A' Body wfBody => 
      @left_adj_obj _ _ _ pullback_has_left_adjoint (interp_h_ty wfBody)
  end.

Inductive CtxWellFormed {Sign : Type} (I : b_ty) : @h_context Sign -> Type :=
  | Ctx_Nil : CtxWellFormed I nil
  | Ctx_Cons : forall Phi G, WellFormed I Phi -> CtxWellFormed I G -> CtxWellFormed I (Phi :: G).

(* Context interpretation follows its well-formedness derivation. *)
Fixpoint interp_h_ctx 
  {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {BSM : BaseSignatureModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} 
  {HM : HyperModel SGF}
  {I : b_ty} {G : @h_context Sign} (wfG : CtxWellFormed I G) : @obj (Fiber (interp_ty I)) :=
  match wfG in (CtxWellFormed _ G') return (@obj (Fiber (interp_ty I))) with
  | Ctx_Nil _ => terminal
  | Ctx_Cons _ Phi G' wfPhi wfG' => prod (interp_h_ctx wfG') (interp_h_ty wfPhi)
  end.