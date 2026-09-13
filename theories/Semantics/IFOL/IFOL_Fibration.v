(* Semantic interface for epsilon-free intuitionistic first-order logic. *)

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

Require Import HyperLogic.Logic.Base.IFOL.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.IFOL.Hyper_Syntax.

Fixpoint interp_ty {C : SetoidCategory} {CC : CartesianCategory C}
  {TSC : TwoSortCategory C} (A : b_ty) : @obj C :=
  match A with
  | b_Unit => terminal
  | b_S => @S C CC TSC
  | b_Prod A B => prod (interp_ty A) (interp_ty B)
  end.

Class BaseIFOLModel {Func : Type} `{FunctionSignature Func}
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} := {
  i_func : forall f : Func,
    @hom C (interp_ty (func_dom f)) (interp_ty (func_cod f))
}.

Fixpoint interp_tm {Func : Type} `{FunctionSignature Func}
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {BIM : BaseIFOLModel}
  {I A : b_ty} {f : @b_tm Func} (d : @base_typing Func H I f A)
  : @hom C (interp_ty I) (interp_ty A) :=
  match d in base_typing I' f' A' return @hom C (interp_ty I') (interp_ty A') with
  | @BT_Id _ _ A' => @id C (interp_ty A')
  | @BT_Comp _ _ A' B' C' g' f' dg df =>
      @compose C (interp_ty A') (interp_ty B') (interp_ty C') (interp_tm dg) (interp_tm df)
  | @BT_Unit _ _ A' => @terminal_map C CC (interp_ty A')
  | @BT_Pair _ _ A' B' C' f' g' df dg =>
      @prod_map C CC (interp_ty A') (interp_ty B') (interp_ty C') (interp_tm df) (interp_tm dg)
  | @BT_Fst _ _ A' B' => @prod_fst C CC (interp_ty A') (interp_ty B')
  | @BT_Snd _ _ A' B' => @prod_snd C CC (interp_ty A') (interp_ty B')
  | @BT_Func _ _ f' => i_func f'
  end.

Class CoherentBaseIFOLModel {Func : Type} `{FunctionSignature Func}
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {BIM : @BaseIFOLModel Func H C CC TSC} := {
  interp_coh : forall {I A : b_ty} {f : @b_tm Func}
    (d1 d2 : @base_typing Func H I f A),
    interp_tm d1 ≅ interp_tm d2
}.

Class IFOLHyperModel {Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred}
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {BIM : BaseIFOLModel} {GF : GoodFibration C} := {
  i_atom : forall (p : Pred) (t : @b_tm Func) (I : b_ty),
    @obj (Fiber (interp_ty I));

  i_atom_pb : forall (p : Pred) (t : @b_tm Func) (I A : b_ty) (f : @b_tm Func)
    (df : @base_typing Func H I f A),
    @fobj _ _ (Pullback (interp_tm df)) (i_atom p t A) ≅O i_atom p (b_comp t f) I;

  i_atom_cong_global : forall (p : Pred) (I A : b_ty) (t1 t2 : @b_tm Func)
    (d1 : @base_typing Func H I t1 A) (d2 : @base_typing Func H I t2 A),
    @base_equiv Func H I A t1 t2 d1 d2 ->
    i_atom p t1 I ≅O i_atom p t2 I
}.

Fixpoint interp_h_ty {Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred}
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {BIM : BaseIFOLModel} {GF : GoodFibration C}
  {IHM : IFOLHyperModel}
  (I : b_ty) (Phi : @h_ty Func Pred) : @obj (Fiber (interp_ty I)) :=
  match Phi with
  | Ty_Unit => terminal
  | Ty_Void => initial
  | Ty_Prod A B => prod (interp_h_ty I A) (interp_h_ty I B)
  | Ty_Sum A B => coprod (interp_h_ty I A) (interp_h_ty I B)
  | Ty_Arrow A B => exp (interp_h_ty I B) (interp_h_ty I A)
  | Ty_Atom p t => i_atom p t I
  | Ty_All A Body => @right_adj_obj _ _ _ pullback_has_right_adjoint (interp_h_ty (b_Prod I A) Body)
  | Ty_Ex A Body => @left_adj_obj _ _ _ pullback_has_left_adjoint (interp_h_ty (b_Prod I A) Body)
  end.

Fixpoint interp_h_ctx {Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred}
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {BIM : BaseIFOLModel} {GF : GoodFibration C}
  {IHM : IFOLHyperModel}
  (I : b_ty) (G : @h_context Func Pred) : @obj (Fiber (interp_ty I)) :=
  match G with
  | nil => terminal
  | Phi :: G' => prod (interp_h_ctx I G') (interp_h_ty I Phi)
  end.
