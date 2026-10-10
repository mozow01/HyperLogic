
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

Require Import HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.

(** Semantic interface for the epsilon-only calculus. *)

Fixpoint interp_ty {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  (A : b_ty) : @obj C :=
  match A with
  | b_Unit => terminal
  | b_S => @S C CC TSC
  | b_Prod A B => prod (interp_ty A) (interp_ty B)
  end.

Class BaseEpsilonModel
  {Sign Func : Type} `{FunctionSignature Func}
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} := {
  i_const : forall (I A : b_ty) (s : Sign), @hom C (interp_ty I) (interp_ty A);
  i_func : forall (f : Func), @hom C (interp_ty (func_dom f)) (interp_ty (func_cod f))
}.

Fixpoint interp_tm
  {Sign Func : Type} `{FunctionSignature Func}
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonModel}
  {I A : b_ty} {f : @b_tm Sign Func} (d : @base_typing Sign Func H I f A)
  : @hom C (interp_ty I) (interp_ty A) :=
  match d in (base_typing I' f' A') return (@hom C (interp_ty I') (interp_ty A')) with
  | @BT_Id _ _ _ A' => @id C (interp_ty A')
  | @BT_Comp _ _ _ A' B' C' g' f' dg df =>
      @compose C (interp_ty A') (interp_ty B') (interp_ty C') (interp_tm dg) (interp_tm df)
  | @BT_Unit _ _ _ A' => @terminal_map C CC (interp_ty A')
  | @BT_Pair _ _ _ A' B' C' f' g' df dg =>
      @prod_map C CC (interp_ty A') (interp_ty B') (interp_ty C') (interp_tm df) (interp_tm dg)
  | @BT_Fst _ _ _ A' B' => @prod_fst C CC (interp_ty A') (interp_ty B')
  | @BT_Snd _ _ _ A' B' => @prod_snd C CC (interp_ty A') (interp_ty B')
  | @BT_Const _ _ _ I' A' s => i_const I' A' s
  | @BT_Func _ _ _ f' => i_func f'
  end.

Class CoherentBaseModel
  {Sign Func : Type} `{FunctionSignature Func}
  {C : SetoidCategory} {CC : CartesianCategory C}
  {TSC : TwoSortCategory C} {BEM : @BaseEpsilonModel Sign Func H C CC TSC} := {
  interp_coh : forall {A B : b_ty} {f : @b_tm Sign Func}
    (d1 d2 : @base_typing Sign Func H A f B),
    interp_tm d1 ≅ interp_tm d2
}.


Class EpsilonHyperModel
  {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred}
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonModel}
  {GF : GoodFibration C} := {
  i_atom : forall (p : Pred) (t : @b_tm Sign Func) (I : b_ty), @obj (Fiber (interp_ty I));

  i_atom_pb : forall (p : Pred) (t : @b_tm Sign Func) (I A : b_ty) (f : @b_tm Sign Func)
    (df : @base_typing Sign Func H I f A),
    @fobj _ _ (Pullback (interp_tm df)) (i_atom p t A) ≅O i_atom p (b_comp t f) I;

  i_atom_cong_global : forall (p : Pred) (I A : b_ty) (t1 t2 : @b_tm Sign Func)
    (d1 : @base_typing Sign Func H I t1 A) (d2 : @base_typing Sign Func H I t2 A),
    @base_equiv Sign Func H I A t1 t2 d1 d2 ->
    i_atom p t1 I ≅O i_atom p t2 I
}.

Fixpoint interp_h_ty
  {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonModel} {GF : GoodFibration C}
  {EHM : EpsilonHyperModel}
  (I : b_ty) (Phi : @h_ty Sign Func Pred) : @obj (Fiber (interp_ty I)) :=
  match Phi with
  | Ty_Unit => terminal
  | Ty_Void => initial
  | Ty_Prod A B => prod (interp_h_ty I A) (interp_h_ty I B)
  | Ty_Sum A B => coprod (interp_h_ty I A) (interp_h_ty I B)
  | Ty_Arrow A B => exp (interp_h_ty I B) (interp_h_ty I A)
  | Ty_Atom p t => i_atom p t I
  | Ty_All A Body =>
      @right_adj_obj _ _ _ pullback_has_right_adjoint (interp_h_ty (b_Prod I A) Body)
  end.

Fixpoint interp_h_ctx
  {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonModel} {GF : GoodFibration C}
  {EHM : EpsilonHyperModel}
  (I : b_ty) (G : @h_context Sign Func Pred) : @obj (Fiber (interp_ty I)) :=
  match G with
  | nil => terminal
  | Phi :: G' => prod (interp_h_ctx I G') (interp_h_ty I Phi)
  end.

Definition eps_instance
  {Sign Func Pred : Type} `{SkolemMapping Sign Func Pred}
  (A : b_ty) (Phi : @h_ty Sign Func Pred) : @h_ty Sign Func Pred :=
  form_subst (b_pair b_id (b_const A (skolem_index A Phi))) Phi.

(** Pasquali-style epsilon structure on well-formed formulas. *)

Class EpsilonGoodFibration
  {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred}
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonModel} {GF : GoodFibration C}
  {EHM : EpsilonHyperModel} := {

  (* Raw formulas may contain ill-typed atoms, so epsilon structure is only
     required on the well-formed fragment interpreted by derivations. *)

  eps_unit : forall (I A : b_ty) (Phi : @h_ty Sign Func Pred),
    WellFormed (b_Prod I A) Phi ->
    hom (interp_h_ty (b_Prod I A) Phi)
        (interp_h_ty (b_Prod I A) (form_subst b_fst (eps_instance A Phi)));

  eps_intro : forall (I A : b_ty) (Phi : @h_ty Sign Func Pred) (f : @b_tm Sign Func),
    WellFormed (b_Prod I A) Phi ->
    base_typing I f A ->
    hom (interp_h_ty I (form_subst (b_pair b_id f) Phi))
        (interp_h_ty I (eps_instance A Phi));

  eps_elim_frobenius : forall (I A : b_ty) (G : @h_context Sign Func Pred)
      (Phi Chi : @h_ty Sign Func Pred),
    All_WellFormed I G ->
    WellFormed (b_Prod I A) Phi ->
    WellFormed I Chi ->
    hom (prod (interp_h_ctx (b_Prod I A) (ctx_subst b_fst G))
              (interp_h_ty (b_Prod I A) Phi))
        (interp_h_ty (b_Prod I A) (form_subst b_fst Chi)) ->
    hom (prod (interp_h_ctx I G) (interp_h_ty I (eps_instance A Phi)))
        (interp_h_ty I Chi);

  eps_functorial_iso : forall (I A : b_ty) (Phi Psi : @h_ty Sign Func Pred),
    WellFormed (b_Prod I A) Phi ->
    WellFormed (b_Prod I A) Psi ->
    interp_h_ty (b_Prod I A) Phi ≅O interp_h_ty (b_Prod I A) Psi ->
    interp_h_ty I (eps_instance A Phi) ≅O interp_h_ty I (eps_instance A Psi);

  eps_beck_chevalley_iso : forall (I J A : b_ty) (g : @b_tm Sign Func)
      (dg : base_typing I g J) (Phi : @h_ty Sign Func Pred),
    WellFormed (b_Prod J A) Phi ->
    interp_h_ty I (form_subst g (eps_instance A Phi)) ≅O
    interp_h_ty I (eps_instance A (form_subst (b_subst_ext g) Phi))
}.
