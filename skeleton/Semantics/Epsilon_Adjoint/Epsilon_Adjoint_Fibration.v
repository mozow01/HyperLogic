(* theories/Semantics/Epsilon_Adjoint/Epsilon_Adjoint_Fibration.v *)

Require Import Coq.Classes.Morphisms.
Require Import List.
Import ListNotations.

(* Kategóriaelméleti alapok *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import HyperLogic.Cat.Fibration.

(* Szintaxis és Orákulum (CSAK AZ ÚJ, ADJOINT MAPPÁBÓL!) *)
Require Import HyperLogic.Logic.Base.Epsilon_Adjoint.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon_Adjoint.Hyper_Syntax.

(* ================================================================= *)
(* 1. BÁZIS SZEMANTIKA ÉS INTERPRETÁCIÓ                              *)
(* ================================================================= *)

Fixpoint interp_ty {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  (A : b_ty) : @obj C :=
  match A with
  | b_Unit => terminal
  | b_S => @S C CC TSC
  | b_Prod A B => prod (interp_ty A) (interp_ty B)
  end.

Class BaseEpsilonModel {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} := {
  i_const : forall (I A : b_ty) (s : Sign), @hom C (interp_ty I) (interp_ty A)
}.

Fixpoint interp_tm {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C}
  {TSC : TwoSortCategory C} {BEM : BaseEpsilonModel}
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

(* ================================================================= *)
(* 2. HYPER SZEMANTIKA (Atomok és Kvantorok)                         *)
(* ================================================================= *)

Class EpsilonHyperModel
  {Sign : Type}
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonModel}
  {GF : GoodFibration C} (SGF : StrictGoodFibration C GF) := {

  i_atom : forall (p : nat) (t : @b_tm Sign) (I : b_ty), @obj (Fiber (interp_ty I)) ;

  i_atom_pb : forall (p : nat) (t : @b_tm Sign) (I A : b_ty) (f : @b_tm Sign) (df : @base_typing Sign I f A),
      @fobj _ _ (Pullback (interp_tm df)) (i_atom p t A) ≅O i_atom p (b_comp t f) I;

  i_atom_cong_global : forall (p : nat) (I_target I_orig A : b_ty) (t1 t2 : b_tm)
                              (d1 : base_typing I_orig t1 A) (d2 : base_typing I_orig t2 A),
                       base_equiv d1 d2 -> i_atom p t1 I_target ≅O i_atom p t2 I_target
}.

Fixpoint interp_h_ty
  {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
  {EHM : EpsilonHyperModel SGF}
  (I : b_ty) (Phi : @h_ty Sign) : @obj (Fiber (interp_ty I)) :=
  match Phi with
  | Ty_Unit => terminal
  | Ty_Void => initial
  | Ty_Prod A B => prod (interp_h_ty I A) (interp_h_ty I B)
  | Ty_Sum A B => coprod (interp_h_ty I A) (interp_h_ty I B)
  | Ty_Arrow A B => exp (interp_h_ty I B) (interp_h_ty I A)
  | Ty_Atom p t => i_atom p t I
  | Ty_All A Body =>
      @right_adj_obj _ _ _ pullback_has_right_adjoint
                           (interp_h_ty (b_Prod I A) Body)
  | Ty_Ex A Body =>
      @left_adj_obj _ _ _ pullback_has_left_adjoint
                          (interp_h_ty (b_Prod I A) Body)
  end.

Fixpoint interp_h_ctx
  {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
  {EHM : EpsilonHyperModel SGF}
  (I : b_ty) (G : @h_context Sign) : @obj (Fiber (interp_ty I)) :=
  match G with
  | nil => terminal
  | Phi :: G' => prod (interp_h_ctx I G') (interp_h_ty I Phi)
  end.

(* ================================================================= *)
(* 3. ADJUNGÁLT FIBRÁCIÓ OSZTÁLY                                     *)
(* ================================================================= *)

Class AdjointEpsilonFibration
  {Sign : Type} {SM : SkolemMapping Sign}
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonModel} {GF : GoodFibration C}
  {SGF : StrictGoodFibration C GF}
  {EHM : EpsilonHyperModel SGF} := {

    eps_is_left_adj_obj : forall (I A : b_ty) (Phi : @h_ty Sign),
    @left_adj_obj _ _ _ pullback_has_left_adjoint
      (interp_h_ty (b_Prod I A) Phi)
    ≅O
    interp_h_ty I (form_subst (b_pair b_id (b_const A (skolem_index A Phi))) Phi) ;

    eps_functorial : forall (I A : b_ty) (Phi Psi : @h_ty Sign),
    interp_h_ty (b_Prod I A) Phi ≅O interp_h_ty (b_Prod I A) Psi ->
    interp_h_ty I (form_subst (b_pair b_id (b_const A (skolem_index A Phi))) Phi)
    ≅O
    interp_h_ty I (form_subst (b_pair b_id (b_const A (skolem_index A Psi))) Psi)
}.