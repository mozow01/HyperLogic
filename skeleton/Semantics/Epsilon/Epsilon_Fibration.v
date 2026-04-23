(*theories/Semantics/Epsilon/Epsilon_Fibration.v*)

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

(* Szintaxis és Orákulum *)
Require Import HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.

(* ================================================================= *)
(* 1. BÁZIS SZEMANTIKA (Epszilon Konstansok)                         *)
(* ================================================================= *)

(** A bázis típusok kategóriaelméleti interpretációja.
    Ez felelteti meg a szintaktikus b_ty elemeit a kategória objektumainak. *)
Fixpoint interp_ty {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  (A : b_ty) : @obj C :=
  match A with
  | b_Unit => terminal
  | b_S => @S C CC TSC   (* <--- ITT A JAVÍTÁS: Mindent expliciten átadunk! *)
  | b_Prod A B => prod (interp_ty A) (interp_ty B)
  end.

(** A bázis modellnek csak annyi a dolga, hogy minden Sign-beli szimbólumhoz
    (amit a skolem_index generál) hozzárendeljen egy bázismorfizmust. *)
Class BaseEpsilonModel {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} := {
  i_const : forall (I A : b_ty) (s : Sign), @hom C (interp_ty I) (interp_ty A)
}.

(** Az interp_tm kiterjesztése az új BT_Const szabállyal. *)
Fixpoint interp_tm {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C}
  {TSC : TwoSortCategory C} {BEM : BaseEpsilonModel}
  {I A : b_ty} {f : @b_tm Sign} (d : @base_typing Sign I f A)
  : @hom C (interp_ty I) (interp_ty A) :=
  match d in (base_typing I' f' A') return (@hom C (interp_ty I') (interp_ty A')) with
  | @BT_Id _ A' => @id C (interp_ty A')

  (* JAVÍTVA: Itt a (interp_tm dg) és (interp_tm df) sorrendjét megcseréltük! *)
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

(** Az EpsilonHyperModel az atomok interpretációját rögzíti, ahogy a Simple logikában is. *)
Class EpsilonHyperModel
  {Sign : Type}
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonModel}  (* <--- ITT A JAVÍTÁS: Szükségünk van a bázismodellre az interp_tm-hez! *)
  {GF : GoodFibration C} (SGF : StrictGoodFibration C GF) := {

  i_atom : forall (p : nat) (t : @b_tm Sign) (I : b_ty), @obj (Fiber (interp_ty I)) ;

  i_atom_pb : forall (p : nat) (t : @b_tm Sign) (I A : b_ty) (f : @b_tm Sign) (df : @base_typing Sign I f A),
      @fobj _ _ (Pullback (interp_tm df)) (i_atom p t A) ≅O i_atom p (b_comp t f) I;

  i_atom_cong_global : forall (p : nat) (I_target I_orig A : b_ty) (t1 t2 : b_tm)
                              (d1 : base_typing I_orig t1 A) (d2 : base_typing I_orig t2 A),
                       base_equiv d1 d2 -> i_atom p t1 I_target ≅O i_atom p t2 I_target
                       (*
  i_atom_cong : forall (p : nat) (I A : b_ty) (t1 t2 : b_tm)
                       (d1 : base_typing I t1 A) (d2 : base_typing I t2 A),
                base_equiv d1 d2 -> i_atom p t1 I ≅O i_atom p t2 I *)  }.

(** A formulák interpretációja, amely már tartalmazza a Ty_All és Ty_Ex kvantorokat is! *)
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
(* 3. INTENZIONÁLIS EPSZILON LOGIKA (Pszeudo-Adjungált)              *)
(* ================================================================= *)

(** Itt jön a mágia! Nem definiálunk funktort. Csak explicit szintaktikai formulákra
    (Phi : @h_ty Sign) követeljük meg az Intro (Unit) és Elim (Frobenius) dedukciós szabályokat,
    amelyeket a skolem_index orákulum köt a bázishoz. *)

Class EpsilonGoodFibration
  {Sign : Type} {SM : SkolemMapping Sign}
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
  {EHM : EpsilonHyperModel SGF} := {

  (** 1. EPSILON INTRO (Unit) *)
  eps_unit : forall (I A : b_ty) (Phi : @h_ty Sign),
      hom (interp_h_ty (b_Prod I A) Phi)
          (interp_h_ty (b_Prod I A)
             (form_pullback b_fst
                (form_pullback (b_pair b_id (b_const A (skolem_index A Phi))) Phi))) ;

  (** 2. EPSILON ELIM (Frobenius Reciprocitás) *)
  eps_elim_frobenius : forall (I A : b_ty) (G : @h_context Sign) (Phi Chi : @h_ty Sign),
      hom (prod (interp_h_ctx (b_Prod I A) (ctx_pullback b_fst G)) (interp_h_ty (b_Prod I A) Phi))
          (interp_h_ty (b_Prod I A) (form_pullback b_fst Chi)) ->
      hom (prod (interp_h_ctx I G)
                (interp_h_ty I (form_pullback (b_pair b_id (b_const A (skolem_index A Phi))) Phi)))
          (interp_h_ty I Chi) ;

  eps_beck_chevalley_iso : forall (I J A : b_ty) (g : b_tm) (dg : base_typing J g I) (Phi : h_ty),
    interp_h_ty J (form_pullback g (form_pullback (b_pair b_id (b_const A (skolem_index A Phi))) Phi)) ≅O
    interp_h_ty J (form_pullback (b_pair (b_comp g b_fst) b_snd) Phi .[ ε A, form_pullback (b_pair (b_comp g b_fst) b_snd) Phi ])
}.