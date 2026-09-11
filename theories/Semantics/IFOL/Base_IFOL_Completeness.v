(* theories/Semantics/IFOL/Base_IFOL_Completeness.v *)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Equality.
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.Fibration.

Require Import HyperLogic.Logic.Base.IFOL.Base_Syntax.
Require Import HyperLogic.Semantics.IFOL.IFOL_Fibration.

(* ================================================================= *)
(* 1. A SZINTAKTIKUS KATEGÓRIA (TERM MODELL) MORFIZMUSAI             *)
(* ================================================================= *)

Class hom_base {Func : Type} `{HFunc : FunctionSignature Func} (A B : b_ty) : Type := mk_hom_base {
  tm_of : @b_tm Func;
  deriv_of : @base_typing Func HFunc A tm_of B
}.

Arguments tm_of {Func HFunc A B} _.
Arguments deriv_of {Func HFunc A B} _.

(* ================================================================= *)
(* 2. A BÁZIS KATEGÓRIA PÉLDÁNYOSÍTÁSA                               *)
(* ================================================================= *)

Instance Base_SetoidCategory (Func : Type) `{HFunc : FunctionSignature Func} : SetoidCategory.
Proof.
  refine (mk_SetoidCategory
    b_ty
    (@hom_base Func HFunc)
    (fun X => @mk_hom_base Func HFunc X X b_id BT_Id)
    (fun X Y Z f g =>
      @mk_hom_base Func HFunc X Z (b_comp (tm_of f) (tm_of g)) (BT_Comp (deriv_of f) (deriv_of g)))
    (fun X Y f g =>
      @base_equiv Func HFunc X Y (tm_of f) (tm_of g) (deriv_of f) (deriv_of g))
    _ _ _ _ _).
  - intros X Y. constructor.
    + intros f. apply BE_Refl.
    + intros f g. apply BE_Sym.
    + intros f g h. apply BE_Trans.
  - intros X Y Z W f g h. apply BE_Assoc.
  - intros X Y f. apply BE_IdR.
  - intros X Y f. apply BE_IdL.
  - unfold Proper, respectful.
    intros X Y Z f g Hfg h i Hhi.
    apply BE_CongComp; assumption.
Defined.

Instance Base_CartesianCategory (Func : Type) `{HFunc : FunctionSignature Func}
  : CartesianCategory (Base_SetoidCategory Func).
Proof.
  refine (mk_CartesianCategory
    (Base_SetoidCategory Func)
    b_Unit
    (fun X => @mk_hom_base Func HFunc X b_Unit b_unit BT_Unit)
    _
    b_Prod
    (fun X Y Z f g =>
      @mk_hom_base Func HFunc X (b_Prod Y Z) (b_pair (tm_of f) (tm_of g)) (BT_Pair (deriv_of f) (deriv_of g)))
    (fun X Y => @mk_hom_base Func HFunc (b_Prod X Y) X b_fst BT_Fst)
    (fun X Y => @mk_hom_base Func HFunc (b_Prod X Y) Y b_snd BT_Snd)
    _ _ _ _).
  - intros X f. apply BE_EtaUnit.
  - intros X Y Z f g. apply BE_BetaFst.
  - intros X Y Z f g. apply BE_BetaSnd.
  - intros X Y Z h. apply BE_EtaPair.
  - unfold Proper, respectful. intros X Y Z f f' Hf g g' Hg.
    apply BE_CongPair; assumption.
Defined.

Instance Base_TwoSortCategory (Func : Type) `{HFunc : FunctionSignature Func}
  : TwoSortCategory (Base_SetoidCategory Func).
Proof.
  refine (mk_TwoSortCategory (Base_SetoidCategory Func) (Base_CartesianCategory Func) b_S _).
  intro H. discriminate H.
Defined.

(* ================================================================= *)
(* 2.5 SZINTAKTIKUS IFOL-MODELL ÉS SEGÉDLEMMÁK                       *)
(* ================================================================= *)

Lemma interp_ty_id : forall (Func : Type) `{HFunc : FunctionSignature Func} (A : b_ty),
  @interp_ty (Base_SetoidCategory Func) (Base_CartesianCategory Func) (Base_TwoSortCategory Func) A = A.
Proof.
  intros Func HFunc A.
  induction A; simpl; congruence.
Defined.

Instance Base_SyntacticIFOLModel (Func : Type) `{HFunc : FunctionSignature Func} :
  @BaseIFOLModel Func HFunc
    (Base_SetoidCategory Func) (Base_CartesianCategory Func) (Base_TwoSortCategory Func).
Proof.
  constructor.
  - intro f.
    rewrite (interp_ty_id Func (func_dom f)).
    rewrite (interp_ty_id Func (func_cod f)).
    exact (@mk_hom_base Func HFunc (func_dom f) (func_cod f) (b_func f) BT_Func).
Defined.

(* ================================================================= *)
(* 3. COMPLETENESS HELPER LEMMÁK                                     *)
(* ================================================================= *)

Lemma tm_of_eq_rect : forall {Func : Type} `{HFunc : FunctionSignature Func}
  (I A I_sem A_sem : b_ty)
  (eqI : I_sem = I) (eqA : A_sem = A) (f : @hom_base Func HFunc I A),
  @tm_of Func HFunc I_sem A_sem
    (eq_rect_r (fun o : b_ty => hom_base o A_sem)
      (eq_rect_r (fun o : b_ty => hom_base I o) f eqA) eqI) =
  @tm_of Func HFunc I A f.
Proof.
  intros Func HFunc I A I_sem A_sem eqI eqA f.
  destruct eqI. destruct eqA. reflexivity.
Defined.

Lemma interp_tm_term : forall {Func : Type} `{HFunc : FunctionSignature Func}
  A B f (df : @base_typing Func HFunc A f B),
  tm_of (@interp_tm Func HFunc
    (Base_SetoidCategory Func) (Base_CartesianCategory Func) (Base_TwoSortCategory Func)
    (Base_SyntacticIFOLModel Func) A B f df) = f.
Proof.
  intros Func HFunc A B f df.
  induction df; simpl.
  - reflexivity.
  - rewrite IHdf1, IHdf2. reflexivity.
  - reflexivity.
  - rewrite IHdf1, IHdf2. reflexivity.
  - reflexivity.
  - reflexivity.
  - apply tm_of_eq_rect.
Defined.

Lemma base_typing_unique : forall {Func : Type} `{HFunc : FunctionSignature Func}
  A f B1 (d1 : @base_typing Func HFunc A f B1) B2 (d2 : @base_typing Func HFunc A f B2),
  B1 = B2.
Proof.
  intros Func HFunc A f B1 d1.
  induction d1; intros B2 d2; dependent destruction d2.
  - reflexivity.
  - assert (H_B : B = B0). { eapply IHd1_2. exact d2_2. }
    subst B0.
    eapply IHd1_1. exact d2_1.
  - reflexivity.
  - assert (H_B : B = B0). { eapply IHd1_1. exact d2_1. }
    assert (H_C : C = C0). { eapply IHd1_2. exact d2_2. }
    subst. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

Lemma base_typing_pi : forall {Func : Type} `{HFunc : FunctionSignature Func}
  A B f (d1 d2 : @base_typing Func HFunc A f B),
  @base_equiv Func HFunc A B f f d1 d2.
Proof.
  intros Func HFunc A B f d1 d2.
  apply BE_Refl.
Defined.

Lemma base_equiv_cast : forall {Func : Type} `{HFunc : FunctionSignature Func}
  A B A' B' f g f' g'
  (eqA : A' = A) (eqB : B' = B)
  (eqF : f' = f) (eqG : g' = g)
  (df' : @base_typing Func HFunc A' f' B') (dg' : @base_typing Func HFunc A' g' B')
  (df : @base_typing Func HFunc A f B) (dg : @base_typing Func HFunc A g B),
  @base_equiv Func HFunc A' B' f' g' df' dg' ->
  @base_equiv Func HFunc A B f g df dg.
Proof.
  intros Func HFunc A B A' B' f g f' g' eqA eqB eqF eqG df' dg' df dg Heq.
  subst.
  eapply BE_Trans.
  - apply base_typing_pi.
  - eapply BE_Trans.
    + exact Heq.
    + apply base_typing_pi.
Defined.

Lemma base_typing_cast : forall {Func : Type} `{HFunc : FunctionSignature Func}
  A' B' A B t,
  A' = A -> B' = B -> @base_typing Func HFunc A' t B' -> @base_typing Func HFunc A t B.
Proof.
  intros Func HFunc A' B' A B t eqA eqB d.
  subst. exact d.
Defined.

(* ================================================================= *)
(* 4. COMPLETENESS (TELJESSÉG) TÉTELEK                               *)
(* ================================================================= *)

Instance Base_SyntacticCoherentModel (Func : Type) `{HFunc : FunctionSignature Func} :
  @CoherentBaseIFOLModel Func HFunc
    (Base_SetoidCategory Func)
    (Base_CartesianCategory Func)
    (Base_TwoSortCategory Func)
    (Base_SyntacticIFOLModel Func).
Proof.
  constructor.
  intros A B f d1 d2.
  cbn.
  eapply base_equiv_cast with
    (A' := A) (B' := B) (f' := f) (g' := f) (df' := d1) (dg' := d2).
  - symmetry. apply interp_ty_id.
  - symmetry. apply interp_ty_id.
  - symmetry. apply interp_tm_term.
  - symmetry. apply interp_tm_term.
  - apply BE_Refl.
Defined.

Theorem base_completeness_equational : forall {Func : Type} `{HFunc : FunctionSignature Func}
  {A B : b_ty} {f g : @b_tm Func}
  (df : @base_typing Func HFunc A f B) (dg : @base_typing Func HFunc A g B),
  (forall (C : SetoidCategory) (CC : CartesianCategory C) (TSC : TwoSortCategory C)
    (BEM : @BaseIFOLModel Func HFunc C CC TSC)
    (CBM : @CoherentBaseIFOLModel Func HFunc C CC TSC BEM),
    @interp_tm Func HFunc C CC TSC BEM A B f df ≅ @interp_tm Func HFunc C CC TSC BEM A B g dg) ->
  @base_equiv Func HFunc A B f g df dg.
Proof.
  intros Func HFunc A B f g df dg H.

  pose proof (H (Base_SetoidCategory Func)
    (Base_CartesianCategory Func)
    (Base_TwoSortCategory Func)
    (Base_SyntacticIFOLModel Func)
    (Base_SyntacticCoherentModel Func)) as Heq.

  eapply base_equiv_cast.
  - apply (interp_ty_id Func).
  - apply (interp_ty_id Func).
  - apply interp_tm_term.
  - apply interp_tm_term.
  - exact Heq.
Defined.
