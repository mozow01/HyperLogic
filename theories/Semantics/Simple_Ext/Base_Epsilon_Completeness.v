
Require Import Coq.Classes.Morphisms. 
Require Import Coq.Program.Equality.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.Fibration.

Require Import HyperLogic.Logic.Base.Simple_Ext.Base_Syntax.
Require Import HyperLogic.Semantics.Simple_Ext.Simple_Ext_Fibration.

(** Legacy syntactic base model. *)

Class hom_base {Sign : Type} (A B : b_ty) : Type := mk_hom_base {
  tm_of : @b_tm Sign;
  deriv_of : @base_typing Sign A tm_of B
}.

Arguments tm_of {Sign A B} _.
Arguments deriv_of {Sign A B} _.


Instance Base_SetoidCategory (Sign : Type) : SetoidCategory.
Proof.
  refine (mk_SetoidCategory 
    b_ty 
    (@hom_base Sign) 
    (fun X => @mk_hom_base Sign X X b_id BT_Id)
    (fun X Y Z f g => @mk_hom_base Sign X Z (b_comp (tm_of f) (tm_of g)) (BT_Comp (deriv_of f) (deriv_of g)))
    (fun X Y f g => @base_equiv Sign X Y (tm_of f) (tm_of g) (deriv_of f) (deriv_of g))
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

Instance Base_CartesianCategory (Sign : Type) : CartesianCategory (Base_SetoidCategory Sign).
Proof.
  refine (mk_CartesianCategory 
    (Base_SetoidCategory Sign)
    b_Unit
    (fun X => @mk_hom_base Sign X b_Unit b_unit BT_Unit)
    _
    b_Prod
    (fun X Y Z f g => @mk_hom_base Sign X (b_Prod Y Z) (b_pair (tm_of f) (tm_of g)) (BT_Pair (deriv_of f) (deriv_of g)))
    (fun X Y => @mk_hom_base Sign (b_Prod X Y) X b_fst BT_Fst)
    (fun X Y => @mk_hom_base Sign (b_Prod X Y) Y b_snd BT_Snd)
    _ _ _ _).
  - intros X f. apply BE_EtaUnit.
  - intros X Y Z f g. apply BE_BetaFst.
  - intros X Y Z f g. apply BE_BetaSnd.
  - intros X Y Z h. apply BE_EtaPair.
  - unfold Proper, respectful. intros X Y Z f f' Hf g g' Hg.
    apply BE_CongPair; assumption.
Defined.

Instance Base_TwoSortCategory (Sign : Type) : TwoSortCategory (Base_SetoidCategory Sign).
Proof.
  refine (mk_TwoSortCategory (Base_SetoidCategory Sign) (Base_CartesianCategory Sign) b_S _).
  intro H. discriminate H.
Defined.


(** Type interpretation is identified with the original syntactic type. *)
Lemma interp_ty_id : forall (Sign : Type) (A : b_ty), 
  @interp_ty (Base_SetoidCategory Sign) (Base_CartesianCategory Sign) (Base_TwoSortCategory Sign) A = A.
Proof.
  intros Sign A.
  induction A; simpl; congruence.
Defined. 

Instance Base_SyntacticEpsilonModel (Sign : Type) : 
  @BaseSignatureModel Sign (Base_SetoidCategory Sign) (Base_CartesianCategory Sign) (Base_TwoSortCategory Sign).
Proof.
  constructor.
  intros I A s.
  
  rewrite (interp_ty_id Sign I).
  rewrite (interp_ty_id Sign A).
  
  exact (@mk_hom_base Sign I A (b_const A s) BT_Const).
Defined.



 

(* Transport leaves [tm_of] unchanged because its result type does not depend on the transported indices. *)
Lemma tm_of_eq_rect : forall {Sign : Type} (I A I_sem A_sem : b_ty) 
  (eqI : I_sem = I) (eqA : A_sem = A) (f : @hom_base Sign I A),
  @tm_of Sign I_sem A_sem (eq_rect_r (fun o : b_ty => hom_base o A_sem)
           (eq_rect_r (fun o : b_ty => hom_base I o) f eqA) eqI) = 
  @tm_of Sign I A f.
Proof.
  intros Sign I A I_sem A_sem eqI eqA f.
  destruct eqI. destruct eqA. reflexivity.
Defined.

Lemma interp_tm_term : forall {Sign : Type} A B f (df : @base_typing Sign A f B),
  tm_of (@interp_tm Sign (Base_SetoidCategory Sign) (Base_CartesianCategory Sign) (Base_TwoSortCategory Sign) (Base_SyntacticEpsilonModel Sign) A B f df) = f.
Proof.
  intros Sign A B f df.
  induction df; simpl.
  - reflexivity.
  - rewrite IHdf1, IHdf2. reflexivity.
  - reflexivity.
  - rewrite IHdf1, IHdf2. reflexivity.
  - reflexivity.
  - reflexivity.
  - apply tm_of_eq_rect.
Defined.

Lemma base_typing_unique : forall {Sign : Type} A f B1 (d1 : @base_typing Sign A f B1) B2 (d2 : @base_typing Sign A f B2),
  B1 = B2.
Proof.
  intros Sign A f B1 d1.
  induction d1; intros B2 d2; dependent destruction d2.
  - reflexivity.
  - assert (H_B : B = B0). { eapply IHd1_2. exact d2_2. }
    subst B0. eapply IHd1_1. exact d2_1.
  - reflexivity.
  - assert (H_B : B = B0). { eapply IHd1_1. exact d2_1. }
    assert (H_C : C = C0). { eapply IHd1_2. exact d2_2. }
    subst. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

Lemma base_typing_pi : forall {Sign : Type} A B f (d1 d2 : @base_typing Sign A f B), 
  @base_equiv Sign A B f f d1 d2.
Proof.
  intros Sign A B f d1.
  induction d1; intros d2; dependent destruction d2.
  - apply BE_Refl.
  - assert (H_B : B = B0). { eapply base_typing_unique. exact d1_2. exact d2_2. }
    subst B0.
    apply BE_CongComp.
    + apply IHd1_2.
    + apply IHd1_1.
  - apply BE_Refl.
  - apply BE_CongPair.
    + apply IHd1_1.
    + apply IHd1_2.
  - apply BE_Refl.
  - apply BE_Refl.
  - apply BE_Refl.
Defined.

Lemma base_equiv_cast : forall {Sign : Type} A B A' B' f g f' g'
  (eqA : A' = A) (eqB : B' = B) 
  (eqF : f' = f) (eqG : g' = g)
  (df' : @base_typing Sign A' f' B') (dg' : @base_typing Sign A' g' B')
  (df : @base_typing Sign A f B) (dg : @base_typing Sign A g B),
  @base_equiv Sign A' B' f' g' df' dg' -> @base_equiv Sign A B f g df dg.
Proof.
  intros Sign A B A' B' f g f' g' eqA eqB eqF eqG df' dg' df dg Heq.
  subst.
  eapply BE_Trans.
  - apply base_typing_pi.
  - eapply BE_Trans.
    + exact Heq.
    + apply base_typing_pi.
Defined.

Lemma base_typing_cast : forall {Sign : Type} A' B' A B t,
  A' = A -> B' = B -> @base_typing Sign A' t B' -> @base_typing Sign A t B.
Proof.
  intros Sign A' B' A B t eqA eqB d.
  subst. exact d.
Defined.

(** Completeness for the legacy epsilon base syntax. *)

Instance Base_SyntacticCoherentModel (Sign : Type) : 
  @CoherentBaseModel Sign (Base_SetoidCategory Sign) 
    (Base_CartesianCategory Sign) (Base_TwoSortCategory Sign) 
    (Base_SyntacticEpsilonModel Sign).
Proof.
  constructor.
  intros A B f d1 d2.
  cbn.
  eapply base_equiv_cast with (A' := A) (B' := B) (f' := f) (g' := f) (df' := d1) (dg' := d2).
  - symmetry. apply interp_ty_id.
  - symmetry. apply interp_ty_id.
  - symmetry. apply interp_tm_term.
  - symmetry. apply interp_tm_term.
  - apply BE_Refl.
Defined.


Theorem base_completeness_equational : forall {Sign : Type} {A B : b_ty} {f g : @b_tm Sign} 
  (df : @base_typing Sign A f B) (dg : @base_typing Sign A g B),
  (forall (C : SetoidCategory) (CC : CartesianCategory C) (TSC : TwoSortCategory C) 
          (BEM : @BaseSignatureModel Sign C CC TSC)
          (CBM : @CoherentBaseModel Sign C CC TSC BEM),
     @interp_tm Sign C CC TSC BEM A B f df ≅ @interp_tm Sign C CC TSC BEM A B g dg) ->
  @base_equiv Sign A B f g df dg.
Proof.
  intros Sign A B f g df dg H.
  
  pose proof (H (Base_SetoidCategory Sign) 
                (Base_CartesianCategory Sign) 
                (Base_TwoSortCategory Sign) 
                (Base_SyntacticEpsilonModel Sign)
                (Base_SyntacticCoherentModel Sign)) as Heq. 
  
  
  eapply base_equiv_cast. 
  - apply (interp_ty_id Sign). 
  - apply (interp_ty_id Sign). 
  - apply interp_tm_term. 
  - apply interp_tm_term. 
  - exact Heq.
Defined.