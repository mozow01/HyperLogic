(* theories/Semantics/Epsilon/Epsilon_Soundness.v *)

Require Import Coq.Classes.Morphisms.
Require Import List Arith PeanoNat Lia.
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
Require Import HyperLogic.Logic.Hyper.Epsilon.Epsilon_Syntax_Lemmas.
Require Import HyperLogic.Semantics.Epsilon.Epsilon_Fibration.

(* ================================================================= *)
(* 0. BASE EQUATIONAL SOUNDNESS                                      *)
(* ================================================================= *)

Lemma base_equiv_sound :
  forall {Sign Func : Type} `{FunctionSignature Func}
    {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
    {BEM : @BaseEpsilonModel Sign Func H C CC TSC}
    {CBM : @CoherentBaseModel Sign Func H C CC TSC BEM}
    {A B : b_ty} {f g : @b_tm Sign Func}
    (df : @base_typing Sign Func H A f B)
    (dg : @base_typing Sign Func H A g B),
  @base_equiv Sign Func H A B f g df dg -> interp_tm df ≅ interp_tm dg.
Proof.
  intros Sign Func H C CC TSC BEM CBM A B f g df dg Heq.
  induction Heq; simpl.
  - apply interp_coh.
  - symmetry. exact IHHeq.
  - etransitivity.
    + exact IHHeq1.
    + exact IHHeq2.
  - rewrite IHHeq1, IHHeq2. reflexivity.
  - rewrite IHHeq1, IHHeq2. reflexivity.
  - apply comp_assoc.
  - apply id_left.
  - apply id_right.
  - apply prod_map_fst.
  - apply prod_map_snd.
  - apply prod_eta.
  - apply terminal_map_unique.
  - symmetry. apply compos_prod.
Defined.

(* ================================================================= *)
(* 1. SUBSTITUTION AS PULLBACK                                       *)
(* ================================================================= *)

Lemma form_subst_iso :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred}
    {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
    {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
    {EHM : EpsilonHyperModel SGF}
    (I A : b_ty) (f : @b_tm Sign Func) (df : base_typing I f A) (Phi : @h_ty Sign Func Pred),
  interp_h_ty I (form_subst f Phi) ≅O
  @fobj _ _ (Pullback (interp_tm df)) (interp_h_ty A Phi).
Proof.
  intros Sign Func Pred HFunc HPred C CC TSC BEM GF SGF EHM.
  intros I A f df Phi.
  revert I A f df.
  induction Phi; intros I J g dg; simpl.
  - symmetry. apply pb_term_iso.
  - symmetry. apply pb_init_iso.
  - eapply iso_trans.
    + apply (prod_iso_cong (IHPhi1 I J g dg) (IHPhi2 I J g dg)).
    + symmetry. apply pb_prod_iso.
  - eapply iso_trans.
    + apply (coprod_iso_cong (IHPhi1 I J g dg) (IHPhi2 I J g dg)).
    + symmetry. apply pb_coprod_iso.
  - eapply iso_trans.
    + apply (exp_iso_cong (IHPhi2 I J g dg) (IHPhi1 I J g dg)).
    + symmetry. apply pb_exp_iso.
  - symmetry. eapply i_atom_pb.
  - eapply iso_trans.
    + apply pi_iso_cong.
      exact (IHPhi (b_Prod I b) (b_Prod J b) (b_subst_ext g) (typing_subst_ext dg)).
    + symmetry. apply beck_chevalley_pi.
Defined.

Lemma ctx_subst_iso :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred}
    {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
    {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
    {EHM : EpsilonHyperModel SGF}
    (I A : b_ty) (G : @h_context Sign Func Pred),
  interp_h_ctx (b_Prod I A) (ctx_subst b_fst G) ≅O
  @fobj _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (Func:=Func) (A:=I) (B:=A))))
    (interp_h_ctx I G).
Proof.
  intros Sign Func Pred HFunc HPred C CC TSC BEM GF SGF EHM I A G.
  induction G as [|Phi G' IHG']; simpl.
  - symmetry. apply pb_term_iso.
  - eapply iso_trans.
    + apply (prod_iso_cong IHG'
        (form_subst_iso (b_Prod I A) I b_fst
          (BT_Fst (Sign:=Sign) (Func:=Func) (A:=I) (B:=A)) Phi)).
    + symmetry. apply pb_prod_iso.
Defined.

Lemma pullback_fmap_iso :
  forall {C : SetoidCategory} {CC : CartesianCategory C} {GF : GoodFibration C}
    {X Y : obj} (f : hom X Y) (A B : @obj (Fiber Y)),
  A ≅O B -> @fobj _ _ (Pullback f) A ≅O @fobj _ _ (Pullback f) B.
Proof.
  intros C CC GF X Y f A B H.
  apply functor_iso_cong.
  exact H.
Defined.

(* ================================================================= *)
(* 2. FORMULA AND CONTEXT EQUIVALENCE SOUNDNESS                      *)
(* ================================================================= *)

Lemma interp_form_equiv :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
    {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
    {BEM : BaseEpsilonModel} {CBM : CoherentBaseModel}
    {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
    {EHM : EpsilonHyperModel SGF} {EGF : EpsilonGoodFibration},
  forall (I : b_ty) (Phi Psi : @h_ty Sign Func Pred),
  form_equiv I Phi Psi -> interp_h_ty I Phi ≅O interp_h_ty I Psi.
Proof.
  intros Sign Func Pred HFunc HPred SM C CC TSC BEM CBM GF SGF EHM EGF I Phi Psi Heq.
  induction Heq; simpl.
  - eapply i_atom_cong_global. exact b.
  - apply iso_refl.
  - symmetry. apply IHHeq.
  - eapply iso_trans. { apply IHHeq1. } { apply IHHeq2. }
  - apply prod_iso_cong. { apply IHHeq1. } { apply IHHeq2. }
  - apply coprod_iso_cong. { apply IHHeq1. } { apply IHHeq2. }
  - apply exp_iso_cong. { apply IHHeq2. } { apply IHHeq1. }
  - apply pi_iso_cong. apply IHHeq.
  - apply eps_functorial_iso.
    + eapply form_equiv_wf1. exact Heq.
    + eapply form_equiv_wf2. exact Heq.
    + exact IHHeq.
  - eapply iso_trans.
    + apply form_subst_iso with (df := BT_Id).
    + apply pullback_id_iso.
  - eapply iso_trans.
    + apply form_subst_iso with (df := dg).
    + eapply iso_trans.
      * apply pullback_fmap_iso.
        apply form_subst_iso with (df := df).
      * eapply iso_trans.
        -- symmetry. apply pullback_comp_iso.
        -- symmetry. apply form_subst_iso with (df := BT_Comp df dg).
  - eapply iso_trans.
    + exact (form_subst_iso I J f df Phi).
    + eapply iso_trans.
      * exact (@pb_iso C CC GF (interp_ty I) (interp_ty J)
          (interp_tm df) (interp_tm dg) (base_equiv_sound df dg b)
          (interp_h_ty J Phi)).
      * exact (iso_sym (form_subst_iso I J g dg Phi)).
  - symmetry. eapply eps_beck_chevalley_iso; eassumption.
Defined.

Lemma interp_ctx_equiv :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
    {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
    {BEM : BaseEpsilonModel} {CBM : CoherentBaseModel}
    {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
    {EHM : EpsilonHyperModel SGF} {EGF : EpsilonGoodFibration},
  forall (I : b_ty) (G1 G2 : @h_context Sign Func Pred),
  ctx_equiv I G1 G2 -> interp_h_ctx I G1 ≅O interp_h_ctx I G2.
Proof.
  intros Sign Func Pred HFunc HPred SM C CC TSC BEM CBM GF SGF EHM EGF I G1 G2 H_ctx.
  induction H_ctx; simpl.
  - apply iso_refl.
  - apply prod_iso_cong.
    + exact IHH_ctx.
    + apply interp_form_equiv. exact f.
Defined.

(* ================================================================= *)
(* 3. SOUNDNESS                                                      *)
(* ================================================================= *)

Theorem soundness :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
    {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
    {BEM : BaseEpsilonModel} {CBM : CoherentBaseModel}
    {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
    {EHM : EpsilonHyperModel SGF} {EGF : EpsilonGoodFibration},
  forall (I : b_ty) (G : @h_context Sign Func Pred)
    (p : @h_tm Sign Func Pred) (Phi : @h_ty Sign Func Pred),
  h_derivation I G p Phi ->
  hom (interp_h_ctx I G) (interp_h_ty I Phi).
Proof.
  intros Sign Func Pred HFunc HPred SM C CC TSC BEM CBM GF SGF EHM EGF I G p Phi H_der.
  induction H_der.
  - apply prod_snd.
  - eapply compose. exact IHH_der. apply prod_fst.
  - apply terminal_map.
  - eapply compose. apply (@iso_to _ _ _ (interp_form_equiv I _ _ f)). exact IHH_der.
  - eapply compose. exact IHH_der. apply (@iso_from _ _ _ (interp_ctx_equiv I _ _ c)).
  - apply exp_map. exact IHH_der.
  - eapply compose. eapply eval. apply (prod_map IHH_der1 IHH_der2).
  - apply (prod_map IHH_der1 IHH_der2).
  - eapply compose. eapply prod_fst. exact IHH_der.
  - eapply compose. eapply prod_snd. exact IHH_der.
  - eapply compose. eapply coprod_inl. exact IHH_der.
  - eapply compose. eapply coprod_inr. exact IHH_der.
  - eapply compose.
    + eapply compose.
      * apply (coprod_map IHH_der2 IHH_der3).
      * eapply compose.
        -- eapply eval.
        -- eapply compose.
           ++ eapply prod_map.
              ** eapply compose.
                 --- apply (coprod_map
                   (exp_map (compose coprod_inl (prod_map prod_snd prod_fst)))
                   (exp_map (compose coprod_inr (prod_map prod_snd prod_fst)))).
                 --- eapply prod_fst.
              ** eapply prod_snd.
           ++ eapply (prod_map prod_snd prod_fst).
    + eapply (prod_map (id _) IHH_der1).
  - eapply compose. apply initial_map. exact IHH_der.
  - apply right_adj_mor.
    eapply compose.
    + exact IHH_der.
    + apply (@iso_from _ _ _ (ctx_subst_iso I A G)).
  - eapply compose.
    + exact (@iso_from _ _ _ (form_subst_iso I (b_Prod I A) (b_pair b_id f)
        (BT_Pair BT_Id b) Phi)).
    + eapply compose.
      * eapply (@fmap _ _ (Pullback (interp_tm (BT_Pair BT_Id b))) _ _).
        apply (@epsilon _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (Func:=Func) (A:=I) (B:=A))))
          pullback_has_right_adjoint).
      * assert (H_eq : compose prod_fst (prod_map (id (interp_ty I)) (interp_tm b)) ≅ id (interp_ty I)).
        { apply prod_map_fst. }
        eapply compose.
        -- apply (@iso_to _ _ _ (pullback_comp_iso prod_fst
             (prod_map (id (interp_ty I)) (interp_tm b)) (interp_h_ty I (Ty_All A Phi)))).
        -- eapply compose.
           ++ apply (@iso_to _ _ _ (pb_iso (id (interp_ty I))
                (compose prod_fst (prod_map (id (interp_ty I)) (interp_tm b)))
                (symmetry H_eq) (interp_h_ty I (Ty_All A Phi)))).
           ++ eapply compose.
              ** apply (@iso_from _ _ _ (pullback_id_iso (interp_h_ty I (Ty_All A Phi)))).
              ** exact IHH_der.
  - eapply compose.
    + apply eps_intro.
      * eapply h_derivation_wf_inv; eassumption.
      * exact b.
    + exact IHH_der.
  - eapply compose.
    + apply (eps_elim_frobenius I A G Phi Chi).
      * eapply meta_ctx_wf. exact H_der1.
      * exact (@h_derivation_wf_inv Sign Func Pred HFunc HPred SM
          I A G p Phi (b_const A (skolem_index A Phi))
          (@BT_Const Sign Func HFunc I A (skolem_index A Phi)) H_der1).
      * eapply form_wf_fst_inv.
        eapply meta_type_wf. exact H_der2.
      * exact IHH_der2.
    + apply prod_map.
      * apply id.
      * exact IHH_der1.
Defined.
