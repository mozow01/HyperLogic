(* theories/Semantics/Individual/Individual_Soundness.v *)

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

Require Import HyperLogic.Logic.Base.Individual.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax_Lemmas.
Require Import HyperLogic.Logic.Hyper.Individual.Hyper_Syntax.
Require Import HyperLogic.Semantics.Individual.Individual_Fibration.

Lemma form_subst_iso :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred}
    {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
    {BEM : BaseEpsilonFullModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
    {EHM : EpsilonHyperModel SGF}
    (I A : b_ty) (f : @b_tm Sign Func) (df : base_typing I f A) (Phi : @h_ty Sign Func Pred),
  interp_h_ty I (form_subst f Phi) ≅O @fobj _ _ (Pullback (interp_tm df)) (interp_h_ty A Phi).
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
  - eapply iso_trans.
    + apply sigma_iso_cong.
      exact (IHPhi (b_Prod I b) (b_Prod J b) (b_subst_ext g) (typing_subst_ext dg)).
    + symmetry. apply beck_chevalley_sigma.
Defined.

Lemma ctx_subst_iso :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred}
    {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
    {BEM : BaseEpsilonFullModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
    {EHM : EpsilonHyperModel SGF}
    (I A : b_ty) (G : @h_context Sign Func Pred),
  interp_h_ctx (b_Prod I A) (ctx_subst b_fst G) ≅O
  @fobj _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (Func:=Func) (A:=I) (B:=A)))) (interp_h_ctx I G).
Proof.
  intros Sign Func Pred HFunc HPred C CC TSC BEM GF SGF EHM I A G.
  induction G as [|Phi G' IHG']; simpl.
  - symmetry. apply pb_term_iso.
  - eapply iso_trans.
    + apply (prod_iso_cong IHG' (form_subst_iso (b_Prod I A) I b_fst (BT_Fst (Sign:=Sign) (Func:=Func) (A:=I) (B:=A)) Phi)).
    + symmetry. apply pb_prod_iso.
Defined.

Lemma interp_subst_cong : forall {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred}
  {C : SetoidCategory} {CC : CartesianCategory C}
  {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonFullModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
  {EHM : EpsilonHyperModel SGF} (I J : b_ty) (f g : @b_tm Sign Func) (Phi : @h_ty Sign Func Pred)
  (df : base_typing I f J) (dg : base_typing I g J),
  base_equiv df dg ->
  WellFormed J Phi ->
  interp_h_ty I (form_subst f Phi) ≅O interp_h_ty I (form_subst g Phi).
Proof.
  intros Sign Func Pred HFunc HPred C CC TSC BEM GF SGF EHM I J f g Phi df dg Heq Hwf.
  revert I f g df dg Heq.
  induction Hwf; intros I' f' g' df' dg' Heq'; simpl.
  - apply iso_refl.
  - apply iso_refl.
  - apply prod_iso_cong. { eapply IHHwf1. exact Heq'. } { eapply IHHwf2. exact Heq'. }
  - apply coprod_iso_cong. { eapply IHHwf1. exact Heq'. } { eapply IHHwf2. exact Heq'. }
  - apply exp_iso_cong. { eapply IHHwf2. exact Heq'. } { eapply IHHwf1. exact Heq'. }
  - eapply i_atom_cong_global. eapply BE_CongComp.
    + exact Heq'.
    + exact (BE_Refl _ _ _ b b).
  - apply pi_iso_cong.
    eapply (IHHwf (b_Prod I' A) (b_subst_ext f') (b_subst_ext g')).
    unfold b_subst_ext. eapply BE_CongPair.
    + eapply BE_CongComp.
      * exact (BE_Refl _ _ _ BT_Fst BT_Fst).
      * exact Heq'.
    + exact (BE_Refl _ _ _ BT_Snd BT_Snd).
  - apply sigma_iso_cong.
    eapply (IHHwf (b_Prod I' A) (b_subst_ext f') (b_subst_ext g')).
    unfold b_subst_ext. eapply BE_CongPair.
    + eapply BE_CongComp.
      * exact (BE_Refl _ _ _ BT_Fst BT_Fst).
      * exact Heq'.
    + exact (BE_Refl _ _ _ BT_Snd BT_Snd).
Defined.

Lemma interp_subst_id : forall {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred}
  {C : SetoidCategory} {CC : CartesianCategory C}
  {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonFullModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
  {EHM : EpsilonHyperModel SGF} (I : b_ty) (Phi : @h_ty Sign Func Pred),
  WellFormed I Phi ->
  interp_h_ty I (form_subst b_id Phi) ≅O interp_h_ty I Phi.
Proof.
  intros Sign Func Pred HFunc HPred C CC TSC BEM GF SGF EHM I Phi Hwf.
  induction Hwf.
  - simpl. apply iso_refl.
  - simpl. apply iso_refl.
  - simpl. apply prod_iso_cong; assumption.
  - simpl. apply coprod_iso_cong; assumption.
  - simpl. apply exp_iso_cong; assumption.
  - simpl. eapply i_atom_cong_global. apply BE_IdR.
  - simpl. apply pi_iso_cong. eapply iso_trans.
    + eapply (@interp_subst_cong Sign Func Pred HFunc HPred C CC TSC BEM GF SGF EHM
        (b_Prod I A) (b_Prod I A) (b_subst_ext b_id) b_id Phi
        (BT_Pair (BT_Comp BT_Id BT_Fst) BT_Snd) BT_Id).
      * unfold b_subst_ext. eapply BE_Trans. 2: { apply BE_EtaPair. }
        eapply BE_CongPair.
        -- eapply BE_Trans. apply BE_IdL. eapply BE_Sym. apply BE_IdR.
        -- eapply BE_Sym. apply BE_IdR.
      * exact Hwf.
    + exact IHHwf.
  - simpl. apply sigma_iso_cong. eapply iso_trans.
    + eapply (@interp_subst_cong Sign Func Pred HFunc HPred C CC TSC BEM GF SGF EHM
        (b_Prod I A) (b_Prod I A) (b_subst_ext b_id) b_id Phi
        (BT_Pair (BT_Comp BT_Id BT_Fst) BT_Snd) BT_Id).
      * unfold b_subst_ext. eapply BE_Trans. 2: { apply BE_EtaPair. }
        eapply BE_CongPair.
        -- eapply BE_Trans. apply BE_IdL. eapply BE_Sym. apply BE_IdR.
        -- eapply BE_Sym. apply BE_IdR.
      * exact Hwf.
    + exact IHHwf.
  Unshelve.
  exact (pred_dom p).
  exact b.
Defined.

Lemma interp_subst_comp : forall {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred}
  {C : SetoidCategory} {CC : CartesianCategory C}
  {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonFullModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
  {EHM : EpsilonHyperModel SGF} (I J K : b_ty) (f g : @b_tm Sign Func) (Phi : @h_ty Sign Func Pred)
  (df : base_typing J f K) (dg : base_typing I g J),
  WellFormed K Phi ->
  interp_h_ty I (form_subst (b_comp f g) Phi) ≅O interp_h_ty I (form_subst g (form_subst f Phi)).
Proof.
  intros Sign Func Pred HFunc HPred C CC TSC BEM GF SGF EHM I J K f g Phi df dg Hwf.
  revert I J f g df dg.
  induction Hwf; intros I0 J0 f0 g0 df0 dg0; simpl.
  - apply iso_refl.
  - apply iso_refl.
  - apply prod_iso_cong. { apply (IHHwf1 I0 J0 f0 g0 df0 dg0). } { apply (IHHwf2 I0 J0 f0 g0 df0 dg0). }
  - apply coprod_iso_cong. { apply (IHHwf1 I0 J0 f0 g0 df0 dg0). } { apply (IHHwf2 I0 J0 f0 g0 df0 dg0). }
  - apply exp_iso_cong. { apply (IHHwf2 I0 J0 f0 g0 df0 dg0). } { apply (IHHwf1 I0 J0 f0 g0 df0 dg0). }
  - eapply i_atom_cong_global.
    exact (BE_Assoc I0 J0 I (pred_dom p) g0 f0 t dg0 df0 b).
  - apply pi_iso_cong. eapply iso_trans.
    + eapply (interp_subst_cong (b_Prod I0 A) (b_Prod I A)
        (b_subst_ext (b_comp f0 g0))
        (b_comp (b_subst_ext f0) (b_subst_ext g0)) Phi).
      * unfold b_subst_ext. eapply BE_Trans.
        { eapply BE_CongPair.
          - eapply BE_Sym. exact (BE_Assoc _ _ _ _ _ _ _ BT_Fst dg0 df0).
          - exact (BE_Refl _ _ _ BT_Snd BT_Snd). }
        eapply BE_Sym. eapply BE_Trans.
        { exact (BE_CompPair _ _ _ _ _ _ _ (BT_Comp df0 BT_Fst) BT_Snd
            (BT_Pair (BT_Comp dg0 BT_Fst) BT_Snd)). }
        eapply BE_CongPair.
        -- eapply BE_Trans.
           { eapply BE_Sym.
             exact (BE_Assoc _ _ _ _ _ _ _
               (BT_Pair (BT_Comp dg0 BT_Fst) BT_Snd) BT_Fst df0). }
           eapply BE_CongComp.
           ++ apply BE_BetaFst.
           ++ exact (BE_Refl _ _ _ df0 df0).
        -- apply BE_BetaSnd.
      * exact Hwf.
    + eapply (IHHwf (b_Prod I0 A) (b_Prod J0 A) (b_subst_ext f0) (b_subst_ext g0)).
      * unfold b_subst_ext. eapply BT_Pair.
        -- eapply BT_Comp.
           ++ exact df0.
           ++ apply BT_Fst.
        -- apply BT_Snd.
      * unfold b_subst_ext. eapply BT_Pair.
        -- eapply BT_Comp.
           ++ exact dg0.
           ++ apply BT_Fst.
        -- apply BT_Snd.
  - apply sigma_iso_cong. eapply iso_trans.
    + eapply (interp_subst_cong (b_Prod I0 A) (b_Prod I A)
        (b_subst_ext (b_comp f0 g0))
        (b_comp (b_subst_ext f0) (b_subst_ext g0)) Phi).
      * unfold b_subst_ext. eapply BE_Trans.
        { eapply BE_CongPair.
          - eapply BE_Sym. exact (BE_Assoc _ _ _ _ _ _ _ BT_Fst dg0 df0).
          - exact (BE_Refl _ _ _ BT_Snd BT_Snd). }
        eapply BE_Sym. eapply BE_Trans.
        { exact (BE_CompPair _ _ _ _ _ _ _ (BT_Comp df0 BT_Fst) BT_Snd
            (BT_Pair (BT_Comp dg0 BT_Fst) BT_Snd)). }
        eapply BE_CongPair.
        -- eapply BE_Trans.
           { eapply BE_Sym.
             exact (BE_Assoc _ _ _ _ _ _ _
               (BT_Pair (BT_Comp dg0 BT_Fst) BT_Snd) BT_Fst df0). }
           eapply BE_CongComp.
           ++ apply BE_BetaFst.
           ++ exact (BE_Refl _ _ _ df0 df0).
        -- apply BE_BetaSnd.
      * exact Hwf.
    + eapply (IHHwf (b_Prod I0 A) (b_Prod J0 A) (b_subst_ext f0) (b_subst_ext g0)).
      * unfold b_subst_ext. eapply BT_Pair.
        -- eapply BT_Comp.
           ++ exact df0.
           ++ apply BT_Fst.
        -- apply BT_Snd.
      * unfold b_subst_ext. eapply BT_Pair.
        -- eapply BT_Comp.
           ++ exact dg0.
           ++ apply BT_Fst.
        -- apply BT_Snd.
Defined.

Lemma interp_ifol_form_equiv :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred}
    {C : SetoidCategory} {CC : CartesianCategory C}
    {TSC : TwoSortCategory C} {BEM : BaseEpsilonFullModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
    {EHM : EpsilonHyperModel SGF},
  forall (I : b_ty) (Phi Psi : @h_ty Sign Func Pred),
  ifol_form_equiv I Phi Psi ->
  interp_h_ty I Phi ≅O interp_h_ty I Psi.
Proof.
  intros Sign Func Pred HFunc HPred C CC TSC BEM GF SGF EHM I Phi Psi Heq.
  induction Heq; simpl.
  - eapply i_atom_cong_global. exact b.
  - apply iso_refl.
  - symmetry. apply IHHeq.
  - eapply iso_trans. { apply IHHeq1. } { apply IHHeq2. }
  - apply prod_iso_cong. { apply IHHeq1. } { apply IHHeq2. }
  - apply coprod_iso_cong. { apply IHHeq1. } { apply IHHeq2. }
  - apply exp_iso_cong. { apply IHHeq2. } { apply IHHeq1. }
  - apply pi_iso_cong. apply IHHeq.
  - apply sigma_iso_cong. apply IHHeq.
  - apply interp_subst_id. exact w.
  - symmetry. apply (interp_subst_comp I J K). exact df. exact dg. exact w.
  - eapply interp_subst_cong. exact b. exact w.
Defined.

Lemma interp_ifol_ctx_equiv :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred}
    {C : SetoidCategory} {CC : CartesianCategory C}
    {TSC : TwoSortCategory C} {BEM : BaseEpsilonFullModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
    {EHM : EpsilonHyperModel SGF},
  forall (I : b_ty) (G1 G2 : @h_context Sign Func Pred),
  ifol_ctx_equiv I G1 G2 ->
  interp_h_ctx I G1 ≅O interp_h_ctx I G2.
Proof.
  intros Sign Func Pred HFunc HPred C CC TSC BEM GF SGF EHM I G1 G2 H_ctx.
  induction H_ctx; simpl.
  - apply iso_refl.
  - apply prod_iso_cong.
    + exact IHH_ctx.
    + apply interp_ifol_form_equiv. exact i.
Defined.

Theorem soundness :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred}
    {C : SetoidCategory} {CC : CartesianCategory C}
    {TSC : TwoSortCategory C} {BEM : BaseEpsilonFullModel} {GF : GoodFibration C}
    {SGF : StrictGoodFibration C GF} {EHM : EpsilonHyperModel SGF},
  forall (I : b_ty) (G : @h_context Sign Func Pred) (p : @h_tm Sign Func Pred) (Phi : @h_ty Sign Func Pred),
  ifol_h_derivation I G p Phi ->
  hom (interp_h_ctx I G) (interp_h_ty I Phi).
Proof.
  intros Sign Func Pred HFunc HPred C CC TSC BEM GF SGF EHM I G p Phi H_der.
  induction H_der.
  - apply prod_snd.
  - eapply compose. exact IHH_der. apply prod_fst.
  - apply terminal_map.
  - eapply compose.
    + match goal with
      | H : ifol_form_equiv _ _ _ |- _ =>
          apply (@iso_to _ _ _ (interp_ifol_form_equiv _ _ _ H))
      end.
    + exact IHH_der.
  - eapply compose.
    + exact IHH_der.
    + match goal with
      | H : ifol_ctx_equiv _ _ _ |- _ =>
          apply (@iso_from _ _ _ (interp_ifol_ctx_equiv _ _ _ H))
      end.
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
                 --- apply (coprod_map (exp_map (compose coprod_inl (prod_map prod_snd prod_fst)))
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
    + exact (@iso_from _ _ _ (form_subst_iso I (b_Prod I A) (b_pair b_id f) (BT_Pair BT_Id b) Phi)).
    + eapply compose.
      * eapply (@fmap _ _ (Pullback (interp_tm (BT_Pair BT_Id b))) _ _).
        apply (@epsilon _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (Func:=Func) (A:=I) (B:=A)))) pullback_has_right_adjoint).
      * assert (H_eq : compose prod_fst (prod_map (id (interp_ty I)) (interp_tm b)) ≅ id (interp_ty I)).
        { apply prod_map_fst. }
        eapply compose.
        -- apply (@iso_to _ _ _ (pullback_comp_iso prod_fst (prod_map (id (interp_ty I)) (interp_tm b)) (interp_h_ty I (Ty_All A Phi)))).
        -- eapply compose.
           ++ apply (@iso_to _ _ _ (pb_iso (id (interp_ty I)) (compose prod_fst (prod_map (id (interp_ty I)) (interp_tm b))) (symmetry H_eq) (interp_h_ty I (Ty_All A Phi)))).
           ++ eapply compose.
              ** apply (@iso_from _ _ _ (pullback_id_iso (interp_h_ty I (Ty_All A Phi)))).
              ** exact IHH_der.
  - eapply compose.
    + apply (@iso_to _ _ _ (pullback_id_iso (interp_h_ty I (Ty_Ex A Phi)))).
    + assert (H_eq : compose prod_fst (prod_map (id (interp_ty I)) (interp_tm b)) ≅ id (interp_ty I)).
      { apply prod_map_fst. }
      eapply compose.
      * apply (@iso_to _ _ _ (pb_iso (compose prod_fst (prod_map (id (interp_ty I)) (interp_tm b))) (id (interp_ty I)) H_eq (interp_h_ty I (Ty_Ex A Phi)))).
      * eapply compose.
        -- apply (@iso_from _ _ _ (pullback_comp_iso prod_fst (prod_map (id (interp_ty I)) (interp_tm b)) (interp_h_ty I (Ty_Ex A Phi)))).
        -- eapply compose.
           ++ eapply (@fmap _ _ (Pullback (interp_tm (BT_Pair BT_Id b))) _ _).
              apply (@unit _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (Func:=Func) (A:=I) (B:=A)))) pullback_has_left_adjoint).
           ++ eapply compose.
              ** exact (@iso_to _ _ _ (form_subst_iso I (b_Prod I A) (b_pair b_id f) (BT_Pair BT_Id b) Phi)).
              ** exact IHH_der.
  - assert (H_premissza : hom (prod (@fobj _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (Func:=Func) (A:=I) (B:=A)))) (interp_h_ctx I G))
      (interp_h_ty (b_Prod I A) Phi))
      (@fobj _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (Func:=Func) (A:=I) (B:=A)))) (interp_h_ty I Chi))).
    { eapply compose.
      + exact (@iso_to _ _ _ (form_subst_iso (b_Prod I A) I b_fst BT_Fst Chi)).
      + eapply compose.
        * exact IHH_der2.
        * cbn. apply prod_map.
          -- eapply compose.
             ++ apply (@iso_from _ _ _ (ctx_subst_iso I A G)).
             ++ apply prod_fst.
          -- apply prod_snd. }
    assert (H_curry : hom (interp_h_ty (b_Prod I A) Phi)
      (exp (@fobj _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (Func:=Func) (A:=I) (B:=A)))) (interp_h_ty I Chi))
        (@fobj _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (Func:=Func) (A:=I) (B:=A)))) (interp_h_ctx I G)))).
    { apply exp_map.
      eapply compose.
      + exact H_premissza.
      + apply prod_map. { apply prod_snd. } { apply prod_fst. } }
    assert (H_pb : hom (interp_h_ty (b_Prod I A) Phi)
      (@fobj _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (Func:=Func) (A:=I) (B:=A))))
        (exp (interp_h_ty I Chi) (interp_h_ctx I G)))).
    { eapply compose.
      + apply (@iso_from _ _ _ (pb_exp_iso (interp_tm (BT_Fst (Sign:=Sign) (Func:=Func) (A:=I) (B:=A))) _ _)).
      + exact H_curry. }
    assert (H_sigma : hom (interp_h_ty I (Ty_Ex A Phi))
      (exp (interp_h_ty I Chi) (interp_h_ctx I G))).
    { apply (@left_adj_mor _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (Func:=Func) (A:=I) (B:=A)))) pullback_has_left_adjoint).
      exact H_pb. }
    eapply compose.
    + apply (@eval (Fiber (interp_ty I)) _ _ (interp_h_ctx I G) (interp_h_ty I Chi)).
    + apply prod_map.
      * eapply compose. { exact H_sigma. } { exact IHH_der1. }
      * apply id.
Defined.

Theorem soundness_inhabited :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred}
    {C : SetoidCategory} {CC : CartesianCategory C}
    {TSC : TwoSortCategory C} {BEM : BaseEpsilonFullModel} {GF : GoodFibration C}
    {SGF : StrictGoodFibration C GF} {EHM : EpsilonHyperModel SGF}
    (I : b_ty) (G : @h_context Sign Func Pred) (p : @h_tm Sign Func Pred) (Phi : @h_ty Sign Func Pred),
  ifol_h_derivation I G p Phi ->
  inhabited (hom (interp_h_ctx I G) (interp_h_ty I Phi)).
Proof.
  intros Sign Func Pred HFunc HPred C CC TSC BEM GF SGF EHM I G p Phi Hder.
  constructor.
  eapply soundness.
  exact Hder.
Defined.
