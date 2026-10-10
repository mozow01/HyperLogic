
Require Import List.
Import ListNotations.

Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax_Lemmas.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.

Require Import Coq.Program.Equality.

Lemma wf_subst : forall {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred}
  {I J : b_ty} (t : @b_tm Sign Func) (dt : base_typing I t J) (Phi : @h_ty Sign Func Pred),
  WellFormed J Phi ->
  WellFormed I (form_subst t Phi).
Proof.
  intros Sign Func Pred HFunc HPred I J t dt Phi H.
  revert I t dt.
  induction H; intros I0 t0 dt0.
  - simpl. apply WF_Unit.
  - simpl. apply WF_Void.
  - simpl. apply WF_Prod.
    + apply IHWellFormed1. exact dt0.
    + apply IHWellFormed2. exact dt0.
  - simpl. apply WF_Sum.
    + apply IHWellFormed1. exact dt0.
    + apply IHWellFormed2. exact dt0.
  - simpl. apply WF_Arrow.
    + apply IHWellFormed1. exact dt0.
    + apply IHWellFormed2. exact dt0.
  - simpl. eapply WF_Atom.
    eapply BT_Comp.
    + eassumption.
    + exact dt0.
  - simpl. apply WF_All.
    apply IHWellFormed.
    unfold b_subst_ext. apply BT_Pair.
    + eapply BT_Comp. exact dt0. apply BT_Fst.
    + apply BT_Snd.
  - simpl. apply WF_Ex.
    apply IHWellFormed.
    unfold b_subst_ext. apply BT_Pair.
    + eapply BT_Comp. exact dt0. apply BT_Fst.
    + apply BT_Snd.
Defined.

Lemma typing_subst_ext : forall {Sign Func : Type} `{FunctionSignature Func}
  {I J A : b_ty} {f : @b_tm Sign Func},
  base_typing I f J ->
  base_typing (b_Prod I A) (b_subst_ext f) (b_Prod J A).
Proof.
  intros Sign Func HFunc I J A f Hf.
  unfold b_subst_ext.
  apply BT_Pair.
  - eapply BT_Comp.
    + exact Hf.
    + apply BT_Fst.
  - apply BT_Snd.
Defined.

Lemma form_equiv_wf : forall {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred}
  (I : b_ty) (Phi Psi : @h_ty Sign Func Pred),
  form_equiv I Phi Psi -> (WellFormed I Phi * WellFormed I Psi)%type.
Proof.
  intros Sign Func Pred HFunc HPred SM I Phi Psi H.
  induction H.
  - split; eapply WF_Atom; eassumption.
  - split; assumption.
  - destruct IHform_equiv; split; assumption.
  - destruct IHform_equiv1, IHform_equiv2; split; eassumption.
  - destruct IHform_equiv1, IHform_equiv2; split; apply WF_Prod; assumption.
  - destruct IHform_equiv1, IHform_equiv2; split; apply WF_Sum; assumption.
  - destruct IHform_equiv1, IHform_equiv2; split; apply WF_Arrow; assumption.
  - destruct IHform_equiv; split; apply WF_All; assumption.
  - destruct IHform_equiv; split; apply WF_Ex; assumption.
  - split.
    + apply WF_Ex. exact w.
    + eapply wf_subst.
      * eapply BT_Pair. apply BT_Id. apply BT_Const.
      * exact w.
  - destruct IHform_equiv as [wf_Phi wf_Psi].
    split.
    + eapply wf_subst.
      * eapply BT_Pair. apply BT_Id. apply BT_Const.
      * exact wf_Phi.
    + eapply wf_subst.
      * eapply BT_Pair. apply BT_Id. apply BT_Const.
      * exact wf_Psi.
  - split.
    + eapply wf_subst. apply BT_Id. exact w.
    + exact w.
  - split.
    + eapply wf_subst. exact dg. eapply wf_subst. exact df. exact w.
    + eapply wf_subst. eapply BT_Comp. exact df. exact dg. exact w.
  - split.
    + eapply wf_subst. exact df. exact w.
    + eapply wf_subst. exact dg. exact w.
  - split.
    + eapply wf_subst.
      * eapply BT_Pair. apply BT_Id. apply BT_Const.
      * eapply wf_subst. eapply typing_subst_ext. exact dt. exact w.
    + eapply wf_subst.
      * exact dt.
      * eapply wf_subst. eapply BT_Pair. apply BT_Id. apply BT_Const. exact w.
Defined.

Lemma ctx_equiv_wf_left : forall {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred}
  (I : b_ty) (G G' : @h_context Sign Func Pred),
  ctx_equiv I G G' -> All_WellFormed I G' -> All_WellFormed I G.
Proof.
  intros Sign Func Pred HFunc HPred SM I G G' H Hwf_G'.
  induction H.
  - exact Hwf_G'.
  - inversion Hwf_G'; subst.
    apply AWF_Cons.
    + apply (form_equiv_wf I Phi Psi f).
    + apply IHctx_equiv. exact X0.
Defined.

Lemma ctx_equiv_wf_right : forall {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred}
  (I : b_ty) (G1 G2 : @h_context Sign Func Pred),
  ctx_equiv I G1 G2 -> All_WellFormed I G1 -> All_WellFormed I G2.
Proof.
  intros Sign Func Pred HFunc HPred SM I G1 G2 H Hwf1.
  induction H.
  - exact Hwf1.
  - inversion Hwf1; subst.
    apply AWF_Cons.
    + destruct (form_equiv_wf I Phi Psi f) as [_ wf_Psi].
      exact wf_Psi.
    + apply IHctx_equiv. exact X0.
Defined.

Lemma form_equiv_subst : forall {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred}
  {I J : b_ty} (t : @b_tm Sign Func) (dt : base_typing I t J) (Phi Psi : @h_ty Sign Func Pred),
  form_equiv J Phi Psi ->
  form_equiv I (form_subst t Phi) (form_subst t Psi).
Proof.
  intros Sign Func Pred HFunc HPred SM I J t dt Phi Psi H.
  revert I t dt.
  induction H; intros I0 t0 dt0.
  - simpl. eapply (@FE_Atom Sign Func Pred HFunc HPred SM I0 p
      (b_comp t1 t0) (b_comp t2 t0)
      (BT_Comp d1 dt0) (BT_Comp d2 dt0)).
    apply BE_CongComp.
    + apply BE_Refl.
    + exact b.
  - apply FE_Refl.
    eapply wf_subst.
    + exact dt0.
    + exact w.
  - apply FE_Sym.
    apply IHform_equiv. exact dt0.
  - eapply FE_Trans.
    + apply IHform_equiv1. exact dt0.
    + apply IHform_equiv2. exact dt0.
  - simpl. apply FE_Prod.
    + apply IHform_equiv1. exact dt0.
    + apply IHform_equiv2. exact dt0.
  - simpl. apply FE_Sum.
    + apply IHform_equiv1. exact dt0.
    + apply IHform_equiv2. exact dt0.
  - simpl. apply FE_Arrow.
    + apply IHform_equiv1. exact dt0.
    + apply IHform_equiv2. exact dt0.
  - simpl. apply FE_All.
    apply IHform_equiv.
    apply typing_subst_ext. exact dt0.
  - simpl. apply FE_Ex.
    apply IHform_equiv.
    apply typing_subst_ext. exact dt0.
  - eapply FE_Trans.
    + apply FE_Eps_Adjoint_Iso.
      eapply wf_subst.
      * exact (BT_Pair (BT_Comp dt0 BT_Fst) BT_Snd).
      * exact w.
    + eapply FE_Eps_BC.
      * exact dt0.
      * exact w.
  - eapply FE_Trans.
    + eapply FE_Sym.
      eapply FE_Eps_BC.
      * exact dt0.
      * exact (fst (form_equiv_wf (b_Prod I A) Phi Psi H)).
    + eapply FE_Trans.
      * eapply FE_Eps_Functorial.
        apply (IHform_equiv (b_Prod I0 A) (b_subst_ext t0)).
        apply typing_subst_ext. exact dt0.
      * eapply FE_Eps_BC.
        -- exact dt0.
        -- exact (snd (form_equiv_wf (b_Prod I A) Phi Psi H)).
  - eapply FE_Trans.
    + eapply FE_Pullback_Comp.
      * apply BT_Id.
      * exact dt0.
      * exact w.
    + eapply FE_Pullback_Cong.
      * apply BE_IdL.
      * exact w.
  - eapply FE_Trans.
    + eapply FE_Pullback_Comp.
      * exact dg.
      * exact dt0.
      * eapply wf_subst.
        -- exact df.
        -- exact w.
    + eapply FE_Trans.
      * eapply FE_Pullback_Comp.
        -- exact df.
        -- eapply BT_Comp. exact dg. exact dt0.
        -- exact w.
      * eapply FE_Trans.
        -- eapply FE_Pullback_Cong.
           ++ apply BE_Assoc.
           ++ exact w.
        -- eapply FE_Sym.
           eapply FE_Pullback_Comp.
           ++ eapply BT_Comp. exact df. exact dg.
           ++ exact dt0.
           ++ exact w.
  - eapply FE_Trans.
    + eapply FE_Pullback_Comp.
      * exact df.
      * exact dt0.
      * exact w.
    + eapply FE_Trans.
      * eapply FE_Pullback_Cong.
        -- eapply BE_CongComp.
           ++ apply BE_Refl.
           ++ exact b.
        -- exact w.
      * eapply FE_Sym.
        eapply FE_Pullback_Comp.
        -- exact dg.
        -- exact dt0.
        -- exact w.
  - eapply FE_Trans.
    + eapply FE_Sym.
      eapply FE_Eps_BC.
      * exact dt0.
      * eapply wf_subst.
        -- eapply typing_subst_ext. exact dt.
        -- exact w.
    + eapply FE_Trans.
      * eapply FE_Eps_Functorial.
        eapply FE_Pullback_Comp.
        -- eapply typing_subst_ext. exact dt.
        -- eapply typing_subst_ext. exact dt0.
        -- exact w.
      * eapply FE_Trans.
        -- eapply FE_Eps_Functorial.
           eapply FE_Pullback_Cong.
           ++ unfold b_subst_ext.
              eapply BE_Trans.
              ** apply BE_CompPair.
              ** eapply BE_CongPair.
                 --- eapply BE_Trans.
                     +++ eapply BE_Sym. apply BE_Assoc.
                     +++ eapply BE_Trans.
                         *** eapply BE_CongComp.
                             ---- apply BE_BetaFst.
                             ---- apply BE_Refl.
                         *** apply BE_Assoc.
                 --- apply BE_BetaSnd.
           ++ exact w.
        -- eapply FE_Trans.
           ++ eapply FE_Eps_BC.
              ** eapply BT_Comp. exact dt. exact dt0.
              ** exact w.
           ++ eapply FE_Sym.
              eapply FE_Pullback_Comp.
              ** exact dt.
              ** exact dt0.
              ** eapply wf_subst.
                 --- eapply BT_Pair. apply BT_Id. apply BT_Const.
                 --- exact w.
  Unshelve.
  all: repeat match goal with
  | |- base_typing _ _ _ =>
      eapply BT_Comp || eapply BT_Pair ||
      apply BT_Id || apply BT_Fst || apply BT_Snd ||
      apply typing_subst_ext || eassumption
  end.
Defined.

Lemma ctx_equiv_subst : forall {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred}
  {I J : b_ty} (t : @b_tm Sign Func) (dt : base_typing I t J) (G1 G2 : @h_context Sign Func Pred),
  ctx_equiv J G1 G2 ->
  ctx_equiv I (ctx_subst t G1) (ctx_subst t G2).
Proof.
  intros Sign Func Pred HFunc HPred SM I J t dt G1 G2 Hctx.
  induction Hctx; simpl.
  - apply CEq_Nil.
  - apply CEq_Cons.
    + eapply form_equiv_subst.
      * exact dt.
      * exact f.
    + exact IHHctx.
Defined.

Lemma form_wf_subst_inv : forall {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
  {I J : b_ty} (f : @b_tm Sign Func) (df : base_typing I f J)
  (Phi : @h_ty Sign Func Pred),
  WellFormed I (form_subst f Phi) ->
  WellFormed J Phi.
Proof.
  intros Sign Func Pred HFunc HPred SM I J f df Phi.
  generalize dependent J.
  generalize dependent I.
  generalize dependent f.
  induction Phi; intros f I J df Hwf; simpl in Hwf; inversion Hwf; subst.
  - apply WF_Unit.
  - apply WF_Void.
  - apply WF_Prod.
    + eapply IHPhi1; eassumption.
    + eapply IHPhi2; eassumption.
  - apply WF_Sum.
    + eapply IHPhi1; eassumption.
    + eapply IHPhi2; eassumption.
  - apply WF_Arrow.
    + eapply IHPhi1; eassumption.
    + eapply IHPhi2; eassumption.
  - eapply WF_Atom.
    match goal with
    | Hcomp : base_typing I (b_comp ?u f) ?B |- base_typing J ?u _ =>
        inversion Hcomp; subst;
        match goal with
        | Hu : base_typing ?Mid u ?B',
          Hf : base_typing I f ?Mid |- _ =>
            assert (H_mid : Mid = J)
              by (eapply base_typing_unique; [exact Hf | exact df]);
            rewrite H_mid in Hu;
            exact Hu
        end
    end.
  - apply WF_All.
    eapply IHPhi.
    + exact (@typing_subst_ext Sign Func HFunc I J b f df).
    + exact X.
  - apply WF_Ex.
    eapply IHPhi.
    + exact (@typing_subst_ext Sign Func HFunc I J b f df).
    + exact X.
Defined.

Lemma form_wf_fst_inv : forall {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
  {I A : b_ty} {Phi : @h_ty Sign Func Pred},
  WellFormed (b_Prod I A) (form_subst b_fst Phi) ->
  WellFormed I Phi.
Proof.
  intros Sign Func Pred HFunc HPred SM I A Phi Hwf.
  eapply form_wf_subst_inv.
  - eapply BT_Fst.
  - exact Hwf.
Defined.

Lemma ctx_wf_fst_inv : forall {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
  {I A : b_ty} {G : @h_context Sign Func Pred},
  All_WellFormed (b_Prod I A) (ctx_subst b_fst G) ->
  All_WellFormed I G.
Proof.
  intros Sign Func Pred HFunc HPred SM I A G H.
  induction G as [|Phi G IH].
  - simpl in H. inversion H. apply AWF_Nil.
  - simpl in H. inversion H; subst.
    apply AWF_Cons.
    + eapply form_wf_fst_inv. exact X.
    + apply IH. exact X0.
Defined.

Lemma form_equiv_wf1 : forall {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
  (I : b_ty) (Phi Psi : @h_ty Sign Func Pred),
  form_equiv I Phi Psi ->
  WellFormed I Phi.
Proof.
  intros Sign Func Pred HFunc HPred SM I Phi Psi H.
  exact (fst (form_equiv_wf I Phi Psi H)).
Defined.

Lemma form_equiv_wf2 : forall {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
  (I : b_ty) (Phi Psi : @h_ty Sign Func Pred),
  form_equiv I Phi Psi ->
  WellFormed I Psi.
Proof.
  intros Sign Func Pred HFunc HPred SM I Phi Psi H.
  exact (snd (form_equiv_wf I Phi Psi H)).
Defined.

Lemma meta_ctx_wf : forall {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
  {I : b_ty} {G : @h_context Sign Func Pred} {p : @h_tm Sign Func Pred} {Phi : @h_ty Sign Func Pred},
  h_derivation I G p Phi ->
  All_WellFormed I G.
Proof.
  intros Sign Func Pred HFunc HPred SM I G p Phi Hderiv.
  induction Hderiv.
  - exact a.
  - apply AWF_Cons; assumption.
  - exact a.
  - exact IHHderiv.
  - eapply ctx_equiv_wf_right.
    + exact c.
    + exact IHHderiv.
  - inversion IHHderiv; subst. assumption.
  - exact IHHderiv1.
  - exact IHHderiv1.
  - exact IHHderiv.
  - exact IHHderiv.
  - exact IHHderiv.
  - exact IHHderiv.
  - exact IHHderiv1.
  - exact IHHderiv.
  - apply ctx_wf_fst_inv in IHHderiv.
    exact IHHderiv.
  - exact IHHderiv.
  - exact IHHderiv.
  - exact IHHderiv1.
  - exact IHHderiv.
  - exact IHHderiv1.
Defined.

Lemma meta_type_wf : forall {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
  {I : b_ty} {G : @h_context Sign Func Pred} {p : @h_tm Sign Func Pred} {Phi : @h_ty Sign Func Pred},
  h_derivation I G p Phi ->
  WellFormed I Phi.
Proof.
  intros Sign Func Pred HFunc HPred SM I G p Phi Hderiv.
  induction Hderiv.
  - inversion a; subst. assumption.
  - assumption.
  - apply WF_Unit.
  - eapply form_equiv_wf2. exact f.
  - assumption.
  - apply WF_Arrow.
    + apply meta_ctx_wf in Hderiv.
      inversion Hderiv; subst. assumption.
    + assumption.
  - inversion IHHderiv1; subst. assumption.
  - apply WF_Prod; assumption.
  - inversion IHHderiv; subst. assumption.
  - inversion IHHderiv; subst. assumption.
  - apply WF_Sum; assumption.
  - apply WF_Sum; assumption.
  - assumption.
  - exact w.
  - apply WF_All. exact IHHderiv.
  - eapply wf_subst.
    + eapply BT_Pair.
      * apply BT_Id.
      * exact b.
    + inversion IHHderiv; subst. assumption.
  - apply WF_Ex.
    eapply form_wf_subst_inv.
    + eapply BT_Pair.
      * apply BT_Id.
      * exact b.
    + exact IHHderiv.
  - apply form_wf_fst_inv in IHHderiv2.
    exact IHHderiv2.
  - eapply wf_subst.
    + eapply BT_Pair.
      * apply BT_Id.
      * apply BT_Const.
    + eapply form_wf_subst_inv.
      * eapply BT_Pair.
        -- apply BT_Id.
        -- exact b.
      * exact IHHderiv.
  - apply form_wf_fst_inv in IHHderiv2.
    exact IHHderiv2.
Defined.

Lemma h_derivation_wf_inv : forall {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
  {I A : b_ty} {G : @h_context Sign Func Pred} {p : @h_tm Sign Func Pred}
  {Phi : @h_ty Sign Func Pred} {t : @b_tm Sign Func},
  base_typing I t A ->
  h_derivation I G p (form_subst (b_pair b_id t) Phi) ->
  WellFormed (b_Prod I A) Phi.
Proof.
  intros Sign Func Pred HFunc HPred SM I A G p Phi t dt Hderiv.
  apply meta_type_wf in Hderiv.
  eapply form_wf_subst_inv.
  - eapply BT_Pair.
    + apply BT_Id.
    + exact dt.
  - exact Hderiv.
Defined.

Lemma ctx_equiv_refl : forall {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred}
  (I : b_ty) (D : @h_context Sign Func Pred),
  All_WellFormed I D -> ctx_equiv I D D.
Proof.
  induction 1; constructor; auto.
  apply FE_Refl; auto.
Defined.

Lemma All_WellFormed_app : forall {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred}
  (I : b_ty) (G D : @h_context Sign Func Pred),
  All_WellFormed I G -> All_WellFormed I D -> All_WellFormed I (G ++ D).
Proof.
  intros Sign Func Pred HFunc HPred I G D H1 H2.
  induction H1; simpl; auto.
  apply AWF_Cons; auto.
Defined.

Lemma ctx_equiv_app : forall {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred}
  (I : b_ty) (G1 G2 D : @h_context Sign Func Pred),
  ctx_equiv I G1 G2 -> All_WellFormed I D -> ctx_equiv I (G1 ++ D) (G2 ++ D).
Proof.
  intros Sign Func Pred HFunc HPred SM I G1 G2 D H Hwf.
  induction H; simpl.
  - apply ctx_equiv_refl; auto.
  - apply CEq_Cons; auto.
Defined.

Lemma All_WellFormed_subst : forall {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred}
  (I J : b_ty) (f : @b_tm Sign Func) (D : @h_context Sign Func Pred),
  base_typing I f J -> All_WellFormed J D -> All_WellFormed I (ctx_subst f D).
Proof.
  intros Sign Func Pred HFunc HPred I J f D dt H.
  induction H; simpl.
  - apply AWF_Nil.
  - apply AWF_Cons.
    + eapply wf_subst; eauto.
    + exact IHAll_WellFormed.
Defined.

Lemma h_derivation_append : forall {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred}
  (I : b_ty) (G D : @h_context Sign Func Pred) (p : @h_tm Sign Func Pred) (Phi : @h_ty Sign Func Pred),
  h_derivation I G p Phi ->
  All_WellFormed I D ->
  h_derivation I (G ++ D) p Phi.
Proof.
  intros Sign Func Pred HFunc HPred SM I G D p Phi H.
  revert D.
  induction H; intros D Hwf; simpl.
  - apply HD_Var0.
    apply (All_WellFormed_app I (Phi :: G) D).
    + exact a.
    + exact Hwf.
  - apply HD_VarS; auto.
  - apply HD_Unit.
    apply All_WellFormed_app; auto.
  - eapply HD_Conv; eauto.
  - eapply HD_Ctx_Conv.
    + apply ctx_equiv_app; eauto.
    + eauto.
  - apply HD_Lam.
    apply IHh_derivation; auto.
  - eapply HD_App; eauto.
  - apply HD_Pair; auto.
  - eapply HD_Fst; eauto.
  - eapply HD_Snd; eauto.
  - apply HD_Inl; auto.
  - apply HD_Inr; auto.
  - eapply HD_Case; eauto.
  - apply HD_Absurd; auto.
  - apply HD_All_Intro.
    unfold ctx_subst.
    rewrite map_app.
    fold (@ctx_subst Sign Func Pred).
    apply IHh_derivation.
    eapply All_WellFormed_subst.
    + apply BT_Fst.
    + exact Hwf.
  - eapply HD_All_Elim; eauto.
  - eapply HD_Ex_Intro; eauto.
  - eapply HD_Ex_Elim.
    + apply IHh_derivation1; auto.
    + unfold ctx_subst.
      rewrite map_app.
      fold (@ctx_subst Sign Func Pred).
      apply IHh_derivation2.
      eapply All_WellFormed_subst.
      * apply BT_Fst.
      * exact Hwf.
  - eapply HD_Eps_Intro; eauto.
  - eapply HD_Eps_Elim.
    + apply IHh_derivation1; auto.
    + unfold ctx_subst.
      rewrite map_app.
      fold (@ctx_subst Sign Func Pred).
      apply IHh_derivation2.
      eapply All_WellFormed_subst.
      * apply BT_Fst.
      * exact Hwf.
Defined.
