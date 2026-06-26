(* theories/Semantics/Metatheory/IFOLFull_NonConservativity.v *)

Require Import List.
Import ListNotations.

Require Import Coq.Program.Equality.

Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax_Lemmas.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax_Lemmas.
Require Import HyperLogic.Logic.Hyper.Individual.Hyper_Syntax.
From HyperLogic.Semantics.Metatheory Require Import DualDrinker.

Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Lemmas.
Require Import HyperLogic.Semantics.Simple.DualDrinker.
Require Import HyperLogic.Semantics.Simple.Simple_Soundness.

Module FullBase := HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Module FullLemmas := HyperLogic.Logic.Base.EpsilonFull.Base_Syntax_Lemmas.
Module FullHyper := HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.
Module IFOL := HyperLogic.Logic.Hyper.Individual.Hyper_Syntax.
Module SimpleBase := HyperLogic.Logic.Base.Simple.Base_Syntax.
Module SimpleHyper := HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.
Module SimpleLemmas := HyperLogic.Logic.Hyper.Simple.Hyper_Lemmas.
Module SimpleDD := HyperLogic.Semantics.Simple.DualDrinker.
Module SimpleSoundness := HyperLogic.Semantics.Simple.Simple_Soundness.
Module MetaDD := HyperLogic.Semantics.Metatheory.DualDrinker.

Inductive NoSign : Type := .
Inductive NoFunc : Type := .

Definition no_func_dom (f : NoFunc) : FullBase.b_ty :=
  match f return FullBase.b_ty with end.

Definition no_func_cod (f : NoFunc) : FullBase.b_ty :=
  match f return FullBase.b_ty with end.

Instance NoFuncSignature : FullBase.FunctionSignature NoFunc :=
  {| FullBase.func_dom := no_func_dom;
     FullBase.func_cod := no_func_cod |}.

Instance NatPredicateSignature : FullHyper.PredicateSignature nat :=
  {| FullHyper.pred_dom _ := FullBase.b_S |}.

Fixpoint to_simple_b_ty (A : FullBase.b_ty) : SimpleBase.b_ty :=
  match A with
  | FullBase.b_Unit => SimpleBase.b_Unit
  | FullBase.b_S => SimpleBase.b_S
  | FullBase.b_Prod A B => SimpleBase.b_Prod (to_simple_b_ty A) (to_simple_b_ty B)
  end.

Fixpoint to_simple_b_tm (t : @FullBase.b_tm NoSign NoFunc) : SimpleBase.b_tm :=
  match t with
  | FullBase.b_id => SimpleBase.b_id
  | FullBase.b_comp g f => SimpleBase.b_comp (to_simple_b_tm g) (to_simple_b_tm f)
  | FullBase.b_unit => SimpleBase.b_unit
  | FullBase.b_pair f g => SimpleBase.b_pair (to_simple_b_tm f) (to_simple_b_tm g)
  | FullBase.b_fst => SimpleBase.b_fst
  | FullBase.b_snd => SimpleBase.b_snd
  | FullBase.b_const _ s => match s with end
  | FullBase.b_func f => match f with end
  end.

Fixpoint T_ifol_language_b_tm {EpsSign : Type}
  (t : @FullBase.b_tm NoSign NoFunc) : @FullBase.b_tm EpsSign NoFunc :=
  match t with
  | FullBase.b_id => FullBase.b_id
  | FullBase.b_comp g f => FullBase.b_comp (T_ifol_language_b_tm g) (T_ifol_language_b_tm f)
  | FullBase.b_unit => FullBase.b_unit
  | FullBase.b_pair f g => FullBase.b_pair (T_ifol_language_b_tm f) (T_ifol_language_b_tm g)
  | FullBase.b_fst => FullBase.b_fst
  | FullBase.b_snd => FullBase.b_snd
  | FullBase.b_const A s => match s with end
  | FullBase.b_func f => match f with end
  end.

Fixpoint T_ifol_language_h_ty {EpsSign : Type}
  (Phi : @FullHyper.h_ty NoSign NoFunc nat) : @FullHyper.h_ty EpsSign NoFunc nat :=
  match Phi with
  | FullHyper.Ty_Unit => FullHyper.Ty_Unit
  | FullHyper.Ty_Void => FullHyper.Ty_Void
  | FullHyper.Ty_Prod A B =>
      FullHyper.Ty_Prod (T_ifol_language_h_ty A) (T_ifol_language_h_ty B)
  | FullHyper.Ty_Sum A B =>
      FullHyper.Ty_Sum (T_ifol_language_h_ty A) (T_ifol_language_h_ty B)
  | FullHyper.Ty_Arrow A B =>
      FullHyper.Ty_Arrow (T_ifol_language_h_ty A) (T_ifol_language_h_ty B)
  | FullHyper.Ty_Atom p t => FullHyper.Ty_Atom p (T_ifol_language_b_tm t)
  | FullHyper.Ty_All A Body => FullHyper.Ty_All A (T_ifol_language_h_ty Body)
  | FullHyper.Ty_Ex A Body => FullHyper.Ty_Ex A (T_ifol_language_h_ty Body)
  end.

Fixpoint to_simple_base_typing
  {I A : FullBase.b_ty} {t : @FullBase.b_tm NoSign NoFunc}
  (d : @FullBase.base_typing NoSign NoFunc NoFuncSignature I t A)
  : SimpleBase.base_typing (to_simple_b_ty I) (to_simple_b_tm t) (to_simple_b_ty A) :=
  match d with
  | @FullBase.BT_Id _ _ _ _ => SimpleBase.BT_Id
  | @FullBase.BT_Comp _ _ _ _ _ _ _ _ dg df =>
      SimpleBase.BT_Comp (to_simple_base_typing dg) (to_simple_base_typing df)
  | @FullBase.BT_Unit _ _ _ _ => SimpleBase.BT_Unit
  | @FullBase.BT_Pair _ _ _ _ _ _ _ _ df dg =>
      SimpleBase.BT_Pair (to_simple_base_typing df) (to_simple_base_typing dg)
  | @FullBase.BT_Fst _ _ _ _ _ => SimpleBase.BT_Fst
  | @FullBase.BT_Snd _ _ _ _ _ => SimpleBase.BT_Snd
  | @FullBase.BT_Const _ _ _ _ _ s => match s with end
  | @FullBase.BT_Func _ _ _ f => match f with end
  end.

Lemma simple_BE_CompPair :
  forall A B C D (f g h : SimpleBase.b_tm)
    (df : SimpleBase.base_typing B f C)
    (dg : SimpleBase.base_typing B g D)
    (dh : SimpleBase.base_typing A h B),
  SimpleBase.base_equiv A (SimpleBase.b_Prod C D)
    (SimpleBase.b_comp (SimpleBase.b_pair f g) h)
    (SimpleBase.b_pair (SimpleBase.b_comp f h) (SimpleBase.b_comp g h)).
Proof.
  intros A B C D f g h df dg dh.
  eapply SimpleBase.BE_Trans.
  - eapply SimpleBase.BE_Sym.
    eapply SimpleBase.BE_EtaPair.
    eapply SimpleBase.BT_Comp.
    + eapply SimpleBase.BT_Pair; eassumption.
    + exact dh.
  - eapply SimpleBase.BE_CongPair.
    + eapply SimpleBase.BE_Trans.
      * eapply SimpleBase.BE_Assoc.
        -- exact dh.
        -- eapply SimpleBase.BT_Pair; eassumption.
        -- apply SimpleBase.BT_Fst.
      * eapply SimpleBase.BE_CongComp.
        -- eapply SimpleBase.BE_BetaFst; eassumption.
        -- eapply SimpleBase.BE_Refl. exact dh.
    + eapply SimpleBase.BE_Trans.
      * eapply SimpleBase.BE_Assoc.
        -- exact dh.
        -- eapply SimpleBase.BT_Pair; eassumption.
        -- apply SimpleBase.BT_Snd.
      * eapply SimpleBase.BE_CongComp.
        -- eapply SimpleBase.BE_BetaSnd; eassumption.
        -- eapply SimpleBase.BE_Refl. exact dh.
Defined.

Lemma to_simple_base_equiv :
  forall {I A : FullBase.b_ty} {f g : @FullBase.b_tm NoSign NoFunc}
    {df : @FullBase.base_typing NoSign NoFunc NoFuncSignature I f A}
    {dg : @FullBase.base_typing NoSign NoFunc NoFuncSignature I g A},
  @FullBase.base_equiv NoSign NoFunc NoFuncSignature I A f g df dg ->
  SimpleBase.base_equiv (to_simple_b_ty I) (to_simple_b_ty A)
    (to_simple_b_tm f) (to_simple_b_tm g).
Proof.
  intros I A f g df dg H.
  induction H.
  - eapply SimpleBase.BE_Refl. exact (to_simple_base_typing df).
  - eapply SimpleBase.BE_Sym. exact IHbase_equiv.
  - eapply SimpleBase.BE_Trans; eassumption.
  - eapply SimpleBase.BE_CongComp; eassumption.
  - eapply SimpleBase.BE_CongPair; eassumption.
  - eapply SimpleBase.BE_Assoc; eauto using to_simple_base_typing.
  - eapply SimpleBase.BE_IdL. exact (to_simple_base_typing df).
  - eapply SimpleBase.BE_IdR. exact (to_simple_base_typing df).
  - eapply SimpleBase.BE_BetaFst; eauto using to_simple_base_typing.
  - eapply SimpleBase.BE_BetaSnd; eauto using to_simple_base_typing.
  - eapply SimpleBase.BE_EtaPair. exact (to_simple_base_typing dh).
  - eapply SimpleBase.BE_Terminal.
    + exact (to_simple_base_typing df).
    + apply SimpleBase.BT_Unit.
  - eapply simple_BE_CompPair; eauto using to_simple_base_typing.
Defined.

Fixpoint to_simple_h_ty (Phi : @FullHyper.h_ty NoSign NoFunc nat) : SimpleHyper.h_ty :=
  match Phi with
  | FullHyper.Ty_Unit => SimpleHyper.Ty_Unit
  | FullHyper.Ty_Void => SimpleHyper.Ty_Void
  | FullHyper.Ty_Prod A B => SimpleHyper.Ty_Prod (to_simple_h_ty A) (to_simple_h_ty B)
  | FullHyper.Ty_Sum A B => SimpleHyper.Ty_Sum (to_simple_h_ty A) (to_simple_h_ty B)
  | FullHyper.Ty_Arrow A B => SimpleHyper.Ty_Arrow (to_simple_h_ty A) (to_simple_h_ty B)
  | FullHyper.Ty_Atom p t => SimpleHyper.Ty_Atom p (to_simple_b_tm t)
  | FullHyper.Ty_All A Body => SimpleHyper.Ty_All (to_simple_b_ty A) (to_simple_h_ty Body)
  | FullHyper.Ty_Ex A Body => SimpleHyper.Ty_Ex (to_simple_b_ty A) (to_simple_h_ty Body)
  end.

Definition to_simple_h_ctx (G : @FullHyper.h_context NoSign NoFunc nat) : SimpleHyper.h_context :=
  map to_simple_h_ty G.

Fixpoint to_simple_h_tm (p : @FullHyper.h_tm NoSign NoFunc nat) : SimpleHyper.h_tm :=
  match p with
  | FullHyper.tm_unit => SimpleHyper.tm_unit
  | FullHyper.tm_var i => SimpleHyper.tm_var i
  | FullHyper.tm_lam Phi p => SimpleHyper.tm_lam (to_simple_h_ty Phi) (to_simple_h_tm p)
  | FullHyper.tm_app p q => SimpleHyper.tm_app (to_simple_h_tm p) (to_simple_h_tm q)
  | FullHyper.tm_pair p q => SimpleHyper.tm_pair (to_simple_h_tm p) (to_simple_h_tm q)
  | FullHyper.tm_fst p => SimpleHyper.tm_fst (to_simple_h_tm p)
  | FullHyper.tm_snd p => SimpleHyper.tm_snd (to_simple_h_tm p)
  | FullHyper.tm_inl Psi p => SimpleHyper.tm_inl (to_simple_h_ty Psi) (to_simple_h_tm p)
  | FullHyper.tm_inr Phi p => SimpleHyper.tm_inr (to_simple_h_ty Phi) (to_simple_h_tm p)
  | FullHyper.tm_case p q r => SimpleHyper.tm_case (to_simple_h_tm p) (to_simple_h_tm q) (to_simple_h_tm r)
  | FullHyper.tm_absurd Phi p => SimpleHyper.tm_absurd (to_simple_h_ty Phi) (to_simple_h_tm p)
  | FullHyper.tm_all_intro p => SimpleHyper.tm_all_intro (to_simple_h_tm p)
  | FullHyper.tm_all_elim p t => SimpleHyper.tm_all_elim (to_simple_h_tm p) (to_simple_b_tm t)
  | FullHyper.tm_ex_intro t p => SimpleHyper.tm_ex_intro (to_simple_b_tm t) (to_simple_h_tm p)
  | FullHyper.tm_ex_elim p q => SimpleHyper.tm_ex_elim (to_simple_h_tm p) (to_simple_h_tm q)
  | FullHyper.tm_eps_intro _ p => to_simple_h_tm p
  | FullHyper.tm_eps_elim p _ => to_simple_h_tm p
  end.

Lemma to_simple_form_subst :
  forall (f : @FullBase.b_tm NoSign NoFunc) Phi,
  to_simple_h_ty (FullHyper.form_subst f Phi) =
  SimpleHyper.form_pullback (to_simple_b_tm f) (to_simple_h_ty Phi).
Proof.
  intros f Phi.
  revert f.
  induction Phi; intro f; simpl; try rewrite IHPhi1; try rewrite IHPhi2; try rewrite IHPhi; reflexivity.
Defined.

Lemma to_simple_ctx_subst :
  forall (f : @FullBase.b_tm NoSign NoFunc) G,
  to_simple_h_ctx (FullHyper.ctx_subst f G) =
  SimpleHyper.ctx_pullback (to_simple_b_tm f) (to_simple_h_ctx G).
Proof.
  intros f G.
  induction G as [|Phi G IH]; simpl.
  - reflexivity.
  - rewrite to_simple_form_subst, IH. reflexivity.
Defined.

Lemma to_simple_wf :
  forall {I : FullBase.b_ty} {Phi : @FullHyper.h_ty NoSign NoFunc nat},
  @FullHyper.WellFormed NoSign NoFunc nat NoFuncSignature NatPredicateSignature I Phi ->
  SimpleHyper.WellFormed (to_simple_b_ty I) (to_simple_h_ty Phi).
Proof.
  intros I Phi Hwf.
  induction Hwf; simpl.
  - apply SimpleHyper.WF_Unit.
  - apply SimpleHyper.WF_Void.
  - apply SimpleHyper.WF_Prod; assumption.
  - apply SimpleHyper.WF_Sum; assumption.
  - apply SimpleHyper.WF_Arrow; assumption.
  - eapply SimpleHyper.WF_Atom.
    exact (to_simple_base_typing b).
  - apply SimpleHyper.WF_All. exact IHHwf.
  - apply SimpleHyper.WF_Ex. exact IHHwf.
Defined.

Fixpoint to_simple_all_wf {I : FullBase.b_ty} {G : @FullHyper.h_context NoSign NoFunc nat}
  (Hwf : @FullHyper.All_WellFormed NoSign NoFunc nat NoFuncSignature NatPredicateSignature I G)
  : SimpleHyper.wf_ctx (to_simple_b_ty I) (to_simple_h_ctx G) :=
  match Hwf with
  | @FullHyper.AWF_Nil _ _ _ _ _ _ => SimpleHyper.WFC_nil _
  | @FullHyper.AWF_Cons _ _ _ _ _ _ Phi G wfPhi wfG =>
      SimpleHyper.WFC_cons _ _ _ (to_simple_wf wfPhi) (to_simple_all_wf wfG)
  end.

Lemma ifol_form_equiv_wf :
  forall (I : FullBase.b_ty) (Phi Psi : @FullHyper.h_ty NoSign NoFunc nat),
  @IFOL.ifol_form_equiv NoSign NoFunc nat NoFuncSignature NatPredicateSignature I Phi Psi ->
  (FullHyper.WellFormed I Phi * FullHyper.WellFormed I Psi)%type.
Proof.
  intros I Phi Psi H.
  induction H.
  - split; eapply FullHyper.WF_Atom; eassumption.
  - split; assumption.
  - destruct IHifol_form_equiv; split; assumption.
  - destruct IHifol_form_equiv1, IHifol_form_equiv2; split; eassumption.
  - destruct IHifol_form_equiv1, IHifol_form_equiv2; split; constructor; assumption.
  - destruct IHifol_form_equiv1, IHifol_form_equiv2; split; constructor; assumption.
  - destruct IHifol_form_equiv1, IHifol_form_equiv2; split; constructor; assumption.
  - destruct IHifol_form_equiv; split; constructor; assumption.
  - destruct IHifol_form_equiv; split; constructor; assumption.
  - split.
    + eapply wf_subst. apply FullBase.BT_Id. exact w.
    + exact w.
  - split.
    + eapply wf_subst. exact dg. eapply wf_subst. exact df. exact w.
    + eapply wf_subst. eapply FullBase.BT_Comp. exact df. exact dg. exact w.
  - split.
    + eapply wf_subst. exact df. exact w.
    + eapply wf_subst. exact dg. exact w.
Defined.

Lemma ifol_ctx_equiv_wf_right :
  forall (I : FullBase.b_ty) (G1 G2 : @FullHyper.h_context NoSign NoFunc nat),
  @IFOL.ifol_ctx_equiv NoSign NoFunc nat NoFuncSignature NatPredicateSignature I G1 G2 ->
  FullHyper.All_WellFormed I G1 ->
  FullHyper.All_WellFormed I G2.
Proof.
  intros I G1 G2 H Hwf1.
  induction H.
  - exact Hwf1.
  - dependent destruction Hwf1.
    apply FullHyper.AWF_Cons.
    + destruct (ifol_form_equiv_wf I Phi Psi i) as [_ wfPsi].
      exact wfPsi.
    + apply IHifol_ctx_equiv. exact Hwf1.
Defined.

Lemma form_wf_subst_inv_no_skolem :
  forall {I J : FullBase.b_ty} (f : @FullBase.b_tm NoSign NoFunc)
    (df : FullBase.base_typing I f J) (Phi : @FullHyper.h_ty NoSign NoFunc nat),
  FullHyper.WellFormed I (FullHyper.form_subst f Phi) ->
  FullHyper.WellFormed J Phi.
Proof.
  intros I J f df Phi.
  generalize dependent J.
  generalize dependent I.
  generalize dependent f.
  induction Phi; intros f I J df Hwf; simpl in Hwf; inversion Hwf; subst.
  - apply FullHyper.WF_Unit.
  - apply FullHyper.WF_Void.
  - apply FullHyper.WF_Prod; eauto.
  - apply FullHyper.WF_Sum; eauto.
  - apply FullHyper.WF_Arrow; eauto.
  - eapply FullHyper.WF_Atom.
    match goal with
    | Hcomp : FullBase.base_typing I (FullBase.b_comp ?u f) ?B |- FullBase.base_typing J ?u _ =>
        inversion Hcomp; subst;
        match goal with
        | Hu : FullBase.base_typing ?Mid u ?B',
          Hf : FullBase.base_typing I f ?Mid |- _ =>
            assert (H_mid : Mid = J)
              by (eapply FullLemmas.base_typing_unique; [exact Hf | exact df]);
            rewrite H_mid in Hu;
            exact Hu
        end
    end.
  - apply FullHyper.WF_All.
    eapply IHPhi.
    + exact (@typing_subst_ext NoSign NoFunc NoFuncSignature I J b f df).
    + match goal with
      | Hbody : FullHyper.WellFormed _ (FullHyper.form_subst _ Phi) |- _ =>
          exact Hbody
      end.
  - apply FullHyper.WF_Ex.
    eapply IHPhi.
    + exact (@typing_subst_ext NoSign NoFunc NoFuncSignature I J b f df).
    + match goal with
      | Hbody : FullHyper.WellFormed _ (FullHyper.form_subst _ Phi) |- _ =>
          exact Hbody
      end.
Defined.

Lemma form_wf_fst_inv_no_skolem :
  forall {I A : FullBase.b_ty} {Phi : @FullHyper.h_ty NoSign NoFunc nat},
  FullHyper.WellFormed (FullBase.b_Prod I A) (FullHyper.form_subst FullBase.b_fst Phi) ->
  FullHyper.WellFormed I Phi.
Proof.
  intros I A Phi Hwf.
  eapply form_wf_subst_inv_no_skolem.
  - apply (FullBase.BT_Fst (A:=I) (B:=A)).
  - exact Hwf.
Defined.

Lemma ctx_wf_fst_inv_no_skolem :
  forall {I A : FullBase.b_ty} {G : @FullHyper.h_context NoSign NoFunc nat},
  FullHyper.All_WellFormed (FullBase.b_Prod I A) (FullHyper.ctx_subst FullBase.b_fst G) ->
  FullHyper.All_WellFormed I G.
Proof.
  intros I A G H.
  induction G as [|Phi G IH].
  - simpl in H. inversion H. apply FullHyper.AWF_Nil.
  - simpl in H. dependent destruction H.
    apply FullHyper.AWF_Cons.
    + eapply form_wf_fst_inv_no_skolem.
      match goal with
      | Hhead : FullHyper.WellFormed _ (FullHyper.form_subst FullBase.b_fst Phi) |- _ =>
          exact Hhead
      end.
    + apply IH.
      match goal with
      | Htail : FullHyper.All_WellFormed _ (FullHyper.ctx_subst FullBase.b_fst G) |- _ =>
          exact Htail
      end.
Defined.

Lemma ifol_meta_ctx_wf :
  forall {I : FullBase.b_ty} {G : @FullHyper.h_context NoSign NoFunc nat}
    {p : @FullHyper.h_tm NoSign NoFunc nat} {Phi : @FullHyper.h_ty NoSign NoFunc nat},
  @IFOL.ifol_h_derivation NoSign NoFunc nat NoFuncSignature NatPredicateSignature I G p Phi ->
  FullHyper.All_WellFormed I G.
Proof.
  intros I G p Phi Hder.
  induction Hder.
  - exact a.
  - apply FullHyper.AWF_Cons; assumption.
  - exact a.
  - exact IHHder.
  - eapply ifol_ctx_equiv_wf_right; eauto.
  - inversion IHHder; subst. assumption.
  - exact IHHder1.
  - exact IHHder1.
  - exact IHHder.
  - exact IHHder.
  - exact IHHder.
  - exact IHHder.
  - exact IHHder1.
  - exact IHHder.
  - apply ctx_wf_fst_inv_no_skolem in IHHder.
    exact IHHder.
  - exact IHHder.
  - exact IHHder.
  - exact IHHder1.
Defined.

Lemma ifol_meta_type_wf :
  forall {I : FullBase.b_ty} {G : @FullHyper.h_context NoSign NoFunc nat}
    {p : @FullHyper.h_tm NoSign NoFunc nat} {Phi : @FullHyper.h_ty NoSign NoFunc nat},
  @IFOL.ifol_h_derivation NoSign NoFunc nat NoFuncSignature NatPredicateSignature I G p Phi ->
  FullHyper.WellFormed I Phi.
Proof.
  intros I G p Phi Hder.
  induction Hder.
  - inversion a; subst. assumption.
  - assumption.
  - apply FullHyper.WF_Unit.
  - destruct (ifol_form_equiv_wf I Phi Psi i) as [_ wfPsi]. exact wfPsi.
  - assumption.
  - apply FullHyper.WF_Arrow.
    + apply ifol_meta_ctx_wf in Hder. inversion Hder; subst. assumption.
    + assumption.
  - inversion IHHder1; subst. assumption.
  - apply FullHyper.WF_Prod; assumption.
  - inversion IHHder; subst. assumption.
  - inversion IHHder; subst. assumption.
  - apply FullHyper.WF_Sum; assumption.
  - apply FullHyper.WF_Sum; assumption.
  - assumption.
  - exact w.
  - apply FullHyper.WF_All. exact IHHder.
  - eapply wf_subst.
    + eapply FullBase.BT_Pair.
      * apply FullBase.BT_Id.
      * exact b.
    + inversion IHHder; subst. assumption.
  - apply FullHyper.WF_Ex.
    eapply form_wf_subst_inv_no_skolem.
    + eapply FullBase.BT_Pair.
      * apply FullBase.BT_Id.
      * exact b.
    + exact IHHder.
  - apply form_wf_fst_inv_no_skolem in IHHder2.
    exact IHHder2.
Defined.

Lemma to_simple_ifol_form_equiv :
  forall {I : FullBase.b_ty} {Phi Psi : @FullHyper.h_ty NoSign NoFunc nat},
  @IFOL.ifol_form_equiv NoSign NoFunc nat NoFuncSignature NatPredicateSignature I Phi Psi ->
  SimpleHyper.form_equiv (to_simple_b_ty I) (to_simple_h_ty Phi) (to_simple_h_ty Psi).
Proof.
  intros I Phi Psi H.
  induction H; simpl.
  - eapply SimpleHyper.FEQ_Atom.
    + exact (to_simple_base_typing d1).
    + exact (to_simple_base_typing d2).
    + exact (@to_simple_base_equiv I (FullHyper.pred_dom p) t1 t2 d1 d2 b).
  - apply SimpleHyper.FEQ_Refl. apply to_simple_wf. exact w.
  - apply SimpleHyper.FEQ_Sym. assumption.
  - eapply SimpleHyper.FEQ_Trans; eassumption.
  - apply SimpleHyper.FEQ_Prod; assumption.
  - apply SimpleHyper.FEQ_Sum; assumption.
  - apply SimpleHyper.FEQ_Arrow; assumption.
  - apply SimpleHyper.FEQ_All. assumption.
  - apply SimpleHyper.FEQ_Ex. assumption.
  - rewrite to_simple_form_subst.
    apply SimpleHyper.FEQ_Pullback_Id.
    apply to_simple_wf. exact w.
  - repeat rewrite to_simple_form_subst.
    eapply SimpleHyper.FEQ_Pullback_Comp with
      (J := to_simple_b_ty J)
      (K := to_simple_b_ty K)
      (f := to_simple_b_tm f)
      (g := to_simple_b_tm g).
    + exact (to_simple_base_typing df).
    + exact (to_simple_base_typing dg).
    + apply to_simple_wf. exact w.
  - repeat rewrite to_simple_form_subst.
    eapply SimpleHyper.FEQ_Pullback_Cong with
      (J := to_simple_b_ty J)
      (f := to_simple_b_tm f)
      (g := to_simple_b_tm g).
    + exact (to_simple_base_typing df).
    + exact (to_simple_base_typing dg).
    + exact (@to_simple_base_equiv I J f g df dg b).
    + apply to_simple_wf. exact w.
Defined.

Lemma to_simple_ifol_ctx_equiv :
  forall {I : FullBase.b_ty} {G1 G2 : @FullHyper.h_context NoSign NoFunc nat},
  @IFOL.ifol_ctx_equiv NoSign NoFunc nat NoFuncSignature NatPredicateSignature I G1 G2 ->
  SimpleHyper.ctx_equiv (to_simple_b_ty I) (to_simple_h_ctx G1) (to_simple_h_ctx G2).
Proof.
  intros I G1 G2 H.
  induction H; simpl.
  - apply SimpleHyper.CEQ_nil.
  - apply SimpleHyper.CEQ_cons.
    + apply to_simple_ifol_form_equiv. exact i.
    + assumption.
Defined.

Lemma to_simple_ifol_derivation :
  forall {I : FullBase.b_ty} {G : @FullHyper.h_context NoSign NoFunc nat}
    {p : @FullHyper.h_tm NoSign NoFunc nat} {Phi : @FullHyper.h_ty NoSign NoFunc nat},
  @IFOL.ifol_h_derivation NoSign NoFunc nat NoFuncSignature NatPredicateSignature I G p Phi ->
  SimpleHyper.h_derivation (to_simple_b_ty I) (to_simple_h_ctx G) (to_simple_h_tm p) (to_simple_h_ty Phi).
Proof.
  intros I G p Phi Hder.
  induction Hder; simpl.
  - dependent destruction a.
    apply SimpleHyper.HD_Var0.
    + apply to_simple_all_wf.
      match goal with
      | Htail : FullHyper.All_WellFormed I G |- _ => exact Htail
      end.
    + apply to_simple_wf.
      match goal with
      | Hhead : FullHyper.WellFormed I Phi |- _ => exact Hhead
      end.
  - apply SimpleHyper.HD_VarS.
    + apply to_simple_wf. exact w.
    + exact IHHder.
  - apply SimpleHyper.HD_Unit.
    apply to_simple_all_wf. exact a.
  - eapply SimpleHyper.HD_Conv.
    + apply SimpleLemmas.ctx_equiv_refl.
      apply to_simple_all_wf.
      eapply ifol_meta_ctx_wf. exact Hder.
    + exact (@to_simple_ifol_form_equiv I Phi Psi i).
    + exact IHHder.
  - eapply SimpleHyper.HD_Conv.
    + exact (@to_simple_ifol_ctx_equiv I G1 G2 i).
    + apply SimpleHyper.FEQ_Refl.
      apply to_simple_wf.
      eapply ifol_meta_type_wf. exact Hder.
    + exact IHHder.
  - apply SimpleHyper.HD_Lam. exact IHHder.
  - eapply SimpleHyper.HD_App; eassumption.
  - apply SimpleHyper.HD_Pair; assumption.
  - eapply SimpleHyper.HD_Fst; eassumption.
  - eapply SimpleHyper.HD_Snd; eassumption.
  - apply SimpleHyper.HD_Inl.
    + apply to_simple_wf. exact w.
    + exact IHHder.
  - apply SimpleHyper.HD_Inr.
    + apply to_simple_wf. exact w.
    + exact IHHder.
  - eapply SimpleHyper.HD_Case; eassumption.
  - apply SimpleHyper.HD_Absurd.
    + apply to_simple_wf. exact w.
    + exact IHHder.
  - rewrite to_simple_ctx_subst in IHHder.
    apply SimpleHyper.HD_All_Intro.
    + apply to_simple_all_wf.
      eapply ctx_wf_fst_inv_no_skolem.
      eapply ifol_meta_ctx_wf. exact Hder.
    + exact IHHder.
  - rewrite to_simple_form_subst.
    eapply SimpleHyper.HD_All_Elim.
    + exact IHHder.
    + exact (to_simple_base_typing b).
  - rewrite to_simple_form_subst in IHHder.
    apply SimpleHyper.HD_Ex_Intro.
    + change (SimpleHyper.WellFormed (to_simple_b_ty (FullBase.b_Prod I A)) (to_simple_h_ty Phi)).
      apply to_simple_wf.
      eapply form_wf_subst_inv_no_skolem.
      * eapply FullBase.BT_Pair.
        -- apply FullBase.BT_Id.
        -- exact b.
      * eapply ifol_meta_type_wf. exact Hder.
    + exact (to_simple_base_typing b).
    + exact IHHder.
  - change (SimpleHyper.h_derivation
      (to_simple_b_ty (FullBase.b_Prod I A))
      (to_simple_h_ty Phi :: to_simple_h_ctx (FullHyper.ctx_subst FullBase.b_fst G))
      (to_simple_h_tm p2)
      (to_simple_h_ty (FullHyper.form_subst FullBase.b_fst Chi))) in IHHder2.
    rewrite to_simple_ctx_subst in IHHder2.
    rewrite to_simple_form_subst in IHHder2.
    refine (@SimpleHyper.HD_Ex_Elim
      (to_simple_b_ty I)
      (to_simple_h_ctx G)
      (to_simple_h_tm p)
      (to_simple_h_tm p2)
      (to_simple_b_ty A)
      (to_simple_h_ty Phi)
      (to_simple_h_ty Chi) _ _ _).
    + apply to_simple_wf.
      eapply form_wf_fst_inv_no_skolem.
      eapply ifol_meta_type_wf. exact Hder2.
    + exact IHHder1.
    + exact IHHder2.
Defined.

Definition IFOL_DualDrinker : @FullHyper.h_ty NoSign NoFunc nat :=
  @MetaDD.DualDrinkerFormula NoSign NoFunc nat 0 FullBase.b_Unit FullBase.b_S.

Lemma to_simple_dual_drinker :
  to_simple_h_ty IFOL_DualDrinker =
  SimpleDD.DualDrinkerFormula SimpleBase.b_Unit SimpleBase.b_S.
Proof.
  reflexivity.
Defined.

Definition Simple_DualDrinker_Derivation : Type :=
  { p : SimpleHyper.h_tm &
      SimpleHyper.h_derivation SimpleBase.b_Unit nil p
        (SimpleDD.DualDrinkerFormula SimpleBase.b_Unit SimpleBase.b_S) }.

Definition simple_dual_drinker_not_derivable_at_unit_s :
  Simple_DualDrinker_Derivation -> False.
Proof.
  intros [p Hder].
  pose proof (SimpleSoundness.hyper_soundness_inhabited
    Hder
    (SimpleDD.wf_ctx_nil_valid SimpleBase.b_Unit)
    (SimpleDD.DualDrinker_WellFormed SimpleBase.b_Unit SimpleBase.b_S)) as Hsem.
  pose proof (Hsem tt) as Hbad.
  compute in Hbad.
  exact Hbad.
Defined.

Definition IFOL_DualDrinker_Derivation : Type :=
  { p : @FullHyper.h_tm NoSign NoFunc nat &
      @IFOL.ifol_h_derivation NoSign NoFunc nat
        NoFuncSignature NatPredicateSignature
        FullBase.b_Unit nil p IFOL_DualDrinker }.

Definition IFOL_DualDrinker_Underivable : Type :=
  IFOL_DualDrinker_Derivation -> False.

Definition ifolfull_dual_drinker_not_derivable :
  IFOL_DualDrinker_Underivable.
Proof.
  intros [p Hder].
  apply simple_dual_drinker_not_derivable_at_unit_s.
  exists (to_simple_h_tm p).
  rewrite <- to_simple_dual_drinker.
  exact (@to_simple_ifol_derivation FullBase.b_Unit nil p IFOL_DualDrinker Hder).
Defined.

Definition EpsilonFull_DualDrinker {EpsSign : Type} :
  @FullHyper.h_ty EpsSign NoFunc nat :=
  @MetaDD.DualDrinkerFormula EpsSign NoFunc nat 0 FullBase.b_Unit FullBase.b_S.

Lemma T_ifol_language_dual_drinker :
  forall {EpsSign : Type},
  @T_ifol_language_h_ty EpsSign IFOL_DualDrinker =
  @EpsilonFull_DualDrinker EpsSign.
Proof.
  reflexivity.
Defined.

Definition EpsilonFull_DualDrinker_Derivation {EpsSign : Type}
  (HSkolem : FullHyper.SkolemMapping EpsSign NoFunc nat) : Type :=
  { p : @FullHyper.h_tm EpsSign NoFunc nat &
      @FullHyper.h_derivation EpsSign NoFunc nat
        NoFuncSignature NatPredicateSignature HSkolem
        FullBase.b_Unit nil p
        (@MetaDD.T_ifol_to_epsilonfull EpsSign NoFunc nat
          (@T_ifol_language_h_ty EpsSign IFOL_DualDrinker)) }.

Definition epsilonfull_proves_translated_dual_drinker :
  forall {EpsSign : Type} (HSkolem : FullHyper.SkolemMapping EpsSign NoFunc nat),
  EpsilonFull_DualDrinker_Derivation HSkolem.
Proof.
  intros EpsSign HSkolem.
  unfold EpsilonFull_DualDrinker_Derivation.
  rewrite T_ifol_language_dual_drinker.
  unfold EpsilonFull_DualDrinker.
  exact (@MetaDD.epsilonfull_dual_drinker_atom_provable
    EpsSign NoFunc nat NoFuncSignature NatPredicateSignature HSkolem
    0 FullBase.b_Unit FullBase.b_S eq_refl).
Defined.

Definition epsilonfull_not_conservative_over_ifolfull :
  forall {EpsSign : Type} (HSkolem : FullHyper.SkolemMapping EpsSign NoFunc nat),
  (IFOL_DualDrinker_Underivable *
   EpsilonFull_DualDrinker_Derivation HSkolem)%type.
Proof.
  intros EpsSign HSkolem.
  split.
  - exact ifolfull_dual_drinker_not_derivable.
  - exact (epsilonfull_proves_translated_dual_drinker HSkolem).
Defined.
