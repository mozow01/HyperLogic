
Require Import List.
Import ListNotations.

Require Import HyperLogic.Logic.Metatheory.EpsilonFull_Translation.
Require Import HyperLogic.Logic.Hyper.Epsilon.Epsilon_Syntax_Lemmas.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax_Lemmas.

Module EpsLemmas := HyperLogic.Logic.Hyper.Epsilon.Epsilon_Syntax_Lemmas.
Module FullLemmas := HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax_Lemmas.

Section BackwardErasure.

Context {SignFull SignEps Func Pred : Type}.

Context `{HFuncEps : EpsBase.FunctionSignature Func}.
Context `{HFuncFull : FullBase.FunctionSignature Func}.
Context {HFuncCompat : @FunctionSignatureCompat Func HFuncEps HFuncFull}.
Context `{HPredEps : EpsHyper.PredicateSignature Pred}.
Context `{HPredFull : FullHyper.PredicateSignature Pred}.
Context {HPredCompat : @PredicateSignatureCompat Pred HPredEps HPredFull}.
Context `{HSkolemEps : EpsHyper.SkolemMapping SignEps Func Pred}.
Context `{HSkolemFull : FullHyper.SkolemMapping SignFull Func Pred}.

Definition erase_b_ty (A : FullBase.b_ty) : EpsBase.b_ty :=
  project_b_ty A.

Fixpoint erase_b_tm_with
  (erase_sign : SignFull -> SignEps)
  (t : @FullBase.b_tm SignFull Func) : @EpsBase.b_tm SignEps Func :=
  match t with
  | FullBase.b_id => EpsBase.b_id
  | FullBase.b_comp g f =>
      EpsBase.b_comp (erase_b_tm_with erase_sign g) (erase_b_tm_with erase_sign f)
  | FullBase.b_unit => EpsBase.b_unit
  | FullBase.b_pair f g =>
      EpsBase.b_pair (erase_b_tm_with erase_sign f) (erase_b_tm_with erase_sign g)
  | FullBase.b_fst => EpsBase.b_fst
  | FullBase.b_snd => EpsBase.b_snd
  | FullBase.b_const A s => EpsBase.b_const (erase_b_ty A) (erase_sign s)
  | FullBase.b_func f => EpsBase.b_func f
  end.

Fixpoint erase_h_ty_with
  (erase_sign : SignFull -> SignEps)
  (Phi : @FullHyper.h_ty SignFull Func Pred)
  : @EpsHyper.h_ty SignEps Func Pred :=
  match Phi with
  | FullHyper.Ty_Unit => EpsHyper.Ty_Unit
  | FullHyper.Ty_Void => EpsHyper.Ty_Void
  | FullHyper.Ty_Prod A B =>
      EpsHyper.Ty_Prod (erase_h_ty_with erase_sign A) (erase_h_ty_with erase_sign B)
  | FullHyper.Ty_Sum A B =>
      EpsHyper.Ty_Sum (erase_h_ty_with erase_sign A) (erase_h_ty_with erase_sign B)
  | FullHyper.Ty_Arrow A B =>
      EpsHyper.Ty_Arrow (erase_h_ty_with erase_sign A) (erase_h_ty_with erase_sign B)
  | FullHyper.Ty_Atom p t =>
      EpsHyper.Ty_Atom p (erase_b_tm_with erase_sign t)
  | FullHyper.Ty_All A Body =>
      EpsHyper.Ty_All (erase_b_ty A) (erase_h_ty_with erase_sign Body)
  | FullHyper.Ty_Ex A Body =>
      EpsHyper.form_subst
        (EpsBase.b_pair EpsBase.b_id
          (EpsBase.b_const (erase_b_ty A)
            (EpsHyper.skolem_index
              (erase_b_ty A) (erase_h_ty_with erase_sign Body))))
        (erase_h_ty_with erase_sign Body)
  end.

Definition erase_h_context_with
  (erase_sign : SignFull -> SignEps)
  (G : @FullHyper.h_context SignFull Func Pred)
  : @EpsHyper.h_context SignEps Func Pred :=
  map (erase_h_ty_with erase_sign) G.

Fixpoint erase_h_tm_with
  (erase_sign : SignFull -> SignEps)
  (p : @FullHyper.h_tm SignFull Func Pred)
  : @EpsHyper.h_tm SignEps Func Pred :=
  match p with
  | FullHyper.tm_unit => EpsHyper.tm_unit
  | FullHyper.tm_var i => EpsHyper.tm_var i
  | FullHyper.tm_lam Phi p' =>
      EpsHyper.tm_lam (erase_h_ty_with erase_sign Phi) (erase_h_tm_with erase_sign p')
  | FullHyper.tm_app p1 p2 =>
      EpsHyper.tm_app (erase_h_tm_with erase_sign p1) (erase_h_tm_with erase_sign p2)
  | FullHyper.tm_pair p1 p2 =>
      EpsHyper.tm_pair (erase_h_tm_with erase_sign p1) (erase_h_tm_with erase_sign p2)
  | FullHyper.tm_fst p' => EpsHyper.tm_fst (erase_h_tm_with erase_sign p')
  | FullHyper.tm_snd p' => EpsHyper.tm_snd (erase_h_tm_with erase_sign p')
  | FullHyper.tm_inl Psi p' =>
      EpsHyper.tm_inl (erase_h_ty_with erase_sign Psi) (erase_h_tm_with erase_sign p')
  | FullHyper.tm_inr Phi p' =>
      EpsHyper.tm_inr (erase_h_ty_with erase_sign Phi) (erase_h_tm_with erase_sign p')
  | FullHyper.tm_case p' p1 p2 =>
      EpsHyper.tm_case
        (erase_h_tm_with erase_sign p')
        (erase_h_tm_with erase_sign p1)
        (erase_h_tm_with erase_sign p2)
  | FullHyper.tm_absurd Phi p' =>
      EpsHyper.tm_absurd (erase_h_ty_with erase_sign Phi) (erase_h_tm_with erase_sign p')
  | FullHyper.tm_all_intro p' =>
      EpsHyper.tm_all_intro (erase_h_tm_with erase_sign p')
  | FullHyper.tm_all_elim p' t =>
      EpsHyper.tm_all_elim (erase_h_tm_with erase_sign p') (erase_b_tm_with erase_sign t)
  | FullHyper.tm_ex_intro t p' =>
      EpsHyper.tm_eps_intro (erase_b_tm_with erase_sign t) (erase_h_tm_with erase_sign p')
  | FullHyper.tm_ex_elim p1 p2 =>
      EpsHyper.tm_eps_elim (erase_h_tm_with erase_sign p1) (erase_h_tm_with erase_sign p2)
  | FullHyper.tm_eps_intro t p' =>
      EpsHyper.tm_eps_intro (erase_b_tm_with erase_sign t) (erase_h_tm_with erase_sign p')
  | FullHyper.tm_eps_elim p1 p2 =>
      EpsHyper.tm_eps_elim (erase_h_tm_with erase_sign p1) (erase_h_tm_with erase_sign p2)
  end.

(** [SkolemErasure] maps full Skolem names to their erased counterparts.
    Its compatibility law is signature coherence, not an object-logic or
    model axiom. Literal equality is required because [b_const] stores raw
    names rather than a separate setoid relation. *)
Class SkolemErasure : Type := {
  erase_sign : SignFull -> SignEps;
  erase_skolem_index :
  forall (A : FullBase.b_ty) (Phi : @FullHyper.h_ty SignFull Func Pred),
    erase_sign (FullHyper.skolem_index A Phi) =
    EpsHyper.skolem_index
      (erase_b_ty A) (erase_h_ty_with erase_sign Phi)
}.

Context `{HSkolemErasure : SkolemErasure}.

Definition erase_b_tm
  (t : @FullBase.b_tm SignFull Func) : @EpsBase.b_tm SignEps Func :=
  erase_b_tm_with erase_sign t.

Definition erase_h_ty
  (Phi : @FullHyper.h_ty SignFull Func Pred)
  : @EpsHyper.h_ty SignEps Func Pred :=
  erase_h_ty_with erase_sign Phi.

Definition erase_h_context
  (G : @FullHyper.h_context SignFull Func Pred)
  : @EpsHyper.h_context SignEps Func Pred :=
  erase_h_context_with erase_sign G.

Definition erase_h_tm
  (p : @FullHyper.h_tm SignFull Func Pred)
  : @EpsHyper.h_tm SignEps Func Pred :=
  erase_h_tm_with erase_sign p.

Lemma erase_func_dom :
  forall f, erase_b_ty (FullBase.func_dom f) = EpsBase.func_dom f.
Proof.
  intro f.
  unfold erase_b_ty.
  rewrite func_dom_compat.
  apply project_embed_b_ty.
Qed.

Lemma erase_func_cod :
  forall f, erase_b_ty (FullBase.func_cod f) = EpsBase.func_cod f.
Proof.
  intro f.
  unfold erase_b_ty.
  rewrite func_cod_compat.
  apply project_embed_b_ty.
Qed.

Lemma erase_pred_dom :
  forall p, erase_b_ty (FullHyper.pred_dom p) = EpsHyper.pred_dom p.
Proof.
  intro p.
  unfold erase_b_ty.
  rewrite pred_dom_compat.
  apply project_embed_b_ty.
Qed.

Lemma erase_b_subst_ext :
  forall (f : @FullBase.b_tm SignFull Func),
    erase_b_tm (FullHyper.b_subst_ext f) =
    EpsHyper.b_subst_ext (erase_b_tm f).
Proof.
  reflexivity.
Qed.

Lemma erase_base_typing :
  forall {I : FullBase.b_ty} {t : @FullBase.b_tm SignFull Func} {A : FullBase.b_ty},
    @FullBase.base_typing SignFull Func HFuncFull I t A ->
    @EpsBase.base_typing SignEps Func HFuncEps
      (erase_b_ty I) (erase_b_tm t) (erase_b_ty A).
Proof.
  intros I t A H.
  induction H; simpl.
  - apply EpsBase.BT_Id.
  - eapply EpsBase.BT_Comp.
    + exact IHbase_typing1.
    + exact IHbase_typing2.
  - apply EpsBase.BT_Unit.
  - apply EpsBase.BT_Pair.
    + exact IHbase_typing1.
    + exact IHbase_typing2.
  - apply EpsBase.BT_Fst.
  - apply EpsBase.BT_Snd.
  - apply EpsBase.BT_Const.
  - rewrite erase_func_dom.
    rewrite erase_func_cod.
    apply EpsBase.BT_Func.
Defined.

Lemma erase_base_equiv :
  forall {I A : FullBase.b_ty} {f g : @FullBase.b_tm SignFull Func}
    {df : @FullBase.base_typing SignFull Func HFuncFull I f A}
    {dg : @FullBase.base_typing SignFull Func HFuncFull I g A},
    @FullBase.base_equiv SignFull Func HFuncFull I A f g df dg ->
    @EpsBase.base_equiv SignEps Func HFuncEps
      (erase_b_ty I) (erase_b_ty A) (erase_b_tm f) (erase_b_tm g)
      (erase_base_typing df) (erase_base_typing dg).
Proof.
  intros I A f g df dg H.
  induction H; simpl.
  - apply EpsBase.BE_Refl.
  - apply EpsBase.BE_Sym. exact IHbase_equiv.
  - eapply EpsBase.BE_Trans.
    + exact IHbase_equiv1.
    + exact IHbase_equiv2.
  - apply EpsBase.BE_CongComp; assumption.
  - apply EpsBase.BE_CongPair; assumption.
  - apply EpsBase.BE_Assoc.
  - apply EpsBase.BE_IdL.
  - apply EpsBase.BE_IdR.
  - apply EpsBase.BE_BetaFst.
  - apply EpsBase.BE_BetaSnd.
  - apply EpsBase.BE_EtaPair.
  - apply EpsBase.BE_EtaUnit.
  - apply EpsBase.BE_CompPair.
Defined.

Definition erase_eps_inst
  (A : FullBase.b_ty) (Phi : @FullHyper.h_ty SignFull Func Pred)
  : @EpsBase.b_tm SignEps Func :=
  EpsBase.b_pair EpsBase.b_id
    (EpsBase.b_const (erase_b_ty A)
      (EpsHyper.skolem_index (erase_b_ty A) (erase_h_ty Phi))).

Lemma erase_full_eps_tm :
  forall (A : FullBase.b_ty) (Phi : @FullHyper.h_ty SignFull Func Pred),
    erase_b_tm
      (FullBase.b_pair FullBase.b_id
        (FullBase.b_const A (FullHyper.skolem_index A Phi))) =
    erase_eps_inst A Phi.
Proof.
  intros A Phi.
  cbn [erase_b_tm erase_b_tm_with erase_eps_inst erase_h_ty erase_h_ty_with].
  rewrite erase_skolem_index.
  reflexivity.
Qed.

Definition cast_eps_base_typing
  {I A B : EpsBase.b_ty} {t : @EpsBase.b_tm SignEps Func}
  (e : B = A)
  (d : @EpsBase.base_typing SignEps Func HFuncEps I t A)
  : @EpsBase.base_typing SignEps Func HFuncEps I t B.
Proof.
  subst.
  exact d.
Defined.

Definition cast_eps_base_equiv
  {I A B : EpsBase.b_ty} {f g : @EpsBase.b_tm SignEps Func}
  {df1 : @EpsBase.base_typing SignEps Func HFuncEps I f A}
  {df2 : @EpsBase.base_typing SignEps Func HFuncEps I g A}
  (e : B = A)
  (H : @EpsBase.base_equiv SignEps Func HFuncEps I A f g df1 df2)
  : @EpsBase.base_equiv SignEps Func HFuncEps I B f g
      (cast_eps_base_typing e df1) (cast_eps_base_typing e df2).
Proof.
  subst.
  exact H.
Defined.

Definition full_eps_inst_typing
  (I A : FullBase.b_ty) (Phi : @FullHyper.h_ty SignFull Func Pred)
  : @FullBase.base_typing SignFull Func HFuncFull I
      (FullBase.b_pair FullBase.b_id
        (FullBase.b_const A (FullHyper.skolem_index A Phi)))
      (FullBase.b_Prod I A).
Proof.
  apply FullBase.BT_Pair.
  - apply FullBase.BT_Id.
  - apply FullBase.BT_Const.
Defined.

Definition full_pair_id_typing
  {I A : FullBase.b_ty} {f : @FullBase.b_tm SignFull Func}
  (df : @FullBase.base_typing SignFull Func HFuncFull I f A)
  : @FullBase.base_typing SignFull Func HFuncFull I
      (FullBase.b_pair FullBase.b_id f) (FullBase.b_Prod I A).
Proof.
  apply FullBase.BT_Pair.
  - apply FullBase.BT_Id.
  - exact df.
Defined.

Lemma erase_wellformed :
  forall {I : FullBase.b_ty} {Phi : @FullHyper.h_ty SignFull Func Pred},
    @FullHyper.WellFormed SignFull Func Pred HFuncFull HPredFull I Phi ->
    @EpsHyper.WellFormed SignEps Func Pred HFuncEps HPredEps
      (erase_b_ty I) (erase_h_ty Phi).
Proof.
  intros I Phi H.
  induction H; simpl.
  - apply EpsHyper.WF_Unit.
  - apply EpsHyper.WF_Void.
  - apply EpsHyper.WF_Prod; assumption.
  - apply EpsHyper.WF_Sum; assumption.
  - apply EpsHyper.WF_Arrow; assumption.
  - eapply EpsHyper.WF_Atom.
    rewrite <- erase_pred_dom.
    exact (erase_base_typing b).
  - apply EpsHyper.WF_All.
    exact IHWellFormed.
  - eapply EpsLemmas.wf_subst.
    + refine (@EpsBase.BT_Pair SignEps Func HFuncEps
        (erase_b_ty I) (erase_b_ty I) (erase_b_ty A)
        EpsBase.b_id
        (EpsBase.b_const (erase_b_ty A)
          (EpsHyper.skolem_index (erase_b_ty A) (erase_h_ty Phi)))
        _ _).
      * apply EpsBase.BT_Id.
      * apply EpsBase.BT_Const.
    + exact IHWellFormed.
Defined.

Lemma erase_all_wellformed :
  forall {I : FullBase.b_ty} {G : @FullHyper.h_context SignFull Func Pred},
    @FullHyper.All_WellFormed SignFull Func Pred HFuncFull HPredFull I G ->
    @EpsHyper.All_WellFormed SignEps Func Pred HFuncEps HPredEps
      (erase_b_ty I) (erase_h_context G).
Proof.
  intros I G H.
  induction H; simpl.
  - apply EpsHyper.AWF_Nil.
  - apply EpsHyper.AWF_Cons.
    + apply erase_wellformed. exact w.
    + exact IHAll_WellFormed.
Defined.

Lemma erase_form_subst_equiv :
  forall {I J : FullBase.b_ty} (t : @FullBase.b_tm SignFull Func)
    (dt : @FullBase.base_typing SignFull Func HFuncFull I t J)
    (Phi : @FullHyper.h_ty SignFull Func Pred),
    @FullHyper.WellFormed SignFull Func Pred HFuncFull HPredFull J Phi ->
    @EpsHyper.form_equiv SignEps Func Pred HFuncEps HPredEps HSkolemEps
      (erase_b_ty I)
      (erase_h_ty (FullHyper.form_subst t Phi))
      (EpsHyper.form_subst (erase_b_tm t) (erase_h_ty Phi)).
Proof.
  intros I J t dt Phi Hwf.
  revert I t dt.
  induction Hwf; intros I0 t0 dt0; simpl.
  - apply EpsHyper.FE_Refl.
    apply EpsHyper.WF_Unit.
  - apply EpsHyper.FE_Refl.
    apply EpsHyper.WF_Void.
  - apply EpsHyper.FE_Prod.
    + apply IHHwf1. exact dt0.
    + apply IHHwf2. exact dt0.
  - apply EpsHyper.FE_Sum.
    + apply IHHwf1. exact dt0.
    + apply IHHwf2. exact dt0.
  - apply EpsHyper.FE_Arrow.
    + apply IHHwf1. exact dt0.
    + apply IHHwf2. exact dt0.
  - apply EpsHyper.FE_Refl.
    eapply EpsHyper.WF_Atom.
    rewrite <- erase_pred_dom.
    eapply EpsBase.BT_Comp.
    + exact (erase_base_typing b).
    + exact (erase_base_typing dt0).
  - apply EpsHyper.FE_All.
    rewrite <- erase_b_subst_ext.
    exact (IHHwf (FullBase.b_Prod I0 A) (FullHyper.b_subst_ext t0)
      (FullLemmas.typing_subst_ext dt0)).
  - eapply EpsHyper.FE_Trans.
    + eapply EpsHyper.FE_Eps_Functorial.
      exact (IHHwf (FullBase.b_Prod I0 A) (FullHyper.b_subst_ext t0)
        (FullLemmas.typing_subst_ext dt0)).
    + eapply EpsHyper.FE_Eps_BC.
      * exact (erase_base_typing dt0).
      * exact (erase_wellformed Hwf).
Defined.

Lemma erase_full_eps_subst_equiv :
  forall (I A : FullBase.b_ty) (Phi : @FullHyper.h_ty SignFull Func Pred),
    @FullHyper.WellFormed SignFull Func Pred HFuncFull HPredFull
      (FullBase.b_Prod I A) Phi ->
    @EpsHyper.form_equiv SignEps Func Pred HFuncEps HPredEps HSkolemEps
      (erase_b_ty I)
      (EpsHyper.form_subst (erase_eps_inst A Phi) (erase_h_ty Phi))
      (erase_h_ty
        (FullHyper.form_subst
          (FullBase.b_pair FullBase.b_id
            (FullBase.b_const A (FullHyper.skolem_index A Phi)))
          Phi)).
Proof.
  intros I A Phi Hwf.
  rewrite <- erase_full_eps_tm.
  apply EpsHyper.FE_Sym.
  exact (erase_form_subst_equiv
    (I:=I) (J:=FullBase.b_Prod I A)
    (FullBase.b_pair FullBase.b_id
      (FullBase.b_const A (FullHyper.skolem_index A Phi)))
    (full_eps_inst_typing I A Phi)
    Phi Hwf).
Defined.

Lemma erase_form_equiv :
  forall {I : FullBase.b_ty} {Phi Psi : @FullHyper.h_ty SignFull Func Pred},
    @FullHyper.form_equiv SignFull Func Pred HFuncFull HPredFull HSkolemFull
      I Phi Psi ->
    @EpsHyper.form_equiv SignEps Func Pred HFuncEps HPredEps HSkolemEps
      (erase_b_ty I) (erase_h_ty Phi) (erase_h_ty Psi).
Proof.
  intros I Phi Psi H.
  induction H; simpl.
  - set (d1' := cast_eps_base_typing (eq_sym (erase_pred_dom p)) (erase_base_typing d1)).
    set (d2' := cast_eps_base_typing (eq_sym (erase_pred_dom p)) (erase_base_typing d2)).
    refine (@EpsHyper.FE_Atom SignEps Func Pred
      HFuncEps HPredEps HSkolemEps (erase_b_ty I) p
      (erase_b_tm t1) (erase_b_tm t2) d1' d2' _).
    exact (cast_eps_base_equiv (eq_sym (erase_pred_dom p)) (erase_base_equiv b)).
  - apply EpsHyper.FE_Refl.
    apply erase_wellformed.
    exact w.
  - apply EpsHyper.FE_Sym.
    exact IHform_equiv.
  - eapply EpsHyper.FE_Trans.
    + exact IHform_equiv1.
    + exact IHform_equiv2.
  - apply EpsHyper.FE_Prod; assumption.
  - apply EpsHyper.FE_Sum; assumption.
  - apply EpsHyper.FE_Arrow; assumption.
  - apply EpsHyper.FE_All.
    exact IHform_equiv.
  - apply EpsHyper.FE_Eps_Functorial.
    exact IHform_equiv.
  - apply erase_full_eps_subst_equiv.
    exact w.
  - match goal with
    | Hfe : @FullHyper.form_equiv _ _ _ _ _ _ (FullBase.b_Prod I A) Phi Psi |- _ =>
        destruct (FullLemmas.form_equiv_wf (FullBase.b_Prod I A) Phi Psi Hfe)
          as [wfPhi wfPsi]
    end.
    eapply EpsHyper.FE_Trans.
    + apply EpsHyper.FE_Sym.
      apply erase_full_eps_subst_equiv.
      exact wfPhi.
    + eapply EpsHyper.FE_Trans.
      * apply EpsHyper.FE_Eps_Functorial.
        exact IHform_equiv.
      * apply erase_full_eps_subst_equiv.
        exact wfPsi.
  - eapply EpsHyper.FE_Trans.
    + exact (erase_form_subst_equiv
        (I:=I) (J:=I) FullBase.b_id FullBase.BT_Id Phi w).
    + apply EpsHyper.FE_Pullback_Id.
      apply erase_wellformed.
      exact w.
  - pose proof
      (erase_form_subst_equiv (I:=I) (J:=J) g dg
        (FullHyper.form_subst f Phi)
        (FullLemmas.wf_subst f df Phi w)) as Hg.
    pose proof
      (erase_form_subst_equiv (I:=J) (J:=K) f df Phi w) as Hf.
    pose proof
      (erase_form_subst_equiv (I:=I) (J:=K)
        (FullBase.b_comp f g) (FullBase.BT_Comp df dg) Phi w) as Hcomp.
    eapply EpsHyper.FE_Trans.
    + exact Hg.
    + eapply EpsHyper.FE_Trans.
      * eapply EpsLemmas.form_equiv_subst.
        -- exact (erase_base_typing dg).
        -- exact Hf.
      * eapply EpsHyper.FE_Trans.
        -- eapply EpsHyper.FE_Pullback_Comp.
           ++ exact (erase_base_typing df).
           ++ exact (erase_base_typing dg).
           ++ apply erase_wellformed. exact w.
        -- apply EpsHyper.FE_Sym.
           exact Hcomp.
  - pose proof
      (erase_form_subst_equiv (I:=I) (J:=J) f df Phi w) as Hf.
    pose proof
      (erase_form_subst_equiv (I:=I) (J:=J) g dg Phi w) as Hg.
    eapply EpsHyper.FE_Trans.
    + exact Hf.
    + eapply EpsHyper.FE_Trans.
      * eapply EpsHyper.FE_Pullback_Cong.
        -- exact (erase_base_equiv b).
        -- apply erase_wellformed. exact w.
      * apply EpsHyper.FE_Sym.
        exact Hg.
  - pose proof
      (FullLemmas.wf_subst
        (FullHyper.b_subst_ext t)
        (FullLemmas.typing_subst_ext dt)
        Phi w) as wf_sub.
    pose proof
      (erase_full_eps_subst_equiv I A
        (FullHyper.form_subst (FullHyper.b_subst_ext t) Phi)
        wf_sub) as Hsrc.
    pose proof
      (erase_form_subst_equiv
        (I:=FullBase.b_Prod I A) (J:=FullBase.b_Prod J A)
        (FullHyper.b_subst_ext t)
        (FullLemmas.typing_subst_ext dt)
        Phi w) as Hbody.
    pose proof
      (erase_full_eps_subst_equiv J A Phi w) as Hphi.
    pose proof
      (FullLemmas.wf_subst
        (FullBase.b_pair FullBase.b_id
          (FullBase.b_const A (FullHyper.skolem_index A Phi)))
        (full_eps_inst_typing J A Phi)
        Phi w) as wf_phi_eps.
    pose proof
      (erase_form_subst_equiv (I:=I) (J:=J) t dt
        (FullHyper.form_subst
          (FullBase.b_pair FullBase.b_id
            (FullBase.b_const A (FullHyper.skolem_index A Phi)))
          Phi)
        wf_phi_eps) as Htarget.
    eapply EpsHyper.FE_Trans.
    + apply EpsHyper.FE_Sym.
      exact Hsrc.
    + eapply EpsHyper.FE_Trans.
      * apply EpsHyper.FE_Eps_Functorial.
        exact Hbody.
      * eapply EpsHyper.FE_Trans.
        -- eapply EpsHyper.FE_Eps_BC.
           ++ exact (erase_base_typing dt).
           ++ exact (erase_wellformed w).
        -- eapply EpsHyper.FE_Trans.
           ++ eapply EpsLemmas.form_equiv_subst.
              ** exact (erase_base_typing dt).
              ** exact Hphi.
           ++ apply EpsHyper.FE_Sym.
              exact Htarget.
Defined.

Lemma erase_ctx_equiv :
  forall {I : FullBase.b_ty} {G1 G2 : @FullHyper.h_context SignFull Func Pred},
    @FullHyper.ctx_equiv SignFull Func Pred HFuncFull HPredFull HSkolemFull
      I G1 G2 ->
    @EpsHyper.ctx_equiv SignEps Func Pred HFuncEps HPredEps HSkolemEps
      (erase_b_ty I) (erase_h_context G1) (erase_h_context G2).
Proof.
  intros I G1 G2 H.
  induction H; simpl.
  - apply EpsHyper.CEq_Nil.
  - apply EpsHyper.CEq_Cons.
    + apply erase_form_equiv. exact f.
    + exact IHctx_equiv.
Defined.

Lemma erase_ctx_subst_equiv :
  forall {I J : FullBase.b_ty} (t : @FullBase.b_tm SignFull Func)
    (dt : @FullBase.base_typing SignFull Func HFuncFull I t J)
    (G : @FullHyper.h_context SignFull Func Pred),
    @FullHyper.All_WellFormed SignFull Func Pred HFuncFull HPredFull J G ->
    @EpsHyper.ctx_equiv SignEps Func Pred HFuncEps HPredEps HSkolemEps
      (erase_b_ty I)
      (erase_h_context (FullHyper.ctx_subst t G))
      (EpsHyper.ctx_subst (erase_b_tm t) (erase_h_context G)).
Proof.
  intros I J t dt G HwfG.
  induction HwfG; simpl.
  - apply EpsHyper.CEq_Nil.
  - apply EpsHyper.CEq_Cons.
    + exact (erase_form_subst_equiv (I:=I) (J:=J) t dt Phi w).
    + exact IHHwfG.
Defined.

Lemma erase_h_derivation :
  forall {I : FullBase.b_ty} {G : @FullHyper.h_context SignFull Func Pred}
    {p : @FullHyper.h_tm SignFull Func Pred}
    {Phi : @FullHyper.h_ty SignFull Func Pred},
    @FullHyper.h_derivation SignFull Func Pred HFuncFull HPredFull HSkolemFull
      I G p Phi ->
    @EpsHyper.h_derivation SignEps Func Pred HFuncEps HPredEps HSkolemEps
      (erase_b_ty I) (erase_h_context G) (erase_h_tm p) (erase_h_ty Phi).
Proof.
  intros I G p Phi H.
  induction H; simpl.
  - apply EpsHyper.HD_Var0.
    exact (erase_all_wellformed a).
  - apply EpsHyper.HD_VarS.
    + apply erase_wellformed. exact w.
    + exact IHh_derivation.
  - apply EpsHyper.HD_Unit.
    exact (erase_all_wellformed a).
  - eapply EpsHyper.HD_Conv.
    + exact IHh_derivation.
    + apply erase_form_equiv. exact f.
  - eapply EpsHyper.HD_Ctx_Conv.
    + exact (erase_ctx_equiv c).
    + exact IHh_derivation.
  - apply EpsHyper.HD_Lam.
    exact IHh_derivation.
  - eapply EpsHyper.HD_App.
    + exact IHh_derivation1.
    + exact IHh_derivation2.
  - apply EpsHyper.HD_Pair; assumption.
  - eapply EpsHyper.HD_Fst.
    exact IHh_derivation.
  - eapply EpsHyper.HD_Snd.
    exact IHh_derivation.
  - apply EpsHyper.HD_Inl.
    + apply erase_wellformed. exact w.
    + exact IHh_derivation.
  - apply EpsHyper.HD_Inr.
    + apply erase_wellformed. exact w.
    + exact IHh_derivation.
  - eapply EpsHyper.HD_Case.
    + exact IHh_derivation1.
    + exact IHh_derivation2.
    + exact IHh_derivation3.
  - apply EpsHyper.HD_Absurd.
    + apply erase_wellformed. exact w.
    + exact IHh_derivation.
  - apply EpsHyper.HD_All_Intro.
    eapply EpsHyper.HD_Ctx_Conv.
    + match goal with
      | Hprem : @FullHyper.h_derivation _ _ _ _ _ _ (FullBase.b_Prod I A)
          (FullHyper.ctx_subst FullBase.b_fst G) p Phi |- _ =>
          pose proof (FullLemmas.meta_ctx_wf Hprem) as Hwf_sub;
          exact (erase_ctx_subst_equiv
            (I:=FullBase.b_Prod I A) (J:=I)
            FullBase.b_fst FullBase.BT_Fst G
            (FullLemmas.ctx_wf_fst_inv Hwf_sub))
      end.
    + exact IHh_derivation.
  - assert (HwfPhi :
      @FullHyper.WellFormed SignFull Func Pred HFuncFull HPredFull
        (FullBase.b_Prod I A) Phi).
    {
      pose proof (FullLemmas.meta_type_wf H) as HwfAll.
      inversion HwfAll; subst.
      exact X.
    }
    eapply EpsHyper.HD_Conv.
    + eapply EpsHyper.HD_All_Elim.
      * exact IHh_derivation.
      * exact (erase_base_typing b).
    + apply EpsHyper.FE_Sym.
      exact (erase_form_subst_equiv
        (I:=I) (J:=FullBase.b_Prod I A)
        (FullBase.b_pair FullBase.b_id f)
        (full_pair_id_typing b)
        Phi HwfPhi).
  - assert (HwfPhi :
      @FullHyper.WellFormed SignFull Func Pred HFuncFull HPredFull
        (FullBase.b_Prod I A) Phi).
    { eapply FullLemmas.h_derivation_wf_inv.
      - exact b.
      - exact H.
    }
    eapply EpsHyper.HD_Eps_Intro.
    + exact (erase_base_typing b).
    + eapply EpsHyper.HD_Conv.
      * exact IHh_derivation.
      * exact (erase_form_subst_equiv
          (I:=I) (J:=FullBase.b_Prod I A)
          (FullBase.b_pair FullBase.b_id f)
          (full_pair_id_typing b)
          Phi HwfPhi).
  - assert (HwfG :
      @FullHyper.All_WellFormed SignFull Func Pred HFuncFull HPredFull I G).
    {
      match goal with
      | Hprem : @FullHyper.h_derivation _ _ _ _ _ _ I G _ (FullHyper.Ty_Ex A Phi) |- _ =>
          exact (FullLemmas.meta_ctx_wf Hprem)
      end.
    }
    assert (HwfPhi :
      @FullHyper.WellFormed SignFull Func Pred HFuncFull HPredFull
        (FullBase.b_Prod I A) Phi).
    {
      match goal with
      | Hprem : @FullHyper.h_derivation _ _ _ _ _ _ I G _ (FullHyper.Ty_Ex A Phi) |- _ =>
          pose proof (FullLemmas.meta_type_wf Hprem) as HwfEx;
          inversion HwfEx; subst;
          exact X
      end.
    }
    assert (HwfChi :
      @FullHyper.WellFormed SignFull Func Pred HFuncFull HPredFull I Chi).
    {
      match goal with
      | Hprem : @FullHyper.h_derivation _ _ _ _ _ _
          (FullBase.b_Prod I A) (Phi :: FullHyper.ctx_subst FullBase.b_fst G)
          _ (FullHyper.form_subst FullBase.b_fst Chi) |- _ =>
          pose proof (FullLemmas.meta_type_wf Hprem) as HwfFst;
          exact (FullLemmas.form_wf_fst_inv HwfFst)
      end.
    }
    eapply EpsHyper.HD_Eps_Elim.
    + exact IHh_derivation1.
    + eapply EpsHyper.HD_Conv.
      * eapply EpsHyper.HD_Ctx_Conv.
        -- apply EpsHyper.CEq_Cons.
           ++ apply EpsHyper.FE_Refl.
              exact (erase_wellformed HwfPhi).
           ++ exact (erase_ctx_subst_equiv
                (I:=FullBase.b_Prod I A) (J:=I)
                FullBase.b_fst FullBase.BT_Fst G HwfG).
        -- exact IHh_derivation2.
      * exact (erase_form_subst_equiv
          (I:=FullBase.b_Prod I A) (J:=I)
          FullBase.b_fst FullBase.BT_Fst Chi HwfChi).
  - assert (HwfPhi :
      @FullHyper.WellFormed SignFull Func Pred HFuncFull HPredFull
        (FullBase.b_Prod I A) Phi).
    { eapply FullLemmas.h_derivation_wf_inv.
      - exact b.
      - exact H.
    }
    eapply EpsHyper.HD_Conv.
    + eapply EpsHyper.HD_Eps_Intro.
      * exact (erase_base_typing b).
      * eapply EpsHyper.HD_Conv.
        -- exact IHh_derivation.
        -- exact (erase_form_subst_equiv
            (I:=I) (J:=FullBase.b_Prod I A)
            (FullBase.b_pair FullBase.b_id f)
            (full_pair_id_typing b)
            Phi HwfPhi).
    + exact (erase_full_eps_subst_equiv I A Phi HwfPhi).
  - assert (HwfG :
      @FullHyper.All_WellFormed SignFull Func Pred HFuncFull HPredFull I G).
    {
      match goal with
      | Hprem : @FullHyper.h_derivation _ _ _ _ _ _ I G _
          (FullHyper.form_subst
            (FullBase.b_pair FullBase.b_id
              (FullBase.b_const A (FullHyper.skolem_index A Phi))) Phi) |- _ =>
          exact (FullLemmas.meta_ctx_wf Hprem)
      end.
    }
    assert (HwfPhi :
      @FullHyper.WellFormed SignFull Func Pred HFuncFull HPredFull
        (FullBase.b_Prod I A) Phi).
    { eapply FullLemmas.h_derivation_wf_inv.
      - exact (@FullBase.BT_Const SignFull Func HFuncFull I A
          (FullHyper.skolem_index A Phi)).
      - match goal with
        | Hprem : @FullHyper.h_derivation _ _ _ _ _ _ I G _
            (FullHyper.form_subst
              (FullBase.b_pair FullBase.b_id
                (FullBase.b_const A (FullHyper.skolem_index A Phi))) Phi) |- _ =>
            exact Hprem
        end.
    }
    assert (HwfChi :
      @FullHyper.WellFormed SignFull Func Pred HFuncFull HPredFull I Chi).
    {
      match goal with
      | Hprem : @FullHyper.h_derivation _ _ _ _ _ _
          (FullBase.b_Prod I A) (Phi :: FullHyper.ctx_subst FullBase.b_fst G)
          _ (FullHyper.form_subst FullBase.b_fst Chi) |- _ =>
          pose proof (FullLemmas.meta_type_wf Hprem) as HwfFst;
          exact (FullLemmas.form_wf_fst_inv HwfFst)
      end.
    }
    eapply EpsHyper.HD_Eps_Elim.
    + eapply EpsHyper.HD_Conv.
      * exact IHh_derivation1.
      * apply EpsHyper.FE_Sym.
        exact (erase_full_eps_subst_equiv I A Phi HwfPhi).
    + eapply EpsHyper.HD_Conv.
      * eapply EpsHyper.HD_Ctx_Conv.
        -- apply EpsHyper.CEq_Cons.
           ++ apply EpsHyper.FE_Refl.
              exact (erase_wellformed HwfPhi).
           ++ exact (erase_ctx_subst_equiv
                (I:=FullBase.b_Prod I A) (J:=I)
                FullBase.b_fst FullBase.BT_Fst G HwfG).
        -- exact IHh_derivation2.
      * exact (erase_form_subst_equiv
          (I:=FullBase.b_Prod I A) (J:=I)
          FullBase.b_fst FullBase.BT_Fst Chi HwfChi).
Defined.

End BackwardErasure.
