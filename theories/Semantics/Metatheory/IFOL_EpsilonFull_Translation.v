(* The canonical inclusion of epsilon-free iFOL syntax into EpsilonFull. *)

Require Import List.
Import ListNotations.

Require HyperLogic.Logic.Base.IFOL.Base_Syntax.
Require HyperLogic.Logic.Hyper.IFOL.Hyper_Syntax.
Require HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Require HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.
Require HyperLogic.Semantics.IFOL.DualDrinker.

Module IBase := HyperLogic.Logic.Base.IFOL.Base_Syntax.
Module IHyper := HyperLogic.Logic.Hyper.IFOL.Hyper_Syntax.
Module EBase := HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Module EHyper := HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.
Module IDD := HyperLogic.Semantics.IFOL.DualDrinker.

Fixpoint ifol_to_epsilon_base_ty (A : IBase.b_ty) : EBase.b_ty :=
  match A with
  | IBase.b_Unit => EBase.b_Unit
  | IBase.b_S => EBase.b_S
  | IBase.b_Prod B C => EBase.b_Prod
      (ifol_to_epsilon_base_ty B) (ifol_to_epsilon_base_ty C)
  end.

Definition ifol_to_epsilon_function_signature (Func : Type)
  (F : IBase.FunctionSignature Func) : EBase.FunctionSignature Func :=
  {| EBase.func_dom f := ifol_to_epsilon_base_ty (IBase.func_dom f);
     EBase.func_cod f := ifol_to_epsilon_base_ty (IBase.func_cod f) |}.

Definition ifol_to_epsilon_predicate_signature (Pred : Type)
  (P : IHyper.PredicateSignature Pred) : EHyper.PredicateSignature Pred :=
  {| EHyper.pred_dom p := ifol_to_epsilon_base_ty (IHyper.pred_dom p) |}.

Section Translation.
  Context {Func Pred Sign : Type}.
  Context `{IFunc : IBase.FunctionSignature Func}.
  Context `{IPred : IHyper.PredicateSignature Pred}.
  Local Instance EFunc : EBase.FunctionSignature Func :=
    ifol_to_epsilon_function_signature Func IFunc.
  Local Instance EPred : EHyper.PredicateSignature Pred :=
    ifol_to_epsilon_predicate_signature Pred IPred.

  Fixpoint ifol_to_epsilon_base_tm (t : @IBase.b_tm Func) : @EBase.b_tm Sign Func :=
    match t with
    | IBase.b_id => EBase.b_id
    | IBase.b_comp g f => EBase.b_comp
        (ifol_to_epsilon_base_tm g) (ifol_to_epsilon_base_tm f)
    | IBase.b_unit => EBase.b_unit
    | IBase.b_pair f g => EBase.b_pair
        (ifol_to_epsilon_base_tm f) (ifol_to_epsilon_base_tm g)
    | IBase.b_fst => EBase.b_fst
    | IBase.b_snd => EBase.b_snd
    | IBase.b_func f => EBase.b_func f
    end.

  Fixpoint ifol_to_epsilon_h_ty (Phi : @IHyper.h_ty Func Pred)
    : @EHyper.h_ty Sign Func Pred :=
    match Phi with
    | IHyper.Ty_Unit => EHyper.Ty_Unit
    | IHyper.Ty_Void => EHyper.Ty_Void
    | IHyper.Ty_Prod A B => EHyper.Ty_Prod
        (ifol_to_epsilon_h_ty A) (ifol_to_epsilon_h_ty B)
    | IHyper.Ty_Sum A B => EHyper.Ty_Sum
        (ifol_to_epsilon_h_ty A) (ifol_to_epsilon_h_ty B)
    | IHyper.Ty_Arrow A B => EHyper.Ty_Arrow
        (ifol_to_epsilon_h_ty A) (ifol_to_epsilon_h_ty B)
    | IHyper.Ty_Atom p t => EHyper.Ty_Atom p (ifol_to_epsilon_base_tm t)
    | IHyper.Ty_All A Body => EHyper.Ty_All
        (ifol_to_epsilon_base_ty A) (ifol_to_epsilon_h_ty Body)
    | IHyper.Ty_Ex A Body => EHyper.Ty_Ex
        (ifol_to_epsilon_base_ty A) (ifol_to_epsilon_h_ty Body)
    end.

  Definition ifol_to_epsilon_context (G : @IHyper.h_context Func Pred)
    : @EHyper.h_context Sign Func Pred := map ifol_to_epsilon_h_ty G.

  Fixpoint ifol_to_epsilon_proof_tm (p : @IHyper.h_tm Func Pred)
    : @EHyper.h_tm Sign Func Pred :=
    match p with
    | IHyper.tm_unit => EHyper.tm_unit
    | IHyper.tm_var n => EHyper.tm_var n
    | IHyper.tm_lam A q => EHyper.tm_lam (ifol_to_epsilon_h_ty A)
        (ifol_to_epsilon_proof_tm q)
    | IHyper.tm_app q r => EHyper.tm_app
        (ifol_to_epsilon_proof_tm q) (ifol_to_epsilon_proof_tm r)
    | IHyper.tm_pair q r => EHyper.tm_pair
        (ifol_to_epsilon_proof_tm q) (ifol_to_epsilon_proof_tm r)
    | IHyper.tm_fst q => EHyper.tm_fst (ifol_to_epsilon_proof_tm q)
    | IHyper.tm_snd q => EHyper.tm_snd (ifol_to_epsilon_proof_tm q)
    | IHyper.tm_inl A q => EHyper.tm_inl (ifol_to_epsilon_h_ty A)
        (ifol_to_epsilon_proof_tm q)
    | IHyper.tm_inr A q => EHyper.tm_inr (ifol_to_epsilon_h_ty A)
        (ifol_to_epsilon_proof_tm q)
    | IHyper.tm_case q r s => EHyper.tm_case
        (ifol_to_epsilon_proof_tm q) (ifol_to_epsilon_proof_tm r)
        (ifol_to_epsilon_proof_tm s)
    | IHyper.tm_absurd A q => EHyper.tm_absurd (ifol_to_epsilon_h_ty A)
        (ifol_to_epsilon_proof_tm q)
    | IHyper.tm_all_intro q => EHyper.tm_all_intro (ifol_to_epsilon_proof_tm q)
    | IHyper.tm_all_elim q t => EHyper.tm_all_elim
        (ifol_to_epsilon_proof_tm q) (ifol_to_epsilon_base_tm t)
    | IHyper.tm_ex_intro t q => EHyper.tm_ex_intro
        (ifol_to_epsilon_base_tm t) (ifol_to_epsilon_proof_tm q)
    | IHyper.tm_ex_elim q r => EHyper.tm_ex_elim
        (ifol_to_epsilon_proof_tm q) (ifol_to_epsilon_proof_tm r)
    end.

  Fixpoint ifol_to_epsilon_base_typing {I A : IBase.b_ty}
    {t : @IBase.b_tm Func}
    (d : @IBase.base_typing Func IFunc I t A)
    : @EBase.base_typing Sign Func EFunc
        (ifol_to_epsilon_base_ty I) (ifol_to_epsilon_base_tm t)
        (ifol_to_epsilon_base_ty A) :=
    match d with
    | @IBase.BT_Id _ _ A => EBase.BT_Id
    | @IBase.BT_Comp _ _ A B C g f dg df => EBase.BT_Comp
        (ifol_to_epsilon_base_typing dg) (ifol_to_epsilon_base_typing df)
    | @IBase.BT_Unit _ _ A => EBase.BT_Unit
    | @IBase.BT_Pair _ _ A B C f g df dg => EBase.BT_Pair
        (ifol_to_epsilon_base_typing df) (ifol_to_epsilon_base_typing dg)
    | @IBase.BT_Fst _ _ A B => EBase.BT_Fst
    | @IBase.BT_Snd _ _ A B => EBase.BT_Snd
    | @IBase.BT_Func _ _ f => EBase.BT_Func
    end.

  Lemma ifol_to_epsilon_base_equiv {I A : IBase.b_ty}
    {t s : @IBase.b_tm Func}
    {dt : @IBase.base_typing Func IFunc I t A}
    {ds : @IBase.base_typing Func IFunc I s A}
    (e : @IBase.base_equiv Func IFunc I A t s dt ds)
    : @EBase.base_equiv Sign Func EFunc
        (ifol_to_epsilon_base_ty I) (ifol_to_epsilon_base_ty A)
        (ifol_to_epsilon_base_tm t) (ifol_to_epsilon_base_tm s)
        (ifol_to_epsilon_base_typing dt) (ifol_to_epsilon_base_typing ds).
  Proof.
    induction e.
    - apply EBase.BE_Refl.
    - apply EBase.BE_Sym. exact IHe.
    - eapply EBase.BE_Trans; eassumption.
    - eapply EBase.BE_CongComp; eassumption.
    - eapply EBase.BE_CongPair; eassumption.
    - apply EBase.BE_Assoc.
    - apply EBase.BE_IdL.
    - apply EBase.BE_IdR.
    - apply EBase.BE_BetaFst.
    - apply EBase.BE_BetaSnd.
    - apply EBase.BE_EtaPair.
    - apply EBase.BE_EtaUnit.
    - apply EBase.BE_CompPair.
  Defined.

  Lemma ifol_to_epsilon_form_subst : forall (f : @IBase.b_tm Func) Phi,
    ifol_to_epsilon_h_ty (IHyper.form_subst f Phi) =
    EHyper.form_subst (ifol_to_epsilon_base_tm f) (ifol_to_epsilon_h_ty Phi).
  Proof.
    intros f Phi. revert f.
    induction Phi; intro f; simpl; try rewrite IHPhi1; try rewrite IHPhi2;
      try rewrite IHPhi; reflexivity.
  Defined.

  Lemma ifol_to_epsilon_context_subst : forall (f : @IBase.b_tm Func) G,
    ifol_to_epsilon_context (IHyper.ctx_subst f G) =
    EHyper.ctx_subst (ifol_to_epsilon_base_tm f) (ifol_to_epsilon_context G).
  Proof.
    intros f G. induction G as [|Phi G IH]; simpl.
    - reflexivity.
    - rewrite ifol_to_epsilon_form_subst, IH. reflexivity.
  Defined.

  Lemma ifol_to_epsilon_well_formed {I : IBase.b_ty}
    {Phi : @IHyper.h_ty Func Pred}
    (w : @IHyper.WellFormed Func Pred IFunc IPred I Phi)
    : @EHyper.WellFormed Sign Func Pred EFunc EPred
        (ifol_to_epsilon_base_ty I) (ifol_to_epsilon_h_ty Phi).
  Proof.
    induction w; simpl.
    - apply EHyper.WF_Unit.
    - apply EHyper.WF_Void.
    - apply EHyper.WF_Prod; assumption.
    - apply EHyper.WF_Sum; assumption.
    - apply EHyper.WF_Arrow; assumption.
    - apply EHyper.WF_Atom. apply ifol_to_epsilon_base_typing. exact b.
    - apply EHyper.WF_All. assumption.
    - apply EHyper.WF_Ex. assumption.
  Defined.

  Lemma ifol_to_epsilon_all_well_formed {I : IBase.b_ty}
    {G : @IHyper.h_context Func Pred}
    (w : @IHyper.All_WellFormed Func Pred IFunc IPred I G)
    : @EHyper.All_WellFormed Sign Func Pred EFunc EPred
        (ifol_to_epsilon_base_ty I) (ifol_to_epsilon_context G).
  Proof.
    induction w; simpl.
    - apply EHyper.AWF_Nil.
    - apply EHyper.AWF_Cons.
      + apply ifol_to_epsilon_well_formed. exact w.
      + exact IHw.
  Defined.
End Translation.

Section Preservation.
  Context {Func Pred Sign : Type}.
  Context `{IFunc : IBase.FunctionSignature Func}.
  Context `{IPred : IHyper.PredicateSignature Pred}.
  Local Instance EFuncP : EBase.FunctionSignature Func :=
    ifol_to_epsilon_function_signature Func IFunc.
  Local Instance EPredP : EHyper.PredicateSignature Pred :=
    ifol_to_epsilon_predicate_signature Pred IPred.
  Context `{ESkolem : EHyper.SkolemMapping Sign Func Pred}.

  Lemma ifol_to_epsilon_form_equiv {I : IBase.b_ty}
    {Phi Psi : @IHyper.h_ty Func Pred}
    (e : @IHyper.form_equiv Func Pred IFunc IPred I Phi Psi)
    : @EHyper.form_equiv Sign Func Pred EFuncP EPredP ESkolem
        (ifol_to_epsilon_base_ty I)
        (ifol_to_epsilon_h_ty Phi) (ifol_to_epsilon_h_ty Psi).
  Proof.
    induction e; simpl.
    - eapply EHyper.FE_Atom.
      exact (ifol_to_epsilon_base_equiv (dt:=d1) (ds:=d2) b).
    - apply EHyper.FE_Refl. apply ifol_to_epsilon_well_formed. exact w.
    - apply EHyper.FE_Sym. exact IHe.
    - eapply EHyper.FE_Trans; eassumption.
    - apply EHyper.FE_Prod; assumption.
    - apply EHyper.FE_Sum; assumption.
    - apply EHyper.FE_Arrow; assumption.
    - apply EHyper.FE_All. exact IHe.
    - apply EHyper.FE_Ex. exact IHe.
    - rewrite ifol_to_epsilon_form_subst.
      apply EHyper.FE_Pullback_Id.
      apply ifol_to_epsilon_well_formed. exact w.
    - repeat rewrite ifol_to_epsilon_form_subst.
      eapply EHyper.FE_Pullback_Comp.
      + exact (ifol_to_epsilon_base_typing (I:=J) (A:=K) df).
      + exact (ifol_to_epsilon_base_typing (I:=I) (A:=J) dg).
      + apply ifol_to_epsilon_well_formed. exact w.
    - repeat rewrite ifol_to_epsilon_form_subst.
      eapply EHyper.FE_Pullback_Cong.
      + exact (ifol_to_epsilon_base_equiv (dt:=df) (ds:=dg) b).
      + apply ifol_to_epsilon_well_formed. exact w.
  Defined.

  Lemma ifol_to_epsilon_context_equiv {I : IBase.b_ty}
    {G1 G2 : @IHyper.h_context Func Pred}
    (e : @IHyper.ctx_equiv Func Pred IFunc IPred I G1 G2)
    : @EHyper.ctx_equiv Sign Func Pred EFuncP EPredP ESkolem
        (ifol_to_epsilon_base_ty I)
        (ifol_to_epsilon_context G1) (ifol_to_epsilon_context G2).
  Proof.
    induction e; simpl.
    - apply EHyper.CEq_Nil.
    - apply EHyper.CEq_Cons.
      + apply ifol_to_epsilon_form_equiv. assumption.
      + exact IHe.
  Defined.

  Lemma ifol_to_epsilon_derivation {I : IBase.b_ty}
    {G : @IHyper.h_context Func Pred} {p : @IHyper.h_tm Func Pred}
    {Phi : @IHyper.h_ty Func Pred}
    (d : @IHyper.h_derivation Func Pred IFunc IPred I G p Phi)
    : @EHyper.h_derivation Sign Func Pred EFuncP EPredP ESkolem
        (ifol_to_epsilon_base_ty I) (ifol_to_epsilon_context G)
        (ifol_to_epsilon_proof_tm p) (ifol_to_epsilon_h_ty Phi).
  Proof.
    induction d; simpl.
    - apply EHyper.HD_Var0.
      cbn [ifol_to_epsilon_context].
      exact (ifol_to_epsilon_all_well_formed (G:=Phi :: G) a).
    - apply EHyper.HD_VarS.
      + apply ifol_to_epsilon_well_formed. exact w.
      + exact IHd.
    - apply EHyper.HD_Unit.
      apply ifol_to_epsilon_all_well_formed. exact a.
    - eapply EHyper.HD_Conv.
      + exact IHd.
      + apply ifol_to_epsilon_form_equiv. assumption.
    - eapply EHyper.HD_Ctx_Conv.
      + exact (ifol_to_epsilon_context_equiv (G1:=G1) (G2:=G2) c).
      + exact IHd.
    - apply EHyper.HD_Lam. exact IHd.
    - eapply EHyper.HD_App; eassumption.
    - apply EHyper.HD_Pair; assumption.
    - eapply EHyper.HD_Fst; eassumption.
    - eapply EHyper.HD_Snd; eassumption.
    - apply EHyper.HD_Inl.
      + apply ifol_to_epsilon_well_formed. exact w.
      + exact IHd.
    - apply EHyper.HD_Inr.
      + apply ifol_to_epsilon_well_formed. exact w.
      + exact IHd.
    - eapply EHyper.HD_Case; eassumption.
    - apply EHyper.HD_Absurd.
      + apply ifol_to_epsilon_well_formed. exact w.
      + exact IHd.
    - rewrite ifol_to_epsilon_context_subst in IHd.
      apply EHyper.HD_All_Intro. exact IHd.
    - rewrite ifol_to_epsilon_form_subst.
      eapply EHyper.HD_All_Elim.
      + exact IHd.
      + apply ifol_to_epsilon_base_typing. exact b.
    - rewrite ifol_to_epsilon_form_subst in IHd.
      apply EHyper.HD_Ex_Intro.
      + apply ifol_to_epsilon_base_typing. exact b.
      + exact IHd.
    - change (EHyper.h_derivation
        (ifol_to_epsilon_base_ty (IBase.b_Prod I A))
        (ifol_to_epsilon_h_ty Phi ::
          ifol_to_epsilon_context (IHyper.ctx_subst IBase.b_fst G))
        (ifol_to_epsilon_proof_tm p2)
        (ifol_to_epsilon_h_ty (IHyper.form_subst IBase.b_fst Chi))) in IHd2.
      rewrite ifol_to_epsilon_context_subst in IHd2.
      rewrite ifol_to_epsilon_form_subst in IHd2.
      eapply EHyper.HD_Ex_Elim.
      + exact IHd1.
      + exact IHd2.
  Defined.
End Preservation.

Definition ifol_dual_drinker_epsilon_translation {Sign : Type}
  : @EHyper.h_ty Sign IDD.ifol_dd_func IDD.ifol_dd_pred :=
  @ifol_to_epsilon_h_ty IDD.ifol_dd_func IDD.ifol_dd_pred Sign
    (IDD.ifol_dual_drinker_formula IBase.b_Unit).

Lemma ifol_dual_drinker_translation_is_structural : forall Sign,
  @ifol_dual_drinker_epsilon_translation Sign =
  @ifol_to_epsilon_h_ty IDD.ifol_dd_func IDD.ifol_dd_pred Sign
    (IDD.ifol_dual_drinker_formula IBase.b_Unit).
Proof. reflexivity. Defined.
