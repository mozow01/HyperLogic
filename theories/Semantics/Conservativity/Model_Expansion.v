
Require Import List.
Import ListNotations.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import HyperLogic.Cat.Fibration.

Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Logic.Base.Simple_Ext.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple_Ext.Hyper_Syntax.
Require Import HyperLogic.Semantics.Simple_Ext.Simple_Ext_Fibration.

Module S_Base := HyperLogic.Logic.Base.Simple.Base_Syntax.
Module SE_Base := HyperLogic.Logic.Base.Simple_Ext.Base_Syntax.
Module S_Hyper := HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.
Module SE_Hyper := HyperLogic.Logic.Hyper.Simple_Ext.Hyper_Syntax.

Require Import HyperLogic.Semantics.Simple_Ext.Base_Epsilon_Completeness.
Require Import HyperLogic.Semantics.Simple.Simple_Completeness.
Require Import HyperLogic.Semantics.Simple_Ext.Simple_Ext_Soundness.
Module S_Comp := HyperLogic.Semantics.Simple.Simple_Completeness.
Module SE_Mod := HyperLogic.Semantics.Simple_Ext.Simple_Ext_Soundness.

(* Module S_Mod := HyperLogic.Logic.Semantics.Simple.HyperModel_Def. *)
(* Module SE_Mod := HyperLogic.Logic.Semantics.Simple_Ext.HyperModel_Def. *)
Require Import Coq.Init.Logic.

(** Expansion along the empty signature. *)

Definition Empty_Sign : Type := Empty_set.

(* Eliminating [s : Empty_set] supplies the otherwise required morphism. *)
Instance Trivial_SignatureModel {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} : 
  @BaseSignatureModel Empty_Sign C CC TSC.
Proof.
  constructor. intros I A s. destruct s.
Defined.

(** Embedding the legacy syntax into the signature-indexed syntax. *)

Fixpoint embed_b_ty (A : S_Base.b_ty) : SE_Base.b_ty :=
  match A with
  | S_Base.b_Unit => SE_Base.b_Unit
  | S_Base.b_S => SE_Base.b_S
  | S_Base.b_Prod A1 A2 => SE_Base.b_Prod (embed_b_ty A1) (embed_b_ty A2)
  end.

Fixpoint embed_b_tm (t : S_Base.b_tm) : @SE_Base.b_tm Empty_Sign :=
  match t with
  | S_Base.b_id => @SE_Base.b_id Empty_Sign
  | S_Base.b_comp f g => @SE_Base.b_comp Empty_Sign (embed_b_tm f) (embed_b_tm g)
  | S_Base.b_unit => @SE_Base.b_unit Empty_Sign
  | S_Base.b_pair f g => @SE_Base.b_pair Empty_Sign (embed_b_tm f) (embed_b_tm g)
  | S_Base.b_fst => @SE_Base.b_fst Empty_Sign
  | S_Base.b_snd => @SE_Base.b_snd Empty_Sign
  end.

Fixpoint embed_ty (Phi : S_Hyper.h_ty) : @SE_Hyper.h_ty Empty_Sign :=
  match Phi with
  | S_Hyper.Ty_Unit => @SE_Hyper.Ty_Unit Empty_Sign
  | S_Hyper.Ty_Void => @SE_Hyper.Ty_Void Empty_Sign
  | S_Hyper.Ty_Prod A B => @SE_Hyper.Ty_Prod Empty_Sign (embed_ty A) (embed_ty B)
  | S_Hyper.Ty_Sum A B => @SE_Hyper.Ty_Sum Empty_Sign (embed_ty A) (embed_ty B)
  | S_Hyper.Ty_Arrow A B => @SE_Hyper.Ty_Arrow Empty_Sign (embed_ty A) (embed_ty B)
  | S_Hyper.Ty_Atom p t => @SE_Hyper.Ty_Atom Empty_Sign p (embed_b_tm t)
  | S_Hyper.Ty_All A Body => @SE_Hyper.Ty_All Empty_Sign (embed_b_ty A) (embed_ty Body)
  | S_Hyper.Ty_Ex A Body => @SE_Hyper.Ty_Ex Empty_Sign (embed_b_ty A) (embed_ty Body)
  end.

(** The embedding preserves typing and well-formedness. *)

Lemma embed_b_typing : forall I t A,
  S_Base.base_typing I t A ->
  @SE_Base.base_typing Empty_Sign (embed_b_ty I) (embed_b_tm t) (embed_b_ty A).
Proof.
  intros I t A H. induction H; simpl.
  - apply SE_Base.BT_Id.
  - eapply SE_Base.BT_Comp; eauto.
  - apply SE_Base.BT_Unit.
  - apply SE_Base.BT_Pair; auto.
  - apply SE_Base.BT_Fst.
  - apply SE_Base.BT_Snd.
Defined.

Lemma embed_wf : forall I Phi,
  S_Hyper.WellFormed I Phi ->
  @SE_Hyper.WellFormed Empty_Sign (embed_b_ty I) (embed_ty Phi).
Proof.
  intros I Phi H. induction H; simpl.
  - apply SE_Hyper.WF_Unit.
  - apply SE_Hyper.WF_Void.
  - apply SE_Hyper.WF_Prod; auto.
  - apply SE_Hyper.WF_Sum; auto.
  - apply SE_Hyper.WF_Arrow; auto.
  - eapply SE_Hyper.WF_Atom. apply embed_b_typing. exact b.
  - apply SE_Hyper.WF_All. exact IHWellFormed.
  - apply SE_Hyper.WF_Ex. exact IHWellFormed.
Defined.

(** Forgetting the empty-signature extension. *)

Fixpoint forget_b_ty (A : SE_Base.b_ty) : S_Base.b_ty :=
  match A with
  | SE_Base.b_Unit => S_Base.b_Unit
  | SE_Base.b_S => S_Base.b_S
  | SE_Base.b_Prod A1 A2 => S_Base.b_Prod (forget_b_ty A1) (forget_b_ty A2)
  end.

Fixpoint forget_b_tm (t : @SE_Base.b_tm Empty_Sign) : S_Base.b_tm :=
  match t with
  | SE_Base.b_id => S_Base.b_id
  | SE_Base.b_comp f g => S_Base.b_comp (forget_b_tm f) (forget_b_tm g)
  | SE_Base.b_unit => S_Base.b_unit
  | SE_Base.b_pair f g => S_Base.b_pair (forget_b_tm f) (forget_b_tm g)
  | SE_Base.b_fst => S_Base.b_fst
  | SE_Base.b_snd => S_Base.b_snd
  | SE_Base.b_const _ s => match s with end (* The constant case is impossible for [Empty_Sign]. *)
  end.

Lemma forget_base_typing : forall {I A} {t : @SE_Base.b_tm Empty_Sign},
  @SE_Base.base_typing Empty_Sign I t A -> 
  S_Base.base_typing (forget_b_ty I) (forget_b_tm t) (forget_b_ty A).
Proof.
  intros I A t dt. induction dt; simpl.
  - apply S_Base.BT_Id.
  - eapply S_Base.BT_Comp; eauto.
  - apply S_Base.BT_Unit.
  - apply S_Base.BT_Pair; eauto.
  - apply S_Base.BT_Fst.
  - apply S_Base.BT_Snd.
  - destruct s.
Defined.

(** [CompPair] is derived from beta and eta rather than assumed. *)
Lemma S_Base_CompPair : forall A B C D f g h 
  (df : S_Base.base_typing B f C)
  (dg : S_Base.base_typing B g D)
  (dh : S_Base.base_typing A h B),
  S_Base.base_equiv A (S_Base.b_Prod C D) 
    (S_Base.b_comp (S_Base.b_pair f g) h) 
    (S_Base.b_pair (S_Base.b_comp f h) (S_Base.b_comp g h)).
Proof.
  intros A B C D f g h df dg dh.
  assert (dX : S_Base.base_typing A (S_Base.b_comp (S_Base.b_pair f g) h) (S_Base.b_Prod C D)).
  { eapply S_Base.BT_Comp. eapply S_Base.BT_Pair. exact df. exact dg. exact dh. }
  
  eapply S_Base.BE_Trans. 
  1: { 
    eapply S_Base.BE_Sym. 
    eapply S_Base.BE_EtaPair. 
    exact dX. 
  }
  
  eapply S_Base.BE_CongPair.
  -
    eapply S_Base.BE_Trans.
    + eapply S_Base.BE_Assoc.
      * exact dh.
      * eapply S_Base.BT_Pair. exact df. exact dg.
      * apply S_Base.BT_Fst.
    + eapply S_Base.BE_CongComp.
      * eapply S_Base.BE_BetaFst. exact df. exact dg.
      * eapply S_Base.BE_Refl. exact dh.
      
  -
    eapply S_Base.BE_Trans.
    + eapply S_Base.BE_Assoc.
      * exact dh.
      * eapply S_Base.BT_Pair. exact df. exact dg.
      * apply S_Base.BT_Snd.
    + eapply S_Base.BE_CongComp.
      * eapply S_Base.BE_BetaSnd. exact df. exact dg.
      * eapply S_Base.BE_Refl. exact dh.
Qed.

Lemma forget_base_equiv_core : forall I J f g df dg,
  @SE_Base.base_equiv Empty_Sign I J f g df dg -> 
  S_Base.base_equiv (forget_b_ty I) (forget_b_ty J) (forget_b_tm f) (forget_b_tm g).
Proof.
  intros I J f g df dg Heq.
  induction Heq; simpl.
  
  Ltac solve_typing :=
    match goal with
    | H : @SE_Base.base_typing Empty_Sign _ ?t _ |- S_Base.base_typing _ (forget_b_tm ?t) _ =>
        exact (forget_base_typing H)
    end.
    
  -
    eapply S_Base.BE_Refl. solve_typing.
    
  -
    eapply S_Base.BE_Sym. exact IHHeq.
    
  -
    eapply S_Base.BE_Trans. exact IHHeq1. exact IHHeq2.
    
  -
    eapply S_Base.BE_CongComp. exact IHHeq2. exact IHHeq1.
    
  -
    eapply S_Base.BE_CongPair. exact IHHeq1. exact IHHeq2.
    
  -
    eapply S_Base.BE_Assoc; solve_typing.
    
  -
    eapply S_Base.BE_IdL. solve_typing.
    
  -
    eapply S_Base.BE_IdR. solve_typing.
    
  -
    eapply S_Base.BE_BetaFst; solve_typing.
    
  -
    eapply S_Base.BE_BetaSnd; solve_typing.
    
  -
    eapply S_Base.BE_EtaPair. solve_typing.
    
  -
    eapply S_Base.BE_Terminal.
    + solve_typing.
    + apply S_Base.BT_Unit.
    
  -
    eapply S_Base_CompPair; solve_typing.
Qed.


(* Notations keep the underlying [hom_base] types transparent to unification. *)
Notation S_C   := (@S_Comp.Base_SetoidCategory nat).
Notation S_CC  := (@S_Comp.Base_CartesianCategory nat).
Notation S_TSC := (@S_Comp.Base_TwoSortCategory nat).
Notation S_GF  := (@S_Comp.Syntactic_GoodFibration nat).
Notation S_SGF := (@S_Comp.Syntactic_StrictGoodFibration nat).

Instance Expanded_BEM : @BaseSignatureModel Empty_Sign S_C S_CC S_TSC.
Proof.
  constructor. intros I A s. destruct s.
Defined.

(** Interpretation in the expanded model agrees with forgetting. *)

Lemma expand_interp_ty_term : forall A, 
  @interp_ty S_C S_CC S_TSC A = forget_b_ty A.
Proof.
  intros A. induction A; simpl; try reflexivity.
  f_equal; eauto.
Qed.

Lemma expand_interp_tm_term : forall I J f (df : @SE_Base.base_typing Empty_Sign I f J),
  S_Comp.b_tm_of _ _ (@interp_tm Empty_Sign S_C S_CC S_TSC Expanded_BEM I J f df) = forget_b_tm f.
Proof.
  intros I J f df.
  induction df; simpl; try reflexivity.
  - f_equal; eauto.
  - f_equal; eauto.
  - destruct s.
Qed.


Instance Expanded_CBM : @CoherentBaseModel Empty_Sign S_C S_CC S_TSC Expanded_BEM.
Proof.
  constructor. intros A B f d1 d2.
  
  pose proof (expand_interp_tm_term A B f d1) as H1.
  pose proof (expand_interp_tm_term A B f d2) as H2.
  
  (* Reduce the categorical wrappers to the inductive base equivalence. *)
  repeat red.
  
  rewrite H1. rewrite H2.
  
  rewrite (expand_interp_ty_term A).
  rewrite (expand_interp_ty_term B).
  
  eapply S_Base.BE_Refl.
  apply forget_base_typing. exact d1.
Defined.

(** Hyperdoctrine model expanded along the empty signature. *)

Instance Expanded_HM : @SE_Mod.HyperModel Empty_Sign S_C S_CC S_TSC S_GF S_SGF Expanded_BEM Expanded_CBM.
Proof.
  unshelve econstructor.
  -   intros p t I A dt.
    exists (S_Hyper.Ty_Atom p (forget_b_tm t)).
    pose proof (S_Hyper.WF_Atom (forget_b_ty I) p (forget_b_tm t) (forget_b_ty A) (forget_base_typing dt)) as Hwf.
    unfold S_Comp.syn_obj.
    rewrite (expand_interp_ty_term I).
    exact Hwf.
    
  -   intros p t I J A f df dt.
    apply S_Comp.syn_iso_from_eq. simpl. 
    
    unfold S_Comp.syn_hom, S_Comp.syn_obj.
    rewrite expand_interp_tm_term.
    
    reflexivity.
    
    -   intros p t1 t2 I A d1 d2 Heq.
    apply S_Comp.syn_iso_from_equiv. simpl. 
    
    rewrite (expand_interp_ty_term I).
    
    eapply S_Hyper.FEQ_Atom.
    
    + eapply forget_base_typing. exact d1.
    
    + apply forget_base_typing. exact d2.
    
    + eapply forget_base_equiv_core. exact Heq.
Defined.

(** Interpretation agreement and conservativity. *)

Lemma embed_forget_b_ty : forall A, forget_b_ty (embed_b_ty A) = A.
Proof. induction A; simpl; f_equal; auto. Qed.

Lemma embed_forget_b_tm : forall t, forget_b_tm (embed_b_tm t) = t.
Proof. induction t; simpl; f_equal; auto. Qed.

(** Embedded formulas interpret to their original formulas. *)
Lemma interpretation_agreement : forall I Phi (wf : S_Hyper.WellFormed I Phi),
  (@SE_Mod.interp_h_ty Empty_Sign S_C S_CC S_TSC S_GF S_SGF Expanded_BEM Expanded_CBM Expanded_HM
    (embed_b_ty I) (embed_ty Phi) (embed_wf I Phi wf) : S_Hyper.h_ty) = Phi.
Proof.
  intros I Phi wf.
  induction wf; simpl; try reflexivity.
  
  -   f_equal; auto.
  -   f_equal; auto.
  -   f_equal; auto.
  
  -
    f_equal. apply embed_forget_b_tm.
    
  -
    f_equal. 
    +
      unfold S_Comp.syn_obj. 
      rewrite expand_interp_ty_term. 
      apply embed_forget_b_ty.
    + exact IHwf.
    
  -
    f_equal. 
    +
      unfold S_Comp.syn_obj. 
      rewrite expand_interp_ty_term. 
      apply embed_forget_b_ty.
    + exact IHwf.
Qed.


(** The empty-signature extension is conservative. *)
Theorem simple_ext_is_conservative : forall (Phi : S_Hyper.h_ty) (wf : S_Hyper.WellFormed S_Base.b_Unit Phi),
  (exists (p_ext : @SE_Hyper.h_tm Empty_Sign), 
      inhabited (@SE_Hyper.h_derivation Empty_Sign SE_Base.b_Unit nil p_ext (embed_ty Phi))) ->
  (exists (p_simp : S_Hyper.h_tm), 
      inhabited (S_Hyper.h_derivation S_Base.b_Unit nil p_simp Phi)).
Proof.
  intros Phi wf [p_ext [D_ext]].
  
  pose proof (@SE_Mod.hyper_soundness_inhabited Empty_Sign S_C S_CC S_TSC S_GF S_SGF Expanded_BEM Expanded_CBM Expanded_HM
    _ _ _ _ D_ext (@SE_Hyper.WFC_nil Empty_Sign _) (embed_wf _ _ wf)) as H_sem.
    
  destruct H_sem as [p_simp D_simp].
  
  pose proof (interpretation_agreement S_Base.b_Unit Phi wf) as Heq_Phi.
  
  change (embed_b_ty S_Base.b_Unit) with SE_Base.b_Unit in Heq_Phi.
  
  assert (Heq_Ctx : (@SE_Mod.interp_h_ctx Empty_Sign S_C S_CC S_TSC S_GF S_SGF Expanded_BEM Expanded_CBM Expanded_HM 
      SE_Base.b_Unit nil (@SE_Hyper.WFC_nil Empty_Sign _) : S_Hyper.h_ty) = S_Hyper.Ty_Unit).
  { reflexivity. }
  
  rewrite Heq_Phi in D_simp.
  rewrite Heq_Ctx in D_simp.
  
  exists (S_Hyper.tm_app (S_Hyper.tm_lam S_Hyper.Ty_Unit p_simp) S_Hyper.tm_unit).
  
  constructor. 
  
  eapply S_Hyper.HD_App.
  - apply S_Hyper.HD_Lam. 
    exact D_simp.
  - apply S_Hyper.HD_Unit. apply S_Hyper.WFC_nil.
Qed.


(** Syntactic derivations lift through the embedding. *)

Definition embed_ctx (G : list S_Hyper.h_ty) : list (@SE_Hyper.h_ty Empty_Sign) :=
  map embed_ty G.

Lemma embed_ctx_In : forall Phi G,
  In Phi G -> In (embed_ty Phi) (embed_ctx G).
Proof.
  intros Phi G H. unfold embed_ctx. apply in_map; auto.
Qed.

Lemma embed_ctx_nth_error : forall G n Phi,
  nth_error G n = Some Phi ->
  nth_error (embed_ctx G) n = Some (embed_ty Phi).
Proof.
  induction G; intros n Phi H.
  - destruct n; simpl in H; discriminate.
  - destruct n; simpl in H; simpl.
    + injection H as ->. reflexivity.
    + apply IHG. exact H.
Qed.

Lemma embed_wf_ctx : forall I G,
  S_Hyper.wf_ctx I G -> @SE_Hyper.wf_ctx Empty_Sign (embed_b_ty I) (embed_ctx G).
Proof.
  intros I G w_ctx. induction w_ctx; simpl.
  -
    constructor.
  -
    constructor.
    +
      apply embed_wf. exact w.
    +
      exact IHw_ctx.
Qed.

Lemma embed_form_pullback : forall f Phi,
  embed_ty (S_Hyper.form_pullback f Phi) = 
  SE_Hyper.form_pullback (embed_b_tm f) (embed_ty Phi).
Proof.
  intros f Phi.
  
  (* Generalize [f] so induction remains valid under changed substitutions. *)
  generalize dependent f. 
  
  induction Phi; intros f; simpl; f_equal; auto.
Qed.

Lemma embed_ctx_map_pullback : forall f G,
  embed_ctx (map (S_Hyper.form_pullback f) G) = 
  map (SE_Hyper.form_pullback (embed_b_tm f)) (embed_ctx G).
Proof.
  intros f G. induction G; simpl; f_equal; auto.
  apply embed_form_pullback.
Qed.


Theorem embed_derivation : forall I G p Phi,
  S_Hyper.h_derivation I G p Phi ->
  { p_ext : @SE_Hyper.h_tm Empty_Sign & @SE_Hyper.h_derivation Empty_Sign (embed_b_ty I) (embed_ctx G) p_ext (embed_ty Phi) }.
Proof.
  intros I G p Phi D.
  induction D; simpl.
  
  all: repeat match goal with
       | H : { _ & _ } |- _ => destruct H as [?p_ext ?D_ext]
       end.
       
  all: try rewrite embed_form_pullback in *.
  all: try rewrite embed_ctx_map_pullback in *.
  
  all: try solve [
    eexists; econstructor; 
    eauto 10 using embed_wf, embed_b_typing, embed_wf_ctx
  ].
  
  - eexists (SE_Hyper.tm_var 0).
    eapply SE_Hyper.HD_Var0.
    + apply embed_wf_ctx; assumption.
    + apply embed_wf; assumption.
  
  - eexists (SE_Hyper.tm_var (S i)).
    eapply SE_Hyper.HD_VarS.
    + exact D_ext.
    + apply embed_wf; assumption.

  - eexists. eapply SE_Hyper.HD_All_Intro. apply embed_wf_ctx; eassumption. exact D_ext.
  
  - eexists. eapply SE_Hyper.HD_Ex_Intro. apply embed_wf; eassumption. apply embed_b_typing; eassumption. exact D_ext.
  
  - eexists. eapply SE_Hyper.HD_Ex_Elim. apply embed_wf; eassumption. exact D_ext1. exact D_ext2.
  
  - eexists. eapply SE_Hyper.HD_Ctx_Conv. exact D_ext. 
    eauto. eauto.
Qed.
