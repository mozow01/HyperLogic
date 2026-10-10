
Require Import List.
Import ListNotations.

Require Import HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.

Module EpsBase := HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Module FullBase := HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Module EpsHyper := HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.
Module FullHyper := HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.

Fixpoint embed_b_ty (A : EpsBase.b_ty) : FullBase.b_ty :=
  match A with
  | EpsBase.b_Unit => FullBase.b_Unit
  | EpsBase.b_S => FullBase.b_S
  | EpsBase.b_Prod A B => FullBase.b_Prod (embed_b_ty A) (embed_b_ty B)
  end.

Fixpoint project_b_ty (A : FullBase.b_ty) : EpsBase.b_ty :=
  match A with
  | FullBase.b_Unit => EpsBase.b_Unit
  | FullBase.b_S => EpsBase.b_S
  | FullBase.b_Prod A B => EpsBase.b_Prod (project_b_ty A) (project_b_ty B)
  end.

Fixpoint embed_b_tm {Sign Func : Type}
  (t : @EpsBase.b_tm Sign Func) : @FullBase.b_tm Sign Func :=
  match t with
  | EpsBase.b_id => FullBase.b_id
  | EpsBase.b_comp g f => FullBase.b_comp (embed_b_tm g) (embed_b_tm f)
  | EpsBase.b_unit => FullBase.b_unit
  | EpsBase.b_pair f g => FullBase.b_pair (embed_b_tm f) (embed_b_tm g)
  | EpsBase.b_fst => FullBase.b_fst
  | EpsBase.b_snd => FullBase.b_snd
  | EpsBase.b_const A s => FullBase.b_const (embed_b_ty A) s
  | EpsBase.b_func f => FullBase.b_func f
  end.

Fixpoint project_b_tm {Sign Func : Type}
  (t : @FullBase.b_tm Sign Func) : @EpsBase.b_tm Sign Func :=
  match t with
  | FullBase.b_id => EpsBase.b_id
  | FullBase.b_comp g f => EpsBase.b_comp (project_b_tm g) (project_b_tm f)
  | FullBase.b_unit => EpsBase.b_unit
  | FullBase.b_pair f g => EpsBase.b_pair (project_b_tm f) (project_b_tm g)
  | FullBase.b_fst => EpsBase.b_fst
  | FullBase.b_snd => EpsBase.b_snd
  | FullBase.b_const A s => EpsBase.b_const (project_b_ty A) s
  | FullBase.b_func f => EpsBase.b_func f
  end.

Fixpoint embed_h_ty {Sign Func Pred : Type}
  (Phi : @EpsHyper.h_ty Sign Func Pred) : @FullHyper.h_ty Sign Func Pred :=
  match Phi with
  | EpsHyper.Ty_Unit => FullHyper.Ty_Unit
  | EpsHyper.Ty_Void => FullHyper.Ty_Void
  | EpsHyper.Ty_Prod A B => FullHyper.Ty_Prod (embed_h_ty A) (embed_h_ty B)
  | EpsHyper.Ty_Sum A B => FullHyper.Ty_Sum (embed_h_ty A) (embed_h_ty B)
  | EpsHyper.Ty_Arrow A B => FullHyper.Ty_Arrow (embed_h_ty A) (embed_h_ty B)
  | EpsHyper.Ty_Atom p t => FullHyper.Ty_Atom p (embed_b_tm t)
  | EpsHyper.Ty_All A Body => FullHyper.Ty_All (embed_b_ty A) (embed_h_ty Body)
  end.

Definition embed_h_context {Sign Func Pred : Type}
  (G : @EpsHyper.h_context Sign Func Pred) : @FullHyper.h_context Sign Func Pred :=
  map embed_h_ty G.

Fixpoint project_h_ty {Sign Func Pred : Type}
  (Phi : @FullHyper.h_ty Sign Func Pred) : option (@EpsHyper.h_ty Sign Func Pred) :=
  match Phi with
  | FullHyper.Ty_Unit => Some EpsHyper.Ty_Unit
  | FullHyper.Ty_Void => Some EpsHyper.Ty_Void
  | FullHyper.Ty_Prod A B =>
      match project_h_ty A, project_h_ty B with
      | Some A', Some B' => Some (EpsHyper.Ty_Prod A' B')
      | _, _ => None
      end
  | FullHyper.Ty_Sum A B =>
      match project_h_ty A, project_h_ty B with
      | Some A', Some B' => Some (EpsHyper.Ty_Sum A' B')
      | _, _ => None
      end
  | FullHyper.Ty_Arrow A B =>
      match project_h_ty A, project_h_ty B with
      | Some A', Some B' => Some (EpsHyper.Ty_Arrow A' B')
      | _, _ => None
      end
  | FullHyper.Ty_Atom p t => Some (EpsHyper.Ty_Atom p (project_b_tm t))
  | FullHyper.Ty_All A Body =>
      match project_h_ty Body with
      | Some Body' => Some (EpsHyper.Ty_All (project_b_ty A) Body')
      | None => None
      end
  | FullHyper.Ty_Ex _ _ => None
  end.

Fixpoint project_h_context {Sign Func Pred : Type}
  (G : @FullHyper.h_context Sign Func Pred) : option (@EpsHyper.h_context Sign Func Pred) :=
  match G with
  | [] => Some []
  | Phi :: G' =>
      match project_h_ty Phi, project_h_context G' with
      | Some Phi', Some G'' => Some (Phi' :: G'')
      | _, _ => None
      end
  end.

Fixpoint embed_h_tm {Sign Func Pred : Type}
  (p : @EpsHyper.h_tm Sign Func Pred) : @FullHyper.h_tm Sign Func Pred :=
  match p with
  | EpsHyper.tm_unit => FullHyper.tm_unit
  | EpsHyper.tm_var i => FullHyper.tm_var i
  | EpsHyper.tm_lam Phi p' => FullHyper.tm_lam (embed_h_ty Phi) (embed_h_tm p')
  | EpsHyper.tm_app p1 p2 => FullHyper.tm_app (embed_h_tm p1) (embed_h_tm p2)
  | EpsHyper.tm_pair p1 p2 => FullHyper.tm_pair (embed_h_tm p1) (embed_h_tm p2)
  | EpsHyper.tm_fst p' => FullHyper.tm_fst (embed_h_tm p')
  | EpsHyper.tm_snd p' => FullHyper.tm_snd (embed_h_tm p')
  | EpsHyper.tm_inl Psi p' => FullHyper.tm_inl (embed_h_ty Psi) (embed_h_tm p')
  | EpsHyper.tm_inr Phi p' => FullHyper.tm_inr (embed_h_ty Phi) (embed_h_tm p')
  | EpsHyper.tm_case p' p1 p2 => FullHyper.tm_case (embed_h_tm p') (embed_h_tm p1) (embed_h_tm p2)
  | EpsHyper.tm_absurd Phi p' => FullHyper.tm_absurd (embed_h_ty Phi) (embed_h_tm p')
  | EpsHyper.tm_all_intro p' => FullHyper.tm_all_intro (embed_h_tm p')
  | EpsHyper.tm_all_elim p' t => FullHyper.tm_all_elim (embed_h_tm p') (embed_b_tm t)
  | EpsHyper.tm_eps_intro t p' => FullHyper.tm_eps_intro (embed_b_tm t) (embed_h_tm p')
  | EpsHyper.tm_eps_elim p1 p2 => FullHyper.tm_eps_elim (embed_h_tm p1) (embed_h_tm p2)
  end.

Fixpoint project_h_tm {Sign Func Pred : Type}
  (p : @FullHyper.h_tm Sign Func Pred) : option (@EpsHyper.h_tm Sign Func Pred) :=
  match p with
  | FullHyper.tm_unit => Some EpsHyper.tm_unit
  | FullHyper.tm_var i => Some (EpsHyper.tm_var i)
  | FullHyper.tm_lam Phi p' =>
      match project_h_ty Phi, project_h_tm p' with
      | Some Phi', Some p'' => Some (EpsHyper.tm_lam Phi' p'')
      | _, _ => None
      end
  | FullHyper.tm_app p1 p2 =>
      match project_h_tm p1, project_h_tm p2 with
      | Some p1', Some p2' => Some (EpsHyper.tm_app p1' p2')
      | _, _ => None
      end
  | FullHyper.tm_pair p1 p2 =>
      match project_h_tm p1, project_h_tm p2 with
      | Some p1', Some p2' => Some (EpsHyper.tm_pair p1' p2')
      | _, _ => None
      end
  | FullHyper.tm_fst p' =>
      match project_h_tm p' with
      | Some p'' => Some (EpsHyper.tm_fst p'')
      | None => None
      end
  | FullHyper.tm_snd p' =>
      match project_h_tm p' with
      | Some p'' => Some (EpsHyper.tm_snd p'')
      | None => None
      end
  | FullHyper.tm_inl Psi p' =>
      match project_h_ty Psi, project_h_tm p' with
      | Some Psi', Some p'' => Some (EpsHyper.tm_inl Psi' p'')
      | _, _ => None
      end
  | FullHyper.tm_inr Phi p' =>
      match project_h_ty Phi, project_h_tm p' with
      | Some Phi', Some p'' => Some (EpsHyper.tm_inr Phi' p'')
      | _, _ => None
      end
  | FullHyper.tm_case p' p1 p2 =>
      match project_h_tm p', project_h_tm p1, project_h_tm p2 with
      | Some p'', Some p1', Some p2' => Some (EpsHyper.tm_case p'' p1' p2')
      | _, _, _ => None
      end
  | FullHyper.tm_absurd Phi p' =>
      match project_h_ty Phi, project_h_tm p' with
      | Some Phi', Some p'' => Some (EpsHyper.tm_absurd Phi' p'')
      | _, _ => None
      end
  | FullHyper.tm_all_intro p' =>
      match project_h_tm p' with
      | Some p'' => Some (EpsHyper.tm_all_intro p'')
      | None => None
      end
  | FullHyper.tm_all_elim p' t =>
      match project_h_tm p' with
      | Some p'' => Some (EpsHyper.tm_all_elim p'' (project_b_tm t))
      | None => None
      end
  | FullHyper.tm_ex_intro _ _ => None
  | FullHyper.tm_ex_elim _ _ => None
  | FullHyper.tm_eps_intro t p' =>
      match project_h_tm p' with
      | Some p'' => Some (EpsHyper.tm_eps_intro (project_b_tm t) p'')
      | None => None
      end
  | FullHyper.tm_eps_elim p1 p2 =>
      match project_h_tm p1, project_h_tm p2 with
      | Some p1', Some p2' => Some (EpsHyper.tm_eps_elim p1' p2')
      | _, _ => None
      end
  end.

Lemma project_embed_b_ty :
  forall A, project_b_ty (embed_b_ty A) = A.
Proof.
  induction A; simpl; congruence.
Qed.

Lemma project_embed_b_tm :
  forall {Sign Func : Type} (t : @EpsBase.b_tm Sign Func),
    project_b_tm (embed_b_tm t) = t.
Proof.
  induction t; simpl; try reflexivity.
  all: repeat match goal with
  | IH : project_b_tm (embed_b_tm ?u) = ?u |- context [project_b_tm (embed_b_tm ?u)] =>
      rewrite IH
  | |- context [project_b_ty (embed_b_ty ?A)] =>
      rewrite (project_embed_b_ty A)
  end.
  all: reflexivity.
Qed.

Lemma project_embed_h_ty :
  forall {Sign Func Pred : Type} (Phi : @EpsHyper.h_ty Sign Func Pred),
    project_h_ty (embed_h_ty Phi) = Some Phi.
Proof.
  induction Phi; simpl; try reflexivity.
  all: repeat match goal with
  | IH : project_h_ty (embed_h_ty ?A) = Some ?A |- context [project_h_ty (embed_h_ty ?A)] =>
      rewrite IH
  | |- context [project_b_tm (embed_b_tm ?t)] =>
      rewrite (project_embed_b_tm t)
  | |- context [project_b_ty (embed_b_ty ?A)] =>
      rewrite (project_embed_b_ty A)
  end.
  all: reflexivity.
Qed.

Lemma project_embed_h_context :
  forall {Sign Func Pred : Type} (G : @EpsHyper.h_context Sign Func Pred),
    project_h_context (embed_h_context G) = Some G.
Proof.
  induction G as [|Phi G IH]; simpl.
  - reflexivity.
  - rewrite project_embed_h_ty, IH. reflexivity.
Qed.

Lemma project_embed_h_tm :
  forall {Sign Func Pred : Type} (p : @EpsHyper.h_tm Sign Func Pred),
    project_h_tm (embed_h_tm p) = Some p.
Proof.
  induction p; simpl; try reflexivity.
  all: repeat match goal with
  | IH : project_h_tm (embed_h_tm ?q) = Some ?q |- context [project_h_tm (embed_h_tm ?q)] =>
      rewrite IH
  | IH : project_h_ty (embed_h_ty ?A) = Some ?A |- context [project_h_ty (embed_h_ty ?A)] =>
      rewrite IH
  | |- context [project_h_ty (embed_h_ty ?A)] =>
      rewrite (project_embed_h_ty A)
  | |- context [project_embed_b_tm ?t] =>
      rewrite (project_embed_b_tm t)
  | |- context [project_b_tm (embed_b_tm ?t)] =>
      rewrite (project_embed_b_tm t)
  end.
  all: reflexivity.
Qed.

Class FunctionSignatureCompat {Func : Type}
  `{HFuncEps : EpsBase.FunctionSignature Func}
  `{HFuncFull : FullBase.FunctionSignature Func} : Prop := {
  func_dom_compat :
    forall f, FullBase.func_dom f = embed_b_ty (EpsBase.func_dom f);
  func_cod_compat :
    forall f, FullBase.func_cod f = embed_b_ty (EpsBase.func_cod f)
}.

Class PredicateSignatureCompat {Pred : Type}
  `{HPredEps : EpsHyper.PredicateSignature Pred}
  `{HPredFull : FullHyper.PredicateSignature Pred} : Prop := {
  pred_dom_compat :
    forall p, FullHyper.pred_dom p = embed_b_ty (EpsHyper.pred_dom p)
}.

Class SkolemMappingCompat {Sign Func Pred : Type}
  `{HSkolemEps : EpsHyper.SkolemMapping Sign Func Pred}
  `{HSkolemFull : FullHyper.SkolemMapping Sign Func Pred} : Prop := {
  skolem_index_compat :
    forall (A : EpsBase.b_ty) (Phi : @EpsHyper.h_ty Sign Func Pred),
      FullHyper.skolem_index (embed_b_ty A) (embed_h_ty Phi) =
      EpsHyper.skolem_index A Phi
}.

Section ForwardTranslation.

Context {Sign Func Pred : Type}.

Context `{HFuncEps : EpsBase.FunctionSignature Func}.
Context `{HFuncFull : FullBase.FunctionSignature Func}.
Context {HFuncCompat : @FunctionSignatureCompat Func HFuncEps HFuncFull}.

Context `{HPredEps : EpsHyper.PredicateSignature Pred}.
Context `{HPredFull : FullHyper.PredicateSignature Pred}.
Context {HPredCompat : @PredicateSignatureCompat Pred HPredEps HPredFull}.

Context `{HSkolemEps : EpsHyper.SkolemMapping Sign Func Pred}.
Context `{HSkolemFull : FullHyper.SkolemMapping Sign Func Pred}.
Context {HSkolemCompat : @SkolemMappingCompat Sign Func Pred HSkolemEps HSkolemFull}.

Lemma embed_b_subst_ext :
  forall (f : @EpsBase.b_tm Sign Func),
    embed_b_tm (EpsHyper.b_subst_ext f) =
    FullHyper.b_subst_ext (embed_b_tm f).
Proof.
  reflexivity.
Qed.

Lemma embed_form_subst :
  forall (f : @EpsBase.b_tm Sign Func) (Phi : @EpsHyper.h_ty Sign Func Pred),
    embed_h_ty (EpsHyper.form_subst f Phi) =
    FullHyper.form_subst (embed_b_tm f) (embed_h_ty Phi).
Proof.
  intros f Phi.
  revert f.
  induction Phi; intros f; simpl;
    try rewrite IHPhi1;
    try rewrite IHPhi2;
    try rewrite IHPhi;
    try rewrite embed_b_subst_ext;
    reflexivity.
Qed.

Lemma embed_ctx_subst :
  forall (f : @EpsBase.b_tm Sign Func) (G : @EpsHyper.h_context Sign Func Pred),
    embed_h_context (EpsHyper.ctx_subst f G) =
    FullHyper.ctx_subst (embed_b_tm f) (embed_h_context G).
Proof.
  intros f G.
  induction G as [|Phi G IH]; simpl.
  - reflexivity.
  - rewrite embed_form_subst, IH. reflexivity.
Qed.

Lemma embed_epsilon_const :
  forall (A : EpsBase.b_ty) (Phi : @EpsHyper.h_ty Sign Func Pred),
    embed_b_tm (@EpsBase.b_const Sign Func A (EpsHyper.skolem_index A Phi)) =
    FullBase.b_const (embed_b_ty A)
      (FullHyper.skolem_index (embed_b_ty A) (embed_h_ty Phi)).
Proof.
  intros A Phi.
  simpl.
  rewrite skolem_index_compat.
  reflexivity.
Qed.

Lemma embed_eps_instantiation :
  forall (A : EpsBase.b_ty) (Phi : @EpsHyper.h_ty Sign Func Pred),
    embed_h_ty
      (EpsHyper.form_subst
        (EpsBase.b_pair EpsBase.b_id
          (EpsBase.b_const A (EpsHyper.skolem_index A Phi))) Phi) =
    FullHyper.form_subst
      (FullBase.b_pair FullBase.b_id
        (FullBase.b_const (embed_b_ty A)
          (FullHyper.skolem_index (embed_b_ty A) (embed_h_ty Phi))))
      (embed_h_ty Phi).
Proof.
  intros A Phi.
  rewrite embed_form_subst.
  simpl.
  rewrite skolem_index_compat.
  reflexivity.
Qed.

Lemma embed_base_typing :
  forall {I : EpsBase.b_ty} {t : @EpsBase.b_tm Sign Func} {A : EpsBase.b_ty},
    @EpsBase.base_typing Sign Func HFuncEps I t A ->
    @FullBase.base_typing Sign Func HFuncFull
      (embed_b_ty I) (embed_b_tm t) (embed_b_ty A).
Proof.
  intros I t A H.
  induction H; simpl.
  - apply FullBase.BT_Id.
  - eapply FullBase.BT_Comp.
    + exact IHbase_typing1.
    + exact IHbase_typing2.
  - apply FullBase.BT_Unit.
  - apply FullBase.BT_Pair.
    + exact IHbase_typing1.
    + exact IHbase_typing2.
  - apply FullBase.BT_Fst.
  - apply FullBase.BT_Snd.
  - apply FullBase.BT_Const.
  - rewrite <- func_dom_compat.
    rewrite <- func_cod_compat.
    apply FullBase.BT_Func.
Defined.

Lemma embed_base_equiv :
  forall {I A : EpsBase.b_ty} {f g : @EpsBase.b_tm Sign Func}
    {df : @EpsBase.base_typing Sign Func HFuncEps I f A}
    {dg : @EpsBase.base_typing Sign Func HFuncEps I g A},
    @EpsBase.base_equiv Sign Func HFuncEps I A f g df dg ->
    @FullBase.base_equiv Sign Func HFuncFull
      (embed_b_ty I) (embed_b_ty A) (embed_b_tm f) (embed_b_tm g)
      (embed_base_typing df) (embed_base_typing dg).
Proof.
  intros I A f g df dg H.
  induction H; simpl.
  - apply FullBase.BE_Refl.
  - apply FullBase.BE_Sym.
    exact IHbase_equiv.
  - eapply FullBase.BE_Trans.
    + exact IHbase_equiv1.
    + exact IHbase_equiv2.
  - apply FullBase.BE_CongComp.
    + exact IHbase_equiv1.
    + exact IHbase_equiv2.
  - apply FullBase.BE_CongPair.
    + exact IHbase_equiv1.
    + exact IHbase_equiv2.
  - apply FullBase.BE_Assoc.
  - apply FullBase.BE_IdL.
  - apply FullBase.BE_IdR.
  - apply FullBase.BE_BetaFst.
  - apply FullBase.BE_BetaSnd.
  - apply FullBase.BE_EtaPair.
  - apply FullBase.BE_EtaUnit.
  - apply FullBase.BE_CompPair.
Defined.

Definition cast_base_typing
  {I A B : FullBase.b_ty} {t : @FullBase.b_tm Sign Func}
  (e : B = A)
  (d : @FullBase.base_typing Sign Func HFuncFull I t A)
  : @FullBase.base_typing Sign Func HFuncFull I t B.
Proof.
  subst.
  exact d.
Defined.

Definition cast_base_equiv
  {I A B : FullBase.b_ty} {f g : @FullBase.b_tm Sign Func}
  {df1 : @FullBase.base_typing Sign Func HFuncFull I f A}
  {df2 : @FullBase.base_typing Sign Func HFuncFull I g A}
  (e : B = A)
  (H : @FullBase.base_equiv Sign Func HFuncFull I A f g df1 df2)
  : @FullBase.base_equiv Sign Func HFuncFull I B f g
      (cast_base_typing e df1) (cast_base_typing e df2).
Proof.
  subst.
  exact H.
Defined.

Lemma embed_wellformed :
  forall {I : EpsBase.b_ty} {Phi : @EpsHyper.h_ty Sign Func Pred},
    @EpsHyper.WellFormed Sign Func Pred HFuncEps HPredEps I Phi ->
    @FullHyper.WellFormed Sign Func Pred HFuncFull HPredFull (embed_b_ty I) (embed_h_ty Phi).
Proof.
  intros I Phi H.
  induction H; simpl.
  - apply FullHyper.WF_Unit.
  - apply FullHyper.WF_Void.
  - apply FullHyper.WF_Prod; assumption.
  - apply FullHyper.WF_Sum; assumption.
  - apply FullHyper.WF_Arrow; assumption.
  - eapply FullHyper.WF_Atom.
    replace (FullHyper.pred_dom p) with (embed_b_ty (EpsHyper.pred_dom p)).
    2:{ symmetry. apply pred_dom_compat. }
    exact (embed_base_typing b).
  - apply FullHyper.WF_All.
    exact IHWellFormed.
Defined.

Lemma embed_all_wellformed :
  forall {I : EpsBase.b_ty} {G : @EpsHyper.h_context Sign Func Pred},
    @EpsHyper.All_WellFormed Sign Func Pred HFuncEps HPredEps I G ->
    @FullHyper.All_WellFormed Sign Func Pred HFuncFull HPredFull (embed_b_ty I) (embed_h_context G).
Proof.
  intros I G H.
  induction H; simpl.
  - apply FullHyper.AWF_Nil.
  - apply FullHyper.AWF_Cons.
    + apply embed_wellformed. eassumption.
    + exact IHAll_WellFormed.
Defined.

Lemma embed_form_equiv :
  forall {I : EpsBase.b_ty} {Phi Psi : @EpsHyper.h_ty Sign Func Pred},
    @EpsHyper.form_equiv Sign Func Pred HFuncEps HPredEps HSkolemEps I Phi Psi ->
    @FullHyper.form_equiv Sign Func Pred HFuncFull HPredFull HSkolemFull
      (embed_b_ty I) (embed_h_ty Phi) (embed_h_ty Psi).
Proof.
  intros I Phi Psi H.
  induction H; simpl.
  - set (d1' := cast_base_typing (pred_dom_compat p) (embed_base_typing d1)).
    set (d2' := cast_base_typing (pred_dom_compat p) (embed_base_typing d2)).
    refine (@FullHyper.FE_Atom Sign Func Pred
      HFuncFull HPredFull HSkolemFull (embed_b_ty I) p
      (embed_b_tm t1) (embed_b_tm t2) d1' d2'
      (cast_base_equiv (pred_dom_compat p) (embed_base_equiv b))).
  - apply FullHyper.FE_Refl.
    apply embed_wellformed.
    eassumption.
  - apply FullHyper.FE_Sym.
    exact IHform_equiv.
  - eapply FullHyper.FE_Trans.
    + exact IHform_equiv1.
    + exact IHform_equiv2.
  - apply FullHyper.FE_Prod; assumption.
  - apply FullHyper.FE_Sum; assumption.
  - apply FullHyper.FE_Arrow; assumption.
  - apply FullHyper.FE_All.
    exact IHform_equiv.
  - rewrite embed_eps_instantiation.
    rewrite embed_eps_instantiation.
    apply FullHyper.FE_Eps_Functorial.
    exact IHform_equiv.
  - rewrite embed_form_subst.
    apply FullHyper.FE_Pullback_Id.
    apply embed_wellformed.
    exact w.
  - repeat rewrite embed_form_subst.
    refine (@FullHyper.FE_Pullback_Comp Sign Func Pred
      HFuncFull HPredFull HSkolemFull (embed_b_ty I) (embed_b_ty J) (embed_b_ty K)
      (embed_b_tm f) (embed_b_tm g) (embed_h_ty Phi)
      (embed_base_typing df) (embed_base_typing dg) _).
    apply embed_wellformed. eassumption.
  - repeat rewrite embed_form_subst.
    refine (@FullHyper.FE_Pullback_Cong Sign Func Pred
      HFuncFull HPredFull HSkolemFull (embed_b_ty I) (embed_b_ty J)
      (embed_b_tm f) (embed_b_tm g) (embed_h_ty Phi)
      (embed_base_typing df) (embed_base_typing dg)
      (embed_base_equiv b) _).
    apply embed_wellformed. eassumption.
  - repeat rewrite embed_eps_instantiation.
    repeat rewrite embed_form_subst.
    repeat rewrite embed_b_subst_ext.
    simpl.
    repeat rewrite <- skolem_index_compat.
    refine (@FullHyper.FE_Eps_BC Sign Func Pred
      HFuncFull HPredFull HSkolemFull (embed_b_ty I) (embed_b_ty J) (embed_b_ty A)
      (embed_b_tm t) (embed_base_typing dt) (embed_h_ty Phi) _).
    exact (embed_wellformed w).
Defined.

Lemma embed_ctx_equiv :
  forall {I : EpsBase.b_ty} {G1 G2 : @EpsHyper.h_context Sign Func Pred},
    @EpsHyper.ctx_equiv Sign Func Pred HFuncEps HPredEps HSkolemEps I G1 G2 ->
    @FullHyper.ctx_equiv Sign Func Pred HFuncFull HPredFull HSkolemFull
      (embed_b_ty I) (embed_h_context G1) (embed_h_context G2).
Proof.
  intros I G1 G2 H.
  induction H; simpl.
  - apply FullHyper.CEq_Nil.
  - apply FullHyper.CEq_Cons.
    + apply embed_form_equiv. exact f.
    + exact IHctx_equiv.
Defined.

Lemma embed_h_derivation :
  forall {I : EpsBase.b_ty} {G : @EpsHyper.h_context Sign Func Pred}
    {p : @EpsHyper.h_tm Sign Func Pred} {Phi : @EpsHyper.h_ty Sign Func Pred},
    @EpsHyper.h_derivation Sign Func Pred HFuncEps HPredEps HSkolemEps I G p Phi ->
    @FullHyper.h_derivation Sign Func Pred HFuncFull HPredFull HSkolemFull
      (embed_b_ty I) (embed_h_context G) (embed_h_tm p) (embed_h_ty Phi).
Proof.
  intros I G p Phi H.
  induction H; simpl.
  - apply FullHyper.HD_Var0.
    exact (embed_all_wellformed a).
  - apply FullHyper.HD_VarS.
    + apply embed_wellformed. eassumption.
    + exact IHh_derivation.
  - apply FullHyper.HD_Unit.
    exact (embed_all_wellformed a).
  - eapply FullHyper.HD_Conv.
    + exact IHh_derivation.
    + exact (embed_form_equiv f).
  - eapply FullHyper.HD_Ctx_Conv.
    + exact (embed_ctx_equiv c).
    + exact IHh_derivation.
  - apply FullHyper.HD_Lam.
    exact IHh_derivation.
  - eapply FullHyper.HD_App.
    + exact IHh_derivation1.
    + exact IHh_derivation2.
  - apply FullHyper.HD_Pair; assumption.
  - eapply FullHyper.HD_Fst.
    exact IHh_derivation.
  - eapply FullHyper.HD_Snd.
    exact IHh_derivation.
  - apply FullHyper.HD_Inl.
    + apply embed_wellformed. eassumption.
    + exact IHh_derivation.
  - apply FullHyper.HD_Inr.
    + apply embed_wellformed. eassumption.
    + exact IHh_derivation.
  - eapply FullHyper.HD_Case.
    + exact IHh_derivation1.
    + exact IHh_derivation2.
    + exact IHh_derivation3.
  - apply FullHyper.HD_Absurd.
    + apply embed_wellformed. eassumption.
    + exact IHh_derivation.
  - apply FullHyper.HD_All_Intro.
    change (@FullHyper.h_derivation Sign Func Pred
      HFuncFull HPredFull HSkolemFull
      (FullBase.b_Prod (embed_b_ty I) (embed_b_ty A))
      (FullHyper.ctx_subst FullBase.b_fst (embed_h_context G))
      (embed_h_tm p) (embed_h_ty Phi)).
    replace (FullHyper.ctx_subst FullBase.b_fst (embed_h_context G))
      with (embed_h_context (EpsHyper.ctx_subst EpsBase.b_fst G)).
    2:{ exact (embed_ctx_subst EpsBase.b_fst G). }
    exact IHh_derivation.
  - rewrite embed_form_subst.
    eapply FullHyper.HD_All_Elim.
    + exact IHh_derivation.
    + exact (embed_base_typing b).
  - rewrite embed_eps_instantiation.
    eapply FullHyper.HD_Eps_Intro.
    + exact (embed_base_typing b).
    + change (@FullHyper.h_derivation Sign Func Pred
        HFuncFull HPredFull HSkolemFull
        (embed_b_ty I) (embed_h_context G) (embed_h_tm p)
        (FullHyper.form_subst
          (FullBase.b_pair FullBase.b_id (embed_b_tm f))
          (embed_h_ty Phi))).
      replace
        (FullHyper.form_subst
          (FullBase.b_pair FullBase.b_id (embed_b_tm f))
          (embed_h_ty Phi))
        with (embed_h_ty
          (EpsHyper.form_subst
            (EpsBase.b_pair EpsBase.b_id f) Phi)).
      2:{ exact (embed_form_subst (EpsBase.b_pair EpsBase.b_id f) Phi). }
      exact IHh_derivation.
  - eapply FullHyper.HD_Eps_Elim.
    + rewrite <- embed_eps_instantiation.
      exact IHh_derivation1.
    + change (@FullHyper.h_derivation Sign Func Pred
        HFuncFull HPredFull HSkolemFull
        (FullBase.b_Prod (embed_b_ty I) (embed_b_ty A))
        (embed_h_ty Phi :: FullHyper.ctx_subst FullBase.b_fst (embed_h_context G))
        (embed_h_tm p2)
        (FullHyper.form_subst FullBase.b_fst (embed_h_ty Chi))).
      replace (FullHyper.ctx_subst FullBase.b_fst (embed_h_context G))
        with (embed_h_context (EpsHyper.ctx_subst EpsBase.b_fst G)).
      2:{ exact (embed_ctx_subst EpsBase.b_fst G). }
      replace (FullHyper.form_subst FullBase.b_fst (embed_h_ty Chi))
        with (embed_h_ty (EpsHyper.form_subst EpsBase.b_fst Chi)).
      2:{ exact (embed_form_subst EpsBase.b_fst Chi). }
      exact IHh_derivation2.
Defined.

Theorem epsilon_derivation_to_epsilonfull :
  forall (I : EpsBase.b_ty) (G : @EpsHyper.h_context Sign Func Pred)
    (p : @EpsHyper.h_tm Sign Func Pred) (Phi : @EpsHyper.h_ty Sign Func Pred),
    @EpsHyper.h_derivation Sign Func Pred HFuncEps HPredEps HSkolemEps I G p Phi ->
    @FullHyper.h_derivation Sign Func Pred HFuncFull HPredFull HSkolemFull
      (embed_b_ty I) (embed_h_context G) (embed_h_tm p) (embed_h_ty Phi).
Proof.
  intros I G p Phi H.
  exact (embed_h_derivation H).
Qed.

End ForwardTranslation.
