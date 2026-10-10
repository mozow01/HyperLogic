(** Canonical comparison between epsilon-only and epsilon-exists syntax. *)

Require Import List.
Import ListNotations.

Require Import HyperLogic.Logic.Hyper.Epsilon.Canonical_Skolem.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Canonical_Skolem.
Require Import HyperLogic.Logic.Metatheory.EpsilonFull_Translation.
Require Import HyperLogic.Logic.Metatheory.EpsilonFull_Erasure.

Module EpsCanonical :=
  HyperLogic.Logic.Hyper.Epsilon.Canonical_Skolem.CanonicalEpsilon.
Module FullCanonical :=
  HyperLogic.Logic.Hyper.EpsilonFull.Canonical_Skolem.CanonicalEpsilonFull.

Module CanonicalEpsilonComparison.

Section SyntaxMaps.

Context {Func Pred : Type}.

Definition EpsilonSign : Type := EpsCanonical.EpsilonLabel Func Pred.
Definition EpsilonFullSign : Type := FullCanonical.EpsilonLabel Func Pred.

Fixpoint embed_label (s : EpsilonSign) : EpsilonFullSign :=
  match s with
  | EpsCanonical.epsilon_label A Phi =>
      FullCanonical.epsilon_label (embed_b_ty A)
        (let fix embed_formula
          (X : @EpsHyper.h_ty EpsilonSign Func Pred)
          : @FullHyper.h_ty EpsilonFullSign Func Pred :=
          match X with
          | EpsHyper.Ty_Unit => FullHyper.Ty_Unit
          | EpsHyper.Ty_Void => FullHyper.Ty_Void
          | EpsHyper.Ty_Prod X Y =>
              FullHyper.Ty_Prod (embed_formula X) (embed_formula Y)
          | EpsHyper.Ty_Sum X Y =>
              FullHyper.Ty_Sum (embed_formula X) (embed_formula Y)
          | EpsHyper.Ty_Arrow X Y =>
              FullHyper.Ty_Arrow (embed_formula X) (embed_formula Y)
          | EpsHyper.Ty_Atom p t =>
              FullHyper.Ty_Atom p
                (let fix embed_term
                  (u : @EpsBase.b_tm EpsilonSign Func)
                  : @FullBase.b_tm EpsilonFullSign Func :=
                  match u with
                  | EpsBase.b_id => FullBase.b_id
                  | EpsBase.b_comp v w =>
                      FullBase.b_comp (embed_term v) (embed_term w)
                  | EpsBase.b_unit => FullBase.b_unit
                  | EpsBase.b_pair v w =>
                      FullBase.b_pair (embed_term v) (embed_term w)
                  | EpsBase.b_fst => FullBase.b_fst
                  | EpsBase.b_snd => FullBase.b_snd
                  | EpsBase.b_const B r =>
                      FullBase.b_const (embed_b_ty B) (embed_label r)
                  | EpsBase.b_func f => FullBase.b_func f
                  end
                in embed_term t)
          | EpsHyper.Ty_All B X =>
              FullHyper.Ty_All (embed_b_ty B) (embed_formula X)
          end
        in embed_formula Phi)
  end.

Fixpoint embed_b_tm
  (t : @EpsBase.b_tm EpsilonSign Func)
  : @FullBase.b_tm EpsilonFullSign Func :=
  match t with
  | EpsBase.b_id => FullBase.b_id
  | EpsBase.b_comp u v => FullBase.b_comp (embed_b_tm u) (embed_b_tm v)
  | EpsBase.b_unit => FullBase.b_unit
  | EpsBase.b_pair u v => FullBase.b_pair (embed_b_tm u) (embed_b_tm v)
  | EpsBase.b_fst => FullBase.b_fst
  | EpsBase.b_snd => FullBase.b_snd
  | EpsBase.b_const A s => FullBase.b_const (embed_b_ty A) (embed_label s)
  | EpsBase.b_func f => FullBase.b_func f
  end.

Fixpoint embed_h_ty
  (Phi : @EpsHyper.h_ty EpsilonSign Func Pred)
  : @FullHyper.h_ty EpsilonFullSign Func Pred :=
  match Phi with
  | EpsHyper.Ty_Unit => FullHyper.Ty_Unit
  | EpsHyper.Ty_Void => FullHyper.Ty_Void
  | EpsHyper.Ty_Prod X Y => FullHyper.Ty_Prod (embed_h_ty X) (embed_h_ty Y)
  | EpsHyper.Ty_Sum X Y => FullHyper.Ty_Sum (embed_h_ty X) (embed_h_ty Y)
  | EpsHyper.Ty_Arrow X Y => FullHyper.Ty_Arrow (embed_h_ty X) (embed_h_ty Y)
  | EpsHyper.Ty_Atom p t => FullHyper.Ty_Atom p (embed_b_tm t)
  | EpsHyper.Ty_All A X => FullHyper.Ty_All (embed_b_ty A) (embed_h_ty X)
  end.

Definition embed_h_context
  (G : @EpsHyper.h_context EpsilonSign Func Pred)
  : @FullHyper.h_context EpsilonFullSign Func Pred :=
  map embed_h_ty G.

Fixpoint embed_h_tm
  (p : @EpsHyper.h_tm EpsilonSign Func Pred)
  : @FullHyper.h_tm EpsilonFullSign Func Pred :=
  match p with
  | EpsHyper.tm_unit => FullHyper.tm_unit
  | EpsHyper.tm_var i => FullHyper.tm_var i
  | EpsHyper.tm_lam Phi q => FullHyper.tm_lam (embed_h_ty Phi) (embed_h_tm q)
  | EpsHyper.tm_app q r => FullHyper.tm_app (embed_h_tm q) (embed_h_tm r)
  | EpsHyper.tm_pair q r => FullHyper.tm_pair (embed_h_tm q) (embed_h_tm r)
  | EpsHyper.tm_fst q => FullHyper.tm_fst (embed_h_tm q)
  | EpsHyper.tm_snd q => FullHyper.tm_snd (embed_h_tm q)
  | EpsHyper.tm_inl Phi q => FullHyper.tm_inl (embed_h_ty Phi) (embed_h_tm q)
  | EpsHyper.tm_inr Phi q => FullHyper.tm_inr (embed_h_ty Phi) (embed_h_tm q)
  | EpsHyper.tm_case q r u =>
      FullHyper.tm_case (embed_h_tm q) (embed_h_tm r) (embed_h_tm u)
  | EpsHyper.tm_absurd Phi q =>
      FullHyper.tm_absurd (embed_h_ty Phi) (embed_h_tm q)
  | EpsHyper.tm_all_intro q => FullHyper.tm_all_intro (embed_h_tm q)
  | EpsHyper.tm_all_elim q t =>
      FullHyper.tm_all_elim (embed_h_tm q) (embed_b_tm t)
  | EpsHyper.tm_eps_intro t q =>
      FullHyper.tm_eps_intro (embed_b_tm t) (embed_h_tm q)
  | EpsHyper.tm_eps_elim q r =>
      FullHyper.tm_eps_elim (embed_h_tm q) (embed_h_tm r)
  end.

Fixpoint erase_label (s : EpsilonFullSign) : EpsilonSign :=
  match s with
  | FullCanonical.epsilon_label A Phi =>
      EpsCanonical.epsilon_label (project_b_ty A)
        (let fix erase_formula
          (X : @FullHyper.h_ty EpsilonFullSign Func Pred)
          : @EpsHyper.h_ty EpsilonSign Func Pred :=
          match X with
          | FullHyper.Ty_Unit => EpsHyper.Ty_Unit
          | FullHyper.Ty_Void => EpsHyper.Ty_Void
          | FullHyper.Ty_Prod X Y =>
              EpsHyper.Ty_Prod (erase_formula X) (erase_formula Y)
          | FullHyper.Ty_Sum X Y =>
              EpsHyper.Ty_Sum (erase_formula X) (erase_formula Y)
          | FullHyper.Ty_Arrow X Y =>
              EpsHyper.Ty_Arrow (erase_formula X) (erase_formula Y)
          | FullHyper.Ty_Atom p t =>
              EpsHyper.Ty_Atom p
                (let fix erase_term
                  (u : @FullBase.b_tm EpsilonFullSign Func)
                  : @EpsBase.b_tm EpsilonSign Func :=
                  match u with
                  | FullBase.b_id => EpsBase.b_id
                  | FullBase.b_comp v w =>
                      EpsBase.b_comp (erase_term v) (erase_term w)
                  | FullBase.b_unit => EpsBase.b_unit
                  | FullBase.b_pair v w =>
                      EpsBase.b_pair (erase_term v) (erase_term w)
                  | FullBase.b_fst => EpsBase.b_fst
                  | FullBase.b_snd => EpsBase.b_snd
                  | FullBase.b_const B r =>
                      EpsBase.b_const (project_b_ty B) (erase_label r)
                  | FullBase.b_func f => EpsBase.b_func f
                  end
                in erase_term t)
          | FullHyper.Ty_All B X =>
              EpsHyper.Ty_All (project_b_ty B) (erase_formula X)
          | FullHyper.Ty_Ex B X =>
              let X' := erase_formula X in
              EpsHyper.form_subst
                (EpsBase.b_pair EpsBase.b_id
                  (EpsBase.b_const (project_b_ty B)
                    (EpsCanonical.epsilon_label (project_b_ty B) X'))) X'
          end
        in erase_formula Phi)
  end.

Definition erase_b_tm
  (t : @FullBase.b_tm EpsilonFullSign Func)
  : @EpsBase.b_tm EpsilonSign Func :=
  @erase_b_tm_with EpsilonFullSign EpsilonSign Func erase_label t.

Definition erase_h_ty
  (Phi : @FullHyper.h_ty EpsilonFullSign Func Pred)
  : @EpsHyper.h_ty EpsilonSign Func Pred :=
  @erase_h_ty_with EpsilonFullSign EpsilonSign Func Pred
    (EpsCanonical.CanonicalSkolemMapping Func Pred) erase_label Phi.

Definition erase_h_context
  (G : @FullHyper.h_context EpsilonFullSign Func Pred)
  : @EpsHyper.h_context EpsilonSign Func Pred :=
  map erase_h_ty G.

Definition erase_h_tm
  (p : @FullHyper.h_tm EpsilonFullSign Func Pred)
  : @EpsHyper.h_tm EpsilonSign Func Pred :=
  @erase_h_tm_with EpsilonFullSign EpsilonSign Func Pred
    (EpsCanonical.CanonicalSkolemMapping Func Pred) erase_label p.

Lemma local_erase_b_tm_eq :
  forall t : @FullBase.b_tm EpsilonFullSign Func,
    (let fix go (u : @FullBase.b_tm EpsilonFullSign Func)
      : @EpsBase.b_tm EpsilonSign Func :=
      match u with
      | FullBase.b_id => EpsBase.b_id
      | FullBase.b_comp v w => EpsBase.b_comp (go v) (go w)
      | FullBase.b_unit => EpsBase.b_unit
      | FullBase.b_pair v w => EpsBase.b_pair (go v) (go w)
      | FullBase.b_fst => EpsBase.b_fst
      | FullBase.b_snd => EpsBase.b_snd
      | FullBase.b_const B r =>
          EpsBase.b_const (project_b_ty B) (erase_label r)
      | FullBase.b_func f => EpsBase.b_func f
      end
    in go t) = erase_b_tm t.
Proof.
  fix IH 1.
  destruct t; cbn [erase_b_tm erase_b_tm_with].
  - reflexivity.
  - f_equal; apply IH.
  - reflexivity.
  - f_equal; apply IH.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma embed_label_unfold :
  forall (A : EpsBase.b_ty)
    (Phi : @EpsHyper.h_ty EpsilonSign Func Pred),
    embed_label (EpsCanonical.epsilon_label A Phi) =
    FullCanonical.epsilon_label (embed_b_ty A) (embed_h_ty Phi).
Proof.
  intros A Phi.
  reflexivity.
Qed.

Lemma erase_label_unfold :
  forall (A : FullBase.b_ty)
    (Phi : @FullHyper.h_ty EpsilonFullSign Func Pred),
    erase_label (FullCanonical.epsilon_label A Phi) =
    EpsCanonical.epsilon_label (project_b_ty A) (erase_h_ty Phi).
Proof.
  intros A Phi.
  cbn [erase_label].
  f_equal.
  induction Phi; cbn [erase_label erase_h_ty erase_h_ty_with
    erase_b_tm erase_b_tm_with] in *;
    try rewrite IHPhi1;
    try rewrite IHPhi2;
    try rewrite IHPhi;
    try reflexivity.
  f_equal.
  apply local_erase_b_tm_eq.
Qed.

Global Instance CanonicalSkolemErasure :
  @SkolemErasure EpsilonFullSign EpsilonSign Func Pred
    (EpsCanonical.CanonicalSkolemMapping Func Pred)
    (FullCanonical.CanonicalSkolemMapping Func Pred).
Proof.
  refine {| erase_sign := erase_label |}.
  intros A Phi.
  apply erase_label_unfold.
Defined.

Lemma embed_skolem_index :
  forall (A : EpsBase.b_ty)
    (Phi : @EpsHyper.h_ty EpsilonSign Func Pred),
    embed_label
      (EpsHyper.skolem_index A Phi) =
    FullHyper.skolem_index (embed_b_ty A) (embed_h_ty Phi).
Proof.
  intros A Phi.
  apply embed_label_unfold.
Qed.

Lemma erase_skolem_index :
  forall (A : FullBase.b_ty)
    (Phi : @FullHyper.h_ty EpsilonFullSign Func Pred),
    erase_label
      (FullHyper.skolem_index A Phi) =
    EpsHyper.skolem_index (project_b_ty A) (erase_h_ty Phi).
Proof.
  intros A Phi.
  apply erase_label_unfold.
Qed.

Lemma erase_embed_b_tm_from :
  forall (t : @EpsBase.b_tm EpsilonSign Func),
    (forall s, EpsCanonical.occurs_in_b_tm s t ->
      erase_label (embed_label s) = s) ->
    erase_b_tm (embed_b_tm t) = t.
Proof.
  intros t.
  induction t; intro Hlabels; cbn [embed_b_tm erase_b_tm erase_b_tm_with].
  - reflexivity.
  - f_equal.
    + apply IHt1. intros s Hs. apply Hlabels.
      apply EpsCanonical.occurs_b_comp_l. exact Hs.
    + apply IHt2. intros s Hs. apply Hlabels.
      apply EpsCanonical.occurs_b_comp_r. exact Hs.
  - reflexivity.
  - f_equal.
    + apply IHt1. intros s Hs. apply Hlabels.
      apply EpsCanonical.occurs_b_pair_l. exact Hs.
    + apply IHt2. intros s Hs. apply Hlabels.
      apply EpsCanonical.occurs_b_pair_r. exact Hs.
  - reflexivity.
  - reflexivity.
  - rewrite project_embed_b_ty.
    f_equal.
    apply Hlabels.
    apply EpsCanonical.occurs_b_const.
  - reflexivity.
Qed.

Lemma erase_embed_h_ty_from :
  forall (Phi : @EpsHyper.h_ty EpsilonSign Func Pred),
    (forall s, EpsCanonical.occurs_in_h_ty s Phi ->
      erase_label (embed_label s) = s) ->
    erase_h_ty (embed_h_ty Phi) = Phi.
Proof.
  intros Phi.
  induction Phi; intro Hlabels;
    cbn [embed_h_ty erase_h_ty erase_h_ty_with].
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply IHPhi1. intros s Hs. apply Hlabels.
      apply EpsCanonical.occurs_h_prod_l. exact Hs.
    + apply IHPhi2. intros s Hs. apply Hlabels.
      apply EpsCanonical.occurs_h_prod_r. exact Hs.
  - f_equal.
    + apply IHPhi1. intros s Hs. apply Hlabels.
      apply EpsCanonical.occurs_h_sum_l. exact Hs.
    + apply IHPhi2. intros s Hs. apply Hlabels.
      apply EpsCanonical.occurs_h_sum_r. exact Hs.
  - f_equal.
    + apply IHPhi1. intros s Hs. apply Hlabels.
      apply EpsCanonical.occurs_h_arrow_l. exact Hs.
    + apply IHPhi2. intros s Hs. apply Hlabels.
      apply EpsCanonical.occurs_h_arrow_r. exact Hs.
  - f_equal.
    apply erase_embed_b_tm_from.
    intros s Hs.
    apply Hlabels.
    apply EpsCanonical.occurs_h_atom.
    exact Hs.
  - rewrite project_embed_b_ty.
    f_equal.
    apply IHPhi.
    intros s Hs.
    apply Hlabels.
    apply EpsCanonical.occurs_h_all.
    exact Hs.
Qed.

Theorem erase_embed_label :
  forall s : EpsilonSign, erase_label (embed_label s) = s.
Proof.
  refine (@well_founded_ind
    EpsilonSign EpsCanonical.immediate_dependency
    EpsCanonical.immediate_dependency_well_founded
    (fun s => erase_label (embed_label s) = s) _).
  intros [A Phi] IH.
  rewrite embed_label_unfold.
  rewrite erase_label_unfold.
  rewrite project_embed_b_ty.
  f_equal.
  apply erase_embed_h_ty_from.
  intros s Hocc.
  apply IH.
  exact Hocc.
Qed.

Theorem erase_embed_b_tm :
  forall t : @EpsBase.b_tm EpsilonSign Func,
    erase_b_tm (embed_b_tm t) = t.
Proof.
  intro t.
  apply erase_embed_b_tm_from.
  intros s _.
  apply erase_embed_label.
Qed.

Theorem erase_embed_h_ty :
  forall Phi : @EpsHyper.h_ty EpsilonSign Func Pred,
    erase_h_ty (embed_h_ty Phi) = Phi.
Proof.
  intro Phi.
  apply erase_embed_h_ty_from.
  intros s _.
  apply erase_embed_label.
Qed.

Theorem erase_embed_h_context :
  forall G : @EpsHyper.h_context EpsilonSign Func Pred,
    erase_h_context (embed_h_context G) = G.
Proof.
  induction G as [|Phi G IH]; simpl.
  - reflexivity.
  - rewrite erase_embed_h_ty, IH. reflexivity.
Qed.

Theorem erase_embed_h_tm :
  forall p : @EpsHyper.h_tm EpsilonSign Func Pred,
    erase_h_tm (embed_h_tm p) = p.
Proof.
  induction p; cbn [embed_h_tm erase_h_tm erase_h_tm_with];
    repeat f_equal;
    try assumption;
    try apply erase_embed_h_ty;
    try apply erase_embed_b_tm.
Qed.

End SyntaxMaps.

Section ForwardTranslation.

Context {Func Pred : Type}.

Context `{HFuncEps : EpsBase.FunctionSignature Func}.
Context `{HFuncFull : FullBase.FunctionSignature Func}.
Context {HFuncCompat : @FunctionSignatureCompat Func HFuncEps HFuncFull}.
Context `{HPredEps : EpsHyper.PredicateSignature Pred}.
Context `{HPredFull : FullHyper.PredicateSignature Pred}.
Context {HPredCompat : @PredicateSignatureCompat Pred HPredEps HPredFull}.

Lemma canonical_embed_b_subst_ext :
  forall (f : @EpsBase.b_tm (@EpsilonSign Func Pred) Func),
    embed_b_tm (EpsHyper.b_subst_ext f) =
    FullHyper.b_subst_ext (embed_b_tm f).
Proof.
  reflexivity.
Qed.

Lemma canonical_embed_form_subst :
  forall (f : @EpsBase.b_tm (@EpsilonSign Func Pred) Func)
    (Phi : @EpsHyper.h_ty (@EpsilonSign Func Pred) Func Pred),
    embed_h_ty (EpsHyper.form_subst f Phi) =
    FullHyper.form_subst (embed_b_tm f) (embed_h_ty Phi).
Proof.
  intros f Phi.
  revert f.
  induction Phi; intros f; simpl;
    try rewrite IHPhi1;
    try rewrite IHPhi2;
    try rewrite IHPhi;
    try rewrite canonical_embed_b_subst_ext;
    reflexivity.
Qed.

Lemma canonical_embed_ctx_subst :
  forall (f : @EpsBase.b_tm (@EpsilonSign Func Pred) Func)
    (G : @EpsHyper.h_context (@EpsilonSign Func Pred) Func Pred),
    embed_h_context (EpsHyper.ctx_subst f G) =
    FullHyper.ctx_subst (embed_b_tm f) (embed_h_context G).
Proof.
  intros f G.
  induction G as [|Phi G IH]; simpl.
  - reflexivity.
  - rewrite canonical_embed_form_subst, IH. reflexivity.
Qed.

Lemma canonical_embed_epsilon_const :
  forall (A : EpsBase.b_ty)
    (Phi : @EpsHyper.h_ty (@EpsilonSign Func Pred) Func Pred),
    embed_b_tm
      (EpsBase.b_const A (EpsHyper.skolem_index A Phi)) =
    FullBase.b_const (embed_b_ty A)
      (FullHyper.skolem_index (embed_b_ty A) (embed_h_ty Phi)).
Proof.
  intros A Phi.
  simpl.
  reflexivity.
Qed.

Lemma canonical_embed_eps_instantiation :
  forall (A : EpsBase.b_ty)
    (Phi : @EpsHyper.h_ty (@EpsilonSign Func Pred) Func Pred),
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
  rewrite canonical_embed_form_subst.
  simpl.
  reflexivity.
Qed.

Lemma canonical_embed_base_typing :
  forall {I : EpsBase.b_ty}
    {t : @EpsBase.b_tm (@EpsilonSign Func Pred) Func}
    {A : EpsBase.b_ty},
    @EpsBase.base_typing (@EpsilonSign Func Pred) Func HFuncEps I t A ->
    @FullBase.base_typing (@EpsilonFullSign Func Pred) Func HFuncFull
      (embed_b_ty I) (embed_b_tm t) (embed_b_ty A).
Proof.
  intros I t A H.
  induction H; simpl.
  - apply FullBase.BT_Id.
  - eapply FullBase.BT_Comp; eassumption.
  - apply FullBase.BT_Unit.
  - apply FullBase.BT_Pair; eassumption.
  - apply FullBase.BT_Fst.
  - apply FullBase.BT_Snd.
  - apply FullBase.BT_Const.
  - rewrite <- func_dom_compat.
    rewrite <- func_cod_compat.
    apply FullBase.BT_Func.
Defined.

Lemma canonical_embed_base_equiv :
  forall {I A : EpsBase.b_ty}
    {f g : @EpsBase.b_tm (@EpsilonSign Func Pred) Func}
    {df : @EpsBase.base_typing (@EpsilonSign Func Pred) Func HFuncEps I f A}
    {dg : @EpsBase.base_typing (@EpsilonSign Func Pred) Func HFuncEps I g A},
    @EpsBase.base_equiv (@EpsilonSign Func Pred) Func HFuncEps
      I A f g df dg ->
    @FullBase.base_equiv (@EpsilonFullSign Func Pred) Func HFuncFull
      (embed_b_ty I) (embed_b_ty A) (embed_b_tm f) (embed_b_tm g)
      (canonical_embed_base_typing df) (canonical_embed_base_typing dg).
Proof.
  intros I A f g df dg H.
  induction H; simpl.
  - apply FullBase.BE_Refl.
  - apply FullBase.BE_Sym. exact IHbase_equiv.
  - eapply FullBase.BE_Trans; eassumption.
  - apply FullBase.BE_CongComp; assumption.
  - apply FullBase.BE_CongPair; assumption.
  - apply FullBase.BE_Assoc.
  - apply FullBase.BE_IdL.
  - apply FullBase.BE_IdR.
  - apply FullBase.BE_BetaFst.
  - apply FullBase.BE_BetaSnd.
  - apply FullBase.BE_EtaPair.
  - apply FullBase.BE_EtaUnit.
  - apply FullBase.BE_CompPair.
Defined.

Definition cast_full_base_typing
  {I A B : FullBase.b_ty}
  {t : @FullBase.b_tm (@EpsilonFullSign Func Pred) Func}
  (e : B = A)
  (d : @FullBase.base_typing (@EpsilonFullSign Func Pred) Func
    HFuncFull I t A)
  : @FullBase.base_typing (@EpsilonFullSign Func Pred) Func
      HFuncFull I t B.
Proof.
  subst.
  exact d.
Defined.

Definition cast_full_base_equiv
  {I A B : FullBase.b_ty}
  {f g : @FullBase.b_tm (@EpsilonFullSign Func Pred) Func}
  {df : @FullBase.base_typing (@EpsilonFullSign Func Pred) Func
    HFuncFull I f A}
  {dg : @FullBase.base_typing (@EpsilonFullSign Func Pred) Func
    HFuncFull I g A}
  (e : B = A)
  (H : @FullBase.base_equiv (@EpsilonFullSign Func Pred) Func HFuncFull
    I A f g df dg)
  : @FullBase.base_equiv (@EpsilonFullSign Func Pred) Func HFuncFull
      I B f g (cast_full_base_typing e df) (cast_full_base_typing e dg).
Proof.
  subst.
  exact H.
Defined.

Lemma canonical_embed_wellformed :
  forall {I : EpsBase.b_ty}
    {Phi : @EpsHyper.h_ty (@EpsilonSign Func Pred) Func Pred},
    @EpsHyper.WellFormed (@EpsilonSign Func Pred) Func Pred
      HFuncEps HPredEps I Phi ->
    @FullHyper.WellFormed (@EpsilonFullSign Func Pred) Func Pred
      HFuncFull HPredFull (embed_b_ty I) (embed_h_ty Phi).
Proof.
  intros I Phi H.
  induction H; simpl.
  - apply FullHyper.WF_Unit.
  - apply FullHyper.WF_Void.
  - apply FullHyper.WF_Prod; assumption.
  - apply FullHyper.WF_Sum; assumption.
  - apply FullHyper.WF_Arrow; assumption.
  - eapply FullHyper.WF_Atom.
    replace (FullHyper.pred_dom p) with
      (embed_b_ty (EpsHyper.pred_dom p)).
    2:{ symmetry. apply pred_dom_compat. }
    exact (canonical_embed_base_typing b).
  - apply FullHyper.WF_All.
    exact IHWellFormed.
Defined.

Lemma canonical_embed_all_wellformed :
  forall {I : EpsBase.b_ty}
    {G : @EpsHyper.h_context (@EpsilonSign Func Pred) Func Pred},
    @EpsHyper.All_WellFormed (@EpsilonSign Func Pred) Func Pred
      HFuncEps HPredEps I G ->
    @FullHyper.All_WellFormed (@EpsilonFullSign Func Pred) Func Pred
      HFuncFull HPredFull (embed_b_ty I) (embed_h_context G).
Proof.
  intros I G H.
  induction H; simpl.
  - apply FullHyper.AWF_Nil.
  - apply FullHyper.AWF_Cons.
    + apply canonical_embed_wellformed. exact w.
    + exact IHAll_WellFormed.
Defined.

Lemma canonical_embed_form_equiv :
  forall {I : EpsBase.b_ty}
    {Phi Psi : @EpsHyper.h_ty (@EpsilonSign Func Pred) Func Pred},
    @EpsHyper.form_equiv (@EpsilonSign Func Pred) Func Pred
      HFuncEps HPredEps (EpsCanonical.CanonicalSkolemMapping Func Pred)
      I Phi Psi ->
    @FullHyper.form_equiv (@EpsilonFullSign Func Pred) Func Pred
      HFuncFull HPredFull (FullCanonical.CanonicalSkolemMapping Func Pred)
      (embed_b_ty I) (embed_h_ty Phi) (embed_h_ty Psi).
Proof.
  intros I Phi Psi H.
  induction H.
  - set (d1' := cast_full_base_typing
      (pred_dom_compat p) (canonical_embed_base_typing d1)).
    set (d2' := cast_full_base_typing
      (pred_dom_compat p) (canonical_embed_base_typing d2)).
    refine (@FullHyper.FE_Atom (@EpsilonFullSign Func Pred) Func Pred
      HFuncFull HPredFull (FullCanonical.CanonicalSkolemMapping Func Pred)
      (embed_b_ty I) p (embed_b_tm t1) (embed_b_tm t2)
      d1' d2' (cast_full_base_equiv
        (pred_dom_compat p) (canonical_embed_base_equiv b))).
  - apply FullHyper.FE_Refl.
    exact (canonical_embed_wellformed w).
  - apply FullHyper.FE_Sym. exact IHform_equiv.
  - eapply FullHyper.FE_Trans; eassumption.
  - apply FullHyper.FE_Prod; assumption.
  - apply FullHyper.FE_Sum; assumption.
  - apply FullHyper.FE_Arrow; assumption.
  - apply FullHyper.FE_All. exact IHform_equiv.
  - repeat rewrite canonical_embed_eps_instantiation.
    apply FullHyper.FE_Eps_Functorial.
    exact IHform_equiv.
  - rewrite canonical_embed_form_subst.
    apply FullHyper.FE_Pullback_Id.
    apply canonical_embed_wellformed. exact w.
  - repeat rewrite canonical_embed_form_subst.
    refine (@FullHyper.FE_Pullback_Comp
      (@EpsilonFullSign Func Pred) Func Pred
      HFuncFull HPredFull (FullCanonical.CanonicalSkolemMapping Func Pred)
      (embed_b_ty I) (embed_b_ty J) (embed_b_ty K)
      (embed_b_tm f) (embed_b_tm g) (embed_h_ty Phi)
      (canonical_embed_base_typing df) (canonical_embed_base_typing dg) _).
    apply canonical_embed_wellformed. exact w.
  - repeat rewrite canonical_embed_form_subst.
    refine (@FullHyper.FE_Pullback_Cong
      (@EpsilonFullSign Func Pred) Func Pred
      HFuncFull HPredFull (FullCanonical.CanonicalSkolemMapping Func Pred)
      (embed_b_ty I) (embed_b_ty J)
      (embed_b_tm f) (embed_b_tm g) (embed_h_ty Phi)
      (canonical_embed_base_typing df) (canonical_embed_base_typing dg)
      (canonical_embed_base_equiv b) _).
    apply canonical_embed_wellformed. exact w.
  - repeat rewrite canonical_embed_eps_instantiation.
    repeat rewrite canonical_embed_form_subst.
    repeat rewrite canonical_embed_b_subst_ext.
    refine (@FullHyper.FE_Eps_BC
      (@EpsilonFullSign Func Pred) Func Pred
      HFuncFull HPredFull (FullCanonical.CanonicalSkolemMapping Func Pred)
      (embed_b_ty I) (embed_b_ty J) (embed_b_ty A)
      (embed_b_tm t) (canonical_embed_base_typing dt) (embed_h_ty Phi) _).
    exact (canonical_embed_wellformed w).
Defined.

Lemma canonical_embed_ctx_equiv :
  forall {I : EpsBase.b_ty}
    {G1 G2 : @EpsHyper.h_context (@EpsilonSign Func Pred) Func Pred},
    @EpsHyper.ctx_equiv (@EpsilonSign Func Pred) Func Pred
      HFuncEps HPredEps (EpsCanonical.CanonicalSkolemMapping Func Pred)
      I G1 G2 ->
    @FullHyper.ctx_equiv (@EpsilonFullSign Func Pred) Func Pred
      HFuncFull HPredFull (FullCanonical.CanonicalSkolemMapping Func Pred)
      (embed_b_ty I) (embed_h_context G1) (embed_h_context G2).
Proof.
  intros I G1 G2 H.
  induction H; simpl.
  - apply FullHyper.CEq_Nil.
  - apply FullHyper.CEq_Cons.
    + apply canonical_embed_form_equiv. exact f.
    + exact IHctx_equiv.
Defined.

Theorem canonical_embed_h_derivation :
  forall {I : EpsBase.b_ty}
    {G : @EpsHyper.h_context (@EpsilonSign Func Pred) Func Pred}
    {p : @EpsHyper.h_tm (@EpsilonSign Func Pred) Func Pred}
    {Phi : @EpsHyper.h_ty (@EpsilonSign Func Pred) Func Pred},
    @EpsHyper.h_derivation (@EpsilonSign Func Pred) Func Pred
      HFuncEps HPredEps (EpsCanonical.CanonicalSkolemMapping Func Pred)
      I G p Phi ->
    @FullHyper.h_derivation (@EpsilonFullSign Func Pred) Func Pred
      HFuncFull HPredFull (FullCanonical.CanonicalSkolemMapping Func Pred)
      (embed_b_ty I) (embed_h_context G) (embed_h_tm p) (embed_h_ty Phi).
Proof.
  intros I G p Phi H.
  induction H.
  - apply FullHyper.HD_Var0.
    exact (canonical_embed_all_wellformed a).
  - apply FullHyper.HD_VarS.
    + exact (canonical_embed_wellformed w).
    + exact IHh_derivation.
  - apply FullHyper.HD_Unit.
    exact (canonical_embed_all_wellformed a).
  - eapply FullHyper.HD_Conv.
    + exact IHh_derivation.
    + exact (canonical_embed_form_equiv f).
  - eapply FullHyper.HD_Ctx_Conv.
    + exact (canonical_embed_ctx_equiv c).
    + exact IHh_derivation.
  - apply FullHyper.HD_Lam. exact IHh_derivation.
  - eapply FullHyper.HD_App; eassumption.
  - apply FullHyper.HD_Pair; assumption.
  - eapply FullHyper.HD_Fst. exact IHh_derivation.
  - eapply FullHyper.HD_Snd. exact IHh_derivation.
  - apply FullHyper.HD_Inl.
    + exact (canonical_embed_wellformed w).
    + exact IHh_derivation.
  - apply FullHyper.HD_Inr.
    + exact (canonical_embed_wellformed w).
    + exact IHh_derivation.
  - eapply FullHyper.HD_Case; eassumption.
  - apply FullHyper.HD_Absurd.
    + exact (canonical_embed_wellformed w).
    + exact IHh_derivation.
  - apply FullHyper.HD_All_Intro.
    change (@FullHyper.h_derivation (@EpsilonFullSign Func Pred) Func Pred
      HFuncFull HPredFull (FullCanonical.CanonicalSkolemMapping Func Pred)
      (FullBase.b_Prod (embed_b_ty I) (embed_b_ty A))
      (FullHyper.ctx_subst FullBase.b_fst (embed_h_context G))
      (embed_h_tm p) (embed_h_ty Phi)).
    replace (FullHyper.ctx_subst FullBase.b_fst (embed_h_context G))
      with (embed_h_context (EpsHyper.ctx_subst EpsBase.b_fst G)).
    2:{ exact (canonical_embed_ctx_subst EpsBase.b_fst G). }
    exact IHh_derivation.
  - rewrite canonical_embed_form_subst.
    eapply FullHyper.HD_All_Elim.
    + exact IHh_derivation.
    + exact (canonical_embed_base_typing b).
  - rewrite canonical_embed_eps_instantiation.
    eapply FullHyper.HD_Eps_Intro.
    + exact (canonical_embed_base_typing b).
    + replace
        (FullHyper.form_subst
          (FullBase.b_pair FullBase.b_id (embed_b_tm f)) (embed_h_ty Phi))
        with
        (embed_h_ty
          (EpsHyper.form_subst
            (EpsBase.b_pair EpsBase.b_id f) Phi)).
      2:{ exact (canonical_embed_form_subst
        (EpsBase.b_pair EpsBase.b_id f) Phi). }
      exact IHh_derivation.
  - eapply FullHyper.HD_Eps_Elim.
    + rewrite <- canonical_embed_eps_instantiation.
      exact IHh_derivation1.
    + change (@FullHyper.h_derivation
        (@EpsilonFullSign Func Pred) Func Pred
        HFuncFull HPredFull (FullCanonical.CanonicalSkolemMapping Func Pred)
        (FullBase.b_Prod (embed_b_ty I) (embed_b_ty A))
        (embed_h_ty Phi ::
          FullHyper.ctx_subst FullBase.b_fst (embed_h_context G))
        (embed_h_tm p2)
        (FullHyper.form_subst FullBase.b_fst (embed_h_ty Chi))).
      replace (FullHyper.ctx_subst FullBase.b_fst (embed_h_context G))
        with (embed_h_context (EpsHyper.ctx_subst EpsBase.b_fst G)).
      2:{ exact (canonical_embed_ctx_subst EpsBase.b_fst G). }
      replace (FullHyper.form_subst FullBase.b_fst (embed_h_ty Chi))
        with (embed_h_ty (EpsHyper.form_subst EpsBase.b_fst Chi)).
      2:{ exact (canonical_embed_form_subst EpsBase.b_fst Chi). }
      exact IHh_derivation2.
Defined.

Definition canonical_epsilon_derivation_to_epsilonfull
  {I : EpsBase.b_ty}
  {G : @EpsHyper.h_context (@EpsilonSign Func Pred) Func Pred}
  {p : @EpsHyper.h_tm (@EpsilonSign Func Pred) Func Pred}
  {Phi : @EpsHyper.h_ty (@EpsilonSign Func Pred) Func Pred}
  (d : @EpsHyper.h_derivation (@EpsilonSign Func Pred) Func Pred
    HFuncEps HPredEps (EpsCanonical.CanonicalSkolemMapping Func Pred)
    I G p Phi)
  : @FullHyper.h_derivation (@EpsilonFullSign Func Pred) Func Pred
      HFuncFull HPredFull (FullCanonical.CanonicalSkolemMapping Func Pred)
      (embed_b_ty I) (embed_h_context G) (embed_h_tm p) (embed_h_ty Phi) :=
  canonical_embed_h_derivation d.

End ForwardTranslation.

Section Conservativity.

Context {Func Pred : Type}.

Context `{HFuncEps : EpsBase.FunctionSignature Func}.
Context `{HFuncFull : FullBase.FunctionSignature Func}.
Context {HFuncCompat : @FunctionSignatureCompat Func HFuncEps HFuncFull}.
Context `{HPredEps : EpsHyper.PredicateSignature Pred}.
Context `{HPredFull : FullHyper.PredicateSignature Pred}.
Context {HPredCompat : @PredicateSignatureCompat Pred HPredEps HPredFull}.

Definition canonical_epsilon_derivable
  (I : EpsBase.b_ty)
  (G : @EpsHyper.h_context (@EpsilonSign Func Pred) Func Pred)
  (Phi : @EpsHyper.h_ty (@EpsilonSign Func Pred) Func Pred) : Type :=
  { p_eps : @EpsHyper.h_tm (@EpsilonSign Func Pred) Func Pred &
    @EpsHyper.h_derivation (@EpsilonSign Func Pred) Func Pred
      HFuncEps HPredEps (EpsCanonical.CanonicalSkolemMapping Func Pred)
      I G p_eps Phi }.

Definition canonical_embedded_epsilonfull_derivable
  (I : EpsBase.b_ty)
  (G : @EpsHyper.h_context (@EpsilonSign Func Pred) Func Pred)
  (Phi : @EpsHyper.h_ty (@EpsilonSign Func Pred) Func Pred) : Type :=
  { p_full : @FullHyper.h_tm (@EpsilonFullSign Func Pred) Func Pred &
    @FullHyper.h_derivation (@EpsilonFullSign Func Pred) Func Pred
      HFuncFull HPredFull (FullCanonical.CanonicalSkolemMapping Func Pred)
      (embed_b_ty I) (embed_h_context G) p_full (embed_h_ty Phi) }.

Definition canonical_epsilonfull_conservative_over_epsilon : Type :=
  forall (I : EpsBase.b_ty)
    (G : @EpsHyper.h_context (@EpsilonSign Func Pred) Func Pred)
    (Phi : @EpsHyper.h_ty (@EpsilonSign Func Pred) Func Pred),
    { p_full : @FullHyper.h_tm (@EpsilonFullSign Func Pred) Func Pred &
      @FullHyper.h_derivation (@EpsilonFullSign Func Pred) Func Pred
        HFuncFull HPredFull (FullCanonical.CanonicalSkolemMapping Func Pred)
        (embed_b_ty I) (embed_h_context G) p_full (embed_h_ty Phi) } ->
    { p_eps : @EpsHyper.h_tm (@EpsilonSign Func Pred) Func Pred &
      @EpsHyper.h_derivation (@EpsilonSign Func Pred) Func Pred
        HFuncEps HPredEps (EpsCanonical.CanonicalSkolemMapping Func Pred)
        I G p_eps Phi }.

Theorem canonical_epsilonfull_conservativity :
  canonical_epsilonfull_conservative_over_epsilon.
Proof.
  intros I G Phi [p_full Hfull].
  pose proof (@erase_h_derivation
    (@EpsilonFullSign Func Pred) (@EpsilonSign Func Pred) Func Pred
    HFuncEps HFuncFull HFuncCompat
    HPredEps HPredFull HPredCompat
    (EpsCanonical.CanonicalSkolemMapping Func Pred)
    (FullCanonical.CanonicalSkolemMapping Func Pred)
    (@CanonicalSkolemErasure Func Pred)
    (embed_b_ty I) (embed_h_context G) p_full (embed_h_ty Phi)
    Hfull) as Herased.
  exists (erase_h_tm p_full).
  change (@EpsHyper.h_derivation (@EpsilonSign Func Pred) Func Pred
    HFuncEps HPredEps (EpsCanonical.CanonicalSkolemMapping Func Pred)
    (project_b_ty (embed_b_ty I))
    (erase_h_context (embed_h_context G))
    (erase_h_tm p_full)
    (erase_h_ty (embed_h_ty Phi))) in Herased.
  rewrite project_embed_b_ty in Herased.
  rewrite erase_embed_h_context in Herased.
  rewrite erase_embed_h_ty in Herased.
  exact Herased.
Qed.

(* Unlike bare erasure preservation, this statement returns to the original
   epsilon-only context and formula via the proved erase-after-embed laws. *)
Theorem canonical_derivability_equivalence :
  forall (I : EpsBase.b_ty)
    (G : @EpsHyper.h_context (@EpsilonSign Func Pred) Func Pred)
    (Phi : @EpsHyper.h_ty (@EpsilonSign Func Pred) Func Pred),
    ((canonical_epsilon_derivable I G Phi ->
      canonical_embedded_epsilonfull_derivable I G Phi) *
     (canonical_embedded_epsilonfull_derivable I G Phi ->
      canonical_epsilon_derivable I G Phi))%type.
Proof.
  intros I G Phi.
  split.
  - intros [p_eps Heps].
    exists (embed_h_tm p_eps).
    exact (canonical_embed_h_derivation Heps).
  - apply canonical_epsilonfull_conservativity.
Qed.

End Conservativity.

End CanonicalEpsilonComparison.
