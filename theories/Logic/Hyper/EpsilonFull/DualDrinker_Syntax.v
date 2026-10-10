(** Syntax and substitution calculations for the EpsilonFull dual drinker. *)

Require Import List.
Import ListNotations.

Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax_Lemmas.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax_Lemmas.

(** Compatibility identity on EpsilonFull formulas, retained for Dual Drinker
    uses. It does not translate IFOL syntax. The structural translation is
    [HyperLogic.Semantics.Metatheory.IFOL_EpsilonFull_Translation.ifol_to_epsilon_h_ty]. *)
Definition T_ifol_to_epsilonfull {Sign Func Pred : Type}
  (Phi : @h_ty Sign Func Pred) : @h_ty Sign Func Pred := Phi.

Definition Dual_Drinker {Sign Func Pred : Type}
  (I D : b_ty) (Phi : @h_ty Sign Func Pred) : @h_ty Sign Func Pred :=
  Ty_Ex D (Ty_Arrow (form_subst b_fst (Ty_Ex D Phi)) Phi).

Definition P_x {Sign Func Pred : Type} (p : Pred) : @h_ty Sign Func Pred :=
  Ty_Atom p b_snd.

Definition DualDrinkerFormula {Sign Func Pred : Type}
  (p : Pred) (I D : b_ty) : @h_ty Sign Func Pred :=
  Dual_Drinker I D (P_x p).

Lemma DualDrinker_WellFormed :
  forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}
    (p : Pred) (I D : b_ty),
  pred_dom p = D ->
  WellFormed I (@DualDrinkerFormula Sign Func Pred p I D).
Proof.
  intros Sign Func Pred HFunc HPred p I D Hp.
  unfold DualDrinkerFormula, Dual_Drinker, P_x.
  subst D.
  repeat econstructor.
Defined.

Lemma BT_Comp_Pair_Id_Fst_Correct :
  forall {Sign Func : Type} `{FunctionSignature Func} {I D : b_ty}
    {t : @b_tm Sign Func},
  base_typing I t D ->
  base_typing I (b_comp b_fst (b_pair b_id t)) I.
Proof.
  intros Sign Func HFunc I D t Ht.
  eapply BT_Comp.
  - apply (BT_Fst (A:=I) (B:=D)).
  - eapply BT_Pair.
    + apply BT_Id.
    + exact Ht.
Defined.

Lemma BE_Comp_Pair_Id_Fst_Correct :
  forall {Sign Func : Type} `{FunctionSignature Func} {I D : b_ty}
    {t : @b_tm Sign Func} (Ht : base_typing I t D),
  base_equiv
    (BT_Comp_Pair_Id_Fst_Correct Ht)
    (BT_Id (A:=I)).
Proof.
  intros.
  apply BE_BetaFst.
Defined.

Lemma BE_Substitution_Law :
  forall {Sign Func : Type} `{FunctionSignature Func}
    I J D (f t : @b_tm Sign Func)
    (df : base_typing I f J) (dt : base_typing I t D),
  base_equiv
    (BT_Comp
      (BT_Pair (BT_Comp df BT_Fst) BT_Snd)
      (BT_Pair BT_Id dt))
    (BT_Pair df dt).
Proof.
  intros Sign Func HFunc I J D f t df dt.
  unfold b_subst_ext.
  eapply BE_Trans.
  { apply BE_CompPair. }
  eapply BE_CongPair.
  - eapply BE_Trans.
    { eapply BE_Sym. apply BE_Assoc. }
    eapply BE_Trans.
    { eapply BE_CongComp.
      - apply BE_BetaFst.
      - apply BE_Refl. }
    apply BE_IdR.
  - apply BE_BetaSnd.
Defined.

Lemma FE_Substitution_Law :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred}
    I J D (f t : @b_tm Sign Func) (Phi : @h_ty Sign Func Pred)
    (df : base_typing I f J) (dt : base_typing I t D),
  WellFormed (b_Prod J D) Phi ->
  form_equiv I
    (form_subst (b_pair b_id t) (form_subst (b_subst_ext f) Phi))
    (form_subst (b_pair f t) Phi).
Proof.
  intros Sign Func Pred HFunc HPred SM I J D f t Phi df dt Hwf.
  eapply FE_Trans.
  - eapply FE_Pullback_Comp.
    + unfold b_subst_ext. eapply BT_Pair.
      * eapply BT_Comp.
        -- exact df.
        -- apply (BT_Fst (A:=I) (B:=D)).
      * apply (BT_Snd (A:=I) (B:=D)).
    + eapply BT_Pair.
      * apply BT_Id.
      * exact dt.
    + exact Hwf.
  - eapply FE_Pullback_Cong.
    + exact (@BE_Substitution_Law Sign Func HFunc I J D f t df dt).
    + exact Hwf.
Defined.

Lemma FE_Local_Id :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred}
    I D (Phi : @h_ty Sign Func Pred),
  WellFormed (b_Prod I D) Phi ->
  form_equiv (b_Prod I D) (form_subst (b_pair b_fst b_snd) Phi) Phi.
Proof.
  intros Sign Func Pred HFunc HPred SM I D Phi Hwf.
  eapply FE_Trans.
  2: { apply FE_Pullback_Id. exact Hwf. }
  eapply FE_Pullback_Cong.
  - eapply BE_Trans.
    1: {
      eapply BE_CongPair.
      - eapply BE_Sym. apply BE_IdR.
      - eapply BE_Sym. apply BE_IdR.
    }
    apply BE_EtaPair.
  - exact Hwf.
Defined.

Lemma FE_Pullback_Ext_Fst_Snd :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred}
    I D (Phi : @h_ty Sign Func Pred),
  WellFormed (b_Prod I D) Phi ->
  form_equiv (b_Prod I D)
    (form_subst (b_pair b_id b_snd) (form_subst (b_subst_ext b_fst) Phi))
    Phi.
Proof.
  intros Sign Func Pred HFunc HPred SM I D Phi Hwf.
  eapply FE_Trans.
  - eapply FE_Substitution_Law.
    + apply BT_Fst.
    + apply BT_Snd.
    + exact Hwf.
  - apply FE_Local_Id. exact Hwf.
Defined.


(** The displayed base equation in the diagonal calculation. *)
Definition diagonal_base_equation :
  forall {Sign Func : Type} `{FunctionSignature Func} (I A : b_ty),
  @base_equiv_typed Sign Func H (b_Prod I A) (b_Prod I A)
    (b_comp (b_subst_ext b_fst) (b_pair b_id b_snd)) b_id.
Proof.
  intros Sign Func H I A.
  exists (BT_Comp (typing_subst_ext (BT_Fst (A:=I) (B:=A)))
    (BT_Pair BT_Id (BT_Snd (A:=I) (B:=A)))).
  exists BT_Id.
  eapply BE_Trans.
  - apply BE_Substitution_Law.
  - eapply BE_Trans.
    + apply BE_CongPair; apply BE_Sym; apply BE_IdR.
    + apply BE_EtaPair.
Defined.
