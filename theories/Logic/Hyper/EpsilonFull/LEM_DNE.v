
Require Import List.
Import ListNotations.

Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.

Section LEM_DNE.

Context {Sign Func Pred : Type}.
Context `{FunctionSignature Func}.
Context `{PredicateSignature Pred}.
Context `{SkolemMapping Sign Func Pred}.

Definition h_not (Phi : @h_ty Sign Func Pred) : @h_ty Sign Func Pred :=
  Ty_Arrow Phi Ty_Void.

Definition h_lem (Phi : @h_ty Sign Func Pred) : @h_ty Sign Func Pred :=
  Ty_Sum Phi (h_not Phi).

Definition h_dne (Phi : @h_ty Sign Func Pred) : @h_ty Sign Func Pred :=
  Ty_Arrow (h_not (h_not Phi)) Phi.

Definition h_lem_implies_dne (Phi : @h_ty Sign Func Pred) : @h_ty Sign Func Pred :=
  Ty_Arrow (h_lem Phi) (h_dne Phi).

Definition lem_implies_dne_tm
  (Phi : @h_ty Sign Func Pred) : @h_tm Sign Func Pred :=
  tm_lam (h_lem Phi)
    (tm_lam (h_not (h_not Phi))
      (tm_case
        (tm_var 1)
        (tm_var 0)
        (tm_absurd Phi (tm_app (tm_var 1) (tm_var 0))))).

Lemma wf_not :
  forall (I : b_ty) (Phi : @h_ty Sign Func Pred),
    WellFormed I Phi ->
    WellFormed I (h_not Phi).
Proof.
  intros I Phi HPhi.
  unfold h_not.
  apply WF_Arrow.
  - exact HPhi.
  - apply WF_Void.
Qed.

Lemma wf_lem :
  forall (I : b_ty) (Phi : @h_ty Sign Func Pred),
    WellFormed I Phi ->
    WellFormed I (h_lem Phi).
Proof.
  intros I Phi HPhi.
  unfold h_lem.
  apply WF_Sum.
  - exact HPhi.
  - apply wf_not; exact HPhi.
Qed.

Lemma wf_dne :
  forall (I : b_ty) (Phi : @h_ty Sign Func Pred),
    WellFormed I Phi ->
    WellFormed I (h_dne Phi).
Proof.
  intros I Phi HPhi.
  unfold h_dne.
  apply WF_Arrow.
  - apply wf_not, wf_not; exact HPhi.
  - exact HPhi.
Qed.

Theorem lem_implies_dne :
  forall (I : b_ty) (Phi : @h_ty Sign Func Pred),
    WellFormed I Phi ->
    h_derivation I [] (lem_implies_dne_tm Phi) (h_lem_implies_dne Phi).
Proof.
  intros I Phi HPhi.
  unfold lem_implies_dne_tm, h_lem_implies_dne, h_dne.
  apply HD_Lam.
  apply HD_Lam.
  eapply HD_Case.
  - apply HD_VarS.
    + apply wf_not, wf_not; exact HPhi.
    + apply HD_Var0.
      constructor.
      * apply wf_lem; exact HPhi.
      * constructor.
  - apply HD_Var0.
    constructor.
    + exact HPhi.
    + constructor.
      * apply wf_not, wf_not; exact HPhi.
      * constructor.
        -- apply wf_lem; exact HPhi.
        -- constructor.
  - apply HD_Absurd.
    + exact HPhi.
    + eapply HD_App.
      * apply HD_VarS.
        -- apply wf_not; exact HPhi.
        -- apply HD_Var0.
           constructor.
           ++ apply wf_not, wf_not; exact HPhi.
           ++ constructor.
              ** apply wf_lem; exact HPhi.
              ** constructor.
      * apply HD_Var0.
        constructor.
        -- apply wf_not; exact HPhi.
        -- constructor.
           ++ apply wf_not, wf_not; exact HPhi.
           ++ constructor.
              ** apply wf_lem; exact HPhi.
              ** constructor.
Qed.

End LEM_DNE.
