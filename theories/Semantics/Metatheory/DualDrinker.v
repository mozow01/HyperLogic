(* theories/Semantics/Metatheory/DualDrinker.v *)

Require Import List.
Import ListNotations.

Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax_Lemmas.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax_Lemmas.

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

Ltac solve_full_bt :=
  eauto using BT_Const, BT_Id, BT_Fst, BT_Snd, BT_Pair, BT_Comp.

Ltac solve_full_wf :=
  try solve [eassumption];
  try solve [constructor];
  match goal with
  | |- All_WellFormed _ (ctx_subst _ _) =>
      unfold ctx_subst; simpl; solve_full_wf
  | |- All_WellFormed _ nil => constructor
  | |- All_WellFormed _ (_ :: _) =>
      constructor; solve_full_wf
  | |- WellFormed _ (form_subst _ _) =>
      eapply wf_subst; [solve_full_bt | solve_full_wf]
  | |- WellFormed _ (Ty_Prod _ _) =>
      constructor; solve_full_wf
  | |- WellFormed _ (Ty_Sum _ _) =>
      constructor; solve_full_wf
  | |- WellFormed _ (Ty_Arrow _ _) =>
      constructor; solve_full_wf
  | |- WellFormed _ (Ty_All _ _) =>
      constructor; solve_full_wf
  | |- WellFormed _ (Ty_Ex _ _) =>
      constructor; solve_full_wf
  | |- WellFormed _ (Ty_Atom _ _) =>
      eapply WF_Atom; solve_full_bt
  end.

Lemma epsilonfull_dual_drinker_provable :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred}
    (I D : b_ty) (Phi : @h_ty Sign Func Pred),
  WellFormed (b_Prod I D) Phi ->
  { p : @h_tm Sign Func Pred &
      h_derivation I nil p (T_ifol_to_epsilonfull (Dual_Drinker I D Phi)) }.
Proof.
  intros Sign Func Pred HFunc HPred SM I D Phi wf_Phi.
  unfold T_ifol_to_epsilonfull.
  eexists.
  unfold Dual_Drinker.
  eapply HD_Ex_Intro with (f := b_const D (skolem_index D Phi)).
  - solve_full_bt.
  - eapply HD_Lam with
      (Phi := form_subst
        (b_pair b_id (b_const D (skolem_index D Phi)))
        (form_subst b_fst (Ty_Ex D Phi))).
    eapply HD_Ex_Elim with
      (A := D)
      (Phi := Phi)
      (Chi := form_subst
        (b_pair b_id (b_const D (skolem_index D Phi))) Phi).
    + eapply HD_Conv.
      * apply HD_Var0.
        solve_full_wf.
      * eapply FE_Trans.
        1: {
          eapply FE_Pullback_Comp.
          - solve_full_bt.
          - eapply BT_Pair; solve_full_bt.
          - solve_full_wf.
        }
        eapply FE_Trans.
        2: { apply FE_Pullback_Id. solve_full_wf. }
        eapply FE_Pullback_Cong.
        -- apply (BE_Comp_Pair_Id_Fst_Correct (BT_Const (I:=I) (A:=D) (s:=skolem_index D Phi))).
        -- solve_full_wf.
    + eapply HD_Conv.
      * eapply HD_Eps_Intro with
          (f := b_snd)
          (Phi := form_subst (b_subst_ext b_fst) Phi).
        -- solve_full_bt.
        -- eapply HD_Conv.
           ++ apply HD_Var0.
              solve_full_wf.
           ++ eapply FE_Sym.
              apply FE_Pullback_Ext_Fst_Snd.
              exact wf_Phi.
      * eapply FE_Eps_BC with (J := I) (t := b_fst).
        -- solve_full_bt.
        -- exact wf_Phi.
Defined.

Lemma epsilonfull_dual_drinker_atom_provable :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred}
    (p : Pred) (I D : b_ty),
  pred_dom p = D ->
  { q : @h_tm Sign Func Pred &
      h_derivation I nil q
        (T_ifol_to_epsilonfull (@DualDrinkerFormula Sign Func Pred p I D)) }.
Proof.
  intros Sign Func Pred HFunc HPred SM p I D Hp.
  unfold DualDrinkerFormula.
  apply epsilonfull_dual_drinker_provable.
  unfold P_x.
  subst D.
  eapply WF_Atom.
  apply BT_Snd.
Defined.
