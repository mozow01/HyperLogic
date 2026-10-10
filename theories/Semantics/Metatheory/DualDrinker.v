Require Import List.
Import ListNotations.
Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax_Lemmas.
Require Export HyperLogic.Logic.Hyper.EpsilonFull.DualDrinker_Syntax.

(* Preserve the historical qualified name used by the nonconservativity result. *)
Definition DualDrinkerFormula {Sign Func Pred : Type}
  (p : Pred) (I D : b_ty) : @h_ty Sign Func Pred :=
  HyperLogic.Logic.Hyper.EpsilonFull.DualDrinker_Syntax.DualDrinkerFormula p I D.

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
