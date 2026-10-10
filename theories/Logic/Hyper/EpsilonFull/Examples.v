(** Concrete EpsilonFull terms and rank calculations from the manuscript. *)
Require Import List.
Import ListNotations.
Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax_Lemmas.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Canonical_Skolem.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.DualDrinker_Syntax.

Module Labels := CanonicalEpsilonFull.

Section LabelNesting.
Variable Pred : Type.
Variable r : Pred.
Definition first_label : Labels.EpsilonLabel Empty_set Pred :=
  Labels.epsilon_label b_S Ty_Unit.
Definition first_nested_formula :
  @h_ty (Labels.EpsilonLabel Empty_set Pred) Empty_set Pred :=
  Ty_Atom r (b_const b_S first_label).
Definition second_label : Labels.EpsilonLabel Empty_set Pred :=
  Labels.epsilon_label b_S first_nested_formula.

Definition first_label_rank : Labels.epsilon_rank first_label = 1 := eq_refl.
Definition nested_formula_rank : Labels.h_ty_rank first_nested_formula = 1 := eq_refl.
Definition second_label_rank : Labels.epsilon_rank second_label = 2 := eq_refl.
Definition first_label_depends_in_second :
  Labels.immediate_dependency first_label second_label.
Proof.
  unfold Labels.immediate_dependency, second_label, first_nested_formula.
  apply Labels.occurs_h_atom.
  apply Labels.occurs_b_const.
Defined.
End LabelNesting.

Section NestedEpsilonTerm.
Definition nested_predicate_signature : PredicateSignature Datatypes.unit :=
  {| pred_dom _ := b_Prod b_S b_S |}.
Definition nested_func_dom (f : Empty_set) : b_ty := match f with end.
Definition nested_func_cod (f : Empty_set) : b_ty := match f with end.
Definition nested_function_signature : FunctionSignature Empty_set :=
  {| func_dom := nested_func_dom; func_cod := nested_func_cod |}.
Definition inner_formula :
  @h_ty (Labels.EpsilonLabel Empty_set Datatypes.unit)
    Empty_set Datatypes.unit :=
  Ty_Atom tt (b_pair b_fst b_snd).
Definition inner_label : Labels.EpsilonLabel Empty_set Datatypes.unit :=
  Labels.epsilon_label b_S inner_formula.
Definition inner_witness_over_x :
  @b_tm (Labels.EpsilonLabel Empty_set Datatypes.unit) Empty_set :=
  b_const b_S inner_label.
Definition nested_outer_formula :
  @h_ty (Labels.EpsilonLabel Empty_set Datatypes.unit)
    Empty_set Datatypes.unit :=
  Ty_Atom tt (b_pair b_snd (b_comp inner_witness_over_x b_snd)).
Definition nested_outer_label : Labels.EpsilonLabel Empty_set Datatypes.unit :=
  Labels.epsilon_label b_S nested_outer_formula.
Definition nested_epsilon_term :
  @b_tm (Labels.EpsilonLabel Empty_set Datatypes.unit) Empty_set :=
  b_const b_S nested_outer_label.

Definition inner_formula_wellformed :
  @WellFormed (Labels.EpsilonLabel Empty_set Datatypes.unit)
    Empty_set Datatypes.unit nested_function_signature
    nested_predicate_signature (b_Prod b_S b_S) inner_formula.
Proof. apply WF_Atom. apply BT_Pair; [apply BT_Fst | apply BT_Snd]. Defined.

Definition nested_outer_formula_wellformed :
  @WellFormed (Labels.EpsilonLabel Empty_set Datatypes.unit)
    Empty_set Datatypes.unit nested_function_signature
    nested_predicate_signature (b_Prod b_Unit b_S) nested_outer_formula.
Proof.
  apply WF_Atom.
  apply BT_Pair.
  - apply BT_Snd.
  - eapply BT_Comp; [apply BT_Const | apply BT_Snd].
Defined.

Definition nested_epsilon_term_typing :
  @base_typing (Labels.EpsilonLabel Empty_set Datatypes.unit)
    Empty_set nested_function_signature b_Unit nested_epsilon_term b_S :=
  BT_Const.
Definition inner_label_rank : Labels.epsilon_rank inner_label = 1 := eq_refl.
Definition nested_outer_label_rank : Labels.epsilon_rank nested_outer_label = 2 := eq_refl.
End NestedEpsilonTerm.

Section PersonsExample.
Context {Sign Func Pred : Type}.
Context `{HFunc : FunctionSignature Func}.
Context `{HPred : PredicateSignature Pred}.
Variable r : Pred.
Hypothesis r_arity : pred_dom r = b_Prod b_S (b_Prod b_S b_S).

Definition persons_y : @b_tm Sign Func := b_fst.
Definition persons_x : @b_tm Sign Func := b_comp b_fst b_snd.
Definition persons_z : @b_tm Sign Func := b_comp b_snd b_snd.
Definition persons_permutation : @b_tm Sign Func :=
  b_pair persons_x (b_pair persons_y persons_z).

Definition persons_permutation_typing :
  base_typing (b_Prod b_S (b_Prod b_S b_S)) persons_permutation
    (b_Prod b_S (b_Prod b_S b_S)).
Proof.
  unfold persons_permutation, persons_x, persons_y, persons_z.
  apply BT_Pair.
  - eapply BT_Comp.
    + apply (BT_Fst (A:=b_S) (B:=b_S)).
    + apply (BT_Snd (A:=b_S) (B:=b_Prod b_S b_S)).
  - apply BT_Pair.
    + apply (BT_Fst (A:=b_S) (B:=b_Prod b_S b_S)).
    + eapply BT_Comp.
      * apply (BT_Snd (A:=b_S) (B:=b_S)).
      * apply (BT_Snd (A:=b_S) (B:=b_Prod b_S b_S)).
Defined.

Definition persons_under_binder_wellformed :
  WellFormed b_S (Ty_All (b_Prod b_S b_S)
    (Ty_Atom r persons_permutation)).
Proof.
  apply WF_All.
  apply WF_Atom.
  rewrite r_arity.
  exact persons_permutation_typing.
Defined.
End PersonsExample.

Section SubstitutionExamples.
Context {Sign Func Pred : Type}.
Context `{HFunc : FunctionSignature Func}.
Context `{HPred : PredicateSignature Pred}.
Context {SM : SkolemMapping Sign Func Pred}.

Definition free_bound_lift_typing
  (I J A : b_ty) (f : @b_tm Sign Func)
  (df : base_typing J f I) :
  base_typing (b_Prod J A) (b_subst_ext f) (b_Prod I A) :=
  typing_subst_ext df.

Definition free_bound_formula_wellformed
  (I J A : b_ty) (f : @b_tm Sign Func)
  (df : base_typing J f I) (Theta : @h_ty Sign Func Pred)
  (wf : WellFormed (b_Prod I A) Theta) :
  WellFormed (b_Prod J A) (form_subst (b_subst_ext f) Theta) :=
  wf_subst (b_subst_ext f) (typing_subst_ext df) Theta wf.

Definition free_bound_quantifier_substitution
  (I J A : b_ty) (f : @b_tm Sign Func)
  (Theta : @h_ty Sign Func Pred) :
  form_subst f (Ty_All A Theta) =
  Ty_All A (form_subst (b_subst_ext f) Theta) := eq_refl.

Definition free_bound_projection_equation
  (I J A : b_ty) (f : @b_tm Sign Func)
  (df : base_typing J f I) :
  base_equiv
    (BT_Comp (BT_Snd (A:=I) (B:=A)) (typing_subst_ext df))
    (BT_Snd (A:=J) (B:=A)).
Proof.
  unfold b_subst_ext.
  apply BE_BetaSnd.
Defined.

Definition conversion_along_equal_witnesses
  (I A : b_ty) (a b : @b_tm Sign Func)
  (da : base_typing I a A) (db : base_typing I b A)
  (eq_ab : base_equiv da db)
  (Phi : @h_ty Sign Func Pred)
  (wf : WellFormed (b_Prod I A) Phi) :
  form_equiv I
    (form_subst (b_pair b_id a) Phi)
    (form_subst (b_pair b_id b) Phi).
Proof.
  refine (@FE_Pullback_Cong Sign Func Pred HFunc HPred SM
    I (b_Prod I A) (b_pair b_id a) (b_pair b_id b) Phi
    (BT_Pair BT_Id da) (BT_Pair BT_Id db) _ wf).
  apply BE_CongPair.
  - apply BE_Refl.
  - exact eq_ab.
Defined.

Definition projection_epsilon_beck_chevalley
  (I A B : b_ty) (Phi : @h_ty Sign Func Pred)
  (wf : WellFormed (b_Prod I A) Phi) :
  form_equiv (b_Prod I B)
    (form_subst
      (b_pair b_id
        (b_const A (skolem_index A (form_subst (b_subst_ext b_fst) Phi))))
      (form_subst (b_subst_ext b_fst) Phi))
    (form_subst b_fst
      (form_subst (b_pair b_id (b_const A (skolem_index A Phi))) Phi)).
Proof.
  eapply FE_Eps_BC with (J:=I) (t:=b_fst).
  - apply (BT_Fst (A:=I) (B:=B)).
  - exact wf.
Defined.
End SubstitutionExamples.

Section ExistentialExamples.
Context {Sign Func Pred : Type}.
Context `{HFunc : FunctionSignature Func}.
Context `{HPred : PredicateSignature Pred}.
Context {SM : SkolemMapping Sign Func Pred}.
Variable I A : b_ty.
Variable Phi : @h_ty Sign Func Pred.
Variable wf_Phi : WellFormed (b_Prod I A) Phi.

Definition selected_formula : @h_ty Sign Func Pred :=
  form_subst (b_pair b_id (b_const A (skolem_index A Phi))) Phi.
Definition existence_to_selected_term : @h_tm Sign Func Pred :=
  tm_lam (Ty_Ex A Phi)
    (tm_ex_elim (tm_var 0) (tm_eps_intro b_snd (tm_var 0))).
Definition selected_to_existence_term : @h_tm Sign Func Pred :=
  tm_lam selected_formula
    (tm_ex_intro (b_const A (skolem_index A Phi)) (tm_var 0)).

Definition selected_to_existence_typing :
  h_derivation I [] selected_to_existence_term
    (Ty_Arrow selected_formula (Ty_Ex A Phi)).
Proof.
  unfold selected_to_existence_term, selected_formula.
  apply HD_Lam.
  eapply HD_Ex_Intro with (Phi:=Phi).
  - apply BT_Const.
  - apply HD_Var0.
    apply AWF_Cons.
    + eapply wf_subst with
        (t:=b_pair b_id (b_const A (skolem_index A Phi))).
      * exact (@BT_Pair Sign Func HFunc I I A b_id
          (b_const A (skolem_index A Phi)) BT_Id BT_Const).
      * exact wf_Phi.
    + apply AWF_Nil.
Defined.

Definition existence_to_selected_typing :
  h_derivation I [] existence_to_selected_term
    (Ty_Arrow (Ty_Ex A Phi) selected_formula).
Proof.
  unfold existence_to_selected_term, selected_formula.
  apply HD_Lam.
  eapply HD_Ex_Elim with (Phi:=Phi).
  - apply HD_Var0.
    apply AWF_Cons; [apply WF_Ex; exact wf_Phi | apply AWF_Nil].
  - eapply HD_Conv.
    + eapply HD_Eps_Intro with
        (Phi:=form_subst (b_subst_ext b_fst) Phi).
      * apply (BT_Snd (A:=I) (B:=A)).
      * eapply HD_Conv.
        -- apply HD_Var0.
           apply AWF_Cons.
           ++ exact wf_Phi.
           ++ apply AWF_Cons.
              ** eapply wf_subst.
                 --- apply (BT_Fst (A:=I) (B:=A)).
                 --- apply WF_Ex. exact wf_Phi.
              ** apply AWF_Nil.
        -- apply FE_Sym.
           apply FE_Pullback_Ext_Fst_Snd.
           exact wf_Phi.
    + eapply FE_Eps_BC with (J:=I) (t:=b_fst).
      * apply (BT_Fst (A:=I) (B:=A)).
      * exact wf_Phi.
Defined.

Definition represented_selection_witness_typing :
  base_typing I (b_const A (skolem_index A Phi)) A := BT_Const.

Definition represented_selection_from_existence
  (p : @h_tm Sign Func Pred)
  (d : h_derivation I [] p (Ty_Ex A Phi)) :
  h_derivation I [] p selected_formula.
Proof.
  eapply HD_Conv.
  - exact d.
  - apply FE_Eps_Adjoint_Iso. exact wf_Phi.
Defined.

Variable Psi : @h_ty Sign Func Pred.
Variable wf_Psi : WellFormed I Psi.
Definition existential_prenex_term : @h_tm Sign Func Pred :=
  tm_all_intro
    (tm_lam Phi
      (tm_app (tm_var 1) (tm_ex_intro b_snd (tm_var 0)))).

Definition existential_prenex_typing :
  h_derivation I [Ty_Arrow (Ty_Ex A Phi) Psi]
    existential_prenex_term
    (Ty_All A (Ty_Arrow Phi (form_subst b_fst Psi))).
Proof.
  unfold existential_prenex_term.
  apply HD_All_Intro.
  apply HD_Lam.
  eapply HD_App.
  - apply HD_VarS.
    + exact wf_Phi.
    + apply HD_Var0.
      apply AWF_Cons.
      * change (WellFormed (b_Prod I A)
          (form_subst b_fst (Ty_Arrow (Ty_Ex A Phi) Psi))).
        eapply wf_subst.
        -- apply (BT_Fst (A:=I) (B:=A)).
        -- apply WF_Arrow; [apply WF_Ex; exact wf_Phi | exact wf_Psi].
      * apply AWF_Nil.
  - eapply HD_Ex_Intro with (Phi:=form_subst (b_subst_ext b_fst) Phi).
    + apply (BT_Snd (A:=I) (B:=A)).
    + eapply HD_Conv.
      * apply HD_Var0.
        apply AWF_Cons.
        -- exact wf_Phi.
        -- apply AWF_Cons.
           ++ change (WellFormed (b_Prod I A)
                (form_subst b_fst (Ty_Arrow (Ty_Ex A Phi) Psi))).
              eapply wf_subst.
              ** apply (BT_Fst (A:=I) (B:=A)).
              ** apply WF_Arrow; [apply WF_Ex; exact wf_Phi | exact wf_Psi].
           ++ apply AWF_Nil.
      * apply FE_Sym.
        apply FE_Pullback_Ext_Fst_Snd.
        exact wf_Phi.
Defined.
End ExistentialExamples.
