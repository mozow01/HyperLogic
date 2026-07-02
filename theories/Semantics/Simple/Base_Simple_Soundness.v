(* Semantics/Simple/Base_Simple_Soundness.v  *)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Eqdep_dec.
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.Fibration.
Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.

(* ================================================================= *)
(* 1. INTERPRETATION OF TYPES AND MORPHISMS                          *)
(* ================================================================= *)

Fixpoint interp_ty {C : SetoidCategory} {CC : CartesianCategory C} 
  {TSC : TwoSortCategory C} (A : b_ty) : @obj C :=
  match A with
  | b_Unit => terminal
  | b_S => S TSC
  | b_Prod A1 A2 => prod (interp_ty A1) (interp_ty A2)
  end.

Fixpoint interp_tm {C : SetoidCategory} {CC : CartesianCategory C} 
  {TSC : TwoSortCategory C} {A B : b_ty} {f : b_tm} (d : base_typing A f B) 
  : hom (interp_ty A) (interp_ty B) :=
  match d with
  | BT_Id => id _
  | BT_Comp dg dh => compose (interp_tm dg) (interp_tm dh)
  | BT_Unit => terminal_map
  | BT_Pair d1 d2 => prod_map (interp_tm d1) (interp_tm d2)
  | BT_Fst => prod_fst
  | BT_Snd => prod_snd
  end.

(* ================================================================= *)
(* 2. AXIOM-FREE PROOF IRRELEVANCE FOR DERIVATIONS                   *)
(* ================================================================= *)

(* 1. Decidable Equality for Types and Terms *)
Lemma b_ty_eq_dec : forall A B : b_ty, {A = B} + {A <> B}.
Proof. decide equality. Qed.

Lemma b_tm_eq_dec : forall f g : b_tm, {f = g} + {f <> g}.
Proof. decide equality. Qed.

(* 2. We pack all three indices into a single index type *)
Definition b_index := (b_ty * b_tm * b_ty)%type.

Lemma b_index_eq_dec : forall x y : b_index, {x = y} + {x <> y}.
Proof. 
  intros x y.
  decide equality.
  - (* Goal 1: The right-most element (b_ty) *)
    apply b_ty_eq_dec.
  - (* Goal 2: The left tuple (b_ty * b_tm) *)
    decide equality.
    + (* Goal 2.1: The right element of the left tuple (b_tm) *)
      apply b_tm_eq_dec.
    + (* Goal 2.2: The left element of the left tuple (b_ty) *)
      apply b_ty_eq_dec.
Qed.

Definition base_typing_idx (idx : b_index) : Set :=
  match idx with (A, f, B) => base_typing A f B end.

(* We pack the derivation and its free indices together *)
Definition bt_pack := { idx : b_index & base_typing_idx idx }.

(* 3. The Decoupled Induction: Destructs safely because the indices are 100% free! *)
Lemma bt_pack_pi : forall (p1 p2 : bt_pack), projT1 p1 = projT1 p2 -> p1 = p2.
Proof.
  intros [ [ [A1 f1] B1 ] d1 ].
  (* We induct on d1, then bring in d2 and its completely free variables *)
  induction d1; intros [ [ [A2 f2] B2 ] d2 ] Heq; 
  destruct d2; inversion Heq; subst; clear Heq;
  
  (* 1. Force Coq to fully unpack the syntax tree equalities so g=g0 and f=f0! *)
  repeat match goal with
  | [ H : b_comp _ _ = b_comp _ _ |- _ ] => inversion H; subst; clear H
  | [ H : b_pair _ _ = b_pair _ _ |- _ ] => inversion H; subst; clear H
  end;
  try reflexivity.
  
  - (* BT_Comp *)
    assert (Hmid : B = B0) by (eapply base_typing_unique; [exact d1_2 | exact d2_2]).
    subst B0.
    
    (* 2. Dynamically bind the exact variables Coq is currently using! *)
    match type of d1_1 with
    | base_typing ?B_ ?g_ ?C_ =>
        assert (H1 : existT base_typing_idx (B_, g_, C_) d1_1 = existT base_typing_idx (B_, g_, C_) d2_1)
          by (apply (IHd1_1 (existT base_typing_idx (B_, g_, C_) d2_1)); reflexivity);
        apply (inj_pair2_eq_dec _ b_index_eq_dec) in H1
    end.
    
    match type of d1_2 with
    | base_typing ?A_ ?f_ ?B_ =>
        assert (H2 : existT base_typing_idx (A_, f_, B_) d1_2 = existT base_typing_idx (A_, f_, B_) d2_2)
          by (apply (IHd1_2 (existT base_typing_idx (A_, f_, B_) d2_2)); reflexivity);
        apply (inj_pair2_eq_dec _ b_index_eq_dec) in H2
    end.
    
    subst. reflexivity.
    
  - (* BT_Pair *)
    match type of d1_1 with
    | base_typing ?A_ ?f_ ?B_ =>
        assert (H1 : existT base_typing_idx (A_, f_, B_) d1_1 = existT base_typing_idx (A_, f_, B_) d2_1)
          by (apply (IHd1_1 (existT base_typing_idx (A_, f_, B_) d2_1)); reflexivity);
        apply (inj_pair2_eq_dec _ b_index_eq_dec) in H1
    end.
    
    match type of d1_2 with
    | base_typing ?A_ ?g_ ?C_ =>
        assert (H2 : existT base_typing_idx (A_, g_, C_) d1_2 = existT base_typing_idx (A_, g_, C_) d2_2)
          by (apply (IHd1_2 (existT base_typing_idx (A_, g_, C_) d2_2)); reflexivity);
        apply (inj_pair2_eq_dec _ b_index_eq_dec) in H2
    end.
    
    subst. reflexivity.
Qed.

(* 4. The Final Pure Gallina PI Lemma! *)
Lemma base_typing_pi : forall A B f (d1 d2 : base_typing A f B), d1 = d2.
Proof.
  intros A B f d1 d2.
  assert (H : existT base_typing_idx (A, f, B) d1 = existT base_typing_idx (A, f, B) d2).
  { apply (bt_pack_pi (existT base_typing_idx (A, f, B) d1) (existT base_typing_idx (A, f, B) d2)). reflexivity. }
  apply (inj_pair2_eq_dec _ b_index_eq_dec) in H.
  exact H.
Qed.

(* This lemma allows us to mathematically cast any semantic interpretation! *)
Lemma interp_tm_cast : forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {A B f} (d1 d2 : base_typing A f B), @interp_tm C CC TSC A B f d1 ≅ interp_tm d2.
Proof.
  intros. assert (H : d1 = d2) by apply base_typing_pi; subst; reflexivity.
Qed.

(* Because BE_Refl requires a derivation, base_equiv strictly preserves typeability! 
   We wrap the return type in 'inhabited' so it stays in Prop, bypassing the elimination restriction! *)
Lemma base_equiv_type_preservation : forall A B f g,
  base_equiv A B f g -> inhabited (base_typing A f B * base_typing A g B).
Proof.
  intros A B f g Heq. induction Heq.
  - constructor. split; exact df.
  - destruct IHHeq as [[df' dg']]. constructor. split; assumption.
  - destruct IHHeq1 as [[df1 dg1]]. destruct IHHeq2 as [[df2 dg2]]. 
    constructor. split; assumption.
  - destruct IHHeq1 as [[dg1 dg1']]. destruct IHHeq2 as [[df1 df1']].
    constructor. split.
    + eapply BT_Comp; eauto.
    + eapply BT_Comp; eauto.
  - destruct IHHeq1 as [[df1 df1']]. destruct IHHeq2 as [[dg1 dg1']].
    constructor. split.
    + eapply BT_Pair; eauto.
    + eapply BT_Pair; eauto.
  - constructor. split. eapply BT_Comp; [apply BT_Id | exact df]. exact df.
  - constructor. split. eapply BT_Comp; [exact df | apply BT_Id]. exact df.
  - constructor. split.
    + eapply BT_Comp. exact dh. eapply BT_Comp. exact dg. exact df.
    + eapply BT_Comp. eapply BT_Comp. exact dh. exact dg. exact df.
  - constructor. split. eapply BT_Comp; [eapply BT_Fst | apply BT_Pair; [exact df | exact dg]]. exact df.
  - constructor. split. eapply BT_Comp; [eapply BT_Snd | apply BT_Pair; [exact df | exact dg]]. exact dg.
  - constructor. split. eapply BT_Pair; [ eapply BT_Comp; [eapply BT_Fst | exact df] | eapply BT_Comp; [eapply BT_Snd | exact df] ]. exact df.
  - constructor. split; assumption.
Qed.

(* ================================================================= *)
(* 3. SOUNDNESS THEOREMS                                             *)
(* ================================================================= *)

Theorem base_soundness_inhabitational : forall {C : SetoidCategory} {CC : CartesianCategory C} 
  {TSC : TwoSortCategory C} {A B : b_ty},
  (exists (t : b_tm), inhabited (base_typing A t B)) -> 
  inhabited (hom (interp_ty A) (interp_ty B)).
Proof.
  intros C CC TSC A B [t [d]]. constructor. exact (interp_tm d).
Defined.

Theorem base_soundness_equational : forall {C : SetoidCategory} {CC : CartesianCategory C} 
  {TSC : TwoSortCategory C} {A B : b_ty} {f g : b_tm} 
  (df_goal : base_typing A f B) (dg_goal : base_typing A g B),
  base_equiv A B f g -> interp_tm df_goal ≅ interp_tm dg_goal.
Proof.
  intros C CC TSC A B f g df_goal dg_goal Heq.
  revert df_goal dg_goal.
  induction Heq; intros df_goal dg_goal.
  
  - (* BE_Refl *) 
    apply interp_tm_cast.
  - (* BE_Sym *) 
    symmetry. apply IHHeq.
  - (* BE_Trans *) 
    (* Because our goal (≅) is in Prop, Coq legally lets us destruct the inhabited Prop! *)
    destruct (base_equiv_type_preservation _ _ _ _ Heq1) as [[df_mid dg_mid]].
    eapply transitivity.
    + apply IHHeq1 with (dg_goal := dg_mid).
    + apply IHHeq2 with (df_goal := dg_mid).
  - (* BE_CongComp *)
    destruct (base_equiv_type_preservation _ _ _ _ Heq1) as [[dg_axiom dg'_axiom]].
    destruct (base_equiv_type_preservation _ _ _ _ Heq2) as [[df_axiom df'_axiom]].
    eapply transitivity. { apply (interp_tm_cast df_goal (BT_Comp dg_axiom df_axiom)). }
    eapply transitivity. 2: { symmetry. apply (interp_tm_cast dg_goal (BT_Comp dg'_axiom df'_axiom)). }
    simpl. rewrite (IHHeq1 dg_axiom dg'_axiom). rewrite (IHHeq2 df_axiom df'_axiom). reflexivity.
  - (* BE_CongPair *)
    destruct (base_equiv_type_preservation _ _ _ _ Heq1) as [[df_axiom df'_axiom]].
    destruct (base_equiv_type_preservation _ _ _ _ Heq2) as [[dg_axiom dg'_axiom]].
    eapply transitivity. { apply (interp_tm_cast df_goal (BT_Pair df_axiom dg_axiom)). }
    eapply transitivity. 2: { symmetry. apply (interp_tm_cast dg_goal (BT_Pair df'_axiom dg'_axiom)). }
    simpl. rewrite (IHHeq1 df_axiom df'_axiom). rewrite (IHHeq2 dg_axiom dg'_axiom). reflexivity.
  - (* BE_IdL *)
    eapply transitivity. { apply (interp_tm_cast df_goal (BT_Comp BT_Id df)). }
    eapply transitivity. 2: { symmetry. apply (interp_tm_cast dg_goal df). }
    simpl. apply id_left.
  - (* BE_IdR *)
    eapply transitivity. { apply (interp_tm_cast df_goal (BT_Comp df BT_Id)). }
    eapply transitivity. 2: { symmetry. apply (interp_tm_cast dg_goal df). }
    simpl. apply id_right.
  - (* BE_Assoc *)
    eapply transitivity. { apply (interp_tm_cast df_goal (BT_Comp dh (BT_Comp dg df))). }
    eapply transitivity. 2: { symmetry. apply (interp_tm_cast dg_goal (BT_Comp (BT_Comp dh dg) df)). }
    simpl. apply comp_assoc.
  - (* BE_BetaFst *)
    eapply transitivity. { apply (interp_tm_cast df_goal (BT_Comp BT_Fst (BT_Pair df dg))). }
    eapply transitivity. 2: { symmetry. apply (interp_tm_cast dg_goal df). }
    simpl. apply prod_map_fst.
  - (* BE_BetaSnd *)
    eapply transitivity. { apply (interp_tm_cast df_goal (BT_Comp BT_Snd (BT_Pair df dg))). }
    eapply transitivity. 2: { symmetry. apply (interp_tm_cast dg_goal dg). }
    simpl. apply prod_map_snd.
  - (* BE_EtaPair *)
    eapply transitivity. { apply (interp_tm_cast df_goal (BT_Pair (BT_Comp BT_Fst df) (BT_Comp BT_Snd df))). }
    eapply transitivity. 2: { symmetry. apply (interp_tm_cast dg_goal df). }
    simpl. apply prod_eta.
  - (* BE_Terminal *)
    eapply transitivity. { apply terminal_map_unique. }
    symmetry. apply terminal_map_unique.
Qed.