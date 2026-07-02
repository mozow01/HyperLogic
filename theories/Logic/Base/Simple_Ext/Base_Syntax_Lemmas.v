(* Logic/Base/Simple_Ext/Base_Syntax_Lemmas.v *)

Require Import Setoid.
Require Import Relation_Definitions.
Require Import Morphisms.  
 
Require Import HyperLogic.Logic.Base.Epsilon_Adjoint.Base_Syntax.

Require Import Coq.Program.Equality.

Lemma base_typing_unique : forall {Sign : Type}
  {I : b_ty} {t : @b_tm Sign} {A1 A2 : b_ty},
  base_typing I t A1 ->
  base_typing I t A2 ->
  A1 = A2.
Proof.
  intros Sign I t A1 A2 d1.
  revert A2.
  induction d1; intros A2 d2; dependent destruction d2.
  - reflexivity.

  - (* BT_Comp *)
    match goal with
    | Hf1 : base_typing A f B,
      Hf2 : base_typing A f ?B0,
      Hg1 : base_typing B g C,
      Hg2 : base_typing ?B0 g ?C0 |- C = ?C0 =>
        assert (HB : B = B0)
          by (eapply IHd1_2; exact Hf2);
        subst B0;
        eapply IHd1_1;
        exact Hg2
    end.

  - reflexivity.

  - (* BT_Pair *)
    match goal with
    | Hf1 : base_typing A f B,
      Hf2 : base_typing A f ?B0,
      Hg1 : base_typing A g C,
      Hg2 : base_typing A g ?C0 |- b_Prod B C = b_Prod ?B0 ?C0 =>
        assert (HB : B = B0)
          by (eapply IHd1_1; exact Hf2);
        assert (HC : C = C0)
          by (eapply IHd1_2; exact Hg2);
        subst;
        reflexivity
    end.

  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

Lemma decide_base_typing : forall {Sign : Type} (I : b_ty) (t : @b_tm Sign),
  sum { A : b_ty & base_typing I t A }
      (forall A : b_ty, base_typing I t A -> Empty_set).
Proof.
  intros Sign I t.
  revert I.

  induction t as
    [ (* b_id *)
    | g IHg f IHf
    | (* b_unit *)
    | f IHf g IHg
    | (* b_fst *)
    | (* b_snd *)
    | A s
    ];
    intro I.

  - (* b_id *)
    left.
    exists I.
    apply BT_Id.

    - (* b_comp g f *)
    destruct (IHf I) as [[B df] | Hbad_f].
    + destruct (IHg B) as [[C dg] | Hbad_g].
      * left.
        exists C.
        eapply BT_Comp.
        -- exact dg.
        -- exact df.

      * right.
        intros C Hcomp.
        dependent destruction Hcomp.
        assert (HB : B0 = B).
        {
          eapply base_typing_unique.
          - exact Hcomp2.
          - exact df.
        }
        subst B0.
        (* exact (Hbad_g C H) *)
        apply Hbad_g with (A:=C). exact Hcomp1.

    + right.
      intros C Hcomp.
      dependent destruction Hcomp.
      apply Hbad_f with (A:=B). exact Hcomp2.
      
  - (* b_unit *)
    left.
    exists b_Unit.
    apply BT_Unit.

    - (* b_pair f g *)
    destruct (IHf I) as [[B df] | Hbad_f].
    + destruct (IHg I) as [[C dg] | Hbad_g].
      * left.
        exists (b_Prod B C).
        eapply BT_Pair.
        -- exact df.
        -- exact dg.

      * right.
        intros D Hpair.
        dependent destruction Hpair.
        apply Hbad_g with (A:=C). exact Hpair2.
        

    + right.
      intros D Hpair.
      dependent destruction Hpair.
      apply Hbad_f with (A:=B). exact Hpair1.
     
  - (* b_fst *)
    destruct I as [| | A B].
    + right.
      intros C H.
      dependent destruction H.
    + right.
      intros C H.
      dependent destruction H.
    + left.
      exists A.
      apply BT_Fst.

  - (* b_snd *)
    destruct I as [| | A B].
    + right.
      intros C H.
      dependent destruction H.
    + right.
      intros C H.
      dependent destruction H.
    + left.
      exists B.
      apply BT_Snd.

  - (* b_const A s *)
    left.
    exists A.
    apply BT_Const.
Defined.