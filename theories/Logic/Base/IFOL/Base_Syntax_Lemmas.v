(** Structural lemmas for the epsilon-free iFOL base syntax. *)

Require Import Coq.Program.Equality.
Require Import HyperLogic.Logic.Base.IFOL.Base_Syntax.

Lemma base_typing_unique : forall {Func : Type} `{FunctionSignature Func}
  {I : b_ty} {t : @b_tm Func} {A1 A2 : b_ty},
  base_typing I t A1 -> base_typing I t A2 -> A1 = A2.
Proof.
  intros Func H I t A1 A2 d1.
  revert A2.
  induction d1; intros A2 d2; dependent destruction d2.
  - reflexivity.
  - match goal with
    | Hf1 : base_typing A f B,
      Hf2 : base_typing A f ?B0,
      Hg2 : base_typing ?B0 g ?C0 |- C = ?C0 =>
        assert (HB : B = B0) by (eapply IHd1_2; exact Hf2);
        subst B0;
        eapply IHd1_1;
        exact Hg2
    end.
  - reflexivity.
  - match goal with
    | Hf1 : base_typing A f B,
      Hf2 : base_typing A f ?B0,
      Hg1 : base_typing A g C,
      Hg2 : base_typing A g ?C0 |- b_Prod B C = b_Prod ?B0 ?C0 =>
        assert (HB : B = B0) by (eapply IHd1_1; exact Hf2);
        assert (HC : C = C0) by (eapply IHd1_2; exact Hg2);
        subst;
        reflexivity
    end.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

Lemma decide_base_typing : forall {Func : Type} `{FunctionSignature Func}
  (I : b_ty) (t : @b_tm Func),
  sum { A : b_ty & base_typing I t A }
      (forall A : b_ty, base_typing I t A -> Empty_set).
Proof.
  intros Func H I t.
  revert I.
  induction t as [|g IHg f IHf| |f IHf g IHg| | | sym]; intro I.
  - left. exists I. apply BT_Id.
  - destruct (IHf I) as [[B df]|Hbad_f].
    + destruct (IHg B) as [[C dg]|Hbad_g].
      * left. exists C. now apply (BT_Comp dg df).
      * right. intros C Hcomp. dependent destruction Hcomp.
        assert (HB : B0 = B) by (eapply base_typing_unique; [exact Hcomp2|exact df]).
        subst B0. apply (Hbad_g C). exact Hcomp1.
    + right. intros C Hcomp. dependent destruction Hcomp.
      apply (Hbad_f B). exact Hcomp2.
  - left. exists b_Unit. apply BT_Unit.
  - destruct (IHf I) as [[B df]|Hbad_f].
    + destruct (IHg I) as [[C dg]|Hbad_g].
      * left. exists (b_Prod B C). now apply (BT_Pair df dg).
      * right. intros D Hpair. dependent destruction Hpair.
        apply (Hbad_g C). exact Hpair2.
    + right. intros D Hpair. dependent destruction Hpair.
      apply (Hbad_f B). exact Hpair1.
  - destruct I as [| | A B].
    + right. intros C Htyp. dependent destruction Htyp.
    + right. intros C Htyp. dependent destruction Htyp.
    + left. exists A. apply BT_Fst.
  - destruct I as [| | A B].
    + right. intros C Htyp. dependent destruction Htyp.
    + right. intros C Htyp. dependent destruction Htyp.
    + left. exists B. apply BT_Snd.
  - destruct (b_ty_eq_dec I (func_dom sym)) as [HI|HI].
    + subst I. left. exists (func_cod sym). apply BT_Func.
    + right. intros A Hfunc. dependent destruction Hfunc.
      destruct (HI eq_refl).
Defined.
