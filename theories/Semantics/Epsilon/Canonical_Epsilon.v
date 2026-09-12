(* Semantic entry points for the canonical epsilon-only signature. *)

Require Import HyperLogic.Logic.Hyper.Epsilon.Canonical_Skolem.
Require Import HyperLogic.Semantics.Epsilon.Epsilon_Soundness.
Require Import HyperLogic.Semantics.Epsilon.Epsilon_Completeness.

Module CanonicalEpsilonSemantics.

Module Labels :=
  HyperLogic.Logic.Hyper.Epsilon.Canonical_Skolem.CanonicalEpsilon.
Module Base := HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Module Hyper := HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.
Module Soundness := HyperLogic.Semantics.Epsilon.Epsilon_Soundness.
Module Completeness := HyperLogic.Semantics.Epsilon.Epsilon_Completeness.

Definition Sign (Func Pred : Type) : Type :=
  Labels.EpsilonLabel Func Pred.

Definition SkolemMapping (Func Pred : Type) :
  Hyper.SkolemMapping (Sign Func Pred) Func Pred :=
  Labels.CanonicalSkolemMapping Func Pred.

Section CanonicalSemantics.

Context {Func Pred : Type}.
Context `{HFunc : Base.FunctionSignature Func}.
Context `{HPred : Hyper.PredicateSignature Pred}.

Definition soundness :=
  @Soundness.soundness (Sign Func Pred) Func Pred
    HFunc HPred (SkolemMapping Func Pred).

Definition completeness :=
  @Completeness.epsilon_completeness_inhabitational_gen
    (Sign Func Pred) Func Pred HFunc HPred (SkolemMapping Func Pred).

Definition TermModel_GoodFibration :=
  @Completeness.TermModel_GoodFibration
    (Sign Func Pred) Func Pred HFunc HPred (SkolemMapping Func Pred).

Definition TermModel_StrictGoodFibration :=
  @Completeness.TermModel_StrictGoodFibration
    (Sign Func Pred) Func Pred HFunc HPred (SkolemMapping Func Pred).

Definition TermModel_EpsilonHyperModel :=
  @Completeness.TermModel_EpsilonHyperModel
    (Sign Func Pred) Func Pred HFunc HPred (SkolemMapping Func Pred).

Definition TermModel_EpsilonGoodFibration :=
  @Completeness.TermModel_EpsilonGoodFibration
    (Sign Func Pred) Func Pred HFunc HPred (SkolemMapping Func Pred).

End CanonicalSemantics.

End CanonicalEpsilonSemantics.
