(** Semantic entry points for the canonical epsilon-exists signature. *)

Require Import HyperLogic.Logic.Hyper.EpsilonFull.Canonical_Skolem.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_Soundness.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_Completeness.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_ModelCategory.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_AllPredicates.
Require Import HyperLogic.Semantics.EpsilonFull.FiniteHeytingPredicates.
Require Import HyperLogic.Semantics.EpsilonFull.Canonical_FiniteChain_Model.

Module CanonicalEpsilonFullSemantics.

Module Labels :=
  HyperLogic.Logic.Hyper.EpsilonFull.Canonical_Skolem.CanonicalEpsilonFull.
Module Base := HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Module Hyper := HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.
Module Fibration := HyperLogic.Semantics.EpsilonFull.EpsilonFull_Fibration.
Module Soundness := HyperLogic.Semantics.EpsilonFull.EpsilonFull_Soundness.
Module Completeness := HyperLogic.Semantics.EpsilonFull.EpsilonFull_Completeness.
Module Models := HyperLogic.Semantics.EpsilonFull.EpsilonFull_ModelCategory.
Module AllPredicates :=
  HyperLogic.Semantics.EpsilonFull.EpsilonFull_AllPredicates.
Module FinitePredicates :=
  HyperLogic.Semantics.EpsilonFull.FiniteHeytingPredicates.
Module FiniteChainModels :=
  HyperLogic.Semantics.EpsilonFull.Canonical_FiniteChain_Model.

Definition Sign (Func Pred : Type) : Type :=
  Labels.EpsilonLabel Func Pred.

Definition SkolemMapping (Func Pred : Type) :
  Hyper.SkolemMapping (Sign Func Pred) Func Pred :=
  Labels.CanonicalSkolemMapping Func Pred.

Section CanonicalSemantics.

Context {Func Pred : Type}.
Context `{HFunc : Base.FunctionSignature Func}.
Context `{HPred : Hyper.PredicateSignature Pred}.

Definition Model : Type :=
  @Models.EpsilonFullModel (Sign Func Pred) Func Pred
    HFunc HPred (SkolemMapping Func Pred).

Definition TermModel : Model :=
  @Models.TermModel_EpsilonFullModel (Sign Func Pred) Func Pred
    HFunc HPred (SkolemMapping Func Pred).

Definition soundness :=
  @Soundness.soundness (Sign Func Pred) Func Pred
    HFunc HPred (SkolemMapping Func Pred).

Definition completeness :=
  @Completeness.epsilon_adjoint_completeness_inhabitational_gen
    (Sign Func Pred) Func Pred HFunc HPred (SkolemMapping Func Pred).

Definition all_predicate_valid :=
  @AllPredicates.all_predicate_epsilonfull_valid
    (Sign Func Pred) Func Pred HFunc HPred (SkolemMapping Func Pred).

Definition all_predicate_soundness_completeness :=
  @AllPredicates.all_predicate_epsilonfull_soundness_completeness
    (Sign Func Pred) Func Pred HFunc HPred (SkolemMapping Func Pred).

Definition TermModel_all_predicate_model :=
  @AllPredicates.TermModel_AllPredicateEpsilonFullModel
    (Sign Func Pred) Func Pred HFunc HPred (SkolemMapping Func Pred).

Definition TermModel_to (M : Model) :
  @Models.EpsilonFullModelHom (Sign Func Pred) Func Pred
    HFunc HPred (SkolemMapping Func Pred) TermModel M :=
  @Models.TermModel_to (Sign Func Pred) Func Pred
    HFunc HPred (SkolemMapping Func Pred) M.

(* These are exactly the existing weak existence and morphism-level
   uniqueness results; this module does not strengthen the model morphisms. *)
Definition TermModel_weak_initial :
  forall M : Model,
    inhabited
      (@Models.EpsilonFullModelHom (Sign Func Pred) Func Pred
        HFunc HPred (SkolemMapping Func Pred) TermModel M) :=
  @Models.TermModel_weak_initial (Sign Func Pred) Func Pred
    HFunc HPred (SkolemMapping Func Pred).

Definition TermModel_initial_unique :
  forall (M : Model)
    (F G : @Models.EpsilonFullModelHom (Sign Func Pred) Func Pred
      HFunc HPred (SkolemMapping Func Pred) TermModel M),
    @Models.EpsilonFullModelHom_equiv (Sign Func Pred) Func Pred
      HFunc HPred (SkolemMapping Func Pred) TermModel M F G :=
  @Models.TermModel_initial_unique (Sign Func Pred) Func Pred
    HFunc HPred (SkolemMapping Func Pred).

End CanonicalSemantics.

End CanonicalEpsilonFullSemantics.
