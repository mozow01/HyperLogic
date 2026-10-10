(** The epsilon extension proves a translated iFOL formula that iFOL refutes. *)

Require Import List.
Import ListNotations.

Require Import HyperLogic.Semantics.IFOL.DualDrinker.
Require Import HyperLogic.Semantics.Metatheory.DualDrinker.
Require Import HyperLogic.Semantics.Metatheory.IFOL_EpsilonFull_Translation.

Module IBase := HyperLogic.Logic.Base.IFOL.Base_Syntax.
Module IHyper := HyperLogic.Logic.Hyper.IFOL.Hyper_Syntax.
Module IDD := HyperLogic.Semantics.IFOL.DualDrinker.
Module EBase := HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Module EHyper := HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.
Module EDD := HyperLogic.Semantics.Metatheory.DualDrinker.

Definition IFOL_DualDrinker :
  @IHyper.h_ty IDD.ifol_dd_func IDD.ifol_dd_pred :=
  IDD.ifol_dual_drinker_formula IBase.b_Unit.

Definition IFOL_DualDrinker_Derivation : Type :=
  { p : @IHyper.h_tm IDD.ifol_dd_func IDD.ifol_dd_pred &
    @IHyper.h_derivation IDD.ifol_dd_func IDD.ifol_dd_pred
      IDD.ifol_dd_function_signature IDD.ifol_dd_predicate_signature
      IBase.b_Unit nil p IFOL_DualDrinker }.

Definition IFOL_DualDrinker_Underivable : Type :=
  IFOL_DualDrinker_Derivation -> False.

Definition ifol_dual_drinker_not_derivable :
  IFOL_DualDrinker_Underivable :=
  IDD.ifol_dual_drinker_underivable_at_unit.

(* Compatibility name retained for users of the former Individual/iFOLFull path. *)
Definition ifolfull_dual_drinker_not_derivable :
  IFOL_DualDrinker_Underivable :=
  ifol_dual_drinker_not_derivable.

Definition EpsilonFull_DualDrinker {Sign : Type} :
  @EHyper.h_ty Sign IDD.ifol_dd_func IDD.ifol_dd_pred :=
  @ifol_to_epsilon_h_ty IDD.ifol_dd_func IDD.ifol_dd_pred Sign
    IFOL_DualDrinker.

Lemma translated_dual_drinker_is_epsilon_dual_drinker :
  forall Sign : Type,
    @EpsilonFull_DualDrinker Sign =
    @EDD.DualDrinkerFormula Sign IDD.ifol_dd_func IDD.ifol_dd_pred
      IDD.ifol_dd_predicate EBase.b_Unit EBase.b_S.
Proof.
  intro Sign.
  reflexivity.
Defined.

Section EpsilonProvability.
  Context {Sign : Type}.

  Local Instance translated_function_signature :
    EBase.FunctionSignature IDD.ifol_dd_func :=
    ifol_to_epsilon_function_signature
      IDD.ifol_dd_func IDD.ifol_dd_function_signature.

  Local Instance translated_predicate_signature :
    EHyper.PredicateSignature IDD.ifol_dd_pred :=
    ifol_to_epsilon_predicate_signature
      IDD.ifol_dd_pred IDD.ifol_dd_predicate_signature.

  Context `{ESkolem : EHyper.SkolemMapping
    Sign IDD.ifol_dd_func IDD.ifol_dd_pred}.

  Definition EpsilonFull_DualDrinker_Derivation : Type :=
    { q : @EHyper.h_tm Sign IDD.ifol_dd_func IDD.ifol_dd_pred &
      @EHyper.h_derivation Sign IDD.ifol_dd_func IDD.ifol_dd_pred
        translated_function_signature translated_predicate_signature ESkolem
        EBase.b_Unit nil q (@EpsilonFull_DualDrinker Sign) }.

  Definition epsilonfull_proves_translated_dual_drinker :
    EpsilonFull_DualDrinker_Derivation.
  Proof.
    unfold EpsilonFull_DualDrinker_Derivation.
    rewrite translated_dual_drinker_is_epsilon_dual_drinker.
    exact (@EDD.epsilonfull_dual_drinker_atom_provable
      Sign IDD.ifol_dd_func IDD.ifol_dd_pred
      translated_function_signature translated_predicate_signature ESkolem
      IDD.ifol_dd_predicate EBase.b_Unit EBase.b_S eq_refl).
  Defined.

  Definition epsilonfull_not_conservative_over_ifol :
    IFOL_DualDrinker_Underivable * EpsilonFull_DualDrinker_Derivation :=
    (ifol_dual_drinker_not_derivable,
     epsilonfull_proves_translated_dual_drinker).

  (* Compatibility name retained for the former module API. *)
  Definition epsilonfull_not_conservative_over_ifolfull :=
    epsilonfull_not_conservative_over_ifol.
End EpsilonProvability.
