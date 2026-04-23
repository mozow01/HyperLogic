(* ========================================================================= *)
(* Logic/Hyper/Epsilon/Critical_Epsilon_Provable.v                           *)
(* ========================================================================= *)

Require Import HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.

(* Import logical notations *)
Require Import HyperLogic.Logic.Hyper.Epsilon.Notations.

(* Import substitution lemmas (the "engine room") *)
Require Import HyperLogic.Logic.Hyper.Epsilon.Epsilon_Syntax_Lemmas.

Require Import List.
Import ListNotations.

Open Scope logic_scope.

(* ------------------------------------------------------------------------- *)
(* Terms and Base Morphisms                                                  *)
(* ------------------------------------------------------------------------- *)

(* 'var0' represents the top local variable, which categorically corresponds
   to the second projection (π₂) *)
Notation "'var0'" := π₂ : logic_scope.

(* ------------------------------------------------------------------------- *)
(* Definition of the "Dual Drinker" Paradox                                  *)
(* ------------------------------------------------------------------------- *)

(* The classic Drinker paradox is: ∃x (D(x) -> ∀y D(y)).
   Its dual is: ∃x ( (∃y D(y)) -> D(x) ).

   In our intuitionistic fibered system, the global statement (∃y) must be
   lifted to the local level (⇑) before it can form an implication with
   the local formula.
*)
Definition Dual_Drinker {Sign : Type} `{SkolemMapping Sign}
  (I D : b_ty) (Phi : @h_ty Sign) : @h_ty Sign :=
  ∃ D , ( (⇑ (∃ D , Phi)) ⇒ Phi ).

(* ------------------------------------------------------------------------- *)
(* Proof. Admitted.