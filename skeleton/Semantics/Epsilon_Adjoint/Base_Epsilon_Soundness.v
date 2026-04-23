(* theories/Semantics/Epsilon_Adjoint/Base_Epsilon_Soundness.v *)

Require Import Coq.Classes.Morphisms.

(* Kategóriaelméleti alapok *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.Fibration.

(* Szintaxis és Fibráció (Epsilon Adjoint) *)
Require Import HyperLogic.Logic.Base.Epsilon_Adjoint.Base_Syntax.
Require Import HyperLogic.Semantics.Epsilon_Adjoint.Epsilon_Adjoint_Fibration.

(* ================================================================= *)
(* SOUNDNESS TÉTELEK A BÁZISHOZ (Epsilon Adjoint)                    *)
(* ================================================================= *)

(** Inhabitational Soundness
    Ha létezik egy szintaktikus term, akkor a szemantikai hom-halmaz sem üres. *)
Theorem base_soundness_inhabitational :
  forall {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C}
  {TSC : TwoSortCategory C} {BEM : @BaseEpsilonModel Sign C CC TSC} {A B : b_ty},
  (exists (t : @b_tm Sign), inhabited (base_typing A t B)) ->
  inhabited (hom (interp_ty A) (interp_ty B)).
Proof. Admitted.

(** Equational Soundness
    Ha két szintaktikus levezetés ekvivalens (base_equiv), akkor a
    szemantikai interpretációjuk morfizmusként izomorf (≅) a C kategóriában. *)
Theorem base_soundness_equational :
  forall {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C}
  {TSC : TwoSortCategory C} {BEM : @BaseEpsilonModel Sign C CC TSC}
  {A B : b_ty} {f g : @b_tm Sign}
  (df : base_typing A f B) (dg : base_typing A g B),
  base_equiv df dg -> interp_tm df ≅ interp_tm dg.
Proof. Admitted.