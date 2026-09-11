(* theories/Semantics/IFOL/Base_IFOL_Soundness.v *)

Require Import Coq.Classes.Morphisms.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.Fibration.

Require Import HyperLogic.Logic.Base.IFOL.Base_Syntax.
Require Import HyperLogic.Semantics.IFOL.IFOL_Fibration.

(* ================================================================= *)
(* Soundness theorems for the iFOL base syntax. *)
(* ================================================================= *)

Theorem base_soundness_inhabitational :
  forall {Func : Type} `{HFunc : FunctionSignature Func}
    {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
    {BEM : @BaseIFOLModel Func HFunc C CC TSC} {A B : b_ty},
  (exists (t : @b_tm Func), inhabited (base_typing A t B)) ->
  inhabited (hom (interp_ty A) (interp_ty B)).
Proof.
  intros Func HFunc C CC TSC BEM A B [t [d]].
  constructor.
  exact (interp_tm d).
Defined.

Theorem base_soundness_equational :
  forall {Func : Type} `{HFunc : FunctionSignature Func}
    {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
    {BEM : @BaseIFOLModel Func HFunc C CC TSC}
    {CBM : @CoherentBaseIFOLModel Func HFunc C CC TSC BEM}
    {A B : b_ty} {f g : @b_tm Func}
    (df : base_typing A f B) (dg : base_typing A g B),
  base_equiv_typed A B f g -> interp_tm df ≅ interp_tm dg.
Proof.
  intros Func HFunc C CC TSC BEM CBM A B f g df dg [df' [dg' Heq_base]].

  transitivity (interp_tm df').
  { apply interp_coh. }

  transitivity (interp_tm dg').
  2:{ apply interp_coh. }

  clear df dg.
  induction Heq_base; simpl.
  - apply interp_coh.
  - symmetry. exact IHHeq_base.
  - etransitivity.
    + exact IHHeq_base1.
    + exact IHHeq_base2.
  - rewrite IHHeq_base1, IHHeq_base2. reflexivity.
  - rewrite IHHeq_base1, IHHeq_base2. reflexivity.
  - apply comp_assoc.
  - apply id_left.
  - apply id_right.
  - apply prod_map_fst.
  - apply prod_map_snd.
  - apply prod_eta.
  - apply terminal_map_unique.
  - symmetry. apply compos_prod.
Defined.
