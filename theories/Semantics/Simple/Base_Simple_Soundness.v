Require Import Coq.Classes.Morphisms.
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.Fibration.
Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.

(* ================================================================= *)
(* 1. INTERPRETATION OF TYPES (OBJECTS)                              *)
(* ================================================================= *)

(** Maps a syntactic base type [b_ty] to a semantic object in a Cartesian Category [C].
    The individual sort [b_S] is mapped to the distinguished object [S] from [TwoSortCategory]. *)
Fixpoint interp_ty {C : SetoidCategory} {CC : CartesianCategory C} 
  {TSC : TwoSortCategory C} (A : b_ty) : @obj C :=
  match A with
  | b_Unit => terminal
  | b_S => S TSC
  | b_Prod A1 A2 => prod (interp_ty A1) (interp_ty A2)
  end.

(* ================================================================= *)
(* 2. INTERPRETATION OF MORPHISMS (DERIVATIONS)                      *)
(* ================================================================= *)

(** Maps a valid base typing derivation [base_typing A f B] to a semantic morphism 
    [hom (interp_ty A) (interp_ty B)] in the category [C]. *)
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
(* 3. SOUNDNESS THEOREMS                                             *)
(* ================================================================= *)

(** Inhabitational Soundness for Base
    If there exists a base term [t] such that the typing [base_typing A t B] is inhabited, then the semantic hom-set [hom (interp_ty A) (interp_ty B)] is also inhabited. *)
Theorem base_soundness_inhabitational : forall {C : SetoidCategory} {CC : CartesianCategory C} 
  {TSC : TwoSortCategory C} {A B : b_ty},
  (exists (t : b_tm), inhabited (base_typing A t B)) -> 
  inhabited (hom (interp_ty A) (interp_ty B)).
Proof.
  intros C CC TSC A B [t [d]].
  constructor.
  exact (interp_tm d).
Defined.

(** Equational Soundness for Base
    If two syntactic typing derivations are syntactically equivalent ([base_equiv]), then their semantic interpretations are equal as morphisms in the category [C]. *)
Theorem base_soundness_equational : forall {C : SetoidCategory} {CC : CartesianCategory C} 
  {TSC : TwoSortCategory C} {A B : b_ty} {f g : b_tm} 
  (df : base_typing A f B) (dg : base_typing A g B),
  base_equiv df dg -> interp_tm df ≅ interp_tm dg.
Proof.
  intros C CC TSC A B f g df dg Heq.
  induction Heq; simpl.
  
  - (* BE_Refl *) reflexivity.
  - (* BE_Sym *) symmetry; assumption.
  - (* BE_Trans *) etransitivity; eassumption.
  - (* BE_CongComp *) rewrite IHHeq1, IHHeq2. reflexivity.
  - (* BE_CongPair *) rewrite IHHeq1, IHHeq2. reflexivity.
  - (* BE_Assoc *) apply comp_assoc.
  - (* BE_IdL *) apply id_left.
  - (* BE_IdR *) apply id_right.
  - (* BE_BetaFst *) apply prod_map_fst.
  - (* BE_BetaSnd *) apply prod_map_snd.
  - (* BE_EtaPair *) apply prod_eta.
  - (* BE_EtaUnit *) apply terminal_map_unique.  
Defined.