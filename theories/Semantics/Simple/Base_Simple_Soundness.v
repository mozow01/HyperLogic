Require Import Coq.Classes.Morphisms.

(* A te kategória-könyvtáraid *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.Fibration. (* Innen jön a TwoSortCategory *)

(* A letisztult morfizmus-alapú bázis szintaxisod *)
Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.

(* ================================================================= *)
(* 1. TÍPUSOK (OBJEKTUMOK) INTERPRETÁCIÓJA                           *)
(* ================================================================= *)

(* Az S_sem paraméter eltűnt! Helyette a TSC szolgáltatja az S objektumot. *)
Fixpoint interp_ty {C : SetoidCategory} {CC : CartesianCategory C} 
  {TSC : TwoSortCategory C} (A : b_ty) : @obj C :=
  match A with
  | b_Unit => terminal
  | b_S => S  (* Ezt az S-t most már a TwoSortCategory adja! *)
  | b_Prod A1 A2 => prod (interp_ty A1) (interp_ty A2)
  end.

(* ================================================================= *)
(* 2. MORFIZMUSOK (DERIVÁCIÓK) INTERPRETÁCIÓJA                       *)
(* ================================================================= *)

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
(* 3. BASE SOUNDNESS TÉTEL                                           *)
(* ================================================================= *)

Theorem base_soundness : forall {C : SetoidCategory} {CC : CartesianCategory C} 
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
Qed.