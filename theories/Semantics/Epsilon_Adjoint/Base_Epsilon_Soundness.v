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
Proof.
  intros Sign C CC TSC BEM A B [t [d]].
  constructor.
  exact (interp_tm d).
Defined.

(** Equational Soundness
    Ha két szintaktikus levezetés ekvivalens (base_equiv), akkor a 
    szemantikai interpretációjuk morfizmusként izomorf (≅) a C kategóriában. *)
Theorem base_soundness_equational : 
  forall {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} 
  {TSC : TwoSortCategory C} {BEM : @BaseEpsilonModel Sign C CC TSC} 
  {A B : b_ty} {f g : @b_tm Sign} 
  (df : base_typing A f B) (dg : base_typing A g B),
  base_equiv df dg -> interp_tm df ≅ interp_tm dg.
Proof.
  intros Sign C CC TSC BEM A B f g df dg Heq.
  
  induction Heq; simpl.
  
  - (* BE_Refl *) reflexivity.
  - (* BE_Sym *) symmetry; assumption.
  - (* BE_Trans *) etransitivity; eassumption.
  
  (* Kongruencia *)
  - (* BE_CongComp *) rewrite IHHeq1, IHHeq2. reflexivity.
  - (* BE_CongPair *) rewrite IHHeq1, IHHeq2. reflexivity.
  
  (* Kategória axiómák *)
  - (* BE_Assoc *) apply comp_assoc.
  - (* BE_IdL *) apply id_left.
  - (* BE_IdR *) apply id_right.
  
  (* Cartesian (Beta/Eta) axiómák *)
  - (* BE_BetaFst *) apply prod_map_fst.
  - (* BE_BetaSnd *) apply prod_map_snd.
  - (* BE_EtaPair *) apply prod_eta.
  - (* BE_EtaUnit *) apply terminal_map_unique.
  
  (* BE_CompPair *) 
  - symmetry. apply compos_prod.
Defined.