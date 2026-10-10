
Require Import Coq.Classes.Morphisms.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.Fibration.

Require Import HyperLogic.Logic.Base.Simple_Ext.Base_Syntax.
Require Import HyperLogic.Semantics.Simple_Ext.Simple_Ext_Fibration.
 

(** A syntactic term yields an inhabited semantic hom-set. *)
Theorem base_soundness_inhabitational : 
  forall {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} 
  {TSC : TwoSortCategory C} {BEM : @BaseSignatureModel Sign C CC TSC} {A B : b_ty},
  (exists (t : @b_tm Sign), inhabited (base_typing A t B)) -> 
  inhabited (hom (interp_ty A) (interp_ty B)).
Proof.
  intros Sign C CC TSC BEM A B [t [d]].
  constructor.
  exact (interp_tm d).
Defined.

Theorem base_soundness_equational : 
  forall {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} 
  {TSC : TwoSortCategory C} {BEM : @BaseSignatureModel Sign C CC TSC} {CBM : @CoherentBaseModel Sign C CC TSC BEM}
  {A B : b_ty} {f g : @b_tm Sign} 
  (df : base_typing A f B) (dg : base_typing A g B),
  base_equiv_typed A B f g -> interp_tm df ≅ interp_tm dg.
Proof.
  intros Sign C CC TSC BEM CBM A B f g df dg [df' [dg' Heq_base]].
  
  (* Explicit intermediate objects avoid unresolved evars. *)
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