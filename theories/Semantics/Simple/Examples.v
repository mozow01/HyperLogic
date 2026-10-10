
Require Import Coq.Classes.Morphisms.
Require Import List Arith PeanoNat Lia.
Import ListNotations.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import HyperLogic.Cat.Fibration.

Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Semantics.Simple.Base_Simple_Soundness.
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Lemmas.
Require Import HyperLogic.Semantics.Simple.Simple_Soundness.


Section Base_Translation_Example.
  Context {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}.

  (** Examples of syntactic and semantic interpretation. *)
  Definition syntax_prod_S_Unit := b_Prod b_S b_Unit. (* [cite: 2, 3] *)
  
  (* [interp_ty] maps the product to [S x 1] [cite: 39]. *)
  Definition sem_prod_S_Unit := interp_ty syntax_prod_S_Unit. (* [cite: 40, 41] *)

  (* The example term is [<id, unit> : S -> S x Unit]. *)
  Definition my_term := b_pair b_id b_unit. (* [cite: 4, 5] *)
  
  Definition my_typing : base_typing b_S my_term (b_Prod b_S b_Unit).
  Proof.
    apply BT_Pair.
    - apply BT_Id.
    - apply BT_Unit.
  Defined.

  (* Its interpretation is [<id, !> : S --> S x 1] [cite: 42]. *)
  Definition my_semantics := interp_tm my_typing. (* [cite: 43, 44] *)
  
  Check my_semantics : hom (S TSC) (prod (S TSC) terminal).
End Base_Translation_Example.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.Fibration.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.Fibration.

Section Total_And_Coherence_Examples.
  Context {B : SetoidCategory} {CB : CartesianCategory B}.
  Context {GF : GoodFibration B} {SGF : StrictGoodFibration B GF}.

  (** Example morphism in the total category. *)
  Variable A : @obj B.
  Variable Phi : @obj (Fiber A).
  Variable B_obj : @obj B.
  Variable Psi : @obj (Fiber B_obj).
  Variable f : hom A B_obj.
  
  Definition my_total_obj : TotalObj GF := @mk_TotalObj B CB GF A Phi.
  Definition my_target_obj : TotalObj GF := @mk_TotalObj B CB GF B_obj Psi.

  Variable alpha : hom Phi (@fobj _ _ (Pullback f) Psi).

  Definition my_total_hom : TotalHom my_total_obj my_target_obj :=
    @mk_TotalHom B CB GF my_total_obj my_target_obj f alpha.

  (** Reindexing preserves conjunction up to [and_subst_iso]. *)
  
  Variable Psi1 Psi2 : @obj (Fiber B_obj).

  Definition subst_and := 
    @fobj _ _ (Pullback f) (@prod _ (Fiber_is_Cartesian B_obj) Psi1 Psi2).

  Definition and_subst_iso : 
    subst_and ≅O (@prod _ (Fiber_is_Cartesian A) 
                    (@fobj _ _ (Pullback f) Psi1) 
                    (@fobj _ _ (Pullback f) Psi2)) :=
    pb_prod_iso f Psi1 Psi2.

  (* [and_subst_iso] supports rewriting in either direction. *)

End Total_And_Coherence_Examples.
