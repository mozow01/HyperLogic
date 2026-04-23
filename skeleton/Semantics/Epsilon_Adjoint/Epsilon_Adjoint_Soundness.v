(* theories/Semantics/Epsilon_Adjoint/Epsilon_Adjoint_Soundness.v *)

Require Import Coq.Classes.Morphisms.
Require Import List Arith PeanoNat Lia.
Import ListNotations.

(* Kategóriaelméleti alapok *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import HyperLogic.Cat.Fibration.

(* Szintaxis és Adjungált Szemantika *)
Require Import HyperLogic.Logic.Base.Epsilon_Adjoint.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon_Adjoint.Hyper_Syntax.
Require Import HyperLogic.Semantics.Epsilon_Adjoint.Epsilon_Adjoint_Fibration.

(* ================================================================= *)
(* 1. STRUKTURÁLIS KOMPATIBILITÁSI LEMMÁK                            *)
(* ================================================================= *)

Lemma typing_subst_ext :
  forall {Sign : Type} {I J b : b_ty} {g : @b_tm Sign} (dg : base_typing I g J),
  base_typing (b_Prod I b) (b_subst_ext g) (b_Prod J b).
Proof. Admitted.

(* Helyettesítési izomorfizmusok a belső nyelv és a Fibrációs funktorok között. *)
Lemma form_subst_iso :
  forall {Sign : Type} {SM : SkolemMapping Sign}
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
  {EHM : EpsilonHyperModel SGF}
  (I A : b_ty) (f : @b_tm Sign) (df : base_typing I f A) (Phi : @h_ty Sign),
  interp_h_ty I (form_subst f Phi) ≅O @fobj _ _ (Pullback (interp_tm df)) (interp_h_ty A Phi).
Proof. Admitted.

Lemma ctx_subst_iso :
  forall {Sign : Type} {SM : SkolemMapping Sign}
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
  {EHM : EpsilonHyperModel SGF}
  (I A : b_ty) (G : @h_context Sign),
  interp_h_ctx (b_Prod I A) (ctx_subst b_fst G) ≅O @fobj _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (A:=I) (B:=A)))) (interp_h_ctx I G).
Proof. Admitted.

(* ================================================================= *)
(* 2. KONVERZIÓS LEMMÁK                                              *)
(* ================================================================= *)

(* --- SEGÉDLEMMÁK A HELYETTESÍTÉSHEZ --- *)

Lemma interp_subst_cong : forall {Sign : Type} {SM : SkolemMapping Sign}
  {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C}
  {BiCCC : BiCartesianClosedCategory BCCC} {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
  {EHM : EpsilonHyperModel SGF} (I J : b_ty) (f g : @b_tm Sign) (Phi : @h_ty Sign)
  (df : base_typing I f J) (dg : base_typing I g J),
  base_equiv df dg ->
  WellFormed J Phi ->
  (interp_h_ty I (form_subst f Phi)) ≅O (interp_h_ty I (form_subst g Phi)).
Proof. Admitted.

Lemma interp_subst_id : forall {Sign : Type} {SM : SkolemMapping Sign}
  {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C}
  {BiCCC : BiCartesianClosedCategory BCCC} {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
  {EHM : EpsilonHyperModel SGF} (I : b_ty) (Phi : @h_ty Sign),
  WellFormed I Phi ->
  (interp_h_ty I (form_subst b_id Phi)) ≅O (interp_h_ty I Phi).
Proof. Admitted.

Lemma interp_subst_comp : forall {Sign : Type} {SM : SkolemMapping Sign}
  {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C}
  {BiCCC : BiCartesianClosedCategory BCCC} {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
  {EHM : EpsilonHyperModel SGF} (I J K: b_ty) (f g : @b_tm Sign) (Phi : @h_ty Sign)
  (df : base_typing J f K) (dg : base_typing I g J),
  WellFormed K Phi ->
  (interp_h_ty I (form_subst (b_comp f g) Phi)) ≅O (interp_h_ty I (form_subst g (form_subst f Phi))).
Proof. Admitted.
(* --- FŐ KONVERZIÓS LEMMÁK --- *)

Lemma interp_form_equiv :
  forall {Sign : Type} {SM : SkolemMapping Sign}
  {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C} {BiCCC : BiCartesianClosedCategory BCCC}
  {TSC : TwoSortCategory C} {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
  {EHM : EpsilonHyperModel SGF}
  {AdEHM : @AdjointEpsilonFibration Sign SM C CC TSC BEM GF SGF EHM},
  forall (I : b_ty) (Phi Psi : @h_ty Sign),
  form_equiv I Phi Psi ->
  interp_h_ty I Phi ≅O interp_h_ty I Psi.
Proof. Admitted.

Lemma interp_ctx_equiv :
  forall {Sign : Type} {SM : SkolemMapping Sign}
  {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C} {BiCCC : BiCartesianClosedCategory BCCC}
  {TSC : TwoSortCategory C} {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
  {EHM : EpsilonHyperModel SGF}
  {AdEHM : @AdjointEpsilonFibration Sign SM C CC TSC BEM GF SGF EHM},
  forall (I : b_ty) (G1 G2 : @h_context Sign),
  ctx_equiv I G1 G2 ->
  interp_h_ctx I G1 ≅O interp_h_ctx I G2.
Proof. Admitted.

(* ================================================================= *)
(* 3. SOUNDNESS TÉTEL                                                *)
(* ================================================================= *)

Theorem soundness :
  forall {Sign : Type} {SM : SkolemMapping Sign}
  {C : SetoidCategory} {CC : CartesianCategory C}
  {BCCC : CartesianClosedCategory C} {BiCCC : BiCartesianClosedCategory BCCC}
  {TSC : TwoSortCategory C} {BEM : BaseEpsilonModel} {GF : GoodFibration C}
  {SGF : StrictGoodFibration C GF} {EHM : EpsilonHyperModel SGF}
  {AdEHM : @AdjointEpsilonFibration Sign SM C CC TSC BEM GF SGF EHM},
  forall (I : b_ty) (G : @h_context Sign) (p : @h_tm Sign) (Phi : @h_ty Sign),
  h_derivation I G p Phi ->
  hom (interp_h_ctx I G) (interp_h_ty I Phi).
Proof. Admitted.