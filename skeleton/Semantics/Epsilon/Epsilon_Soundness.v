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

(* Szintaxis és Epszilon Bázis Szemantika *)
Require Import HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Require Import HyperLogic.Semantics.Epsilon.Epsilon_Fibration.
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum.
Require Import HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.

(* Ha van Hyper_Lemmas, azt is importáld, ha nincs, vedd ki: *)
(* Require Import HyperLogic.Logic.Hyper.Epsilon.Hyper_Lemmas. *)

(* ================================================================= *)
(* 1. STRUKTURÁLIS KOMPATIBILITÁSI LEMMÁK (AXIÓMÁK)                  *)
(* ================================================================= *)

Lemma typing_pullback_ext :
  forall {Sign : Type} {I J b : b_ty} {g : @b_tm Sign} (dg : base_typing I g J),
  base_typing (b_Prod I b) (b_pullback_ext g) (b_Prod J b).
Proof. Admitted.

Lemma form_pullback_general_iso :
  forall {Sign : Type} {SM : SkolemMapping Sign}
         {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
         {EHM : EpsilonHyperModel SGF} {EGF : EpsilonGoodFibration}
         (Phi : @h_ty Sign) (I J : b_ty) (g : @b_tm Sign) (dg : base_typing I g J),
  interp_h_ty I (form_pullback g Phi) ≅O
  @fobj _ _ (Pullback (interp_tm dg)) (interp_h_ty J Phi).
Proof. Admitted.

(** * Syntactic Substitution = Semantic Pullback *)
Lemma form_pullback_iso :
  forall {Sign : Type} {SM : SkolemMapping Sign}
         {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
         {EHM : EpsilonHyperModel SGF} {EGF : EpsilonGoodFibration}
         (I A : b_ty) (f : @b_tm Sign) (df : base_typing I f A) (Phi : @h_ty Sign),
  interp_h_ty I (form_pullback (b_pair b_id f) Phi) ≅O
  @fobj _ _ (Pullback (interp_tm (BT_Pair BT_Id df))) (interp_h_ty (b_Prod I A) Phi).
Proof. Admitted.

Lemma form_pullback_fst_iso :
  forall {Sign : Type} {SM : SkolemMapping Sign}
         {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
         {EHM : EpsilonHyperModel SGF} {EGF : EpsilonGoodFibration}
         (I A : b_ty) (Phi : @h_ty Sign),
  interp_h_ty (b_Prod I A) (form_pullback b_fst Phi) ≅O
  @fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I Phi).
Proof. Admitted.

Lemma ctx_pullback_iso :
  forall {Sign : Type} {SM : SkolemMapping Sign}
         {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
         {EHM : EpsilonHyperModel SGF} {EGF : EpsilonGoodFibration}
         (I A : b_ty) (G : @h_context Sign),
  interp_h_ctx (b_Prod I A) (ctx_pullback b_fst G) ≅O
  @fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ctx I G).
Proof. Admitted.

(* ================================================================= *)
(* 1.5 FORMULA EKVIVALENCIA = KATEGÓRIAELMÉLETI IZOMORFIZMUS         *)
(* ================================================================= *)

(* 1. Axióma: A szintaktikai identitás visszahúzás izomorf az eredetivel *)

Lemma interp_pb_cong : forall {Sign : Type} {SM : SkolemMapping Sign}
  {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C}
  {BiCCC : BiCartesianClosedCategory BCCC} {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
  {EHM : EpsilonHyperModel SGF} (I J : b_ty) (f g : @b_tm Sign) (Phi : @h_ty Sign)
  (df : base_typing I f J) (dg : base_typing I g J),
  base_equiv df dg ->
  WellFormed J Phi ->
  (interp_h_ty I (form_pullback f Phi)) ≅O (interp_h_ty I (form_pullback g Phi)).
Proof. Admitted.

Lemma interp_pb_id : forall {Sign : Type} {SM : SkolemMapping Sign}
  {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C}
  {BiCCC : BiCartesianClosedCategory BCCC} {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
  {EHM : EpsilonHyperModel SGF} (I : b_ty) (Phi : @h_ty Sign),
  WellFormed I Phi ->
  (interp_h_ty I (form_pullback b_id Phi)) ≅O (interp_h_ty I Phi).
Proof. Admitted.

Lemma interp_pb_comp : forall {Sign : Type} {SM : SkolemMapping Sign}
  {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C}
  {BiCCC : BiCartesianClosedCategory BCCC} {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
  {EHM : EpsilonHyperModel SGF} (I J K: b_ty) (f g : @b_tm Sign) (Phi : @h_ty Sign)
  (df : base_typing J f K) (dg : base_typing I g J),
  WellFormed K Phi ->
  (interp_h_ty I (form_pullback (b_comp f g) Phi)) ≅O (interp_h_ty I (form_pullback g (form_pullback f Phi))).
Proof. Admitted.

Lemma form_equiv_iso :
  forall {Sign : Type} {SM : SkolemMapping Sign}
         {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C} {BiCCC : BiCartesianClosedCategory BCCC}
         {TSC : TwoSortCategory C} {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
         {EHM : EpsilonHyperModel SGF} {EGF : EpsilonGoodFibration}
         (I : b_ty) (Phi Psi : @h_ty Sign),
  form_equiv I Phi Psi -> interp_h_ty I Phi ≅O interp_h_ty I Psi.
Proof. Admitted.

(* ================================================================= *)
(* 2. INHABITED SOUNDNESS TÉTEL                                      *)
(* ================================================================= *)

Theorem hyper_soundness_inhabited
  {Sign : Type} {SM : SkolemMapping Sign}
  {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C} {BiCCC : BiCartesianClosedCategory BCCC}
  {TSC : TwoSortCategory C} {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
  {EHM : EpsilonHyperModel SGF} {EGF : EpsilonGoodFibration}
  {I : b_ty} {G : @h_context Sign} {p : @h_tm Sign} {Phi : @h_ty Sign}
  (D : h_derivation I G p Phi) : hom (interp_h_ctx I G) (interp_h_ty I Phi).
Proof. Admitted.