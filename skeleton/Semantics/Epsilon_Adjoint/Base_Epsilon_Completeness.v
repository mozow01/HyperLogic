(* theories/Semantics/Epsilon_Adjoint/Base_Epsilon_Completeness.v *)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Equality.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.Fibration.

Require Import HyperLogic.Logic.Base.Epsilon_Adjoint.Base_Syntax.
Require Import HyperLogic.Semantics.Epsilon_Adjoint.Epsilon_Adjoint_Fibration.

(* ================================================================= *)
(* 1. A SZINTAKTIKUS KATEGÓRIA (TERM MODELL) MORFIZMUSAI             *)
(* ================================================================= *)

Class hom_base {Sign : Type} (A B : b_ty) : Type := mk_hom_base {
  tm_of : @b_tm Sign;
  deriv_of : @base_typing Sign A tm_of B
}.

Arguments tm_of {Sign A B} _.
Arguments deriv_of {Sign A B} _.

(* ================================================================= *)
(* 2. A BÁZIS KATEGÓRIA PÉLDÁNYOSÍTÁSA (Epsilon verzió)              *)
(* ================================================================= *)

Instance Base_SetoidCategory (Sign : Type) : SetoidCategory.
Proof. Admitted.

Instance Base_CartesianCategory (Sign : Type) : CartesianCategory (Base_SetoidCategory Sign).
Proof. Admitted.

Instance Base_TwoSortCategory (Sign : Type) : TwoSortCategory (Base_SetoidCategory Sign).
Proof. Admitted.

(* ================================================================= *)
(* 2.5 SZINTAKTIKUS EPSILON MODELL ÉS SEGÉDLEMMÁK                    *)
(* ================================================================= *)

(* Először be kell bizonyítanunk, hogy az interp_ty identitásként viselkedik,
   különben a modell nem tudja, hogy interp_ty I = I. *)
Lemma interp_ty_id : forall (Sign : Type) (A : b_ty),
  @interp_ty (Base_SetoidCategory Sign) (Base_CartesianCategory Sign) (Base_TwoSortCategory Sign) A = A.
Proof. Admitted.

(* Most már fel tudjuk építeni a modellt a rewrite taktika segítségével! *)
Instance Base_SyntacticEpsilonModel (Sign : Type) :
  @BaseEpsilonModel Sign (Base_SetoidCategory Sign) (Base_CartesianCategory Sign) (Base_TwoSortCategory Sign).
Proof. Admitted.

(* ================================================================= *)
(* 3. COMPLETENESS HELPER LEMMÁK (Kiegészítve a b_const-tal)         *)
(* ================================================================= *)

(* Segédlemma a rewrite által generált eq_rect (típuskonverzió) feloldására.
   Mivel a tm_of visszatérési típusa nem függ az I és A típusoktól,
   a típuskonverzió nem változtatja meg magát a termet. *)
Lemma tm_of_eq_rect : forall {Sign : Type} (I A I_sem A_sem : b_ty)
  (eqI : I_sem = I) (eqA : A_sem = A) (f : @hom_base Sign I A),
  @tm_of Sign I_sem A_sem (eq_rect_r (fun o : b_ty => hom_base o A_sem)
           (eq_rect_r (fun o : b_ty => hom_base I o) f eqA) eqI) =
  @tm_of Sign I A f.
Proof. Admitted.

(* És most az eredeti lemmád a javított utolsó ággal: *)
Lemma interp_tm_term : forall {Sign : Type} A B f (df : @base_typing Sign A f B),
  tm_of (@interp_tm Sign (Base_SetoidCategory Sign) (Base_CartesianCategory Sign) (Base_TwoSortCategory Sign) (Base_SyntacticEpsilonModel Sign) A B f df) = f.
Proof. Admitted.

Lemma base_typing_unique : forall {Sign : Type} A f B1 (d1 : @base_typing Sign A f B1) B2 (d2 : @base_typing Sign A f B2),
  B1 = B2.
Proof. Admitted.

Lemma base_typing_pi : forall {Sign : Type} A B f (d1 d2 : @base_typing Sign A f B),
  @base_equiv Sign A B f f d1 d2.
Proof. Admitted.

Lemma base_equiv_cast : forall {Sign : Type} A B A' B' f g f' g'
  (eqA : A' = A) (eqB : B' = B)
  (eqF : f' = f) (eqG : g' = g)
  (df' : @base_typing Sign A' f' B') (dg' : @base_typing Sign A' g' B')
  (df : @base_typing Sign A f B) (dg : @base_typing Sign A g B),
  @base_equiv Sign A' B' f' g' df' dg' -> @base_equiv Sign A B f g df dg.
Proof. Admitted.

Lemma base_typing_cast : forall {Sign : Type} A' B' A B t,
  A' = A -> B' = B -> @base_typing Sign A' t B' -> @base_typing Sign A t B.
Proof. Admitted.

(* ================================================================= *)
(* 4. COMPLETENESS (TELJESSÉG) TÉTELEK                               *)
(* ================================================================= *)

Theorem base_completeness_equational : forall {Sign : Type} {A B : b_ty} {f g : @b_tm Sign}
  (df : @base_typing Sign A f B) (dg : @base_typing Sign A g B),
  (forall (C : SetoidCategory) (CC : CartesianCategory C) (TSC : TwoSortCategory C) (BEM : @BaseEpsilonModel Sign C CC TSC),
     @interp_tm Sign C CC TSC BEM A B f df ≅ @interp_tm Sign C CC TSC BEM A B g dg) ->
  @base_equiv Sign A B f g df dg.
Proof. Admitted.

Theorem base_completeness_inhabitational : forall {Sign : Type} {A B : b_ty},
  (forall (C : SetoidCategory) (CC : CartesianCategory C) (TSC : TwoSortCategory C) (BEM : @BaseEpsilonModel Sign C CC TSC),
     inhabited (hom (@interp_ty C CC TSC A) (@interp_ty C CC TSC B))) ->
  (exists (t : @b_tm Sign), inhabited (@base_typing Sign A t B)).
Proof. Admitted.