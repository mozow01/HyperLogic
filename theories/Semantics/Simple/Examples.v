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

(* Szintaxis és Bázis Szemantika *)
Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Semantics.Simple.Base_Simple_Soundness.
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Lemmas.
Require Import HyperLogic.Semantics.Simple.Simple_Soundness.


Section Base_Translation_Example.
  Context {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}.

  (* Példa: Típusok szintaktikusan és szemantikusan *)
  Definition syntax_prod_S_Unit := b_Prod b_S b_Unit. (* [cite: 2, 3] *)
  
  (* Az interp_ty [cite: 39] meghívása: S x 1 lesz belőle *)
  Definition sem_prod_S_Unit := interp_ty syntax_prod_S_Unit. (* [cite: 40, 41] *)

  (* Példa: Egy konkrét term levezetése és interpretációja *)
  (* Term: <id, unit> : S -> S x Unit *)
  Definition my_term := b_pair b_id b_unit. (* [cite: 4, 5] *)
  
  Definition my_typing : base_typing b_S my_term (b_Prod b_S b_Unit).
  Proof.
    apply BT_Pair. (* [cite: 11] *)
    - apply BT_Id. (* [cite: 8] *)
    - apply BT_Unit. (* [cite: 10] *)
  Defined.

  (* Az interpretáció [cite: 42] eredménye: <id, !> : S --> S x 1 *)
  Definition my_semantics := interp_tm my_typing. (* [cite: 43, 44] *)
  
  (* Ellenőrizhetjük, hogy a típusok stimmelnek *)
  Check my_semantics : hom (S TSC) (prod (S TSC) terminal).
End Base_Translation_Example.

(* Examples_TotalCategory.v *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.Fibration.

(* Examples_Hyper_Coherence.v *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.Fibration.

Section Total_And_Coherence_Examples.
  Context {B : SetoidCategory} {CB : CartesianCategory B}.
  Context {GF : GoodFibration B} {SGF : StrictGoodFibration B GF}.

  (* ================================================================= *)
  (* 1. A Total Kategória Morfizmusának javított definíciója           *)
  (* ================================================================= *)
  Variable A : @obj B.
  Variable Phi : @obj (Fiber A).
  Variable B_obj : @obj B.
  Variable Psi : @obj (Fiber B_obj).
  Variable f : hom A B_obj.
  
  (* Két Total objektum *)
  Definition my_total_obj : TotalObj GF := @mk_TotalObj B CB GF A Phi.
  Definition my_target_obj : TotalObj GF := @mk_TotalObj B CB GF B_obj Psi.

  (* Bizonyítás a szálban: Phi -> f^* Psi *)
  Variable alpha : hom Phi (@fobj _ _ (Pullback f) Psi).

  (* JAVÍTÁS: Expliciten megadjuk a forrás és cél objektumokat (my_total_obj, my_target_obj) *)
  Definition my_total_hom : TotalHom my_total_obj my_target_obj :=
    @mk_TotalHom B CB GF my_total_obj my_target_obj f alpha.

  (* ================================================================= *)
  (* 2. Koherencia a gyakorlatban: Helyettesítés és Kötőszavak         *)
  (* ================================================================= *)
  
  (* Tegyük fel, hogy van két formulánk (Psi1, Psi2) a cél típuson (B_obj) *)
  Variable Psi1 Psi2 : @obj (Fiber B_obj).

  (* Szintaktikailag f-fel helyettesítjük a konjunkciójukat: (Psi1 ∧ Psi2)[f] *)
  (* Szemantikailag ez: f^* (Psi1 x Psi2) *)
  Definition subst_and := 
    @fobj _ _ (Pullback f) (@prod _ (Fiber_is_Cartesian B_obj) Psi1 Psi2).

  (* A logikai Soundness bizonyításában szükség van arra, hogy ezt szétbontsuk:
     f^* (Psi1 x Psi2) ≅ (f^* Psi1) x (f^* Psi2) *)
  Definition and_subst_iso : 
    subst_and ≅O (@prod _ (Fiber_is_Cartesian A) 
                    (@fobj _ _ (Pullback f) Psi1) 
                    (@fobj _ _ (Pullback f) Psi2)) :=
    pb_prod_iso f Psi1 Psi2.

  (* Ez az izomorfizmus ('and_subst_iso') a motorja annak a 8 célnak, 
     amit a form_pullback bizonyításánál elkezdtünk! Visszafelé és előrefelé 
     is alkalmazható a rewrite/setoid_rewrite taktikákkal. *)

End Total_And_Coherence_Examples.
