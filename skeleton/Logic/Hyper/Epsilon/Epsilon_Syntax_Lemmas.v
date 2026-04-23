(* Logic/Hyper/Epsilon/Epsilon_Syntax_Lemmas.v *)

Require Import HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon.Notations. (* Vagy ahogy elnevezted *)

Open Scope logic_scope.

(* ================================================================= *)
(* 1. BÁZIS-SZINTŰ IDENTITÁSOK (A Dual Drinker-hez)                  *)
(* ================================================================= *)

(* A <id, t> kompozíciója a projekcióval helyesen gépelhető *)
Lemma BT_Comp_Pair_Id_Fst_Correct {Sign : Type} {I D : b_ty} {t : @b_tm Sign}
  (Ht : I ⊢b t : D) :
  I ⊢b (π₁ ∘ ⟨ id , t ⟩) : I.
Proof. Admitted.

(* Bázis Axióma: A párosítás és a balra-projekció kompozíciója kioltja egymást.
   Olvasat: π₁ ∘ ⟨id, t⟩ ≡ id ⟶ I *)
(* Bázis Axióma: A párosítás és a balra-projekció kompozíciója kioltja egymást.
   Olvasat: π₁ ∘ ⟨id, t⟩ ≡ id ⟶ I *)
Lemma BE_Comp_Pair_Id_Fst_Correct {Sign : Type} {I D : b_ty} {t : @b_tm Sign}
  (Ht : I ⊢b t : D) :
  I ⊢b (π₁ ∘ ⟨ id , t ⟩) ≡ id ⟶ I by (BT_Comp_Pair_Id_Fst_Correct Ht) & BT_Id.
Proof. Admitted.

(* ================================================================= *)
(* 2. BÁZIS-SZINTŰ HELYETTESÍTÉS (A Gépterem)                        *)
(* ================================================================= *)

(* A helyettesítés kategóriaelméleti alapja.
   Olvasat: (f × id) ∘ ⟨id, t⟩ ≡ ⟨f, t⟩ ⟶ J ▹ D *)
Lemma BE_Substitution_Law : forall {Sign : Type} I J D (f t : @b_tm Sign)
  (df : I ⊢b f : J) (dt : I ⊢b t : D),
  I ⊢b (b_pullback_ext f ∘ ⟨ id , t ⟩) ≡ ⟨ f , t ⟩ ⟶ (J ▹ D)
    by (BT_Comp (BT_Pair (BT_Comp df BT_Fst) BT_Snd) (BT_Pair BT_Id dt)) & (BT_Pair df dt).
Proof. Admitted.

(* ================================================================= *)
(* 3. HYPER-SZINTŰ HELYETTESÍTÉS (A Fő Logikai Fegyver)              *)
(* ================================================================= *)

(* Ha egy formulát visszahúzunk f mentén, és behelyettesítjük a t-t,
   az logikailag ekvivalens azzal, mintha az ⟨f, t⟩ mentén húztuk volna vissza. *)
Lemma FE_Substitution_Law : forall {Sign : Type} `{SkolemMapping Sign} I J D
  (f t : @b_tm Sign) (Phi : @h_ty Sign)
  (df : I ⊢b f : J) (dt : I ⊢b t : D),
  (J ▹ D) ⊢ Phi wff ->
  I ⊢ (Phi [ b_pullback_ext f ]*) [ t ] ≡ Phi [ ⟨ f , t ⟩ ]*.
Proof. Admitted.

(* ================================================================= *)
(* 4. LOKÁLIS IDENTITÁS ÉS A "DUAL DRINKER" GYILKOS                  *)
(* ================================================================= *)

(* Segédlemma: A módosítatlan változókontextus mentén vett visszahúzás
   logikailag nem változtatja meg a formulát.
   Olvasat: Phi[⟨π₁, π₂⟩] ≡ Phi *)
Lemma FE_Local_Id : forall {Sign : Type} `{SkolemMapping Sign} I D (Phi : @h_ty Sign),
  (I ▹ D) ⊢ Phi wff ->
  (I ▹ D) ⊢ Phi [ ⟨ π₁ , π₂ ⟩ ]* ≡ Phi.
Proof. Admitted.

(* A VÉGSŐ FEGYVER: A Dual Drinker Epszilon bevezetésének eltüntetésére. *)
Lemma FE_Pullback_Ext_Fst_Snd : forall {Sign : Type} `{SkolemMapping Sign} I D (Phi : @h_ty Sign),
  (I ▹ D) ⊢ Phi wff ->
  (I ▹ D) ⊢ (Phi [ b_pullback_ext π₁ ]*) [ π₂ ] ≡ Phi.
Proof. Admitted.