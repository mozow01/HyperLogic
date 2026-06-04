(* Logic/Hyper/Simple/Simple_Syntax_Lemmas.v *)

Require Import HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple_Ext.Hyper_Syntax.
(* Ha van saját Notations fájlod a Simple szintaxishoz, azt is importáld ide! *)
Require Import HyperLogic.Logic.Hyper.Simple_Ext.Notations. 

Open Scope logic_scope.

(* ================================================================= *)
(* 1. BÁZIS-SZINTŰ IDENTITÁSOK (A Dual Drinker-hez)                  *)
(* ================================================================= *)

(* A <id, t> kompozíciója a projekcióval helyesen gépelhető *)
Lemma BT_Comp_Pair_Id_Fst_Correct {Sign : Type} {I D : b_ty} {t : @b_tm Sign} 
  (Ht : I ⊢b t : D) :
  I ⊢b (π₁ ∘ ⟨ id , t ⟩) : I.
Proof.
  eapply BT_Comp.
  - apply (@BT_Fst Sign I D).
  - eapply BT_Pair. { apply BT_Id. } { exact Ht. }
Defined.

(* Bázis Axióma: A párosítás és a balra-projekció kompozíciója kioltja egymást. 
   Olvasat: π₁ ∘ ⟨id, t⟩ ≡ id ⟶ I *)
Lemma BE_Comp_Pair_Id_Fst_Correct {Sign : Type} {I D : b_ty} {t : @b_tm Sign} 
  (Ht : I ⊢b t : D) :
  I ⊢b (π₁ ∘ ⟨ id , t ⟩) ≡ id ⟶ I by (BT_Comp_Pair_Id_Fst_Correct Ht) & BT_Id.
Proof.
  apply BE_BetaFst.
Defined.

(* ================================================================= *)
(* 2. BÁZIS-SZINTŰ HELYETTESÍTÉS (A Gépterem)                        *)
(* ================================================================= *)

(* A helyettesítés kategóriaelméleti alapja.
   Olvasat: (f × id) ∘ ⟨id, t⟩ ≡ ⟨f, t⟩ ⟶ J ▹ D *)
Lemma BE_Substitution_Law : forall {Sign : Type} I J D (f t : @b_tm Sign) 
  (df : I ⊢b f : J) (dt : I ⊢b t : D),
  I ⊢b (b_pullback_ext f ∘ ⟨ id , t ⟩) 
    ≡ ⟨ f , t ⟩ ⟶ (J ▹ D) 
    by (BT_Comp (BT_Pair (BT_Comp df BT_Fst) BT_Snd) (BT_Pair BT_Id dt)) & (BT_Pair df dt).
Proof.
  intros Sign I J D f t df dt.
  unfold b_pullback_ext.
  eapply BE_Trans. { eapply BE_CompPair. }
  eapply BE_CongPair.
  - eapply BE_Trans. { eapply BE_Sym. apply BE_Assoc. }
    eapply BE_Trans. { eapply BE_CongComp. apply BE_BetaFst. apply BE_Refl. }
    apply BE_IdR.
  - apply BE_BetaSnd.
Defined.

(* ================================================================= *)
(* 3. HYPER-SZINTŰ HELYETTESÍTÉS (A Fő Logikai Fegyver)              *)
(* ================================================================= *)

(* Ha egy formulát visszahúzunk f mentén, és behelyettesítjük a t-t, 
   az logikailag ekvivalens azzal, mintha az ⟨f, t⟩ mentén húztuk volna vissza. *)
Lemma FE_Substitution_Law : forall {Sign : Type} I J D 
  (f t : @b_tm Sign) (Phi : @Hyper_Syntax.h_ty Sign)
  (df : I ⊢b f : J) (dt : I ⊢b t : D),
  (J ▹ D) ⊢ Phi wff ->
  I ⊢ (Phi [ b_pullback_ext f ]*) [ t ] ≡ Phi [ ⟨ f , t ⟩ ]*.
Proof.
  intros Sign I J D f t Phi df dt Hwf.
  eapply FE_Trans.
  1: {
    eapply FE_Pullback_Comp.
    - unfold b_pullback_ext. eapply BT_Pair.
      + eapply BT_Comp. exact df. apply (@BT_Fst Sign I D). 
      + apply (@BT_Snd Sign I D). 
    - eapply BT_Pair. apply BT_Id. exact dt.
    - exact Hwf.
  }
  eapply FE_Pullback_Cong.
  - apply (@BE_Substitution_Law Sign I J D f t df dt).
  - exact Hwf.
Defined.

(* ================================================================= *)
(* 4. LOKÁLIS IDENTITÁS ÉS A "DUAL DRINKER" GYILKOS                  *)
(* ================================================================= *)

(* Segédlemma: A módosítatlan változókontextus mentén vett visszahúzás
   logikailag nem változtatja meg a formulát. 
   Olvasat: Phi[⟨π₁, π₂⟩] ≡ Phi *)
Lemma FE_Local_Id : forall {Sign : Type} I D (Phi : @h_ty Sign),
  (I ▹ D) ⊢ Phi wff ->
  (I ▹ D) ⊢ Phi [ ⟨ π₁ , π₂ ⟩ ]* ≡ Phi.
Proof.
  intros Sign I D Phi Hwf.
  eapply FE_Trans.
  2: { apply FE_Pullback_Id. exact Hwf. }
  eapply FE_Pullback_Cong.
  - eapply BE_Trans.
    1: {
      eapply BE_CongPair.
      - eapply BE_Sym. apply (@BE_IdR Sign (I ▹ D) I π₁ (@BT_Fst Sign I D)).
      - eapply BE_Sym. apply (@BE_IdR Sign (I ▹ D) D π₂ (@BT_Snd Sign I D)).
    }
    apply (@BE_EtaPair Sign (I ▹ D) I D id BT_Id).
  - exact Hwf.
Defined.

(* A VÉGSŐ FEGYVER: A Dual Drinker cáfolásához szükséges levezetésekre. *)
Lemma FE_Pullback_Ext_Fst_Snd : forall {Sign : Type} I D (Phi : @h_ty Sign),
  (I ▹ D) ⊢ Phi wff ->
  (I ▹ D) ⊢ (Phi [ b_pullback_ext π₁ ]*) [ π₂ ] ≡ Phi.
Proof.
  intros Sign I D Phi Hwf.
  eapply FE_Trans.
  1: { 
    eapply FE_Substitution_Law.
    - apply (@BT_Fst Sign I D). 
    - apply (@BT_Snd Sign I D). 
    - exact Hwf. 
  }
  apply FE_Local_Id. exact Hwf.
Defined.