
Require Import HyperLogic.Logic.Base.Simple_Ext.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple_Ext.Hyper_Syntax.
(** Base and substitution lemmas for the legacy syntax. *)
Require Import HyperLogic.Logic.Hyper.Simple_Ext.Notations. 

Open Scope logic_scope.


Lemma BT_Comp_Pair_Id_Fst_Correct {Sign : Type} {I D : b_ty} {t : @b_tm Sign} 
  (Ht : I ⊢b t : D) :
  I ⊢b (π₁ ∘ ⟨ id , t ⟩) : I.
Proof.
  eapply BT_Comp.
  - apply (@BT_Fst Sign I D).
  - eapply BT_Pair. { apply BT_Id. } { exact Ht. }
Defined.

(* Pairing followed by the first projection is the identity. *)
Lemma BE_Comp_Pair_Id_Fst_Correct {Sign : Type} {I D : b_ty} {t : @b_tm Sign} 
  (Ht : I ⊢b t : D) :
  I ⊢b (π₁ ∘ ⟨ id , t ⟩) ≡ id ⟶ I by (BT_Comp_Pair_Id_Fst_Correct Ht) & BT_Id.
Proof.
  apply BE_BetaFst.
Defined.


(* Extending [f] commutes with substitution by [t]. *)
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


(* Pullback followed by substitution equals pullback along the paired map. *)
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


(* Reindexing along the unchanged variable context preserves the formula. *)
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