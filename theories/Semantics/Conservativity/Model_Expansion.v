(* Semantics/Conservativity/Model_Expansion.v *)

Require Import List.
Import ListNotations.

(* Kategóriaelméleti alapok *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import HyperLogic.Cat.Fibration.

Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Logic.Base.Simple_Ext.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple_Ext.Hyper_Syntax.
Require Import HyperLogic.Semantics.Simple_Ext.Simple_Ext_Fibration.

(* Mivel mindkét nyelvhez tartozik külön Hyper_Model fájl, valószínűleg 
   szét kell választanunk az importokat. Feltételezem, hogy a névterek így 
   vannak kialakítva nálad: *)
Module S_Base := HyperLogic.Logic.Base.Simple.Base_Syntax.
Module SE_Base := HyperLogic.Logic.Base.Simple_Ext.Base_Syntax.
Module S_Hyper := HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.
Module SE_Hyper := HyperLogic.Logic.Hyper.Simple_Ext.Hyper_Syntax.

Require Import HyperLogic.Semantics.Simple_Ext.Base_Epsilon_Completeness.
Require Import HyperLogic.Semantics.Simple.Simple_Completeness.
Require Import HyperLogic.Semantics.Simple_Ext.Simple_Ext_Soundness.
Module S_Comp := HyperLogic.Semantics.Simple.Simple_Completeness.
Module SE_Mod := HyperLogic.Semantics.Simple_Ext.Simple_Ext_Soundness.

(* Tegyük fel, hogy a modellek definíciói is két külön modulban vannak: *)
(* Module S_Mod := HyperLogic.Logic.Semantics.Simple.HyperModel_Def. *)
(* Module SE_Mod := HyperLogic.Logic.Semantics.Simple_Ext.HyperModel_Def. *)
Require Import Coq.Init.Logic.

(* ================================================================= *)
(* 1. A TRIVIÁLIS SZIGNATÚRA ÉS MODELLJE                             *)
(* ================================================================= *)

Definition Empty_Sign : Type := Empty_set.

(* Mivel s : Empty_set, sosem kell valós morfizmust szolgáltatnunk! *)
Instance Trivial_SignatureModel {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} : 
  @BaseSignatureModel Empty_Sign C CC TSC.
Proof.
  constructor. intros I A s. destruct s.
Defined.

(* ================================================================= *)
(* 2. A SZINTAKTIKUS BEÁGYAZÁS (SYNTACTIC EMBEDDING)                 *)
(* ================================================================= *)

Fixpoint embed_b_ty (A : S_Base.b_ty) : SE_Base.b_ty :=
  match A with
  | S_Base.b_Unit => SE_Base.b_Unit
  | S_Base.b_S => SE_Base.b_S
  | S_Base.b_Prod A1 A2 => SE_Base.b_Prod (embed_b_ty A1) (embed_b_ty A2)
  end.

Fixpoint embed_b_tm (t : S_Base.b_tm) : @SE_Base.b_tm Empty_Sign :=
  match t with
  | S_Base.b_id => @SE_Base.b_id Empty_Sign
  | S_Base.b_comp f g => @SE_Base.b_comp Empty_Sign (embed_b_tm f) (embed_b_tm g)
  | S_Base.b_unit => @SE_Base.b_unit Empty_Sign
  | S_Base.b_pair f g => @SE_Base.b_pair Empty_Sign (embed_b_tm f) (embed_b_tm g)
  | S_Base.b_fst => @SE_Base.b_fst Empty_Sign
  | S_Base.b_snd => @SE_Base.b_snd Empty_Sign
  end.

Fixpoint embed_ty (Phi : S_Hyper.h_ty) : @SE_Hyper.h_ty Empty_Sign :=
  match Phi with
  | S_Hyper.Ty_Unit => @SE_Hyper.Ty_Unit Empty_Sign
  | S_Hyper.Ty_Void => @SE_Hyper.Ty_Void Empty_Sign
  | S_Hyper.Ty_Prod A B => @SE_Hyper.Ty_Prod Empty_Sign (embed_ty A) (embed_ty B)
  | S_Hyper.Ty_Sum A B => @SE_Hyper.Ty_Sum Empty_Sign (embed_ty A) (embed_ty B)
  | S_Hyper.Ty_Arrow A B => @SE_Hyper.Ty_Arrow Empty_Sign (embed_ty A) (embed_ty B)
  | S_Hyper.Ty_Atom p t => @SE_Hyper.Ty_Atom Empty_Sign p (embed_b_tm t)
  | S_Hyper.Ty_All A Body => @SE_Hyper.Ty_All Empty_Sign (embed_b_ty A) (embed_ty Body)
  | S_Hyper.Ty_Ex A Body => @SE_Hyper.Ty_Ex Empty_Sign (embed_b_ty A) (embed_ty Body)
  end.

(* ================================================================= *)
(* 3. A GÉPELÉS ÉS A JÓL-FORMÁLTSÁG ÁTEMELÉSE (SYNTACTIC LIFTING)    *)
(* ================================================================= *)

Lemma embed_b_typing : forall I t A,
  S_Base.base_typing I t A ->
  @SE_Base.base_typing Empty_Sign (embed_b_ty I) (embed_b_tm t) (embed_b_ty A).
Proof.
  intros I t A H. induction H; simpl.
  - apply SE_Base.BT_Id.
  - eapply SE_Base.BT_Comp; eauto.
  - apply SE_Base.BT_Unit.
  - apply SE_Base.BT_Pair; auto.
  - apply SE_Base.BT_Fst.
  - apply SE_Base.BT_Snd.
Defined.

Lemma embed_wf : forall I Phi,
  S_Hyper.WellFormed I Phi ->
  @SE_Hyper.WellFormed Empty_Sign (embed_b_ty I) (embed_ty Phi).
Proof.
  intros I Phi H. induction H; simpl.
  - apply SE_Hyper.WF_Unit.
  - apply SE_Hyper.WF_Void.
  - apply SE_Hyper.WF_Prod; auto.
  - apply SE_Hyper.WF_Sum; auto.
  - apply SE_Hyper.WF_Arrow; auto.
  - eapply SE_Hyper.WF_Atom. apply embed_b_typing. exact b.
  - apply SE_Hyper.WF_All. exact IHWellFormed.
  - apply SE_Hyper.WF_Ex. exact IHWellFormed.
Defined.

(* ================================================================= *)
(* 3. A FELEJTŐ FUNKTOR (Vissza a Simple bázisra)                    *)
(* ================================================================= *)

Fixpoint forget_b_ty (A : SE_Base.b_ty) : S_Base.b_ty :=
  match A with
  | SE_Base.b_Unit => S_Base.b_Unit
  | SE_Base.b_S => S_Base.b_S
  | SE_Base.b_Prod A1 A2 => S_Base.b_Prod (forget_b_ty A1) (forget_b_ty A2)
  end.

Fixpoint forget_b_tm (t : @SE_Base.b_tm Empty_Sign) : S_Base.b_tm :=
  match t with
  | SE_Base.b_id => S_Base.b_id
  | SE_Base.b_comp f g => S_Base.b_comp (forget_b_tm f) (forget_b_tm g)
  | SE_Base.b_unit => S_Base.b_unit
  | SE_Base.b_pair f g => S_Base.b_pair (forget_b_tm f) (forget_b_tm g)
  | SE_Base.b_fst => S_Base.b_fst
  | SE_Base.b_snd => S_Base.b_snd
  | SE_Base.b_const _ s => match s with end (* Az Empty_Sign varázslata! *)
  end.

Lemma forget_base_typing : forall {I A} {t : @SE_Base.b_tm Empty_Sign},
  @SE_Base.base_typing Empty_Sign I t A -> 
  S_Base.base_typing (forget_b_ty I) (forget_b_tm t) (forget_b_ty A).
Proof.
  intros I A t dt. induction dt; simpl.
  - apply S_Base.BT_Id.
  - eapply S_Base.BT_Comp; eauto.
  - apply S_Base.BT_Unit.
  - apply S_Base.BT_Pair; eauto.
  - apply S_Base.BT_Fst.
  - apply S_Base.BT_Snd.
  - destruct s.
Defined.

(* Itt direkt, kézzel megadjuk a Coq-nak a derivációkat, hogy az eauto ne tévedjen el. *)
(* Segédlemma: A Simple nyelvben a CompPair nem axióma, hanem levezethető tétel! 
   Itt bebizonyítjuk a Beta és Eta szabályokból. *)
Lemma S_Base_CompPair : forall A B C D f g h 
  (df : S_Base.base_typing B f C)
  (dg : S_Base.base_typing B g D)
  (dh : S_Base.base_typing A h B),
  S_Base.base_equiv A (S_Base.b_Prod C D) 
    (S_Base.b_comp (S_Base.b_pair f g) h) 
    (S_Base.b_pair (S_Base.b_comp f h) (S_Base.b_comp g h)).
Proof.
  intros A B C D f g h df dg dh.
  assert (dX : S_Base.base_typing A (S_Base.b_comp (S_Base.b_pair f g) h) (S_Base.b_Prod C D)).
  { eapply S_Base.BT_Comp. eapply S_Base.BT_Pair. exact df. exact dg. exact dh. }
  
  (* ELŐSZÖR jön a tranzitivitás! *)
  eapply S_Base.BE_Trans. 
  1: { 
    (* És csak az első részcélra alkalmazzuk a Szimmetriát + Eta szabályt *)
    eapply S_Base.BE_Sym. 
    eapply S_Base.BE_EtaPair. 
    exact dX. 
  }
  
  (* Most a felfújt formulát kongruenciával kettészedjük *)
  eapply S_Base.BE_CongPair.
  - (* Bal oldal: fst ∘ (<f, g> ∘ h) ≡ f ∘ h *)
    eapply S_Base.BE_Trans.
    + eapply S_Base.BE_Assoc.
      * exact dh.
      * eapply S_Base.BT_Pair. exact df. exact dg.
      * apply S_Base.BT_Fst.
    + eapply S_Base.BE_CongComp.
      * eapply S_Base.BE_BetaFst. exact df. exact dg.
      * eapply S_Base.BE_Refl. exact dh.
      
  - (* Jobb oldal: snd ∘ (<f, g> ∘ h) ≡ g ∘ h *)
    eapply S_Base.BE_Trans.
    + eapply S_Base.BE_Assoc.
      * exact dh.
      * eapply S_Base.BT_Pair. exact df. exact dg.
      * apply S_Base.BT_Snd.
    + eapply S_Base.BE_CongComp.
      * eapply S_Base.BE_BetaSnd. exact df. exact dg.
      * eapply S_Base.BE_Refl. exact dh.
Qed.

(* A Felejtő Lemma: Sorrendtől független intelligens mintaillesztéssel *)
Lemma forget_base_equiv_core : forall I J f g df dg,
  @SE_Base.base_equiv Empty_Sign I J f g df dg -> 
  S_Base.base_equiv (forget_b_ty I) (forget_b_ty J) (forget_b_tm f) (forget_b_tm g).
Proof.
  intros I J f g df dg Heq.
  induction Heq; simpl.
  
  (* Zseniális segédtaktika: megkeresi a gépelést a kontextusban, és
     szintaktikus illesztés (apply) helyett definíciós egyenlőséget (exact) használ! *)
  Ltac solve_typing :=
    match goal with
    | H : @SE_Base.base_typing Empty_Sign _ ?t _ |- S_Base.base_typing _ (forget_b_tm ?t) _ =>
        exact (forget_base_typing H)
    end.
    
  - (* 1. BE_Refl *)
    eapply S_Base.BE_Refl. solve_typing.
    
  - (* 2. BE_Sym *)
    eapply S_Base.BE_Sym. exact IHHeq.
    
  - (* 3. BE_Trans *)
    eapply S_Base.BE_Trans. exact IHHeq1. exact IHHeq2.
    
  - (* 4. BE_CongComp *)
    eapply S_Base.BE_CongComp. exact IHHeq2. exact IHHeq1.
    
  - (* 5. BE_CongPair *)
    eapply S_Base.BE_CongPair. exact IHHeq1. exact IHHeq2.
    
  - (* 6. BE_Assoc *)
    eapply S_Base.BE_Assoc; solve_typing.
    
  - (* 7. BE_IdL *)
    eapply S_Base.BE_IdL. solve_typing.
    
  - (* 8. BE_IdR *)
    eapply S_Base.BE_IdR. solve_typing.
    
  - (* 9. BE_BetaFst *)
    eapply S_Base.BE_BetaFst; solve_typing.
    
  - (* 10. BE_BetaSnd *)
    eapply S_Base.BE_BetaSnd; solve_typing.
    
  - (* 11. BE_EtaPair *)
    eapply S_Base.BE_EtaPair. solve_typing.
    
  - (* 12. BE_Terminal *)
    eapply S_Base.BE_Terminal.
    + solve_typing.
    + apply S_Base.BT_Unit.
    
  - (* 13. BE_CompPair *)
    eapply S_Base_CompPair; solve_typing.
Qed.

(* ================================================================= *)
(* 4. A SZINTAKTIKUS MODELL KITERJESZTÉSE                            *)
(* ================================================================= *)

(* FIGYELEM: A 'Definition'-öket 'Notation'-re cseréltük! 
   Ez megakadályozza, hogy a Coq elrejtse a típusokat az alias mögé, 
   így a morfizmusok azonnal láthatóan 'hom_base' típusúak lesznek. *)
Notation S_C   := (@S_Comp.Base_SetoidCategory nat).
Notation S_CC  := (@S_Comp.Base_CartesianCategory nat).
Notation S_TSC := (@S_Comp.Base_TwoSortCategory nat).
Notation S_GF  := (@S_Comp.Syntactic_GoodFibration nat).
Notation S_SGF := (@S_Comp.Syntactic_StrictGoodFibration nat).

(* 1. Bővített Szignatúra Modell *)
Instance Expanded_BEM : @BaseSignatureModel Empty_Sign S_C S_CC S_TSC.
Proof.
  constructor. intros I A s. destruct s.
Defined.

(* ----------------------------------------------------------------- *)
(* HÍD-LEMMÁK: Az interpretáció és a felejtés pontosan ugyanaz!      *)
(* ----------------------------------------------------------------- *)

Lemma expand_interp_ty_term : forall A, 
  @interp_ty S_C S_CC S_TSC A = forget_b_ty A.
Proof.
  intros A. induction A; simpl; try reflexivity.
  f_equal; eauto.
Qed.

Lemma expand_interp_tm_term : forall I J f (df : @SE_Base.base_typing Empty_Sign I f J),
  S_Comp.b_tm_of _ _ (@interp_tm Empty_Sign S_C S_CC S_TSC Expanded_BEM I J f df) = forget_b_tm f.
Proof.
  intros I J f df.
  induction df; simpl; try reflexivity.
  - f_equal; eauto.
  - f_equal; eauto.
  - destruct s.
Qed.

(* ----------------------------------------------------------------- *)
(* 2. Bővített Koherencia Modell - A Végleges Katarzis               *)
(* ----------------------------------------------------------------- *)

Instance Expanded_CBM : @CoherentBaseModel Empty_Sign S_C S_CC S_TSC Expanded_BEM.
Proof.
  constructor. intros A B f d1 d2.
  
  (* Behozzuk a két híd-lemmát, ahogy eddig *)
  pose proof (expand_interp_tm_term A B f d1) as H1.
  pose proof (expand_interp_tm_term A B f d2) as H2.
  
  (* A Rocq varázsfegyvere: a 'repeat red.' név nélkül addig bontja le 
     a legkülső "dobozokat" (a ≅ jelet, a kategória hom_equiv-jét, 
     és a base_hom_equiv-et), amíg a stabil, Inductive bázis relációhoz nem ér! *)
  repeat red.
  
  (* A cél most már gyönyörűen tiszta és kibontott: 
     S_Base.base_equiv ... (S_Comp.b_tm_of ...) (S_Comp.b_tm_of ...) *)
  rewrite H1. rewrite H2.
  
  (* A típusokat is a helyére pattintjuk *)
  rewrite (expand_interp_ty_term A).
  rewrite (expand_interp_ty_term B).
  
  (* És a Reflexivitás gondolkodás nélkül lezárja a bizonyítást! *)
  eapply S_Base.BE_Refl.
  apply forget_base_typing. exact d1.
Defined.

(* ----------------------------------------------------------------- *)
(* 3. A FŐMŰ: A kiterjesztett Hyper Modell                           *)
(* ----------------------------------------------------------------- *)

Instance Expanded_HM : @SE_Mod.HyperModel Empty_Sign S_C S_CC S_TSC S_GF S_SGF Expanded_BEM Expanded_CBM.
Proof.
  unshelve econstructor.
  - (* i_atom *) intros p t I A dt.
    exists (S_Hyper.Ty_Atom p (forget_b_tm t)).
    pose proof (S_Hyper.WF_Atom (forget_b_ty I) p (forget_b_tm t) (forget_b_ty A) (forget_base_typing dt)) as Hwf.
    unfold S_Comp.syn_obj.
    rewrite (expand_interp_ty_term I).
    exact Hwf.
    
  - (* i_atom_pb *) intros p t I J A f df dt.
    apply S_Comp.syn_iso_from_eq. simpl. 
    
    (* Itt a megoldás: kinyitjuk a morfizmus (syn_hom) ÉS az objektum (syn_obj) 
       dobozait is, hogy a b_tm_of paraméterei meztelenül álljanak! *)
    unfold S_Comp.syn_hom, S_Comp.syn_obj.
    rewrite expand_interp_tm_term.
    
    (* A csere után a bal és a jobb oldal már tényleg karakterre megegyezik! *)
    reflexivity.
    
    - (* i_atom_cong *) intros p t1 t2 I A d1 d2 Heq.
    apply S_Comp.syn_iso_from_equiv. simpl. 
    
    (* 1. Először a híd-lemmával átírjuk az interp_ty-t forget_b_ty-ra, 
          hogy a típusok tökéletesen illeszkedjenek! *)
    rewrite (expand_interp_ty_term I).
    
    (* 2. Ráküldjük a FEQ_Atom szabályt. Ez legenerálja a 3 al-célt. *)
    eapply S_Hyper.FEQ_Atom.
    
    (* 1/3 Cél: Az első term (t1) gépelése *)
    + eapply forget_base_typing. exact d1.
    
    (* 2/3 Cél: A második term (t2) gépelése *)
    + apply forget_base_typing. exact d2.
    
    (* 3/3 Cél: A két term ekvivalenciája (Heq) *)
    + eapply forget_base_equiv_core. exact Heq.
Defined.

(* ================================================================= *)
(* 5. AZ AGREEMENT LEMMA ÉS A KONZERVATIVITÁS                        *)
(* ================================================================= *)

Lemma embed_forget_b_ty : forall A, forget_b_ty (embed_b_ty A) = A.
Proof. induction A; simpl; f_equal; auto. Qed.

Lemma embed_forget_b_tm : forall t, forget_b_tm (embed_b_tm t) = t.
Proof. induction t; simpl; f_equal; auto. Qed.

(* A kiterjesztett modellben kiértékelt beágyazott formula hajszálpontosan visszadja az eredetit! *)
(* A kiterjesztett modellben kiértékelt beágyazott formula hajszálpontosan visszadja az eredetit! *)
Lemma interpretation_agreement : forall I Phi (wf : S_Hyper.WellFormed I Phi),
  (@SE_Mod.interp_h_ty Empty_Sign S_C S_CC S_TSC S_GF S_SGF Expanded_BEM Expanded_CBM Expanded_HM
    (embed_b_ty I) (embed_ty Phi) (embed_wf I Phi wf) : S_Hyper.h_ty) = Phi.
Proof.
  intros I Phi wf.
  induction wf; simpl; try reflexivity.
  
  - (* WF_Prod *) f_equal; auto.
  - (* WF_Sum *) f_equal; auto.
  - (* WF_Arrow *) f_equal; auto.
  
  - (* WF_Atom *) 
    f_equal. apply embed_forget_b_tm.
    
  - (* WF_All *) 
    f_equal. 
    + (* A híd-lemma varázslata: kinyitjuk a dobozt, és lecseréljük az interpretációt! *)
      unfold S_Comp.syn_obj. 
      rewrite expand_interp_ty_term. 
      apply embed_forget_b_ty.
    + exact IHwf.
    
  - (* WF_Ex *) 
    f_equal. 
    + (* Ugyanaz a trükk a létezési kvantorra is *)
      unfold S_Comp.syn_obj. 
      rewrite expand_interp_ty_term. 
      apply embed_forget_b_ty.
    + exact IHwf.
Qed.


(* ÉS VÉGÜL: A Konzervativitás Tétele *)
Theorem simple_ext_is_conservative : forall (Phi : S_Hyper.h_ty) (wf : S_Hyper.WellFormed S_Base.b_Unit Phi),
  (exists (p_ext : @SE_Hyper.h_tm Empty_Sign), 
      inhabited (@SE_Hyper.h_derivation Empty_Sign SE_Base.b_Unit nil p_ext (embed_ty Phi))) ->
  (exists (p_simp : S_Hyper.h_tm), 
      inhabited (S_Hyper.h_derivation S_Base.b_Unit nil p_simp Phi)).
Proof.
  intros Phi wf [p_ext [D_ext]].
  
  (* 1. A Simple_Ext Soundness miatt a p_ext levezetés egy szemantikai morfizmust ad 
        a most kiterjesztett Szintaktikus Modellünkben! *)
  pose proof (@SE_Mod.hyper_soundness_inhabited Empty_Sign S_C S_CC S_TSC S_GF S_SGF Expanded_BEM Expanded_CBM Expanded_HM
    _ _ _ _ D_ext (@SE_Hyper.WFC_nil Empty_Sign _) (embed_wf _ _ wf)) as H_sem.
    
(* 2. Kicsomagoljuk a morfizmust! *)
  destruct H_sem as [p_simp D_simp].
  
  (* 3. Előkészítjük a híd-lemmát explicit formában a célunkra *)
  pose proof (interpretation_agreement S_Base.b_Unit Phi wf) as Heq_Phi.
  
  (* Szinkronizáljuk a Heq_Phi-t a D_simp-pel a change taktikával! 
     SEMMIT sem unfold-olunk, így a 'ty_val' burkolatok tökéletesen egyezni fognak! *)
  change (embed_b_ty S_Base.b_Unit) with SE_Base.b_Unit in Heq_Phi.
  
  (* 4. A kontextus egyenlőségét is felírjuk *)
  assert (Heq_Ctx : (@SE_Mod.interp_h_ctx Empty_Sign S_C S_CC S_TSC S_GF S_SGF Expanded_BEM Expanded_CBM Expanded_HM 
      SE_Base.b_Unit nil (@SE_Hyper.WFC_nil Empty_Sign _) : S_Hyper.h_ty) = S_Hyper.Ty_Unit).
  { reflexivity. }
  
  (* 5. Mivel nem unfold-oltunk semmit, a rewrite szó szerint megtalálja a mintákat! *)
  rewrite Heq_Phi in D_simp.
  rewrite Heq_Ctx in D_simp.
  
  (* 6. Ugyanaz a Lam-App trükk, mint a Completeness végén *)
  exists (S_Hyper.tm_app (S_Hyper.tm_lam S_Hyper.Ty_Unit p_simp) S_Hyper.tm_unit).
  
  (* Felépítjük az inhabited burkolatot *)
  constructor. 
  
  eapply S_Hyper.HD_App.
  - apply S_Hyper.HD_Lam. 
    (* A D_simp bázis indexe 'S_Comp.syn_obj (interp_ty SE_Base.b_Unit)', 
       ami definíciósan egyenlő 'S_Base.b_Unit'-tel, így az exact elfogadja! *)
    exact D_simp.
  - apply S_Hyper.HD_Unit. apply S_Hyper.WFC_nil.
Qed.


(* ================================================================= *)
(* 6. A MÁSIK IRÁNY: BIZONYÍTÁSOK ÁTEMELÉSE (SYNTACTIC LIFTING)     *)
(* ================================================================= *)

(* A környezet (kontextus) beágyazása elemenként *)
Definition embed_ctx (G : list S_Hyper.h_ty) : list (@SE_Hyper.h_ty Empty_Sign) :=
  map embed_ty G.

(* Segédlemmák a változó-keresések átemeléséhez (In és nth_error esetére is) *)
Lemma embed_ctx_In : forall Phi G,
  In Phi G -> In (embed_ty Phi) (embed_ctx G).
Proof.
  intros Phi G H. unfold embed_ctx. apply in_map; auto.
Qed.

Lemma embed_ctx_nth_error : forall G n Phi,
  nth_error G n = Some Phi ->
  nth_error (embed_ctx G) n = Some (embed_ty Phi).
Proof.
  induction G; intros n Phi H.
  - destruct n; simpl in H; discriminate.
  - destruct n; simpl in H; simpl.
    + injection H as ->. reflexivity.
    + apply IHG. exact H.
Qed.

(* --- 1. HÍD-LEMMA: Kontextusok Jól-formáltsága --- *)
(* Ha egy kontextus jó a Simple-ben, akkor a beágyazottja is jó a Simple_Ext-ben *)
Lemma embed_wf_ctx : forall I G,
  S_Hyper.wf_ctx I G -> @SE_Hyper.wf_ctx Empty_Sign (embed_b_ty I) (embed_ctx G).
Proof.
  intros I G w_ctx. induction w_ctx; simpl.
  - (* Nil ág: az üres kontextus jól formált *)
    constructor.
  - (* Cons ág: Phi :: G *)
    constructor.
    + (* 1/2 Cél: A formula jól formált (w) *)
      apply embed_wf. exact w.
    + (* 2/2 Cél: A maradék kontextus jól formált (IHw_ctx) *)
      exact IHw_ctx.
Qed.

(* --- 2. HÍD-LEMMA: Helyettesítések (Pullback) Átemelése --- *)
(* A típus-beágyazás felcserélhető a form_pullback helyettesítéssel *)
Lemma embed_form_pullback : forall f Phi,
  embed_ty (S_Hyper.form_pullback f Phi) = 
  SE_Hyper.form_pullback (embed_b_tm f) (embed_ty Phi).
Proof.
  intros f Phi.
  
  (* A VARÁZSLAT: Visszadobjuk az 'f'-et a célba az indukció előtt, 
     így az Indukciós Hipotézis (IH) minden 'f'-re (akár a megváltozottra is) igaz lesz! *)
  generalize dependent f. 
  
  induction Phi; intros f; simpl; f_equal; auto.
Qed.

(* --- 3. HÍD-LEMMA: Kontextus Helyettesítés Átemelése --- *)
(* Az átemelés és a listán végzett helyettesítés (lifting) sorrendje felcserélhető *)
Lemma embed_ctx_map_pullback : forall f G,
  embed_ctx (map (S_Hyper.form_pullback f) G) = 
  map (SE_Hyper.form_pullback (embed_b_tm f)) (embed_ctx G).
Proof.
  intros f G. induction G; simpl; f_equal; auto.
  apply embed_form_pullback.
Qed.


Theorem embed_derivation : forall I G p Phi,
  S_Hyper.h_derivation I G p Phi ->
  { p_ext : @SE_Hyper.h_tm Empty_Sign & @SE_Hyper.h_derivation Empty_Sign (embed_b_ty I) (embed_ctx G) p_ext (embed_ty Phi) }.
Proof.
  intros I G p Phi D.
  induction D; simpl.
  
  all: repeat match goal with
       | H : { _ & _ } |- _ => destruct H as [?p_ext ?D_ext]
       end.
       
  all: try rewrite embed_form_pullback in *.
  all: try rewrite embed_ctx_map_pullback in *.
  
  all: try solve [
    eexists; econstructor; 
    eauto 10 using embed_wf, embed_b_typing, embed_wf_ctx
  ].
  
  (* HD_Var0 *)
  - eexists (SE_Hyper.tm_var 0).
    eapply SE_Hyper.HD_Var0.
    + apply embed_wf_ctx; assumption.
    + apply embed_wf; assumption.
  
  (* HD_VarS *)
  - eexists (SE_Hyper.tm_var (S i)).
    eapply SE_Hyper.HD_VarS.
    + exact D_ext.
    + apply embed_wf; assumption.

  (* HD_All_Intro *)
  - eexists. eapply SE_Hyper.HD_All_Intro. apply embed_wf_ctx; eassumption. exact D_ext.
  
  (* HD_Ex_Intro *)
  - eexists. eapply SE_Hyper.HD_Ex_Intro. apply embed_wf; eassumption. apply embed_b_typing; eassumption. exact D_ext.
  
  (* HD_Ex_Elim *)
  - eexists. eapply SE_Hyper.HD_Ex_Elim. apply embed_wf; eassumption. exact D_ext1. exact D_ext2.
  
  (* HD_Ctx_Conv *)
  - eexists. eapply SE_Hyper.HD_Ctx_Conv. exact D_ext. 
    (* Ha itt elakad a ctx_equiv miatt, definiálni kell hozzá egy embed_ctx_equiv híd-lemmát, ahogy a wf_ctx-hez is. *)
    eauto. eauto.
Qed.