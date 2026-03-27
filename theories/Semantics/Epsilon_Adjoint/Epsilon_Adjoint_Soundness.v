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
Proof.
  intros Sign I J b g dg.
  unfold b_subst_ext.
  apply BT_Pair.
  - eapply BT_Comp. exact dg. apply BT_Fst.
  - apply BT_Snd.
Defined.

(* Helyettesítési izomorfizmusok a belső nyelv és a Fibrációs funktorok között. *)
Lemma form_subst_iso : 
  forall {Sign : Type} {SM : SkolemMapping Sign} 
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} 
  {EHM : EpsilonHyperModel SGF}
  (I A : b_ty) (f : @b_tm Sign) (df : base_typing I f A) (Phi : @h_ty Sign),
  interp_h_ty I (form_subst f Phi) ≅O @fobj _ _ (Pullback (interp_tm df)) (interp_h_ty A Phi).
Proof.
  intros Sign SM C CC TSC BEM GF SGF EHM.
  (* Mivel a Phi a lemma végén van, revertáljuk a többit, hogy az indukciós hipotézis (IH) 
     megkapja az I, A, f, df paramétereket (hogy a kvantorok ágaiban frissülhessenek a kontextusok). *)
  intros I A f df Phi.
  revert I A f df.
  
  induction Phi; intros I J g dg; simpl.
  - symmetry. apply pb_term_iso.
  - symmetry. apply pb_init_iso.
  - eapply iso_trans.
    + apply (prod_iso_cong (IHPhi1 I J g dg) (IHPhi2 I J g dg)).
    + symmetry. apply pb_prod_iso.
  - eapply iso_trans.
    + apply (coprod_iso_cong (IHPhi1 I J g dg) (IHPhi2 I J g dg)).
    + symmetry. apply pb_coprod_iso.
  - eapply iso_trans.
    + apply (exp_iso_cong (IHPhi2 I J g dg) (IHPhi1 I J g dg)).
    + symmetry. apply pb_exp_iso.
  - symmetry. apply (i_atom_pb n b I J g dg).
  - eapply iso_trans.
    + apply pi_iso_cong.
      (* JAVÍTVA: b_pullback_ext -> b_subst_ext, typing_pullback_ext -> typing_subst_ext *)
      exact (IHPhi (b_Prod I b) (b_Prod J b) (b_subst_ext g) (typing_subst_ext dg)).
    + symmetry. apply beck_chevalley_pi.
  - eapply iso_trans.
    + apply sigma_iso_cong.
      (* JAVÍTVA: Itt is frissítve lettek a strukturális lemmák nevei! *)
      exact (IHPhi (b_Prod I b) (b_Prod J b) (b_subst_ext g) (typing_subst_ext dg)).
    + symmetry. apply beck_chevalley_sigma.
Defined.

Lemma ctx_subst_iso : 
  forall {Sign : Type} {SM : SkolemMapping Sign} 
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} 
  {EHM : EpsilonHyperModel SGF}
  (I A : b_ty) (G : @h_context Sign),
  interp_h_ctx (b_Prod I A) (ctx_subst b_fst G) ≅O @fobj _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (A:=I) (B:=A)))) (interp_h_ctx I G).
Proof.
  intros Sign SM C CC TSC BEM GF SGF EHM I A G.
  induction G as [| Phi G' IHG']; simpl.
  - (* Báziseset: Üres kontextus (terminális objektum) visszahúzása *)
    symmetry. apply pb_term_iso.
  - (* Indukciós lépés: Kontextus kiterjesztése (szorzat) *)
    eapply iso_trans.
    + (* Itt hívjuk meg az általános form_subst_iso-t a b_fst-re (pi1) a régi fst_iso helyett! *)
      apply (prod_iso_cong IHG' (form_subst_iso (b_Prod I A) I b_fst (BT_Fst (Sign:=Sign) (A:=I) (B:=A)) Phi)).
    + (* A szorzat visszahúzása izomorf a visszahúzások szorzatával *)
      symmetry. apply pb_prod_iso.
Defined.

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
Proof. 
  intros Sign SM C CC BCCC BiCCC TSC BEM GF SGF EHM I J f g Phi df dg Heq Hwf.
  revert I f g df dg Heq.
  induction Hwf; intros I' f' g' df' dg' Heq'; simpl.
  
  - apply iso_refl. (* Unit *)
  - apply iso_refl. (* Void *)
  - apply prod_iso_cong. { eapply IHHwf1. exact Heq'. } { eapply IHHwf2. exact Heq'. }
  - apply coprod_iso_cong. { eapply IHHwf1. exact Heq'. } { eapply IHHwf2. exact Heq'. }
  - apply exp_iso_cong. { eapply IHHwf2. exact Heq'. } { eapply IHHwf1. exact Heq'. }
  - eapply i_atom_cong_global. eapply BE_CongComp.
    + exact Heq'. + exact (BE_Refl _ _ _ b).
  - apply pi_iso_cong. eapply (IHHwf (b_Prod I' A) (b_subst_ext f') (b_subst_ext g')).
    unfold b_subst_ext. eapply BE_CongPair.
    + eapply BE_CongComp. * exact (BE_Refl _ _ _ BT_Fst). * exact Heq'.
    + exact (BE_Refl _ _ _ BT_Snd).
  - apply sigma_iso_cong. eapply (IHHwf (b_Prod I' A) (b_subst_ext f') (b_subst_ext g')).
    unfold b_subst_ext. eapply BE_CongPair.
    + eapply BE_CongComp. * exact (BE_Refl _ _ _ BT_Fst). * exact Heq'.    
    + exact (BE_Refl _ _ _ BT_Snd).
Defined. 

Lemma interp_subst_id : forall {Sign : Type} {SM : SkolemMapping Sign} 
  {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C} 
  {BiCCC : BiCartesianClosedCategory BCCC} {TSC : TwoSortCategory C} 
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} 
  {EHM : EpsilonHyperModel SGF} (I : b_ty) (Phi : @h_ty Sign),
  WellFormed I Phi ->
  (interp_h_ty I (form_subst b_id Phi)) ≅O (interp_h_ty I Phi).
Proof. 
  intros Sign SM C CC BCCC BiCCC TSC BEM GF SGF EHM I Phi Hwf.
  induction Hwf.
  - simpl. apply iso_refl.
  - simpl. apply iso_refl.
  - simpl. apply prod_iso_cong; assumption.
  - simpl. apply coprod_iso_cong; assumption.
  - simpl. apply exp_iso_cong; assumption.
  - simpl. eapply i_atom_cong_global. apply BE_IdR.
  - simpl. apply pi_iso_cong. eapply iso_trans.
    + eapply (interp_subst_cong (b_Prod I A) (b_Prod I A) (b_subst_ext b_id) b_id Phi). (* JAVÍTVA: Body -> Phi *)
      * unfold b_subst_ext. eapply BE_Trans. 2: { apply BE_EtaPair. }
        eapply BE_CongPair.
        -- eapply BE_Trans. apply BE_IdL. eapply BE_Sym. apply BE_IdR.
        -- eapply BE_Sym. apply BE_IdR.
      * exact Hwf.
    + exact IHHwf.
  - simpl. apply sigma_iso_cong. eapply iso_trans.
    + eapply (interp_subst_cong (b_Prod I A) (b_Prod I A) (b_subst_ext b_id) b_id Phi). (* JAVÍTVA: Body -> Phi *)
      * unfold b_subst_ext. eapply BE_Trans. 2: { apply BE_EtaPair. }
        eapply BE_CongPair.
        -- eapply BE_Trans. apply BE_IdL. eapply BE_Sym. apply BE_IdR.
        -- eapply BE_Sym. apply BE_IdR.
      * exact Hwf.
    + exact IHHwf.
      Unshelve. exact I. exact A. exact b.
Defined. 

Lemma interp_subst_comp : forall {Sign : Type} {SM : SkolemMapping Sign} 
  {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C} 
  {BiCCC : BiCartesianClosedCategory BCCC} {TSC : TwoSortCategory C} 
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} 
  {EHM : EpsilonHyperModel SGF} (I J K: b_ty) (f g : @b_tm Sign) (Phi : @h_ty Sign)
  (df : base_typing J f K) (dg : base_typing I g J),
  WellFormed K Phi ->
  (interp_h_ty I (form_subst (b_comp f g) Phi)) ≅O (interp_h_ty I (form_subst g (form_subst f Phi))).
Proof.
  intros Sign SM C CC BCCC BiCCC TSC BEM GF SGF EHM I J K f g Phi df dg Hwf.
  revert I J f g df dg.
  induction Hwf; intros I0 J0 f0 g0 df0 dg0; simpl.
  - apply iso_refl.
  - apply iso_refl.
  - apply prod_iso_cong. { apply (IHHwf1 I0 J0 f0 g0 df0 dg0). } { apply (IHHwf2 I0 J0 f0 g0 df0 dg0). }
  - apply coprod_iso_cong. { apply (IHHwf1 I0 J0 f0 g0 df0 dg0). } { apply (IHHwf2 I0 J0 f0 g0 df0 dg0). }
  - apply exp_iso_cong. { apply (IHHwf2 I0 J0 f0 g0 df0 dg0). } { apply (IHHwf1 I0 J0 f0 g0 df0 dg0). }
  - eapply i_atom_cong_global. exact (BE_Assoc I0 J0 I A g0 f0 t dg0 df0 b).
  - apply pi_iso_cong. eapply iso_trans.
    + eapply (interp_subst_cong (b_Prod I0 A) (b_Prod I A) 
                             (b_subst_ext (b_comp f0 g0)) 
                             (b_comp (b_subst_ext f0) (b_subst_ext g0)) Phi). (* JAVÍTVA: Body -> Phi *)
      * unfold b_subst_ext. eapply BE_Trans. 
        { eapply BE_CongPair. - eapply BE_Sym. exact (BE_Assoc _ _ _ _ _ _ _ BT_Fst dg0 df0). - exact (BE_Refl _ _ _ BT_Snd). }
        eapply BE_Sym. eapply BE_Trans. 
        { exact (BE_CompPair _ _ _ _ _ _ _ (BT_Comp df0 BT_Fst) BT_Snd (BT_Pair (BT_Comp dg0 BT_Fst) BT_Snd)). } 
        eapply BE_CongPair.
        -- eapply BE_Trans. { eapply BE_Sym. exact (BE_Assoc _ _ _ _ _ _ _ (BT_Pair (BT_Comp dg0 BT_Fst) BT_Snd) BT_Fst df0). }
           eapply BE_CongComp. ++ apply BE_BetaFst. ++ exact (BE_Refl _ _ _ df0).    
        -- apply BE_BetaSnd.    
      * exact Hwf.
    + eapply (IHHwf (b_Prod I0 A) (b_Prod J0 A) (b_subst_ext f0) (b_subst_ext g0)).
      * unfold b_subst_ext. eapply BT_Pair. -- eapply BT_Comp. exact df0. apply BT_Fst. -- apply BT_Snd.
      * unfold b_subst_ext. eapply BT_Pair. -- eapply BT_Comp. exact dg0. apply BT_Fst. -- apply BT_Snd.
  - apply sigma_iso_cong. eapply iso_trans.
    + eapply (interp_subst_cong (b_Prod I0 A) (b_Prod I A) 
                             (b_subst_ext (b_comp f0 g0)) 
                             (b_comp (b_subst_ext f0) (b_subst_ext g0)) Phi). (* JAVÍTVA: Body -> Phi *)
      * unfold b_subst_ext. eapply BE_Trans. 
        { eapply BE_CongPair. - eapply BE_Sym. exact (BE_Assoc _ _ _ _ _ _ _ BT_Fst dg0 df0). - exact (BE_Refl _ _ _ BT_Snd). }
        eapply BE_Sym. eapply BE_Trans. 
        { exact (BE_CompPair _ _ _ _ _ _ _ (BT_Comp df0 BT_Fst) BT_Snd (BT_Pair (BT_Comp dg0 BT_Fst) BT_Snd)). } 
        eapply BE_CongPair.
        -- eapply BE_Trans. { eapply BE_Sym. exact (BE_Assoc _ _ _ _ _ _ _ (BT_Pair (BT_Comp dg0 BT_Fst) BT_Snd) BT_Fst df0). }
           eapply BE_CongComp. ++ apply BE_BetaFst. ++ exact (BE_Refl _ _ _ df0).    
        -- apply BE_BetaSnd.    
      * exact Hwf.
    + eapply (IHHwf (b_Prod I0 A) (b_Prod J0 A) (b_subst_ext f0) (b_subst_ext g0)).
      * unfold b_subst_ext. eapply BT_Pair. -- eapply BT_Comp. exact df0. apply BT_Fst. -- apply BT_Snd.
      * unfold b_subst_ext. eapply BT_Pair. -- eapply BT_Comp. exact dg0. apply BT_Fst. -- apply BT_Snd.
Defined.
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
Proof. 
  intros Sign SM C CC BCCC BiCCC TSC BEM GF SGF EHM AdEHM I Phi Psi Heq.
  induction Heq; simpl.

  - (* FE_Atom *) eapply i_atom_cong_global. exact b.
  - (* FE_Refl *) apply iso_refl.
  - (* FE_Sym *) symmetry. apply IHHeq.
  - (* FE_Trans *) eapply iso_trans. { apply IHHeq1. } { apply IHHeq2. }
  - (* FE_Prod *) apply prod_iso_cong. { apply IHHeq1. } { apply IHHeq2. }
  - (* FE_Sum *) apply coprod_iso_cong. { apply IHHeq1. } { apply IHHeq2. }
  - (* FE_Arrow *) apply exp_iso_cong. { apply IHHeq2. } { apply IHHeq1. }
  - (* FE_All *) apply pi_iso_cong. apply IHHeq.
  - (* FE_Ex *) apply sigma_iso_cong. apply IHHeq.

  (* AZ ÚJ ADJUNGÁLT AXIÓMÁK BEKÖTÉSE *)
  - (* FE_Eps_Adjoint_Iso *)
    apply eps_is_left_adj_obj.
    
  - (* FE_Eps_Functorial *)
    apply eps_functorial. apply IHHeq.

  (* FIBRÁCIÓS SZABÁLYOK *)
  - (* FE_Pullback_Id *)
    apply interp_subst_id. exact w.
  - (* FE_Pullback_Comp *)
    symmetry. apply (interp_subst_comp I J K). exact df. exact dg. exact w.
  - (* FE_Pullback_Cong *)
    eapply interp_subst_cong. exact b. exact w.
Defined. 

Lemma interp_ctx_equiv : 
  forall {Sign : Type} {SM : SkolemMapping Sign} 
  {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C} {BiCCC : BiCartesianClosedCategory BCCC}
  {TSC : TwoSortCategory C} {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} 
  {EHM : EpsilonHyperModel SGF}
  {AdEHM : @AdjointEpsilonFibration Sign SM C CC TSC BEM GF SGF EHM},
  forall (I : b_ty) (G1 G2 : @h_context Sign),
  ctx_equiv I G1 G2 -> 
  interp_h_ctx I G1 ≅O interp_h_ctx I G2.
Proof.
  intros Sign SM C CC BCCC BiCCC TSC BEM GF SGF EHM AdEHM I G1 G2 H_ctx.
  induction H_ctx; simpl. 
  - apply iso_refl.
  - apply prod_iso_cong.
    + exact IHH_ctx.
    + apply interp_form_equiv. exact f.
Defined.

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
Proof.
  intros Sign SM C CC BCCC BiCCC TSC BEM GF SGF EHM AdEHM I G p Phi H_der.
  induction H_der.
  
  (* VÁLTOZÓK ÉS STRUKTURÁLIS SZABÁLYOK *)
  - apply prod_snd.
  - eapply compose. exact IHH_der. apply prod_fst.
  - eapply compose. apply (@iso_to _ _ _ (interp_form_equiv I _ _ f)). exact IHH_der.
  - eapply compose. exact IHH_der. apply (@iso_from _ _ _ (interp_ctx_equiv I _ _ c)).

  (* PROPOZICIONÁLIS MAG (STLC) *)
  - apply terminal_map.
  - apply exp_map. exact IHH_der.
  - eapply compose. eapply eval. apply (prod_map IHH_der1 IHH_der2).
  - apply (prod_map IHH_der1 IHH_der2).
  - eapply compose. eapply prod_fst. exact IHH_der.
  - eapply compose. eapply prod_snd. exact IHH_der.
  - eapply compose. eapply coprod_inl. exact IHH_der.
  - eapply compose. eapply coprod_inr. exact IHH_der.
  - eapply compose.
    + eapply compose.
      * apply (coprod_map IHH_der2 IHH_der3).
      * eapply compose.
        -- eapply eval.
        -- eapply compose.
           ++ eapply prod_map.
              ** eapply compose.
                 --- apply (coprod_map (exp_map (compose coprod_inl (prod_map prod_snd prod_fst))) 
                                       (exp_map (compose coprod_inr (prod_map prod_snd prod_fst)))).
                 --- eapply prod_fst.
              ** eapply prod_snd.
           ++ eapply (prod_map prod_snd prod_fst).
    + eapply (prod_map (id _) IHH_der1).
  - eapply compose. apply initial_map. exact IHH_der.

  (* --------------------------------------------------------------- *)
  (* KVANTOROK (ÚJ, SUBST alapú levezetés)                           *)
  (* --------------------------------------------------------------- *)

  - (* HD_All_Intro *)
    apply right_adj_mor. 
    eapply compose.
    + exact IHH_der.
    + apply (@iso_from _ _ _ (ctx_subst_iso I A G)). 

  - (* HD_All_Elim *)
    eapply compose.
    + (* JAVÍTÁS ITT: Expliciten átadjuk a b_pair b_id f morfizmust és a BT_Pair BT_Id b bizonyítást! *)
      exact (@iso_from _ _ _ (form_subst_iso I (b_Prod I A) (b_pair b_id f) (BT_Pair BT_Id b) Phi)). 
    + eapply compose.
      * eapply (@fmap _ _ (Pullback (interp_tm (BT_Pair BT_Id b))) _ _).
        apply (@epsilon _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (A:=I) (B:=A)))) pullback_has_right_adjoint). 
      * assert (H_eq : compose prod_fst (prod_map (id (interp_ty I)) (interp_tm b)) ≅ id (interp_ty I)).
        { apply prod_map_fst. }
        eapply compose.
        -- apply (@iso_to _ _ _ (pullback_comp_iso prod_fst (prod_map (id (interp_ty I)) (interp_tm b)) (interp_h_ty I (Ty_All A Phi)))).
        -- eapply compose.
           ++ apply (@iso_to _ _ _ (pb_iso (id (interp_ty I)) (compose prod_fst (prod_map (id (interp_ty I)) (interp_tm b))) (symmetry H_eq) (interp_h_ty I (Ty_All A Phi)))).
           ++ eapply compose.
              ** apply (@iso_from _ _ _ (pullback_id_iso (interp_h_ty I (Ty_All A Phi)))).
              ** exact IHH_der.

  - (* HD_Ex_Intro *)
    eapply compose.
    + apply (@iso_to _ _ _ (pullback_id_iso (interp_h_ty I (Ty_Ex A Phi)))). 
    + assert (H_eq : compose prod_fst (prod_map (id (interp_ty I)) (interp_tm b)) ≅ id (interp_ty I)).
      { apply prod_map_fst. }
      eapply compose.
      * apply (@iso_to _ _ _ (pb_iso (compose prod_fst (prod_map (id (interp_ty I)) (interp_tm b))) (id (interp_ty I)) H_eq (interp_h_ty I (Ty_Ex A Phi)))). 
      * eapply compose.
        -- apply (@iso_from _ _ _ (pullback_comp_iso prod_fst (prod_map (id (interp_ty I)) (interp_tm b)) (interp_h_ty I (Ty_Ex A Phi)))). 
        -- eapply compose.
           ++ eapply (@fmap _ _ (Pullback (interp_tm (BT_Pair BT_Id b))) _ _).
              apply (@unit _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (A:=I) (B:=A)))) pullback_has_left_adjoint). 
           ++ eapply compose.
              ** (* JAVÍTÁS ITT IS: Expliciten megkapja a <id, f> párt! *)
                 exact (@iso_to _ _ _ (form_subst_iso I (b_Prod I A) (b_pair b_id f) (BT_Pair BT_Id b) Phi)). 
              ** exact IHH_der.

  - (* HD_Ex_Elim *)
    assert (H_premissza : hom (prod (@fobj _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (A:=I) (B:=A)))) (interp_h_ctx I G)) 
                                    (interp_h_ty (b_Prod I A) Phi)) 
                              (@fobj _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (A:=I) (B:=A)))) (interp_h_ty I Chi))).
    { eapply compose.
      + (* JAVÍTÁS: A hibás fst_iso helyett a tökéletes, általános form_subst_iso-t hívjuk a b_fst-tel! *)
        exact (@iso_to _ _ _ (form_subst_iso (b_Prod I A) I b_fst BT_Fst Chi)). 
      + eapply compose.
        * exact IHH_der2.
        * cbn. apply prod_map. 
          -- eapply compose.
             ++ apply (@iso_from _ _ _ (ctx_subst_iso I A G)). 
             ++ apply prod_fst. 
          -- apply prod_snd. 
    }
    
    assert (H_curry : hom (interp_h_ty (b_Prod I A) Phi) 
                          (exp (@fobj _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (A:=I) (B:=A)))) (interp_h_ty I Chi)) 
                               (@fobj _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (A:=I) (B:=A)))) (interp_h_ctx I G)))).
    { apply exp_map. 
      eapply compose. 
      + exact H_premissza. 
      + apply prod_map. { apply prod_snd. } { apply prod_fst. } 
    }

    assert (H_pb : hom (interp_h_ty (b_Prod I A) Phi) 
                       (@fobj _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (A:=I) (B:=A)))) 
                              (exp (interp_h_ty I Chi) (interp_h_ctx I G)))).
    { eapply compose. 
      + apply (@iso_from _ _ _ (pb_exp_iso (interp_tm (BT_Fst (Sign:=Sign) (A:=I) (B:=A))) _ _)). 
      + exact H_curry. 
    }

    assert (H_sigma : hom (interp_h_ty I (Ty_Ex A Phi)) 
                          (exp (interp_h_ty I Chi) (interp_h_ctx I G))).
    { apply (@left_adj_mor _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (A:=I) (B:=A)))) pullback_has_left_adjoint). 
      exact H_pb. 
    }

    eapply compose.
    + apply (@eval (Fiber (interp_ty I)) _ _ (interp_h_ctx I G) (interp_h_ty I Chi)). 
    + apply prod_map.
      * eapply compose. { exact H_sigma. } { exact IHH_der1. } 
      * apply id. 

  - (* HD_Eps_Intro *)
    eapply compose.
    + (* 1. Az Egzisztenciális formulát átkonvertáljuk Epszilonná az Adjungált izomorfizmussal! *)
      apply (@iso_to _ _ _ (eps_is_left_adj_obj I A Phi)). 
    + (* 2. Innentől 100%-ban ugyanaz, mint a HD_Ex_Intro: felépítjük az Ex A Phi-t *)
      eapply compose.
      * apply (@iso_to _ _ _ (pullback_id_iso (interp_h_ty I (Ty_Ex A Phi)))). 
      * assert (H_eq : compose prod_fst (prod_map (id (interp_ty I)) (interp_tm b)) ≅ id (interp_ty I)).
        { apply prod_map_fst. }
        eapply compose.
        -- apply (@iso_to _ _ _ (pb_iso (compose prod_fst (prod_map (id (interp_ty I)) (interp_tm b))) (id (interp_ty I)) H_eq (interp_h_ty I (Ty_Ex A Phi)))). 
        -- eapply compose.
           ++ apply (@iso_from _ _ _ (pullback_comp_iso prod_fst (prod_map (id (interp_ty I)) (interp_tm b)) (interp_h_ty I (Ty_Ex A Phi)))). 
           ++ eapply compose.
              ** eapply (@fmap _ _ (Pullback (interp_tm (BT_Pair BT_Id b))) _ _).
                 apply (@unit _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (A:=I) (B:=A)))) pullback_has_left_adjoint). 
              ** eapply compose.
                 --- exact (@iso_to _ _ _ (form_subst_iso I (b_Prod I A) (b_pair b_id f) (BT_Pair BT_Id b) Phi)). 
                 --- exact IHH_der.

  - (* HD_Eps_Elim *)
    (* 1. Átkonvertáljuk a Phi.[eps] bemenetet Ex A Phi bemenetté az inverz izomorfizmussal! *)
    assert (IHD1_ex : hom (interp_h_ctx I G) (interp_h_ty I (Ty_Ex A Phi))).
    { eapply compose.
      + apply (@iso_from _ _ _ (eps_is_left_adj_obj I A Phi)).
      + exact IHH_der1. 
    }

    (* 2. Innentől 100%-ban megegyezik a HD_Ex_Elim levezetésével, csak IHH_der1 helyett IHD1_ex-et használunk! *)
    assert (H_premissza : hom (prod (@fobj _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (A:=I) (B:=A)))) (interp_h_ctx I G)) 
                                    (interp_h_ty (b_Prod I A) Phi)) 
                              (@fobj _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (A:=I) (B:=A)))) (interp_h_ty I Chi))).
    { eapply compose.
      + exact (@iso_to _ _ _ (form_subst_iso (b_Prod I A) I b_fst BT_Fst Chi)). 
      + eapply compose.
        * exact IHH_der2.
        * cbn. apply prod_map. 
          -- eapply compose.
             ++ apply (@iso_from _ _ _ (ctx_subst_iso I A G)). 
             ++ apply prod_fst. 
          -- apply prod_snd. 
    }
    
    assert (H_curry : hom (interp_h_ty (b_Prod I A) Phi) 
                          (exp (@fobj _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (A:=I) (B:=A)))) (interp_h_ty I Chi)) 
                               (@fobj _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (A:=I) (B:=A)))) (interp_h_ctx I G)))).
    { apply exp_map. 
      eapply compose. 
      + exact H_premissza. 
      + apply prod_map. { apply prod_snd. } { apply prod_fst. } 
    }

    assert (H_pb : hom (interp_h_ty (b_Prod I A) Phi) 
                       (@fobj _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (A:=I) (B:=A)))) 
                              (exp (interp_h_ty I Chi) (interp_h_ctx I G)))).
    { eapply compose. 
      + apply (@iso_from _ _ _ (pb_exp_iso (interp_tm (BT_Fst (Sign:=Sign) (A:=I) (B:=A))) _ _)). 
      + exact H_curry. 
    }

    assert (H_sigma : hom (interp_h_ty I (Ty_Ex A Phi)) 
                          (exp (interp_h_ty I Chi) (interp_h_ctx I G))).
    { apply (@left_adj_mor _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (A:=I) (B:=A)))) pullback_has_left_adjoint). 
      exact H_pb. 
    }

    eapply compose.
    + apply (@eval (Fiber (interp_ty I)) _ _ (interp_h_ctx I G) (interp_h_ty I Chi)). 
    + apply prod_map.
      * eapply compose. { exact H_sigma. } { exact IHD1_ex. } (* Itt kapja meg a konvertált bizonyítást! *)
      * apply id. 

Defined.