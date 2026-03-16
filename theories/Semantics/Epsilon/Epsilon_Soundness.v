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
Proof.
  intros Sign I J b g dg.
  unfold b_pullback_ext.
  apply BT_Pair.
  - eapply BT_Comp.
    + exact dg.
    + apply BT_Fst.
  - apply BT_Snd.
Defined.

Lemma form_pullback_general_iso :
  forall {Sign : Type} {SM : SkolemMapping Sign} 
         {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} 
         {EHM : EpsilonHyperModel SGF} {EGF : EpsilonGoodFibration}
         (Phi : @h_ty Sign) (I J : b_ty) (g : @b_tm Sign) (dg : base_typing I g J),
  interp_h_ty I (form_pullback g Phi) ≅O
  @fobj _ _ (Pullback (interp_tm dg)) (interp_h_ty J Phi).
Proof.
  intros Sign SM C CC TSC BEM GF SGF EHM EGF Phi.
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
      exact (IHPhi (b_Prod I b) (b_Prod J b) (b_pullback_ext g) (typing_pullback_ext dg)).
    + symmetry. apply beck_chevalley_pi.
  - eapply iso_trans.
    + apply sigma_iso_cong.
      exact (IHPhi (b_Prod I b) (b_Prod J b) (b_pullback_ext g) (typing_pullback_ext dg)).
    + symmetry. apply beck_chevalley_sigma.
Defined.

(** * Syntactic Substitution = Semantic Pullback *)
Lemma form_pullback_iso :
  forall {Sign : Type} {SM : SkolemMapping Sign} 
         {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} 
         {EHM : EpsilonHyperModel SGF} {EGF : EpsilonGoodFibration}
         (I A : b_ty) (f : @b_tm Sign) (df : base_typing I f A) (Phi : @h_ty Sign),
  interp_h_ty I (form_pullback (b_pair b_id f) Phi) ≅O
  @fobj _ _ (Pullback (interp_tm (BT_Pair BT_Id df))) (interp_h_ty (b_Prod I A) Phi).
Proof.
  intros.
  apply (form_pullback_general_iso Phi I (b_Prod I A) (b_pair b_id f) (BT_Pair BT_Id df)).
Defined.

Lemma form_pullback_fst_iso : 
  forall {Sign : Type} {SM : SkolemMapping Sign} 
         {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} 
         {EHM : EpsilonHyperModel SGF} {EGF : EpsilonGoodFibration}
         (I A : b_ty) (Phi : @h_ty Sign),
  interp_h_ty (b_Prod I A) (form_pullback b_fst Phi) ≅O 
  @fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I Phi).
Proof.
  intros.
  apply form_pullback_general_iso.
Defined.

Lemma ctx_pullback_iso : 
  forall {Sign : Type} {SM : SkolemMapping Sign} 
         {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} 
         {EHM : EpsilonHyperModel SGF} {EGF : EpsilonGoodFibration}
         (I A : b_ty) (G : @h_context Sign),
  interp_h_ctx (b_Prod I A) (ctx_pullback b_fst G) ≅O 
  @fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ctx I G).
Proof.
  intros Sign SM C CC TSC BEM GF SGF EHM EGF I A G.
  induction G as [| Phi G' IHG']; simpl.
  - symmetry. apply pb_term_iso.
  - eapply iso_trans.
    + apply (prod_iso_cong IHG' (form_pullback_fst_iso I A Phi)).
    + symmetry. apply pb_prod_iso.
Defined.

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
Proof. 
  intros Sign SM C CC BCCC BiCCC TSC BEM GF SGF EHM I J f g Phi df dg Heq Hwf.
  
  (* Visszadobjuk az I, f, g paramétereket, hogy a kvantorok ágaiban frissülhessenek! *)
  revert I f g df dg Heq.
  induction Hwf; intros I' f' g' df' dg' Heq'; simpl.
  
  - apply iso_refl. (* Unit *)
  - apply iso_refl. (* Void *)
  - (* Prod *) 
    apply prod_iso_cong.
    { eapply IHHwf1. exact Heq'. }
    { eapply IHHwf2. exact Heq'. }
    
  - (* Sum *) 
    apply coprod_iso_cong.
    { eapply IHHwf1. exact Heq'. }
    { eapply IHHwf2. exact Heq'. }
     
  - (* Arrow *) 
    apply exp_iso_cong.
    { eapply IHHwf2. exact Heq'. } (* Itt kéri a Psi-t, szóval IHHwf2 *)
    { eapply IHHwf1. exact Heq'. } (* Itt pedig a Phi-t, szóval IHHwf1 *)
    
  - (* Atom: b_comp t f' == b_comp t g' *)
    eapply i_atom_cong_global.
    eapply BE_CongComp.
    + exact Heq'.                  (* 1. premissza (belső): f' == g' *)
    + exact (BE_Refl _ _ _ b).     (* 2. premissza (külső): t == t (b gépeléssel) *)
    
 - (* Ty_All: A kvantor kiterjeszti a kontextust. *)
    apply pi_iso_cong.
    eapply (IHHwf (b_Prod I' A) (b_pullback_ext f') (b_pullback_ext g')).
    
    (* A Coq egyből az egyenlőséget kéri, a gépelést ebből nyeri ki! *)
    unfold b_pullback_ext. 
    eapply BE_CongPair.
    + eapply BE_CongComp.
      * exact (BE_Refl _ _ _ BT_Fst). (* belső morfizmus: b_fst == b_fst *)
      * exact Heq'.                   (* külső morfizmus: f' == g' *)
    + exact (BE_Refl _ _ _ BT_Snd).   (* második elem: b_snd == b_snd *)

  - (* Ty_Ex: Hajszálpontosan ugyanaz a struktúra! *)
    apply sigma_iso_cong.
    eapply (IHHwf (b_Prod I' A) (b_pullback_ext f') (b_pullback_ext g')).
    
    unfold b_pullback_ext. 
    eapply BE_CongPair.
    + eapply BE_CongComp.
      * exact (BE_Refl _ _ _ BT_Fst). 
      * exact Heq'.    
    + exact (BE_Refl _ _ _ BT_Snd).
Defined. 

Lemma interp_pb_id : forall {Sign : Type} {SM : SkolemMapping Sign} 
  {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C} 
  {BiCCC : BiCartesianClosedCategory BCCC} {TSC : TwoSortCategory C} 
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} 
  {EHM : EpsilonHyperModel SGF} (I : b_ty) (Phi : @h_ty Sign),
  WellFormed I Phi ->
  (interp_h_ty I (form_pullback b_id Phi)) ≅O (interp_h_ty I Phi).
Proof. 
  intros Sign SM C CC BCCC BiCCC TSC BEM GF SGF EHM I Phi Hwf.
  induction Hwf.
  - simpl. apply iso_refl.
  - simpl. apply iso_refl.
  - simpl. apply prod_iso_cong; assumption.
  - simpl. apply coprod_iso_cong; assumption.
  - simpl. apply exp_iso_cong; assumption.
  
  - (* Atom *)
    simpl. eapply i_atom_cong_global.
    (* Belátjuk, hogy b_comp t b_id == t *)
    apply BE_IdR.
    
  - (* Ty_All *)
    simpl. apply pi_iso_cong.
    eapply iso_trans.
    + (* Explicit megadjuk az interp_pb_cong paramétereit! *)
      eapply (interp_pb_cong (b_Prod I A) (b_Prod I A) (b_pullback_ext b_id) b_id Body).
      * (* Itt jön a bázis-kategória bizonyítás, amit fentebb írtam *)
        unfold b_pullback_ext.
        eapply BE_Trans. 2: { apply BE_EtaPair. }
        eapply BE_CongPair.
        -- eapply BE_Trans. apply BE_IdL. eapply BE_Sym. apply BE_IdR.
        -- eapply BE_Sym. apply BE_IdR.
      * exact Hwf.
    + exact IHHwf.
    
  - (* Ty_Ex *)
    simpl. apply sigma_iso_cong.
    eapply iso_trans.
    + (* Explicit instanciálás: rögzítjük a kontextust és a morfizmusokat *)
      eapply (interp_pb_cong (b_Prod I A) (b_Prod I A) (b_pullback_ext b_id) b_id Body).
      * (* Bázis bizonyítás: <id ∘ π₁, π₂> ≅ id *)
        unfold b_pullback_ext.
        eapply BE_Trans. 2: { apply BE_EtaPair. }
        eapply BE_CongPair.
        -- eapply BE_Trans. apply BE_IdL. eapply BE_Sym. apply BE_IdR.
        -- eapply BE_Sym. apply BE_IdR.
      * exact Hwf.
    + exact IHHwf.
      Unshelve.
  (* Most a Coq kiadja a b_ty és base_typing célokat. *)
  (* Mivel ezek ott vannak a kontextusodban, csak be kell őket fejezni: *)
  exact I.
  exact A.
  exact b.
Defined. 

Lemma interp_pb_comp : forall {Sign : Type} {SM : SkolemMapping Sign} 
  {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C} 
  {BiCCC : BiCartesianClosedCategory BCCC} {TSC : TwoSortCategory C} 
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} 
  {EHM : EpsilonHyperModel SGF} (I J K: b_ty) (f g : @b_tm Sign) (Phi : @h_ty Sign)
  (df : base_typing J f K) (dg : base_typing I g J),
  WellFormed K Phi ->
  (interp_h_ty I (form_pullback (b_comp f g) Phi)) ≅O (interp_h_ty I (form_pullback g (form_pullback f Phi))).
Proof.
  intros Sign SM C CC BCCC BiCCC TSC BEM GF SGF EHM I J K f g Phi df dg Hwf.
  
  (* Fontos: revertálunk mindent, mert a kvantoroknál változni fognak a típusok! *)
  revert I J f g df dg.
  induction Hwf; intros I0 J0 f0 g0 df0 dg0; simpl.
  
  - apply iso_refl. (* Unit *)
  - apply iso_refl. (* Void *)
  
 - (* Prod *) 
    apply prod_iso_cong. 
    { apply (IHHwf1 I0 J0 f0 g0 df0 dg0). } 
    { apply (IHHwf2 I0 J0 f0 g0 df0 dg0). }
    
  - (* Sum *) 
    apply coprod_iso_cong. 
    { apply (IHHwf1 I0 J0 f0 g0 df0 dg0). } 
    { apply (IHHwf2 I0 J0 f0 g0 df0 dg0). }
    
  - (* Arrow: Itt vigyázz, ahogy múltkor is, az 1-es és 2-es cserélődik! *) 
    apply exp_iso_cong. 
    { apply (IHHwf2 I0 J0 f0 g0 df0 dg0). } 
    { apply (IHHwf1 I0 J0 f0 g0 df0 dg0). }
  - (* Atom *)
    eapply i_atom_cong_global.
    (* Explicit Asszociativitás: megadjuk az I0, J0, I, A típusokat és a b bizonyítékot! *)
    exact (BE_Assoc I0 J0 I A g0 f0 t dg0 df0 b).
    
  - (* Ty_All *)
    apply pi_iso_cong.
    eapply iso_trans.
    + eapply (interp_pb_cong (b_Prod I0 A) (b_Prod I A) 
                             (b_pullback_ext (b_comp f0 g0)) 
                             (b_comp (b_pullback_ext f0) (b_pullback_ext g0)) Body).
      * (* Bázis-kategória diagram számolás 100% EXPLICIT gépeléssel *)
        unfold b_pullback_ext.
        eapply BE_Trans. 
        { eapply BE_CongPair.
          - eapply BE_Sym. exact (BE_Assoc _ _ _ _ _ _ _ BT_Fst dg0 df0). 
          - exact (BE_Refl _ _ _ BT_Snd). }
        eapply BE_Sym. eapply BE_Trans. 
        { exact (BE_CompPair _ _ _ _ _ _ _ (BT_Comp df0 BT_Fst) BT_Snd (BT_Pair (BT_Comp dg0 BT_Fst) BT_Snd)). } 
        eapply BE_CongPair.
        -- eapply BE_Trans. 
           { eapply BE_Sym. exact (BE_Assoc _ _ _ _ _ _ _ (BT_Pair (BT_Comp dg0 BT_Fst) BT_Snd) BT_Fst df0). }
           eapply BE_CongComp. 
           ++ apply BE_BetaFst. 
           ++ exact (BE_Refl _ _ _ df0).    
        -- apply BE_BetaSnd.    
      * exact Hwf.
    + (* Explicit megadjuk az indukciós hipotézis paramétereit! *)
      eapply (IHHwf (b_Prod I0 A) (b_Prod J0 A) (b_pullback_ext f0) (b_pullback_ext g0)).
      * unfold b_pullback_ext. eapply BT_Pair.
        -- eapply BT_Comp. exact df0. apply BT_Fst.
        -- apply BT_Snd.
      * unfold b_pullback_ext. eapply BT_Pair.
        -- eapply BT_Comp. exact dg0. apply BT_Fst.
        -- apply BT_Snd.

  - (* Ty_Ex: Hajszálpontosan ugyanaz a bizonyítás *)
    apply sigma_iso_cong.
    eapply iso_trans.
    + eapply (interp_pb_cong (b_Prod I0 A) (b_Prod I A) 
                             (b_pullback_ext (b_comp f0 g0)) 
                             (b_comp (b_pullback_ext f0) (b_pullback_ext g0)) Body).
      * unfold b_pullback_ext.
        eapply BE_Trans. 
        { eapply BE_CongPair.
          - eapply BE_Sym. exact (BE_Assoc _ _ _ _ _ _ _ BT_Fst dg0 df0). 
          - exact (BE_Refl _ _ _ BT_Snd). }
        eapply BE_Sym. eapply BE_Trans. 
        { exact (BE_CompPair _ _ _ _ _ _ _ (BT_Comp df0 BT_Fst) BT_Snd (BT_Pair (BT_Comp dg0 BT_Fst) BT_Snd)). } 
        eapply BE_CongPair.
        -- eapply BE_Trans. 
           { eapply BE_Sym. exact (BE_Assoc _ _ _ _ _ _ _ (BT_Pair (BT_Comp dg0 BT_Fst) BT_Snd) BT_Fst df0). }
           eapply BE_CongComp. 
           ++ apply BE_BetaFst. 
           ++ exact (BE_Refl _ _ _ df0).    
        -- apply BE_BetaSnd.    
      * exact Hwf.
    + eapply (IHHwf (b_Prod I0 A) (b_Prod J0 A) (b_pullback_ext f0) (b_pullback_ext g0)).
      * unfold b_pullback_ext. eapply BT_Pair.
        -- eapply BT_Comp. exact df0. apply BT_Fst.
        -- apply BT_Snd.
      * unfold b_pullback_ext. eapply BT_Pair.
        -- eapply BT_Comp. exact dg0. apply BT_Fst.
        -- apply BT_Snd.
Defined.


Lemma form_equiv_iso :
  forall {Sign : Type} {SM : SkolemMapping Sign} 
         {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C} {BiCCC : BiCartesianClosedCategory BCCC}
         {TSC : TwoSortCategory C} {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} 
         {EHM : EpsilonHyperModel SGF} {EGF : EpsilonGoodFibration}
         (I : b_ty) (Phi Psi : @h_ty Sign),
  form_equiv I Phi Psi -> interp_h_ty I Phi ≅O interp_h_ty I Psi.
Proof. 
  (* 1. Bevezetjük a paramétereket *)
  intros Sign SM C CC BCCC BiCCC TSC BEM GF SGF EHM EGF I Phi Psi Heq.
  
  (* 2. NINCS TÖBBÉ generalize dependent I !!!
     Mivel az I az induktív típus indexe, a Coq mindent elintéz a motorháztető alatt. *)
  
  (* 3. Indukció a form_equiv reláción *)
  induction Heq; simpl.

  - (* FE_Atom *)
    eapply i_atom_cong_global.
    exact b.

  - (* FE_Refl *) apply iso_refl.
  - (* FE_Sym *) symmetry. apply IHHeq.
  - (* FE_Trans *) eapply iso_trans. { apply IHHeq1. } { apply IHHeq2. }
  
  - (* FE_Prod *) apply prod_iso_cong. { apply IHHeq1. } { apply IHHeq2. }
  - (* FE_Sum *) apply coprod_iso_cong. { apply IHHeq1. } { apply IHHeq2. }
  - (* FE_Arrow *) apply exp_iso_cong. { apply IHHeq2. } { apply IHHeq1. }
  
  - (* FE_All *) 
    apply pi_iso_cong. 
    (* Nézd meg, milyen gyönyörű! Nem kell megadni az (I_curr * D)-t, 
       mert az IHHeq már alapból azon a kontextuson él! *)
    apply IHHeq.

  - (* FE_Ex *) 
    apply sigma_iso_cong. 
    apply IHHeq.

  - (* FE_Eps_Lift *)
    (* Mivel a form_equiv_iso szimmetrikus, a cél jobb oldalán lévő 
       (form_pullback g (Phi .[ ε D, Phi ])) kerül balra. *)
    symmetry.
    
    (* Az axióma PONTOSAN ezt az izomorfizmust mondja ki bármely g morfizmusra! *)
    eapply eps_beck_chevalley_iso.
    
    (* Csak átadjuk a gépelést a g-nek, és a Coq mindent megold! *)
    exact dg.

  - (* FE_Pullback_Id *)
    apply interp_pb_id.
    exact w.
 - (* FE_Pullback_Comp *)
    symmetry.
    (* Explicit átadjuk az I, J, K bázisokat, mert a képletből a Coq nem tudja kikövetkeztetni őket! *)
    apply (interp_pb_comp I J K).
    exact df.
    exact dg.
    exact w.
    
  - (* FE_Pullback_Cong *)
    (* AZ IGAZSÁG PILLANATA!
       Tegnap itt omlott össze a Coq, mert I_curr nem volt egyenlő I-vel.
       Most viszont az I tökéletesen egyezik a form_equiv I indexével, 
       így rá tudjuk húzni a tiszta típusos axiómát! *)
    eapply interp_pb_cong.
    exact b.
    exact w.
Defined. 

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
Proof.
  induction D.
  
  - apply prod_snd.
  - eapply compose. exact IHD. apply prod_fst.
  
  (* Ide jön majd az HD_Conv ág is, de egyelőre kihagyom a hossza miatt *)
  - (* HD_Conv *)
    eapply compose.
    { (* 1. A cél (Psi) felé mutató izomorfizmus (a form_equiv_iso lemma 'iso_to' iránya) *)
      apply (@iso_to _ _ _ (form_equiv_iso I Phi Psi f)). }
    { (* 2. A forrás bizonyítás (Phi), amit az indukciós hipotézis ad *)
      exact IHD. }
  
  - apply terminal_map.
  - apply exp_map. exact IHD.
  - eapply compose. eapply eval. apply (prod_map IHD1 IHD2).
  - apply (prod_map IHD1 IHD2).
  - eapply compose. eapply prod_fst. exact IHD.
  - eapply compose. eapply prod_snd. exact IHD.
  - eapply compose. eapply coprod_inl. exact IHD.
  - eapply compose. eapply coprod_inr. exact IHD.
  
  - (* HD_Case *)
    eapply compose.
    { eapply compose.
      { apply (coprod_map IHD2 IHD3). } 
      { eapply compose.
        { eapply eval. }
        { eapply compose.
          { eapply prod_map.
            { eapply compose.
              { apply (coprod_map 
                  (exp_map (compose coprod_inl (prod_map prod_snd prod_fst))) 
                  (exp_map (compose coprod_inr (prod_map prod_snd prod_fst)))
                ). }
              { eapply prod_fst. } }
            { eapply prod_snd. } }
          { eapply (prod_map prod_snd prod_fst). } } } }
    { eapply (prod_map (id _) IHD1). }

  - (* HD_Absurd *)
    eapply compose.
    { apply initial_map. }
    { exact IHD. }
    
  - (* HD_All_Intro *)
    apply right_adj_mor.
    eapply compose.
    { exact IHD. }
    { exact (@iso_from _ _ _ (ctx_pullback_iso I A G)). } 
  - (* HD_All_Elim *)
    eapply compose.
    { (* 1. Lépés: Szintaktikus visszahúzás összekötése a Fibrációs Pullback-kel *)
      exact (@iso_from _ _ _ (form_pullback_iso I A f b Phi)). }
    eapply compose.
    { (* 2. Lépés: A Counit (epsilon) alkalmazása az fmap-en belül *)
      eapply (@fmap _ _ (Pullback (interp_tm (BT_Pair BT_Id b))) _ _).
      apply (@epsilon _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (pullback_has_right_adjoint _)). }
    
    (* 3. Lépés: A bázis kompozíció (pi1 o <id, f> = id) kiszámítása *)
    assert (H_eq : id (interp_ty I) ≅ compose prod_fst (prod_map (id (interp_ty I)) (interp_tm b))).
    { symmetry. apply prod_map_fst. }
    
    eapply compose.
    { (* 4. Lépés: Pullback kompozíció szétszedése *)
      apply (@iso_to _ _ _ (pullback_comp_iso 
                              prod_fst 
                              (prod_map (id (interp_ty I)) (interp_tm b)) 
                              (interp_h_ty I (Ty_All A Phi)))). }
    eapply compose.
    { (* 5. Lépés: Bázis egyenlőség (H_eq) felemelése a szálba (pb_iso) *)
      apply (@iso_to _ _ _ (pb_iso 
                              (id (interp_ty I)) 
                              (compose prod_fst (prod_map (id (interp_ty I)) (interp_tm b))) 
                              H_eq 
                              (interp_h_ty I (Ty_All A Phi)))). }
    eapply compose.
    { (* 6. Lépés: Identitás funktor visszahúzásának leválasztása *)
      apply (@iso_from _ _ _ (pullback_id_iso (interp_h_ty I (Ty_All A Phi)))). }
    { (* 7. Lépés: A bizonyítás (IHD) beillesztése a lánc végére *)
      exact IHD. }
  - (* HD_Ex_Intro *)
    eapply compose.
    { (* 1. Lépés: Célpont: Identitás visszahúzás leválasztása (id* X -> X) *)
      apply (@iso_to _ _ _ (pullback_id_iso (interp_h_ty I (Ty_Ex A Phi)))). }
    
    (* 2. Lépés: Bázis egyenlőség (pi1 o <id, f> = id) bizonyítása *)
    assert (H_eq : compose prod_fst (prod_map (id (interp_ty I)) (interp_tm b)) ≅ id (interp_ty I)).
    { apply prod_map_fst. }
    
    eapply compose.
    { (* 3. Lépés: Bázis egyenlőség (H_eq) felemelése a szálba (pb_iso) *)
      apply (@iso_to _ _ _ (pb_iso 
                              (compose prod_fst (prod_map (id (interp_ty I)) (interp_tm b))) 
                              (id (interp_ty I)) 
                              H_eq 
                              (interp_h_ty I (Ty_Ex A Phi)))). }
                              
    eapply compose.
    { (* 4. Lépés: Pullback kompozíció összerakása (iso_from) *)
      apply (@iso_from _ _ _ (pullback_comp_iso 
                                prod_fst 
                                (prod_map (id (interp_ty I)) (interp_tm b)) 
                                (interp_h_ty I (Ty_Ex A Phi)))). }
                                
    eapply compose.
    { (* 5. Lépés: Az Unit (unit) alkalmazása a Pullback funktor fmap-jén belül *)
      eapply (@fmap _ _ (Pullback (interp_tm (BT_Pair BT_Id b))) _ _).
      apply (@unit _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (pullback_has_left_adjoint _)). }
      
    eapply compose.
    { (* 6. Lépés: A szintaktikus visszahúzás (Phi.[f]) rákötése a Fibrációs Pullback-re *)
      exact (@iso_to _ _ _ (form_pullback_iso I A f b Phi)). }
      
    { (* 7. Lépés: A forrás levezetés (IHD) beillesztése a lánc elejére *)
      exact IHD. }
 - (* HD_Ex_Elim *)
    (* 1. Előkészítjük IHD2-t (a jobboldali premisszát) pontosan olyan alakra, 
          amit majd be tudunk vinni az exponenciális alá. *)
    assert (H_premissza : hom (prod (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ctx I G)) 
                                    (interp_h_ty (b_Prod I A) Phi)) 
                              (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I Chi))).
    {
      eapply compose.
      { exact (@iso_to _ _ _ (form_pullback_fst_iso I A Chi)). }
      eapply compose.
      { exact IHD2. }
      { cbn. apply prod_map. 
        { eapply compose.
          { exact (@iso_from _ _ _ (ctx_pullback_iso I A G)). }
          { apply prod_fst. } }
        { apply prod_snd. } }
    }
    
    (* 2. Curry-zés: Átvisszük a G-t a nyíl jobb oldalára *)
    assert (H_curry : hom (interp_h_ty (b_Prod I A) Phi) 
                          (exp (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I Chi)) 
                               (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ctx I G)))).
    { apply exp_map. 
      eapply compose. 
      { exact H_premissza. } 
      { apply prod_map. { apply prod_snd. } { apply prod_fst. } } }

    (* 3. Visszahúzás (Pullback) kiemelése az exponenciális felett *)
    assert (H_pb : hom (interp_h_ty (b_Prod I A) Phi) 
                       (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) 
                              (exp (interp_h_ty I Chi) (interp_h_ctx I G)))).
    { eapply compose. 
      { apply (@iso_from _ _ _ (pb_exp_iso (interp_tm (BT_Fst (A:=I) (B:=A))) _ _)). } 
      { exact H_curry. } }

    (* 4. Adjungálás alkalmazása (Itt adjuk meg expliciten a funktort a Coq-nak!) *)
    assert (H_sigma : hom (interp_h_ty I (Ty_Ex A Phi)) 
                          (exp (interp_h_ty I Chi) (interp_h_ctx I G))).
    { apply (@left_adj_mor _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (pullback_has_left_adjoint _)). 
      exact H_pb. }

    (* 5. A végső morfizmus összeállítása uncurry-vel (eval) és IHD1 behelyettesítésével *)
    eapply compose.
    { apply (@eval (Fiber (interp_ty I)) _ _ (interp_h_ctx I G) (interp_h_ty I Chi)). }
    { (* Itt építjük fel a <H_sigma o IHD1, id_G> párt *)
      apply prod_map.
      { eapply compose. { exact H_sigma. } { exact IHD1. } }
      { apply id. } }
 - (* HD_Eps_Intro *)
    eapply compose.
    { (* 1. Epszilon Axióma leképezése Ex A Phi -> Phi.[eps] formára.
          Az eps_unit az I x A szálban él: Phi -> pi1*(Phi.[eps]).
          Ezt az adjungálás (left_adj_mor) lehozza az I szálba: Ex A Phi -> Phi.[eps] *)
      apply (@left_adj_mor _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (pullback_has_left_adjoint _)).
      
      eapply compose.
      { (* JAVÍTVA: Itt iso_to kell, mert a szintaktikus form_pullback-ből 
           megyünk a kategóriaelméleti Pullback-be! *)
        exact (@iso_to _ _ _ (form_pullback_fst_iso I A (Phi .[ ε A, Phi ]))). }
      { (* És ide jön maga az Epszilon axióma, aminek a kimenete a form_pullback *)
        apply eps_unit. }
    }
    
    (* 2. Lépés: Most a célunk Ty_Ex A Phi lett (hiszen az Epszilon axióma ebből indult). 
       Ezt hajszálpontosan a HD_Ex_Intro logikájával építjük fel a G-ből és a Phi.[f]-ből (IHD). *)
    eapply compose.
    { apply (@iso_to _ _ _ (pullback_id_iso (interp_h_ty I (Ty_Ex A Phi)))). }
    
    assert (H_eq : compose prod_fst (prod_map (id (interp_ty I)) (interp_tm b)) ≅ id (interp_ty I)).
    { apply prod_map_fst. }
    
    eapply compose.
    { apply (@iso_to _ _ _ (pb_iso 
                              (compose prod_fst (prod_map (id (interp_ty I)) (interp_tm b))) 
                              (id (interp_ty I)) 
                              H_eq 
                              (interp_h_ty I (Ty_Ex A Phi)))). }
                              
    eapply compose.
    { apply (@iso_from _ _ _ (pullback_comp_iso 
                                prod_fst 
                                (prod_map (id (interp_ty I)) (interp_tm b)) 
                                (interp_h_ty I (Ty_Ex A Phi)))). }
                                
    eapply compose.
    { eapply (@fmap _ _ (Pullback (interp_tm (BT_Pair BT_Id b))) _ _).
      apply (@unit _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (pullback_has_left_adjoint _)). }
      
    eapply compose.
    { exact (@iso_to _ _ _ (form_pullback_iso I A f b Phi)). }
      
    { exact IHD. }
  - (* HD_Eps_Elim *)
    (* 1. Lépés: Átalakítjuk a meglévő IHD1-et (ami G -> Phi[eps]) 
       egy egzisztenciális (G -> Ty_Ex A Phi) bizonyítássá. 
       Ezt pontosan úgy tesszük, ahogy a HD_Ex_Intro-ban csináltuk,
       hiszen az 'eps' is csak egy konkrét bázisterm! *)
    assert (IHD1_ex : hom (interp_h_ctx I G) (interp_h_ty I (Ty_Ex A Phi))).
    {
      eapply compose.
      { apply (@iso_to _ _ _ (pullback_id_iso (interp_h_ty I (Ty_Ex A Phi)))). }
      
      (* A bázis-egyenlőség a Skolem konstansra (eps_term) *)
      assert (H_eq : compose prod_fst (prod_map (id (interp_ty I)) (interp_tm (@BT_Const Sign I A (skolem_index A Phi)))) ≅ id (interp_ty I)).
      { apply prod_map_fst. }
      
      eapply compose.
      { apply (@iso_to _ _ _ (pb_iso 
                                (compose prod_fst (prod_map (id (interp_ty I)) (interp_tm (@BT_Const Sign I A (skolem_index A Phi))))) 
                                (id (interp_ty I)) 
                                H_eq 
                                (interp_h_ty I (Ty_Ex A Phi)))). }
                                
      eapply compose.
      { apply (@iso_from _ _ _ (pullback_comp_iso 
                                  prod_fst 
                                  (prod_map (id (interp_ty I)) (interp_tm (@BT_Const Sign I A (skolem_index A Phi)))) 
                                  (interp_h_ty I (Ty_Ex A Phi)))). }
                                  
      eapply compose.
      { eapply (@fmap _ _ (Pullback (interp_tm (BT_Pair BT_Id (@BT_Const Sign I A (skolem_index A Phi))))) _ _).
        apply (@unit _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (pullback_has_left_adjoint _)). }
        
      eapply compose.
      { exact (@iso_to _ _ _ (form_pullback_iso I A (b_const A (skolem_index A Phi)) (@BT_Const Sign I A (skolem_index A Phi)) Phi)). }
        
      { exact IHD1. }
    }

    (* 2. Lépés: Most, hogy van egy IHD1_ex : G -> Ex A Phi bizonyításunk,
       a feladat hajszálpontosan megegyezik az Ex_Elim ággal! 
       Újrahasznosítjuk az előbbi masszív Frobenius eliminációs blokkot. *)
    
    assert (H_premissza : hom (prod (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ctx I G)) 
                                    (interp_h_ty (b_Prod I A) Phi)) 
                              (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I Chi))).
    {
      eapply compose.
      { exact (@iso_to _ _ _ (form_pullback_fst_iso I A Chi)). }
      eapply compose.
      { exact IHD2. }
      { cbn. apply prod_map. 
        { eapply compose.
          { exact (@iso_from _ _ _ (ctx_pullback_iso I A G)). }
          { apply prod_fst. } }
        { apply prod_snd. } }
    }
    
    assert (H_curry : hom (interp_h_ty (b_Prod I A) Phi) 
                          (exp (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I Chi)) 
                               (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ctx I G)))).
    { apply exp_map. 
      eapply compose. 
      { exact H_premissza. } 
      { apply prod_map. { apply prod_snd. } { apply prod_fst. } } }

    assert (H_pb : hom (interp_h_ty (b_Prod I A) Phi) 
                       (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) 
                              (exp (interp_h_ty I Chi) (interp_h_ctx I G)))).
    { eapply compose. 
      { apply (@iso_from _ _ _ (pb_exp_iso (interp_tm (BT_Fst (A:=I) (B:=A))) _ _)). } 
      { exact H_curry. } }

    assert (H_sigma : hom (interp_h_ty I (Ty_Ex A Phi)) 
                          (exp (interp_h_ty I Chi) (interp_h_ctx I G))).
    { apply (@left_adj_mor _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (pullback_has_left_adjoint _)). 
      exact H_pb. }

    eapply compose.
    { apply (@eval (Fiber (interp_ty I)) _ _ (interp_h_ctx I G) (interp_h_ty I Chi)). }
    { apply prod_map.
      { eapply compose. { exact H_sigma. } { exact IHD1_ex. } }
      { apply id. } }
Defined.
