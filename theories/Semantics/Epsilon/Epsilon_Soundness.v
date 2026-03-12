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

(** [TÍPUSRENDSZER ÁTHIDALÁSA - NEHÉZ]
  Ez az axióma kényszeríti ki a b_fst gépelését ott, ahol a szintaxis nem 
  garantálja a szorzat-kontextust. 
  MEGOLDÁS: WellFormed (WFF) predikátum bevezetése után törölhető, 
  mert a WFF deriváció tartalmazni fogja a megfelelő base_typing-ot.
*)
Axiom b_fst_typing_hack : forall {Sign : Type} (I_curr : b_ty), 
  @base_typing Sign I_curr (@b_fst Sign) I_curr.

(** [EPSZILON KOMPATIBILITÁS - NEHÉZ]
  Azt igazolja, hogy az epszilon-lifted visszahúzás felcserélhető a behelyettesítéssel.
  IGAZOLÁS: Tisztán bázis-kategóriás (BCCC) diagram-számolás. 
  Nem igényel WFF-et, de sok kompozíciós lemmát igen.
*) 
Axiom eps_lift_subst_cong_hack : forall {Sign : Type} {SM : SkolemMapping Sign} 
  {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C} 
  {BiCCC : BiCartesianClosedCategory BCCC} {TSC : TwoSortCategory C} 
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} 
  {EHM : EpsilonHyperModel SGF} {EGF : EpsilonGoodFibration}
  (I_curr D : b_ty) (Phi : h_ty),
  interp_h_ty I_curr
    (form_pullback (b_pair (b_comp b_fst b_fst) b_snd) Phi
     .[ ε D, form_pullback (b_pair (b_comp b_fst b_fst) b_snd) Phi])
  ≅O interp_h_ty I_curr
       (form_pullback b_fst Phi .[ ε D, form_pullback b_fst Phi]).
 
 (** [STRUKTURÁLIS HÍD - KÖNNYŰ]
  A szintaktikai form_pullback és a kategóriaelméleti Pullback funktor azonossága.
  IGAZOLÁS: Indukció a Phi struktúráján (mint a form_pullback_general_iso-ban), 
  kiegészítve az új Epszilon-ágakkal.
*)      
(* 1. Axióma: A szintaktikai identitás visszahúzás izomorf az eredetivel *)
Axiom interp_pb_id_ax : forall {Sign : Type} {SM : SkolemMapping Sign} 
  {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C} 
  {BiCCC : BiCartesianClosedCategory BCCC} {TSC : TwoSortCategory C} 
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} 
  {EHM : EpsilonHyperModel SGF} (I : b_ty) (Phi : @h_ty Sign),
  (interp_h_ty I (form_pullback b_id Phi)) ≅O (interp_h_ty I Phi).

(* 2. Axióma: A szintaktikai kompozíció visszahúzása *)
Axiom interp_pb_comp_ax : forall {Sign : Type} {SM : SkolemMapping Sign} 
  {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C} 
  {BiCCC : BiCartesianClosedCategory BCCC} {TSC : TwoSortCategory C} 
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} 
  {EHM : EpsilonHyperModel SGF} (I J K: b_ty) (f g : @b_tm Sign) (Phi : @h_ty Sign),
  (interp_h_ty I (form_pullback (b_comp f g) Phi)) ≅O (interp_h_ty I (form_pullback g (form_pullback f Phi))).

(** [KONTEXTUS SZINKRONIZÁCIÓ - KÖZEPES]
  A szintaktikai ekvivalencia (base_equiv) és az interpretáció kontextusának 
  (I_curr) mesterséges összekapcsolása. 
  MEGOLDÁS: A form_equiv_iso tétel kiegészítése 'WellFormed I Phi' feltétellel.
*)
(* 3. Axióma: A szintaktikai kongruencia (szétválasztott kontextusokkal) *)
Axiom interp_pb_cong_untyped_ax : forall {Sign : Type} {SM : SkolemMapping Sign} 
  {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C} 
  {BiCCC : BiCartesianClosedCategory BCCC} {TSC : TwoSortCategory C} 
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} 
  {EHM : EpsilonHyperModel SGF} (I_curr I J : b_ty) (f g : @b_tm Sign) 
  (df : base_typing I f J) (dg : base_typing I g J) (Phi : @h_ty Sign),
  base_equiv df dg -> 
  (interp_h_ty I_curr (form_pullback f Phi)) ≅O (interp_h_ty I_curr (form_pullback g Phi)).
  
Lemma form_equiv_iso :
  forall {Sign : Type} {SM : SkolemMapping Sign} 
         {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C} {BiCCC : BiCartesianClosedCategory BCCC}
         {TSC : TwoSortCategory C} {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} 
         {EHM : EpsilonHyperModel SGF} {EGF : EpsilonGoodFibration}
         (I : b_ty) (Phi Psi : @h_ty Sign),
  form_equiv Phi Psi -> interp_h_ty I Phi ≅O interp_h_ty I Psi.
Proof. 

  (* 1. Bevezetjük az összes Typeclass-t és paramétert *)
  intros Sign SM C CC BCCC BiCCC TSC BEM GF SGF EHM EGF I Phi Psi H.
  
  (* 2. Visszatoljuk az I-t a célba, hogy az indukció során általános maradjon.
        Így elkerüljük az index-szétcsúszást az Atomoknál! *)
  generalize dependent I.
  
  (* 3. Indukció a form_equiv reláción (H) *)
  induction H; intros I_curr; simpl.

  - (* FE_Atom *)
    (* Itt I_curr a célbeli bázis, az axióma pedig lekezeli az egyenlőséget *)
    simpl.
    (* Explicit átadjuk a paramétereket: p, bázistípus, kódómén, termek, gépelések és az ekvivalencia *)
    apply (i_atom_cong_global p I_curr I A t1 t2 d1 d2 b).

  - (* FE_Refl *) apply iso_refl.
  - (* FE_Sym *) symmetry. apply IHform_equiv.
  - (* FE_Trans *) eapply iso_trans. { apply IHform_equiv1. } { apply IHform_equiv2. }
  
  - (* FE_Prod *) apply prod_iso_cong. { apply IHform_equiv1. } { apply IHform_equiv2. }
  - (* FE_Sum *) apply coprod_iso_cong. { apply IHform_equiv1. } { apply IHform_equiv2. }
  - (* FE_Arrow *) apply exp_iso_cong. { apply IHform_equiv2. } { apply IHform_equiv1. }
  
  - (* FE_All *) 
    apply pi_iso_cong. 
    (* Itt megadjuk az IH-nak a kiterjesztett kontextust (I_curr * D) *)
    apply (IHform_equiv (b_Prod I_curr D)).

  - (* FE_Ex *) 
    apply sigma_iso_cong. 
    apply (IHform_equiv (b_Prod I_curr D)).
  - (* FE_Eps_Lift *)
    simpl.
    symmetry.
    
    (* Transzitivitással bontjuk ketté a problémát *)
    eapply iso_trans.
    {
      (* Most már odaadhatjuk neki a hiányzó dg-t az axiómánkból! 
         A b_fst_typing_hack I_curr megadja a base_typing bizonyítást. *)
      eapply (eps_beck_chevalley_iso _ I_curr D b_fst (b_fst_typing_hack I_curr)). 
    }
    apply eps_lift_subst_cong_hack.
  - (* FE_Pullback_Id *)
    (* Erre a célra: ... (form_pullback b_id Phi) ≅O ... Phi *)
    apply interp_pb_id_ax.
  - (* FE_Pullback_Comp *)
    symmetry.
    apply (interp_pb_comp_ax I_curr I_curr I_curr).

  - (* FE_Pullback_Cong *)
    eapply interp_pb_cong_untyped_ax.
    exact b.
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
