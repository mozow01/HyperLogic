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

(* ================================================================= *)
(* 1. HYPER MODEL ÉS INTERPRETÁCIÓ                                   *)
(* ================================================================= *)

Class HyperModel {C : SetoidCategory} {CC : CartesianCategory C} 
                 {TSC : TwoSortCategory C} {GF : GoodFibration C} 
                 (SGF : StrictGoodFibration C GF) := {
  
  i_atom : forall (p : nat) (t : b_tm) (I : b_ty), @obj (Fiber (interp_ty I)) ;

  i_atom_pb : forall (p : nat) (t : b_tm) (I A : b_ty) (f : b_tm) (df : base_typing I f A),
    @fobj _ _ (Pullback (interp_tm df)) (i_atom p t A) ≅O i_atom p (b_comp t f) I
}.

Fixpoint interp_h_ty {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
                     {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF}
                     (I : b_ty) (Phi : h_ty) : @obj (Fiber (interp_ty I)) :=
  match Phi with
  | Ty_Unit => terminal
  | Ty_Void => initial
  | Ty_Prod A B => prod (interp_h_ty I A) (interp_h_ty I B)
  | Ty_Sum A B => coprod (interp_h_ty I A) (interp_h_ty I B)
  | Ty_Arrow A B => exp (interp_h_ty I B) (interp_h_ty I A)
  | Ty_Atom p t => i_atom p t I
  | Ty_All A Body => 
      @right_adj_obj _ _ _ pullback_has_right_adjoint 
                           (interp_h_ty (b_Prod I A) Body)
  | Ty_Ex A Body => 
      @left_adj_obj _ _ _ pullback_has_left_adjoint 
                          (interp_h_ty (b_Prod I A) Body)
  end.

Fixpoint interp_h_ctx {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
                      {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF}
                      (I : b_ty) (G : h_context) : @obj (Fiber (interp_ty I)) :=
  match G with
  | nil => terminal
  | Phi :: G' => prod (interp_h_ctx I G') (interp_h_ty I Phi)
  end. 
  
(* ================================================================= *)
(* 2. STRUKTURÁLIS KOMPATIBILITÁSI LEMMÁK (AXIÓMÁK)                  *)
(* ================================================================= *)

Lemma typing_pullback_ext :
  forall {I J b : b_ty} {g : b_tm} (dg : base_typing I g J),
  base_typing (b_Prod I b) (b_pullback_ext g) (b_Prod J b).
Proof.
  intros I J b g dg.
  unfold b_pullback_ext.
  apply BT_Pair.
  - eapply BT_Comp. (* Itt az eapply! *)
    + exact dg.
    + apply BT_Fst.
  - apply BT_Snd.
Defined. (* Ne feledd, ide Defined kell! *)

Lemma form_pullback_general_iso :
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF}
         (Phi : h_ty) (I J : b_ty) (g : b_tm) (dg : base_typing I g J),
  interp_h_ty I (form_pullback g Phi) ≅O
  @fobj _ _ (Pullback (interp_tm dg)) (interp_h_ty J Phi).
Proof.
  (* Figyeld meg: a Phi-ig intros-olunk, így az I, J, g, dg a célban marad! *)
  intros C CC TSC GF SGF HM Phi.
  induction Phi; intros I J g dg; simpl.
  - (* Ty_Unit *)
    symmetry. apply pb_term_iso.
  - (* Ty_Void *)
    symmetry. apply pb_init_iso.
  - (* Ty_Prod *)
    eapply iso_trans.
    (* Itt a trükk: kifejezetten átadjuk az IH-nak a jelenlegi I, J, g, dg paramétereket! *)
    + apply (prod_iso_cong (IHPhi1 I J g dg) (IHPhi2 I J g dg)).
    + symmetry. apply pb_prod_iso.
  - (* Ty_Sum *)
    eapply iso_trans.
    + apply (coprod_iso_cong (IHPhi1 I J g dg) (IHPhi2 I J g dg)).
    + symmetry. apply pb_coprod_iso.
  - (* Ty_Arrow *)
    eapply iso_trans.
    (* Ne feledd a felcserélést a nyílnál az interp_h_ty miatt! *)
    + apply (exp_iso_cong (IHPhi2 I J g dg) (IHPhi1 I J g dg)).
    + symmetry. apply pb_exp_iso.
  - (* Ty_Atom *)
    symmetry. apply (i_atom_pb n b I J g dg).
  - (* Ty_All *)
    eapply iso_trans.
    + (* 1. Felhúzzuk az IH-t a kvantor alá a pi_iso_cong segítségével *)
      apply pi_iso_cong.
      (* Alkalmazzuk a nyitott IH-t a kiterjesztett kontextusra és a dg_ext-re *)
      exact (IHPhi (b_Prod I b) (b_Prod J b) (b_pullback_ext g) (typing_pullback_ext dg)).
      
    + (* 2. Beck-Chevalley feltétel alkalmazása *)
      (* A maradék goal pontosan f^* (Pi A) ≅O Pi (f_ext^* A) alakú, 
         ami a beck_chevalley_pi axióma szimmetriája! *)
      symmetry.
      apply beck_chevalley_pi.
  - (* Ty_Ex *)
    eapply iso_trans.
    + apply sigma_iso_cong.
      exact (IHPhi (b_Prod I b) (b_Prod J b) (b_pullback_ext g) (typing_pullback_ext dg)).
    + symmetry.
      apply beck_chevalley_sigma.
Defined.

(** * Syntactic Substitution = Semantic Pullback *)
Lemma form_pullback_iso :
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF}
         (I A : b_ty) (f : b_tm) (df : base_typing I f A) (Phi : h_ty),
  interp_h_ty I (form_pullback (b_pair b_id f) Phi) ≅O
  @fobj _ _ (Pullback (interp_tm (BT_Pair BT_Id df))) (interp_h_ty (b_Prod I A) Phi).
Proof.
  intros.
  (* Egyszerűen csak ráhívjuk az általánosított tételt a konkrét paraméterekkel! *)
  apply (form_pullback_general_iso Phi I (b_Prod I A) (b_pair b_id f) (BT_Pair BT_Id df)).
Defined.

Lemma form_pullback_fst_iso : 
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF} 
         (I A : b_ty) (Phi : h_ty),
  interp_h_ty (b_Prod I A) (form_pullback b_fst Phi) ≅O 
  @fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I Phi).
Proof.
  intros.
  (* Közvetlenül alkalmazzuk az általános lemmát, a Coq kitalálja az implicit paramétereket a célból *)
  apply form_pullback_general_iso.
Defined.

Lemma ctx_pullback_iso : 
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF} 
         (I A : b_ty) (G : h_context),
  interp_h_ctx (b_Prod I A) (ctx_pullback b_fst G) ≅O 
  @fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ctx I G).
Proof.
  intros C CC TSC GF SGF HM I A G.
  induction G as [| Phi G' IHG']; simpl.
  - (* nil eset: az üres kontextus a terminális objektum *)
    symmetry. apply pb_term_iso.
  - (* cons eset: Phi :: G', ami a szemantikában egy szorzat *)
    eapply iso_trans.
    + (* A kongruencia: bal oldalra az IH, jobb oldalra az előzőlemmánk *)
      apply (prod_iso_cong IHG' (form_pullback_fst_iso I A Phi)).
    + (* A szorzat visszahúzásának axiómája *)
      symmetry. apply pb_prod_iso.
Defined.
(* Kvantor struktúrális trükkök (Identitás-visszahúzás és Frobenius Reciprocitás) *)
Lemma pb_eval_iso : 
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF} 
         (I A : b_ty) (f : b_tm) (df : base_typing I f A) (Phi : h_ty),
  hom (interp_h_ty I (Ty_All A Phi)) 
      (@fobj _ _ (Pullback (interp_tm (BT_Pair BT_Id df))) 
        (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I (Ty_All A Phi)))).
Proof.
  intros.
  eapply compose.
  - eapply compose.
    + (* 3. lépés: Kompozíció szétbontása *)
      apply (@iso_to _ _ _ (pullback_comp_iso 
                              prod_fst 
                              (prod_map (id (interp_ty I)) (interp_tm df)) 
                              (interp_h_ty I (Ty_All A Phi)))).
    + (* 2. lépés: Bázis egyenlőség bizonyítása ASSERT-tel! *)
      (* Külön, egyértelműen kimondjuk és bebizonyítjuk a szükséges egyenlőséget *)
      assert (H_eq : id (interp_ty I) ≅ compose prod_fst (prod_map (id (interp_ty I)) (interp_tm df))).
      { symmetry. apply prod_map_fst. }
      
      (* Majd ezt az explicit H_eq bizonyítást adjuk át a _ helyett! *)
      apply (@iso_to _ _ _ (pb_iso 
                              (id (interp_ty I)) 
                              (compose prod_fst (prod_map (id (interp_ty I)) (interp_tm df))) 
                              H_eq 
                              (interp_h_ty I (Ty_All A Phi)))).
  - (* 1. lépés: Identitás visszahúzás *)
    apply (@iso_from _ _ _ (pullback_id_iso (interp_h_ty I (Ty_All A Phi)))).
Defined.

Lemma pb_unit_iso : 
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF} 
         (I A : b_ty) (f : b_tm) (df : base_typing I f A) (Phi : h_ty),
  hom (@fobj _ _ (Pullback (interp_tm (BT_Pair BT_Id df))) 
        (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I (Ty_Ex A Phi)))) 
      (interp_h_ty I (Ty_Ex A Phi)).
Proof.
  intros.
  (* Visszafelé építkezünk az eapply compose miatt: a céltól (jobb oldal) haladunk a forrás (bal oldal) felé *)
  eapply compose.
  - (* 3. (Utolsó) lépés: Pullback(id) X -> X *)
    apply (@iso_to _ _ _ (pullback_id_iso (interp_h_ty I (Ty_Ex A Phi)))).
  - eapply compose.
    + (* 2. (Középső) lépés: Pullback(pi1 o <id, f>) X -> Pullback(id) X *)
      assert (H_eq : compose prod_fst (prod_map (id (interp_ty I)) (interp_tm df)) ≅ id (interp_ty I)).
      { apply prod_map_fst. }
      apply (@iso_to _ _ _ (pb_iso 
                              (compose prod_fst (prod_map (id (interp_ty I)) (interp_tm df))) 
                              (id (interp_ty I)) 
                              H_eq 
                              (interp_h_ty I (Ty_Ex A Phi)))).
    + (* 1. (Első) lépés: Pullback(<id, f>) o Pullback(pi1) X -> Pullback(pi1 o <id, f>) X *)
      (* Ide kell az iso_from! *)
      apply (@iso_from _ _ _ (pullback_comp_iso 
                                prod_fst 
                                (prod_map (id (interp_ty I)) (interp_tm df)) 
                                (interp_h_ty I (Ty_Ex A Phi)))).
Defined.

Lemma ex_elim_frobenius : 
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF} 
         (I A : b_ty) (G : h_context) (Phi Chi : h_ty),
  hom (prod (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ctx I G)) 
            (interp_h_ty (b_Prod I A) Phi)) 
      (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I Chi)) -> 
  hom (prod (interp_h_ctx I G) (interp_h_ty I (Ty_Ex A Phi))) (interp_h_ty I Chi).
Proof.
  intros C CC TSC GF SGF HM I A G Phi Chi H_premissza.
  
  (* 1. Curry-zés a premisszán *)
  assert (H_curry : hom (interp_h_ty (b_Prod I A) Phi) 
                        (exp (@fobj _ _ (Pullback (interp_tm BT_Fst)) (interp_h_ty I Chi)) 
                             (@fobj _ _ (Pullback (interp_tm BT_Fst)) (interp_h_ctx I G)))).
  { apply exp_map. 
    eapply compose. 
    - exact H_premissza. 
    - apply prod_map. { apply prod_snd. } { apply prod_fst. } }

  (* 2. Visszahúzás bevitele az exponenciális alá *)
  assert (H_pb : hom (interp_h_ty (b_Prod I A) Phi) 
                     (@fobj _ _ (Pullback (interp_tm BT_Fst)) 
                            (exp (interp_h_ty I Chi) (interp_h_ctx I G)))).
  { eapply compose. 
    - apply (@iso_from _ _ _ (pb_exp_iso (interp_tm BT_Fst) _ _)). 
    - exact H_curry. }

  (* 3. Adjungálás alkalmazása: Phi -> P*(Chi^G) ból Sigma Phi -> Chi^G *)
  assert (H_sigma : hom (interp_h_ty I (Ty_Ex A Phi)) 
                        (exp (interp_h_ty I Chi) (interp_h_ctx I G))).
  { apply left_adj_mor. exact H_pb. }

  (* 4. A végső morfizmus összeállítása uncurry-vel (eval) *)
  eapply compose.
  - (* Itt adjuk meg explicite az eval paramétereit *)
    apply (@eval (Fiber (interp_ty I)) _ _ (interp_h_ctx I G) (interp_h_ty I Chi)).
  - (* Összeállítjuk a (Chi^G × G) tartományt a bemeneti (G × Sigma) ból *)
    apply prod_map.
    + (* Sigma -> Chi^G *)
      eapply compose. { exact H_sigma. } { apply prod_snd. }
    + (* G -> G *)
      apply prod_fst.
Defined.

(* ================================================================= *)
(* 3. INHABITED SOUNDNESS TÉTEL                                      *)
(* ================================================================= *)

Theorem hyper_soundness_inhabited 
  {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C} {BiCCC : BiCartesianClosedCategory BCCC}
  {TSC : TwoSortCategory C} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF}
  {I : b_ty} {G : h_context} {p : h_tm} {Phi : h_ty}
  (D : h_derivation I G p Phi) : hom (interp_h_ctx I G) (interp_h_ty I Phi).
Proof.
  induction D.
  
  - apply prod_snd.
  - eapply compose. exact IHD. apply prod_fst.
  - apply terminal_map.
  - apply exp_map. exact IHD.
  - eapply compose. eapply eval. apply (prod_map IHD1 IHD2).
  - apply (prod_map IHD1 IHD2).
  - eapply compose. eapply prod_fst. exact IHD.
  - eapply compose. eapply prod_snd. exact IHD.
  - eapply compose. eapply coprod_inl. exact IHD.
  - eapply compose. eapply coprod_inr. exact IHD.
  
  - (* HD_Case - Tisztán BCCC műveletekkel disztributáljuk a G-t a Szorzatokon! *)
    eapply compose.
    { (* Cél: G x (Phi+Psi) -> Chi *)
      eapply compose.
      { (* Cél: X -> Chi, ahol X = (G x Phi) + (G x Psi) *)
        apply (coprod_map IHD2 IHD3). } 
      { (* Cél: G x (Phi+Psi) -> X, a disztributivitás felépítése eval és swap segítségével *)
        eapply compose.
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
    { (* Cél: G -> G x (Phi+Psi) *)
      eapply (prod_map (id _) IHD1). }

- (* HD_Absurd *)
    eapply compose.
    { apply initial_map. }
    { exact IHD. }

  (* --- HYPER KVANTOR SZABÁLYOK --- *)
 
  - (* HD_All_Intro *)
    apply right_adj_mor.
    eapply compose.
    { exact IHD. }
    { exact (@iso_from _ _ _ (ctx_pullback_iso I A G)). }
 
 - (* HD_All_Elim *)
    eapply compose.
    { (* 1. Lépés: Szintaktikus visszahúzás összekötése a fibrációs Pullback-kel *)
      exact (@iso_from _ _ _ (form_pullback_iso I A f b Phi)). }
    eapply compose.
    { (* 2. Lépés: A Counit (epsilon) alkalmazása az fmap-en belül *)
      eapply (@fmap _ _ (Pullback (interp_tm (BT_Pair BT_Id b))) _ _).
      (* JAVÍTVA: Töröltük az aláhúzást és a zárójelet a pullback_has_right_adjoint mellől! *)
      apply (@epsilon _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) pullback_has_right_adjoint). }
    eapply compose.
    { (* 3. Lépés: A pb_eval_iso axióma (ami paraméterek nélkül is egyértelmű a Coq-nak) *)
      apply pb_eval_iso. }
    { (* 4. Lépés: Maga a deriváció (IHD) *)
      exact IHD. }
      
   - (* HD_Ex_Intro *)
    eapply compose.
    { apply pb_unit_iso. }
    eapply compose.
    { (* Az @ jellel pontosan a funktor helyére (3. paraméter) tesszük a Pullback-et *)
      eapply (@fmap _ _ (Pullback (interp_tm (BT_Pair BT_Id b))) _ _).
      (* JAVÍTVA: Töröltük a felesleges ( _ ) paramétert az axióma mögül! *)
      apply (@unit _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) pullback_has_left_adjoint). }
    eapply compose.
    { (* Itt is expliciten átadjuk a form_pullback_iso mind az 5 paraméterét! *)
      exact (@iso_to _ _ _ (form_pullback_iso I A f b Phi)). }
    { exact IHD. }

  - (* HD_Ex_Elim *)
    eapply compose.
    { apply ex_elim_frobenius. 
      
      (* 1. Lépés: Cél konvertálása (form_pullback -> Pullback) *)
      eapply compose.
      { (* Explicit megadjuk az axiómát a Chi célformulával *)
        exact (@iso_to _ _ _ (form_pullback_fst_iso I A Chi)). }
      
      (* 2. Lépés: Maga a deriváció (IHD2) *)
      eapply compose.
      { exact IHD2. }
      
      (* 3. Lépés: Startvonal konvertálása a szorzat bal oldalán *)
      { cbn. 
        (* Explicit megadjuk a G kontextust a bal oldal visszahúzásához *)
        apply (prod_map (compose (@iso_from _ _ _ (ctx_pullback_iso I A G)) prod_fst) prod_snd). } }
        
    (* 4. Lépés: A kontextus megkettőzése és az Egzisztenciális Tanú behelyettesítése *)
    { apply (prod_map (id _) IHD1). }
Defined.
