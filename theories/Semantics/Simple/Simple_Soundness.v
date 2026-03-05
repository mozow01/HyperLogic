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
  i_atom : forall (p : nat) (t : b_tm) (I : b_ty), @obj (Fiber (interp_ty I)) 
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
      @right_adj_obj _ _ _ (pullback_has_right_adjoint (interp_tm (BT_Fst (A:=I) (B:=A)))) 
                           (interp_h_ty (b_Prod I A) Body)
  | Ty_Ex A Body => 
      @left_adj_obj _ _ _ (pullback_has_left_adjoint (interp_tm (BT_Fst (A:=I) (B:=A)))) 
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


Lemma form_pullback_iso : 
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF} 
         (I A : b_ty) (f : b_tm) (df : base_typing I f A) (Phi : h_ty),
  interp_h_ty I (form_pullback (b_pair b_id f) Phi) ≅O 
  @fobj _ _ (Pullback (interp_tm (BT_Pair BT_Id df))) (interp_h_ty (b_Prod I A) Phi).
Proof.
  intros C CC TSC GF SGF HM I A f df Phi.
  induction Phi.
  - (* 1. Ty_Unit (Terminális objektum / Igaz) *)
    simpl.
    symmetry.
    apply pb_term_iso.
Admitted.
    
Axiom form_pullback_fst_iso : 
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF} 
         (I A : b_ty) (Phi : h_ty),
  interp_h_ty (b_Prod I A) (form_pullback b_fst Phi) ≅O 
  @fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I Phi).

Axiom ctx_pullback_iso : 
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF} 
         (I A : b_ty) (G : h_context),
  interp_h_ctx (b_Prod I A) (ctx_pullback b_fst G) ≅O 
  @fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ctx I G).

(* Kvantor struktúrális trükkök (Identitás-visszahúzás és Frobenius Reciprocitás) *)
Axiom pb_eval_iso : 
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF} 
         (I A : b_ty) (f : b_tm) (df : base_typing I f A) (Phi : h_ty),
  hom (interp_h_ty I (Ty_All A Phi)) 
      (@fobj _ _ (Pullback (interp_tm (BT_Pair BT_Id df))) 
        (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I (Ty_All A Phi)))).

Axiom pb_unit_iso : 
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF} 
         (I A : b_ty) (f : b_tm) (df : base_typing I f A) (Phi : h_ty),
  hom (@fobj _ _ (Pullback (interp_tm (BT_Pair BT_Id df))) 
        (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I (Ty_Ex A Phi)))) 
      (interp_h_ty I (Ty_Ex A Phi)).

Axiom ex_elim_frobenius : 
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF} 
         (I A : b_ty) (G : h_context) (Phi Chi : h_ty),
  hom (prod (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ctx I G)) 
            (interp_h_ty (b_Prod I A) Phi)) 
      (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I Chi)) -> 
  hom (prod (interp_h_ctx I G) (interp_h_ty I (Ty_Ex A Phi))) (interp_h_ty I Chi).


(* ================================================================= *)
(* 3. INHABITED SOUNDNESS TÉTEL                                      *)
(* ================================================================= *)

Definition hyper_soundness_inhabited 
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
      apply (@epsilon _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (pullback_has_right_adjoint _)). }
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
      apply (@unit _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (pullback_has_left_adjoint _)). }
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

(* ================================================================= *)
(*              PRENEX NORMÁLFORMA (FROBENIUS / EXISTS)              *)
(* ================================================================= *)

Section Prenex_Coq_Proof.
  (* 1. Behozzuk a környezetet pontosan úgy, ahogy a Soundness.v-ben van *)
  Context {C : SetoidCategory} {CC : CartesianCategory C}
          {BCCC : CartesianClosedCategory C} {BiCCC : BiCartesianClosedCategory BCCC}
          {TSC : TwoSortCategory C} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
          {HM : HyperModel SGF}.

  Variable I A : b_ty.
  Variable Phi : h_ty. (* Ez a formula az I x A felett (tartalmazza a kvantált változót) *)
  Variable G : h_context. (* Ez a kontextus I felett van (szabad a kvantált változótól) *)
  
  (* Képzeljük el, hogy Chi a "prenex alakú" célformula *)
  Variable Chi : h_ty.
  
  (* -----------------------------------------------------------------
     A PRENEX ÁTALAKÍTÁS LOGIKAI JELENTÉSE:
     Azt igazoljuk, hogy a Formula 1-ből következik a Formula 2.

     Hagyományos (változós) logikában:
     Formula 1:  G ∧ (∃x:A. Phi(x))
     Formula 2:  ∃x:A. (G ∧ Phi(x))
     Feltétel:   x ∉ FV(G)

     A mi változómentes (point-free) hiperdoktrínánkban:
     Formula 1:  G ∧ (∃A. Phi)
     Formula 2:  ∃A. (π₁^*G ∧ Phi)
     

     Ahol a π₁^*G (pullback) pontosan azt a feltételt kódolja térben, 
     hogy G független az A-tól (vagyis x ∉ FV(G)).
     
     Let pi1 := Pullback (interp_tm (BT_Fst (A:=I) (B:=A))).
     Let ExA := pullback_has_left_adjoint (interp_tm (BT_Fst (A:=I) (B:=A))).
     
     
     (* FORMULA 1: G ∧ (∃A. Phi) *)
    hom (prod (interp_h_ctx I G) 
              (interp_h_ty I (Ty_Ex A Phi)))
              
    (* FORMULA 2: ∃A. (π₁^*G ∧ Phi) *)
        (@left_adj_obj _ _ _ ExA 
           (prod (@fobj _ _ pi1 (interp_h_ctx I G)) 
                 (interp_h_ty (b_Prod I A) Phi))).
  ----------------------------------------------------------------- *)

  (* A Prenex-emelés "Oda" iránya: 
     Ha a felhúzott kontextus (pi1^* G) és Phi szorzatából következik a felhúzott Chi,
     akkor a G és az ∃A. Phi szorzatából is következik Chi. 
     Ez KÖZVETLENÜL a prenex kiemelés logikája! *)
  Lemma prenex_exists_forth : 
    hom (prod (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ctx I G)) 
              (interp_h_ty (b_Prod I A) Phi)) 
        (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I Chi)) -> 
    hom (prod (interp_h_ctx I G) (interp_h_ty I (Ty_Ex A Phi))) (interp_h_ty I Chi).
  Proof.
    intros H_premise.
    (* Itt a varázslat: az axiómád egyetlen lépésben átviszi a bizonyítást 
       a szálon kívülről a szál belsejébe! *)
    apply ex_elim_frobenius.
    
    (* És a fennmaradó cél pontosan a premisszánk! *)
    exact H_premise.
  Defined.
End Prenex_Coq_Proof.

