(* theories/Logic/Hyper/Epsilon_Adjoint/Hyper_Syntax_Lemmas.v *)

Require Import List.
Import ListNotations.
Require Import HyperLogic.Logic.Base.Epsilon_Adjoint.Base_Syntax.
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum.
Require Import HyperLogic.Logic.Hyper.Epsilon_Adjoint.Hyper_Syntax.
Require Import Coq.Program.Equality.

Lemma wf_subst : forall {Sign : Type} {I J : b_ty} (t : @b_tm Sign) (dt : base_typing I t J) (Phi : @h_ty Sign),
  WellFormed J Phi ->
  WellFormed I (form_subst t Phi).
Proof.
  intros Sign I J t dt Phi H.
  revert I t dt.
  induction H; intros I0 t0 dt.
  - simpl. apply WF_Unit.
  - simpl. apply WF_Void.
  - simpl. apply WF_Prod.
    + apply IHWellFormed1. exact dt.
    + apply IHWellFormed2. exact dt.
  - simpl. apply WF_Sum.
    + apply IHWellFormed1. exact dt.
    + apply IHWellFormed2. exact dt.
  - simpl. apply WF_Arrow.
    + apply IHWellFormed1. exact dt.
    + apply IHWellFormed2. exact dt.
  - simpl. eapply WF_Atom.
    eapply BT_Comp.
    + eassumption.
    + exact dt.
  - (* WF_All *)
    simpl. apply WF_All.
    apply IHWellFormed.
    (* Kibontjuk a bázis-kiterjesztést és bebizonyítjuk a típusosságát: *)
    unfold b_subst_ext. apply BT_Pair.
    + eapply BT_Comp. exact dt. apply BT_Fst.
    + apply BT_Snd.
  - (* WF_Ex *)
    simpl. apply WF_Ex.
    apply IHWellFormed.
    unfold b_subst_ext. apply BT_Pair.
    + eapply BT_Comp. exact dt. apply BT_Fst.
    + apply BT_Snd.
Defined.

Lemma typing_subst_ext : forall {Sign : Type} {I J A : b_ty} {f : @b_tm Sign},
  base_typing I f J ->
  base_typing (b_Prod I A) (b_subst_ext f) (b_Prod J A).
Proof.
  intros SM I J A f.
  intros Hf.
  unfold b_subst_ext.
  apply BT_Pair.
  - eapply BT_Comp.
    + exact Hf.
    + apply BT_Fst.
  - apply BT_Snd.
Defined.

(* Visszanyeri a formulák jólformáltságát az ekvivalenciájukból *)
(* Visszanyeri a formulák jólformáltságát az ekvivalenciájukból *)
Lemma form_equiv_wf : forall {Sign : Type} `{SkolemMapping Sign} (I : b_ty) (Phi Psi : @h_ty Sign),
  form_equiv I Phi Psi -> (WellFormed I Phi * WellFormed I Psi)%type.
Proof.
  intros Sign SM I Phi Psi H.
  induction H.
  - split; eapply WF_Atom; eassumption.
  - split; assumption.
  - destruct IHform_equiv; split; assumption.
  - destruct IHform_equiv1, IHform_equiv2; split; eassumption.
  - destruct IHform_equiv1, IHform_equiv2; split; apply WF_Prod; assumption.
  - destruct IHform_equiv1, IHform_equiv2; split; apply WF_Sum; assumption.
  - destruct IHform_equiv1, IHform_equiv2; split; apply WF_Arrow; assumption.
  - destruct IHform_equiv; split; apply WF_All; assumption.
  - destruct IHform_equiv; split; apply WF_Ex; assumption.
  
  - (* FE_Eps_Adjoint_Iso *)
    split.
    + apply WF_Ex. exact w.
    + eapply wf_subst.
      * eapply BT_Pair. apply BT_Id. apply BT_Const.
      * exact w.

  - (* FE_Eps_Functorial *)
    destruct IHform_equiv as [wf_Phi wf_Psi].
    split.
    + eapply wf_subst.
      * eapply BT_Pair. apply BT_Id. apply BT_Const.
      * exact wf_Phi.
    + eapply wf_subst.
      * eapply BT_Pair. apply BT_Id. apply BT_Const.
      * exact wf_Psi.

  - (* FE_Pullback_Id *)
    split.
    + eapply wf_subst. apply BT_Id. exact w.
    + exact w.

  - (* FE_Pullback_Comp *)
    split.
    + eapply wf_subst. exact dg. eapply wf_subst. exact df. exact w.
    + eapply wf_subst. eapply BT_Comp. exact df. exact dg. exact w.

  - (* FE_Pullback_Cong *)
    split.
    + eapply wf_subst. exact df. exact w.
    + eapply wf_subst. exact dg. exact w.

  - (* FE_Eps_BC *)
    split.
    + eapply wf_subst.
      * eapply BT_Pair. apply BT_Id. apply BT_Const.
      * eapply wf_subst. eapply typing_subst_ext. exact dt. exact w.
    + eapply wf_subst.
      * exact dt.
      * eapply wf_subst. eapply BT_Pair. apply BT_Id. apply BT_Const. exact w.
Defined.

(* Visszanyeri a kontextusok jólformáltságát az ekvivalenciájukból *)
Lemma ctx_equiv_wf_left : forall {Sign : Type} `{SkolemMapping Sign} (I : b_ty) (G G' : @h_context Sign),
  ctx_equiv I G G' -> All_WellFormed I G' -> All_WellFormed I G.
Proof.
  intros Sign SM I G G' H Hwf_G'.
  induction H.
  - (* CEq_Nil *)
    exact Hwf_G'.
  - (* CEq_Cons *)
    (* Invertáljuk a G' jólformáltságát (ami Psi :: G2 alakú) *)
    inversion Hwf_G'; subst.
    apply AWF_Cons.
    + (* A form_equiv_wf lemma adja a Phi jólformáltságát *)
      apply (form_equiv_wf I Phi Psi f).
    + (* Az IH adja a G1 jólformáltságát *)
      apply IHctx_equiv. exact X0.
Defined.

(* Visszanyeri a kontextusok jólformáltságát az ekvivalenciájukból - Jobb irány *)
Lemma ctx_equiv_wf_right : forall {Sign : Type} `{SkolemMapping Sign} (I : b_ty) (G1 G2 : @h_context Sign),
  ctx_equiv I G1 G2 -> All_WellFormed I G1 -> All_WellFormed I G2.
Proof.
  intros Sign SM I G1 G2 H Hwf1.
  induction H.
  - (* CEq_Nil *)
    exact Hwf1.
  - (* CEq_Cons *)
    (* Invertáljuk a G1 jólformáltságát *)
    inversion Hwf1; subst.
    apply AWF_Cons.
    + (* A form_equiv_wf mindkét irányt visszaadja egy párban (szorzatban) *)
      destruct (form_equiv_wf I Phi Psi f) as [wf_Phi wf_Psi].
      exact wf_Psi.
    + (* Az IH adja a G2 maradékának jólformáltságát *)
      apply IHctx_equiv. exact X0.
Defined.

Lemma form_equiv_subst : forall {Sign : Type} `{SkolemMapping Sign}
  {I J : b_ty} (t : @b_tm Sign) (dt : base_typing I t J) (Phi Psi : @h_ty Sign),
  form_equiv J Phi Psi ->
  form_equiv I (form_subst t Phi) (form_subst t Psi).
Proof.
  intros Sign SM I J t dt Phi Psi H.
  revert I t dt.
  induction H; intros I0 t0 dt0.
  - (* FE_Atom *)
    simpl. eapply FE_Atom.
    apply BE_CongComp.
    + apply BE_Refl. (* A helyettesítés (t0) önmagával ekvivalens *)
    + exact b.       (* Az atomok bázis-termjei (t1, t2) ekvivalensek *)
  - (* FE_Refl *)
    apply FE_Refl.
    eapply wf_subst.
    + exact dt0.
    + exact w.
  - (* FE_Sym *)
    apply FE_Sym.
    apply IHform_equiv. exact dt0.
  - (* FE_Trans *)
    eapply FE_Trans.
    + apply IHform_equiv1. exact dt0.
    + apply IHform_equiv2. exact dt0.
  - (* FE_Prod *)
    simpl. apply FE_Prod.
    + apply IHform_equiv1. exact dt0.
    + apply IHform_equiv2. exact dt0.
  - (* FE_Sum *)
    simpl. apply FE_Sum. 
    + apply IHform_equiv1. exact dt0.
    + apply IHform_equiv2. exact dt0.
  - (* FE_Arrow *)
    simpl. apply FE_Arrow.
    + apply IHform_equiv1. exact dt0.
    + apply IHform_equiv2. exact dt0.
  - (* FE_All *)
    simpl. apply FE_All.
    (* Itt használjuk fel az imént bizonyított lemmát! *)
    apply IHform_equiv. apply typing_subst_ext. exact dt0.
  - (* FE_Ex *)
    simpl. apply FE_Ex.
    apply IHform_equiv. apply typing_subst_ext. exact dt0.
 - (* FE_Eps_Adjoint_Iso ág *)
    (* A cél: Ty_Ex A (form_subst (b_subst_ext t0) Phi) ≡ form_subst t0 (Phi .[ ε A, Phi ]) *)
    
    eapply FE_Trans.
    { (* 1. Lépés: Alkalmazzuk az Epszilon-Adjunkciót a BELSŐ (már helyettesített) formulára *)
      apply FE_Eps_Adjoint_Iso.
      (* A wf_pullback (vagy wf_subst) lemma mondja ki, hogy a helyettesítés 
         megőrzi a jólformáltságot, ha a helyettesítő term típushelyes. *)
      eapply wf_subst. 
      
      (* 1. Megadjuk a b_subst_ext t0 (azaz b_pair (b_comp t0 b_fst) b_snd) 
            típushelyességének levezetési fáját: *)
      - exact (BT_Pair (BT_Comp dt0 BT_Fst) BT_Snd).
      
      (* 2. Megadjuk magának a Phi-nek a jólformáltságát, amit a 'w' igazol: *)
      - exact w.
    }
    { (* 2. Lépés: Itt jön a mágia! A tegnap bevezetett Beck-Chevalley axióma (FE_Eps_BC) 
         haajszálpontosan a hiányzó láncszemet bizonyítja a két forma között! *)
      eapply FE_Eps_BC.
      - exact dt0.
      - exact w. 
    }
 - (* FE_Eps_Functorial ág *)
    eapply FE_Trans.
    { (* 1. Lépés: Bal oldalon visszafelé alkalmazzuk a Beck-Chevalley-t *)
      eapply FE_Sym. 
      eapply FE_Eps_BC.
      - exact dt0.
      - exact (fst (form_equiv_wf (b_Prod I A) Phi Psi H)). (* <-- WF_Phi lekérése *)
    }
    
    eapply FE_Trans.
    { (* 2. Lépés: Epszilon Functorial szabály! *)
      eapply FE_Eps_Functorial.
      apply (IHform_equiv (b_Prod I0 A) (b_subst_ext t0)).
      apply typing_subst_ext. exact dt0. 
    }
    
    { (* 3. Lépés: Jobb oldalon előrefelé alkalmazzuk a Beck-Chevalley-t *)
      eapply FE_Eps_BC.
      - exact dt0.
      - exact (snd (form_equiv_wf (b_Prod I A) Phi Psi H)). (* <-- WF_Psi lekérése *)
    }
  - (* FE_Pullback_Id ág *)
    (* Cél: (Phi[id])[t0] ≡ Phi[t0] *)
    eapply FE_Trans.
    { (* 1. Lépés: (Phi[id])[t0] ≡ Phi[id o t0] *)
      eapply FE_Pullback_Comp.
      - apply BT_Id.
      - exact dt0.
      - exact w.
    }
    { (* 2. Lépés: Phi[id o t0] ≡ Phi[t0] 
         mivel id o t0 = t0 a bázis kategóriában. *)
      eapply FE_Pullback_Cong.
      - (* Itt a bázis ekvivalencia kell: id o t0 ≈ t0 *)
        apply BE_IdL. (* Vagy BE_Id_Left, a bázis szintaxisodtól függően *)
      - exact w.
    }
  - (* FE_Pullback_Comp ág *)
    eapply FE_Trans.
    { (* 1. Lépés: (Phi[f])[g][t0] ≡ (Phi[f])[g o t0] *)
      eapply FE_Pullback_Comp.
      - exact dg.   (* A belső helyettesítés: g *)
      - exact dt0.  (* A külső helyettesítés: t0 *)
      - (* Mivel a belső formula itt Phi[f], ehhez kell a wf_subst *)
        eapply wf_subst.
        + exact df.
        + exact w.
    }
    
    eapply FE_Trans.
    { (* 2. Lépés: Phi[f][g o t0] ≡ Phi[f o (g o t0)] *)
      eapply FE_Pullback_Comp.
      - exact df. (* Belső helyettesítés: f *)
      - eapply BT_Comp. exact dg. exact dt0. (* Külső: g o t0 *)
      - exact w.
    }
    
    eapply FE_Trans.
    { (* 3. Lépés: Phi[f o (g o t0)] ≡ Phi[(f o g) o t0] *)
      eapply FE_Pullback_Cong.
      - apply BE_Assoc. (* A bázis kategória asszociativitása *)
      - exact w.
    }
    
    { (* 4. Lépés: Phi[(f o g) o t0] ≡ Phi[f o g][t0] (Visszafelé) *)
      eapply FE_Sym.
      eapply FE_Pullback_Comp.
      - eapply BT_Comp. exact df. exact dg. (* Belső: f o g *)
      - exact dt0. (* Külső: t0 *)
      - exact w.
    }
 - (* FE_Pullback_Cong ág *)
    eapply FE_Trans.
    { (* 1. Lépés: (Phi[f])[t0] ≡ Phi[f o t0] *)
      eapply FE_Pullback_Comp.
      - exact df.  (* Belső helyettesítés: f *)
      - exact dt0. (* Külső helyettesítés: t0 *)
      - exact w.   (* Jólformáltság: w *)
    }
    
    eapply FE_Trans.
    { (* 2. Lépés: Phi[f o t0] ≡ Phi[g o t0] *)
      eapply FE_Pullback_Cong.
      - (* A bázis kongruencia: t0 ≡ t0 és f ≡ g => f o t0 ≡ g o t0 *)
        eapply BE_CongComp.
        + apply BE_Refl. (* A belső term (t0) önmagával ekvivalens *)
        + exact b.       (* A külső termek (f és g) ekvivalensek *)
      - exact w.
    }
    
    { (* 3. Lépés: Phi[g o t0] ≡ (Phi[g])[t0] *)
      eapply FE_Sym.
      eapply FE_Pullback_Comp.
      - exact dg.  (* Belső helyettesítés: g *)
      - exact dt0. (* Külső helyettesítés: t0 *)
      - exact w.
    }
 - (* Új FE_Eps_BC ág (A Coq által generálva az új konstruktorhoz) *)
    eapply FE_Trans.
    { (* 1. Lépés: Bal oldal kibontása: (Phi[ext t][ε...])[t0] ≡ (Phi[ext t][ext t0])[ε...] 
         Ezt a FE_Eps_BC adja visszafelé a t0-ra! *)
      eapply FE_Sym.
      eapply FE_Eps_BC.
      - exact dt0.
      - eapply wf_subst.
        + eapply typing_subst_ext. exact dt.
        + exact w.
    }
    
    eapply FE_Trans.
    { (* 2. Lépés: Belső kompozíció összevonása: (Phi[ext t][ext t0])[ε...] ≡ (Phi[ext t o ext t0])[ε...] *)
      eapply FE_Eps_Functorial.
      eapply FE_Pullback_Comp.
      - eapply typing_subst_ext. exact dt.
      - eapply typing_subst_ext. exact dt0.
      - exact w.
    }
    
    eapply FE_Trans.
    { (* 3. Lépés: Bázis szintű kongruencia: ext t o ext t0 ≡ ext (t o t0) 
         Itt jön be a Base_Syntax Béta-redukciója! *)
      eapply FE_Eps_Functorial.
      eapply FE_Pullback_Cong.
      - unfold b_subst_ext.
        eapply BE_Trans.
        { apply BE_CompPair. }
        eapply BE_CongPair.
        + eapply BE_Trans.
          { eapply BE_Sym. apply BE_Assoc. }
          eapply BE_Trans.
          { eapply BE_CongComp.
            - apply BE_BetaFst.
            - apply BE_Refl. }
          apply BE_Assoc.
        + apply BE_BetaSnd.
      - exact w.
    }
    
    eapply FE_Trans.
    { (* 4. Lépés: Alkalmazzuk a FE_Eps_BC-t a kompozícióra: (Phi[ext (t o t0)])[ε...] ≡ (Phi[ε...])[t o t0] *)
      eapply FE_Eps_BC.
      - eapply BT_Comp. exact dt. exact dt0.
      - exact w.
    }
    
    { (* 5. Lépés: Külső kompozíció szétbontása: (Phi[ε...])[t o t0] ≡ (Phi[ε...])[t][t0] *)
      eapply FE_Sym.
      eapply FE_Pullback_Comp.
      - exact dt.
      - exact dt0.
      - eapply wf_subst.
        + eapply BT_Pair. apply BT_Id. apply BT_Const.
        + exact w.
    }
(* --- A POLC LESÖPRÉSE (Unshelve Magic) --- *)
  Unshelve.
  all: repeat match goal with
  | |- base_typing _ _ _ => eapply BT_Comp || eapply BT_Pair || 
                            apply BT_Id || eapply BT_Fst || eapply BT_Snd || 
                            apply typing_subst_ext || eassumption
  end.
Defined.

Lemma ctx_equiv_subst : forall {Sign : Type} `{SkolemMapping Sign}
  {I J : b_ty} (t : @b_tm Sign) (dt : base_typing I t J) (G1 G2 : @h_context Sign),
  ctx_equiv J G1 G2 ->
  ctx_equiv I (ctx_subst t G1) (ctx_subst t G2).
Proof.
  intros Sign SM I J t dt G1 G2 H.
  induction H.
  - simpl. apply CEq_Nil.
  - simpl. apply CEq_Cons.
    + eapply form_equiv_subst. exact dt. exact f.
    + exact IHctx_equiv.
Defined.


Lemma phi_iso_phi_id_snd : forall {Sign : Type} `{SkolemMapping Sign} (I A : b_ty) (Phi : @h_ty Sign) 
  (wf : WellFormed (b_Prod I A) Phi),
  form_equiv (b_Prod I A) Phi (form_subst (b_pair b_id b_snd) (form_subst b_fst Phi)).
Proof.
  intros Sign SM I A Phi wf.
  
  (* Lépés 1: Phi <==> Phi[id] 
     (Az identitás mentén vett subst izomorf az eredetivel) *)
  eapply FE_Trans.
  { eapply FE_Sym. eapply FE_Pullback_Id. exact wf. }
  
  (* Lépés 2: Phi[id] <==> Phi[fst o <id, snd>] 
     (A bázis kategória egyenlősége alapján: id = fst o <id, snd>) *)
  eapply FE_Trans.
  { eapply FE_Sym. 
    eapply FE_Pullback_Cong with 
      (df := BT_Comp BT_Fst (BT_Pair BT_Id BT_Snd)) 
      (dg := BT_Id).
    - (* ---> ITT A BÁZIS SZINTAXIS MÁGIÁJA <--- *)
      apply BE_BetaFst. 
    - exact wf. 
  }
  
 (* Lépés 3: Phi[fst o <id, snd>] <==> (Phi[fst])[<id, snd>] 
     (A subst funktor kompozíciója megőrzi az izomorfizmust) *)
  { apply FE_Sym.
    eapply FE_Pullback_Comp.
    - (* df: b_fst tipizálása *)
      apply (@BT_Fst Sign (b_Prod I A) A).
    - (* dg: b_pair b_id b_snd tipizálása *)
      apply BT_Pair.
      + apply (@BT_Id Sign (b_Prod I A)).
      + apply (@BT_Snd Sign I A).
    - (* a WellFormed Phi bizonyítás átadása *)
      exact wf. 
  }
Defined.

Lemma ex_implies_eps : forall {Sign : Type} `{SkolemMapping Sign} (I A : b_ty) (Phi : @h_ty Sign)
  (wf : WellFormed (b_Prod I A) Phi), (* <--- EZT ADD HOZZÁ! *)
  h_derivation I [ Ty_Ex A Phi ]
    (tm_ex_elim (tm_var 0) (tm_eps_intro b_snd (tm_var 0)))
    (Phi .[ ε A, Phi ]).
Proof.
  intros Sign SM I A Phi wf.
  
  (* 1. Felnyitjuk az egzisztenciálist az Ex_Elim szabállyal *)
  eapply HD_Ex_Elim.
  - apply HD_Var0.
    apply AWF_Cons.
    + apply WF_Ex. exact wf. (* A Ty_Ex jólformált, mert a magja (wf) az *)
    + apply AWF_Nil.         (* A lista vége *)
  - eapply HD_Conv.
    + (* 2. Epszilon bevezetése a b_snd projekcióra *)
      eapply HD_Eps_Intro.
      * apply BT_Snd.
      * eapply HD_Conv.
        { apply HD_Var0. 
          apply AWF_Cons.
          - exact wf. (* 1. A Phi formula jólformált *)
          - simpl. apply AWF_Cons.
            + (* 2. A (Ty_Ex A Phi)[fst] formula jólformáltsága *)
              apply WF_Ex. 
              eapply wf_subst.
              * (* A kiterjesztett fst projekció tipizálása *)
                eapply typing_subst_ext. apply BT_Fst.
              * (* Maga a belső formula (Phi) jólformált *)
                exact wf.
            + apply AWF_Nil. (* A lista vége *)
        }
        { (* BELSŐ KONVERZIÓ: Phi ≡ (Phi[ext fst])[id, snd] *)
          eapply FE_Trans.
          { eapply FE_Sym. eapply FE_Pullback_Id. exact wf. }
          eapply FE_Trans.
          { eapply FE_Pullback_Cong.
            - (* Bázis mágia: id ≡ ext fst o <id, snd> *)
              eapply BE_Trans.
              { eapply BE_Sym. apply BE_EtaPair. }
              eapply BE_Sym. eapply BE_Trans.
              { apply BE_CompPair. }
              eapply BE_CongPair.
              + eapply BE_Trans. { eapply BE_Sym. apply BE_Assoc. }
                eapply BE_CongComp. 
                * apply BE_BetaFst. 
                * apply BE_Refl.
              + eapply BE_Trans. { apply BE_BetaSnd. }
                eapply BE_Sym. apply BE_IdR.
            - exact wf.
          }
          { apply FE_Sym. eapply FE_Pullback_Comp.
            - eapply typing_subst_ext. eapply BT_Fst.
            - apply BT_Pair. apply BT_Id. apply BT_Snd.
            - exact wf.
          }
        }
    + (* KÜLSŐ KONVERZIÓ: (Phi[ext fst])[ε...] ≡ Phi[ε...][fst] 
         Zseniális: Ez hajszálpontosan a Beck-Chevalley axióma (FE_Eps_BC) a b_fst-re! *)
      eapply FE_Eps_BC.
      * apply BT_Fst.
      * exact wf.
      
  (* --- A POLC LESÖPRÉSE --- *)
  Unshelve.
  all: repeat match goal with
  | |- base_typing _ _ _ => eapply BT_Comp || eapply BT_Pair || apply BT_Id || eapply BT_Fst || eapply BT_Snd || apply typing_subst_ext || eassumption
  end.
Defined.

(* ================================================================= *)
(* WEAKENING (APPEND) LEMMÁK A ZÁRT TERMEKHEZ                        *)
(* ================================================================= *)

Lemma ctx_equiv_refl : forall {Sign : Type} `{SkolemMapping Sign} (I : b_ty) (D : @h_context Sign), 
  All_WellFormed I D -> ctx_equiv I D D.
Proof.
  induction 1; constructor; auto. apply FE_Refl; auto.
Defined.

Lemma All_WellFormed_app : forall {Sign : Type} `{SkolemMapping Sign} (I : b_ty) (G D : @h_context Sign),
  All_WellFormed I G -> All_WellFormed I D -> All_WellFormed I (G ++ D).
Proof.
  intros Sign SM I G D H1 H2. induction H1; simpl; auto.
  apply AWF_Cons; auto.
Defined.

Lemma ctx_equiv_app : forall {Sign : Type} `{SkolemMapping Sign} (I : b_ty) (G1 G2 D : @h_context Sign),
  ctx_equiv I G1 G2 -> All_WellFormed I D -> ctx_equiv I (G1 ++ D) (G2 ++ D).
Proof.
  intros Sign SM I G1 G2 D H Hwf. induction H; simpl.
  - apply ctx_equiv_refl; auto.
  - apply CEq_Cons; auto.
Defined.

Lemma All_WellFormed_subst : forall {Sign : Type} `{SkolemMapping Sign} (I J : b_ty) (f : @b_tm Sign) (D : @h_context Sign),
  base_typing I f J -> All_WellFormed J D -> All_WellFormed I (ctx_subst f D).
Proof.
  intros Sign SM I J f D dt H. induction H; simpl.
  - apply AWF_Nil.
  - apply AWF_Cons. eapply wf_subst; eauto. auto.
Defined.

(* A Varázslat: Ha a kontextus végére fűzünk, a bizonyítás-term VÁLTOZATLAN marad! *)
Lemma h_derivation_append : forall {Sign : Type} `{SkolemMapping Sign} (I : b_ty) (G D : @h_context Sign) (p : @h_tm Sign) (Phi : @h_ty Sign),
  h_derivation I G p Phi ->
  All_WellFormed I D ->
  h_derivation I (G ++ D) p Phi.
Proof.
  (* ITT A JAVÍTÁS: A sorrend G D p Phi *)
  intros Sign SM I G D p Phi H.
  revert D.
  induction H; intros D Hwf; simpl.
 - (* HD_Var0 *)
    apply HD_Var0. 
    (* Expliciten megadjuk a paramétereket, hogy átlépjünk a mintaillesztési hibán *)
    apply (All_WellFormed_app I (Phi :: G) D).
    + exact a.
    + exact Hwf.
  - apply HD_VarS; auto.
  - apply HD_Unit. apply All_WellFormed_app; auto.
  - eapply HD_Conv; eauto.
  - eapply HD_Ctx_Conv. apply ctx_equiv_app; eauto. eauto.
  - apply HD_Lam. apply IHh_derivation; auto.
  - eapply HD_App; eauto.
  - apply HD_Pair; auto.
  - eapply HD_Fst; eauto.
  - eapply HD_Snd; eauto.
  - apply HD_Inl; auto.
  - apply HD_Inr; auto.
  - eapply HD_Case; eauto.
  - apply HD_Absurd; auto.
  - (* HD_All_Intro *)
    apply HD_All_Intro. 
    unfold ctx_subst. rewrite map_app. fold (@ctx_subst Sign).
    apply IHh_derivation. eapply All_WellFormed_subst.
    + apply BT_Fst.
    + exact Hwf.
  - eapply HD_All_Elim; eauto.
  - eapply HD_Ex_Intro; eauto.
  - eapply HD_Ex_Elim. 
    + apply IHh_derivation1; auto.
    + unfold ctx_subst. rewrite map_app. fold (@ctx_subst Sign).
      apply IHh_derivation2. eapply All_WellFormed_subst.
      * apply BT_Fst.
      * exact Hwf.
  - eapply HD_Eps_Intro; eauto.
  - eapply HD_Eps_Elim.
    + apply IHh_derivation1; auto.
    + unfold ctx_subst. rewrite map_app. fold (@ctx_subst Sign).
      apply IHh_derivation2. eapply All_WellFormed_subst; auto. apply BT_Fst.
      exact Hwf.
Defined.

(* ================================================================= *)
(* BASE TYPING UNIQUENESS                                            *)
(* ================================================================= *)

Lemma base_typing_unique : forall {Sign : Type} A f B1
  (d1 : @base_typing Sign A f B1) B2
  (d2 : @base_typing Sign A f B2),
  B1 = B2.
Proof.
  intros Sign A f B1 d1.
  induction d1; intros B2 d2; dependent destruction d2.
  - reflexivity.
  - assert (H_B : B = B0).
    { eapply IHd1_2. exact d2_2. }
    subst B0.
    eapply IHd1_1. exact d2_1.
  - reflexivity.
  - assert (H_B : B = B0).
    { eapply IHd1_1. exact d2_1. }
    assert (H_C : C = C0).
    { eapply IHd1_2. exact d2_2. }
    subst. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

(* ================================================================= *)
(* FORMULA WF INVERSION FOR SUBSTITUTION                             *)
(* ================================================================= *)

Lemma form_wf_subst_inv : forall {Sign : Type} {SM : SkolemMapping Sign}
  {I J : b_ty} (f : @b_tm Sign) (df : base_typing I f J)
  (Phi : @h_ty Sign),
  WellFormed I (form_subst f Phi) ->
  WellFormed J Phi.
Proof.
  intros Sign SM I J f df Phi.
  generalize dependent J.
  generalize dependent I.
  generalize dependent f.

  induction Phi; intros f I J df Hwf; simpl in Hwf; inversion Hwf; subst.
  - apply WF_Unit.
  - apply WF_Void.
  - apply WF_Prod.
    + eapply IHPhi1; eassumption.
    + eapply IHPhi2; eassumption.
  - apply WF_Sum.
    + eapply IHPhi1; eassumption.
    + eapply IHPhi2; eassumption.
  - apply WF_Arrow.
    + eapply IHPhi1; eassumption.
    + eapply IHPhi2; eassumption.
  - (* Ty_Atom *)
    eapply WF_Atom.
    match goal with
    | Hcomp : base_typing I (b_comp ?u f) ?B |- base_typing J ?u _ =>
        inversion Hcomp; subst;
        match goal with
        | Hu : base_typing ?Mid u ?B',
          Hf : base_typing I f ?Mid |- _ =>
            assert (H_mid : Mid = J)
            by (eapply base_typing_unique; [exact Hf | exact df]);
            rewrite H_mid in Hu;
            exact Hu
        end
    end.
   - (* Ty_All *)
    apply WF_All.
    eapply IHPhi.
    + exact (@typing_subst_ext Sign I J b f df).
    + exact X.
  - (* Ty_Ex *)
    apply WF_Ex.
    eapply IHPhi.
    + exact (@typing_subst_ext Sign I J b f df).
    + exact X.
Defined.

Lemma form_wf_fst_inv : forall {Sign : Type} {SM : SkolemMapping Sign}
  {I A : b_ty} {Phi : @h_ty Sign},
  WellFormed (b_Prod I A) (form_subst b_fst Phi) ->
  WellFormed I Phi.
Proof.
  intros Sign SM I A Phi Hwf.
  eapply form_wf_subst_inv.
  - eapply BT_Fst.
  - exact Hwf.
Defined.

Lemma ctx_wf_fst_inv : forall {Sign : Type} {SM : SkolemMapping Sign}
  {I A : b_ty} {G : @h_context Sign},
  All_WellFormed (b_Prod I A) (ctx_subst b_fst G) ->
  All_WellFormed I G.
Proof.
  intros Sign SM I A G H.
  induction G as [|Phi G IH].
  - simpl in H. inversion H. apply AWF_Nil.
  - simpl in H.
    inversion H; subst.
    apply AWF_Cons.
    + eapply form_wf_fst_inv. exact X.
    + apply IH. exact X0.
Defined.

(* ================================================================= *)
(* THE THREE AXIOMS, NOW AS LEMMAS                                    *)
(* ================================================================= *)

Lemma form_equiv_wf1 : forall {Sign : Type} {SM : SkolemMapping Sign}
  (I : b_ty) (Phi Psi : @h_ty Sign),
  form_equiv I Phi Psi ->
  WellFormed I Phi.
Proof.
  intros Sign SM I Phi Psi H.
  exact (fst (form_equiv_wf I Phi Psi H)).
Defined.

Lemma form_equiv_wf2 : forall {Sign : Type} {SM : SkolemMapping Sign}
  (I : b_ty) (Phi Psi : @h_ty Sign),
  form_equiv I Phi Psi ->
  WellFormed I Psi.
Proof.
  intros Sign SM I Phi Psi H.
  exact (snd (form_equiv_wf I Phi Psi H)).
Defined.

(* Kontextus regularitás: ha van deriváció, akkor a kontextus jólformált. *)
Lemma meta_ctx_wf : forall {Sign : Type} {SM : SkolemMapping Sign}
  {I : b_ty} {G : @h_context Sign} {p : @h_tm Sign} {Phi : @h_ty Sign},
  h_derivation I G p Phi ->
  All_WellFormed I G.
Proof.
  intros Sign SM I G p Phi Hderiv.
  induction Hderiv.
  - exact a.
  - apply AWF_Cons; assumption.
  - exact a.
  - exact IHHderiv.
  - eapply ctx_equiv_wf_right.
    + exact c.
    + exact IHHderiv.
  - inversion IHHderiv; subst. assumption.
  - exact IHHderiv1.
  - exact IHHderiv1.
  - exact IHHderiv.
  - exact IHHderiv.
  - exact IHHderiv.
  - exact IHHderiv.
  - exact IHHderiv1.
  - exact IHHderiv.
  - apply ctx_wf_fst_inv in IHHderiv.
    exact IHHderiv.
  - exact IHHderiv.
  - exact IHHderiv.
  - exact IHHderiv1.
  - exact IHHderiv.
  - exact IHHderiv1.
Defined.

(* Típus regularitás: ha van deriváció, akkor a célformula jólformált. *)
Lemma meta_type_wf : forall {Sign : Type} {SM : SkolemMapping Sign}
  {I : b_ty} {G : @h_context Sign} {p : @h_tm Sign} {Phi : @h_ty Sign},
  h_derivation I G p Phi ->
  WellFormed I Phi.
Proof.
  intros Sign SM I G p Phi Hderiv.
  induction Hderiv.
  - inversion a; subst. assumption.
  - assumption.
  - apply WF_Unit.
  - eapply form_equiv_wf2. exact f.
  - assumption.
  - apply WF_Arrow.
    + apply meta_ctx_wf in Hderiv.
      inversion Hderiv; subst. assumption.
    + assumption.
  - inversion IHHderiv1; subst. assumption.
  - apply WF_Prod; assumption.
  - inversion IHHderiv; subst. assumption.
  - inversion IHHderiv; subst. assumption.
  - apply WF_Sum; assumption.
  - apply WF_Sum; assumption.
  - assumption.
  - exact w.
  - apply WF_All. exact IHHderiv.
  - eapply wf_subst.
    + eapply BT_Pair.
      * apply BT_Id.
      * exact b.
    + inversion IHHderiv; subst. assumption.
  - apply WF_Ex.
    eapply form_wf_subst_inv.
    + eapply BT_Pair.
      * apply BT_Id.
      * exact b.
    + exact IHHderiv.
  - apply form_wf_fst_inv in IHHderiv2.
    exact IHHderiv2.
  - eapply wf_subst.
    + eapply BT_Pair.
      * apply BT_Id.
      * apply BT_Const.
    + eapply form_wf_subst_inv.
      * eapply BT_Pair.
        -- apply BT_Id.
        -- exact b.
      * exact IHHderiv.
  - apply form_wf_fst_inv in IHHderiv2.
    exact IHHderiv2.
Defined.

Lemma h_derivation_wf_inv : forall {Sign : Type} {SM : SkolemMapping Sign}
  {I A : b_ty} {G : @h_context Sign} {p : @h_tm Sign}
  {Phi : @h_ty Sign} {t : @b_tm Sign},
  base_typing I t A ->
  h_derivation I G p (form_subst (b_pair b_id t) Phi) ->
  WellFormed (b_Prod I A) Phi.
Proof.
  intros Sign SM I A G p Phi t dt Hderiv.

  apply meta_type_wf in Hderiv.

  eapply form_wf_subst_inv.
  - eapply BT_Pair.
    + apply BT_Id.
    + exact dt.
  - exact Hderiv.
Defined.

 