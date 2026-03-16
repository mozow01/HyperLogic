Require Import HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.

Require Import List.
Import ListNotations.


Declare Scope surface_scope.

(* --- TERMEK ÉS BÁZIS MORFIZMUSOK --- *)
(* A 'var0' a legfelső lokális változó, ami kategóriaelméletileg a második projekció *)
Notation "'var0'" := (b_snd) : surface_scope.

(* Az Epszilon term egy globális Skolem konstans a háttérben *)
Notation "'ε' D , Phi" := (b_const D (skolem_index D Phi)) (at level 50) : surface_scope.


(* --- LOGIKAI OPERÁTOROK --- *)
Notation "A ⇒ B" := (Ty_Arrow A B) (at level 60, right associativity) : surface_scope.
Notation "'∃' D , Phi" := (Ty_Ex D Phi) (at level 50) : surface_scope.
Notation "'∀' D , Phi" := (Ty_All D Phi) (at level 50) : surface_scope.


(* --- STRUKTURÁLIS MŰVELETEK (A LÉNYEG) --- *)

(* GYENGÍTÉS (Lifting / Weakening): 
   Felemeli a formulát az 'I' fibrumból az 'I * D' fibrumba, hogy 
   egy új, lokális változó mellett is használható legyen. 
   Kategóriaelméletben ez egy visszahúzás az első projekció (b_fst) mentén. *)
Notation "⇑ Phi" := (form_pullback b_fst Phi) (at level 40) : surface_scope.

Open Scope surface_scope.

Definition Dual_Drinker {Sign : Type} `{SkolemMapping Sign} (I D : b_ty) (Phi : @h_ty Sign) : @h_ty Sign :=
  ∃ D , ( (⇑ (∃ D , Phi)) ⇒ Phi ).

(* --- TÍPUSOLÁSI AXIÓMÁK A QED-HEZ --- *)
Lemma BT_Comp_Pair_Id_Fst_Correct {Sign : Type} {I D : b_ty} {t : @b_tm Sign} 
  (Ht : @base_typing Sign I t D) :
  @base_typing Sign I (b_comp b_fst (b_pair b_id t)) I.
Proof.
  eapply BT_Comp.
  - eapply BT_Fst.
  - eapply BT_Pair.
    + apply BT_Id.
    + apply Ht.
Defined.
  
(* Bázis Axióma: A párosítás és a balra-projekció kompozíciója kioltja egymást. *)
Lemma BE_Comp_Pair_Id_Fst_Correct {Sign : Type} {I D : b_ty} {t : @b_tm Sign} 
  (Ht : @base_typing Sign I t D) :
  @base_equiv Sign I I (b_comp b_fst (b_pair b_id t)) b_id 
    (BT_Comp BT_Fst (BT_Pair BT_Id Ht)) BT_Id.
Proof.
  apply BE_BetaFst.
Defined.

Lemma dual_drinker_surface_provable {Sign : Type} `{SkolemMapping Sign} 
  (I D : b_ty) (Phi : @h_ty Sign) (wf_Phi : WellFormed (b_Prod I D) Phi) : 
  exists p, h_typing I [] p (Dual_Drinker I D Phi).
Proof.
  eexists. unfold Dual_Drinker.
  eapply HT_Ex_Intro with (f := ε D, Phi).
  - apply BT_Const.
  - (* 1. LÉPÉS: Lambda (Beteszi a kontextusba a ⇑(∃ D, Phi)-t) *)
    eapply HT_Lam.

    (* 2. LÉPÉS: Egzisztenciális Elimináció *)
    (* Kicsomagoljuk az egzisztenciálist, hogy megkapjuk a var0 tanút *)
    eapply HT_Ex_Elim.
    + (* A premissza letisztítása *)
      eapply HT_Conv.
      * apply HT_Var0.
      * eapply FE_Trans. 
        1: { (* KOMPOZÍCIÓ: Szükség van a gépelésre és a WFF-re! *)
             eapply FE_Pullback_Comp.
             - apply (@BT_Fst _ I D). (* <--- ITT A JAVÍTÁS *)
             - eapply BT_Pair. { apply BT_Id. } { apply BT_Const. }
             - apply WF_Ex. exact wf_Phi. 
           }
        eapply FE_Trans. 
        2: { (* IDENTITÁS: Csak a WFF kell! *)
             apply FE_Pullback_Id. 
             apply WF_Ex. exact wf_Phi. 
           }
        (* KONGRUENCIA: Kell a bázis-egyenlőség és a WFF! *)
        eapply FE_Pullback_Cong. 
        -- apply (BE_Comp_Pair_Id_Fst_Correct BT_Const).
        -- apply WF_Ex. exact wf_Phi.

  + (* 3. LÉPÉS: A lokális kontextus feldolgozása az Epszilon bevezetéssel *)
      eapply HT_Conv.
      * (* Itt adjuk át a var0 tanút! A 'Phi' paramétert használjuk 'Psi' helyett! *)
        eapply HT_Eps_Intro with (f := var0) (Phi := form_pullback (b_pullback_ext b_fst) Phi).
        -- apply (@BT_Snd _ I D).
        -- eapply HT_Conv.
           ++ apply HT_Var0.
           ++ eapply FE_Sym.
              eapply FE_Trans. 
              1: { (* KOMPOZÍCIÓ: b_pullback_ext b_fst és a pár *)
                   eapply FE_Pullback_Comp.
                   - unfold b_pullback_ext. eapply BT_Pair.
                     + eapply BT_Comp. apply (@BT_Fst _ I D). apply (@BT_Fst _ (b_Prod I D) D).
                     + apply (@BT_Snd _ (b_Prod I D) D).
                   - eapply BT_Pair. { apply BT_Id. } { apply (@BT_Snd _ I D). }
                   - exact wf_Phi. 
                 }
              eapply FE_Trans.
              2: { (* IDENTITÁS *)
                   apply FE_Pullback_Id. exact wf_Phi. 
                 }
              (* KONGRUENCIA: <f o p1, p2> o <id, p2> == id *)
              eapply FE_Pullback_Cong.
              unfold b_pullback_ext.
                 eapply BE_Trans. { eapply BE_CompPair. }
                 eapply BE_Trans. 
                 { (* Letisztítjuk a komponenseket *)
                   eapply BE_CongPair.
                   - eapply BE_Trans. { eapply BE_Sym. apply BE_Assoc. }
                     eapply BE_Trans. { eapply BE_CongComp. apply BE_BetaFst. apply BE_Refl. }
                     apply BE_IdR.
                   - apply BE_BetaSnd.
                 }
                 eapply BE_Trans.
                 { (* Híd a b_pair b_fst b_snd és az EtaPair között *)
                   eapply BE_CongPair.
                   - eapply BE_Sym. apply BE_IdR.
                   - eapply BE_Sym. apply BE_IdR.
                 }
                 apply BE_EtaPair. 
                 exact wf_Phi.

      * (* 4. LÉPÉS: Beck-Chevalley invariancia *)
        eapply FE_Eps_Lift with (J := I).
        -- apply (@BT_Fst _ I D).
        -- exact wf_Phi.

(* --- A POLC FELTAKARÍTÁSA --- *)
Unshelve.
  all: try exact (b_Prod I D); auto.
Defined.