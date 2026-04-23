(* theories/Logic/Hyper/Epsilon_Adjoint/Hyper_Syntax_Lemmas.v *)

Require Import List.
Import ListNotations.
Require Import HyperLogic.Logic.Base.Epsilon_Adjoint.Base_Syntax.
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum.
Require Import HyperLogic.Logic.Hyper.Epsilon_Adjoint.Hyper_Syntax.

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

Lemma form_equiv_subst : forall {Sign : Type} `{SkolemMapping Sign}
  {I J : b_ty} (t : @b_tm Sign) (dt : base_typing I t J) (Phi Psi : @h_ty Sign),
  form_equiv J Phi Psi ->
  form_equiv I (form_subst t Phi) (form_subst t Psi).
Proof.
  intros Sign SM I J t dt Phi Psi H.
  revert I t dt.
  induction H; intros I0 t0 dt.
  - (* FE_Atom *)
    simpl. eapply FE_Atom.
    apply BE_CongComp.
    + apply BE_Refl. (* A helyettesítés (t0) önmagával ekvivalens *)
    + exact b.       (* Az atomok bázis-termjei (t1, t2) ekvivalensek *)
  - (* FE_Refl *)
    apply FE_Refl.
    eapply wf_subst.
    + exact dt.
    + exact w.
  - (* FE_Sym *)
    apply FE_Sym.
    apply IHform_equiv. exact dt.
  - (* FE_Trans *)
    eapply FE_Trans.
    + apply IHform_equiv1. exact dt.
    + apply IHform_equiv2. exact dt.
  - (* FE_Prod *)
    simpl. apply FE_Prod.
    + apply IHform_equiv1. exact dt.
    + apply IHform_equiv2. exact dt.
  - (* FE_Sum *)
    simpl. apply FE_Sum. 
    + apply IHform_equiv1. exact dt.
    + apply IHform_equiv2. exact dt.
  - (* FE_Arrow *)
    simpl. apply FE_Arrow.
    + apply IHform_equiv1. exact dt.
    + apply IHform_equiv2. exact dt.
  - (* FE_All *)
    simpl. apply FE_All.
    (* Itt használjuk fel az imént bizonyított lemmát! *)
    apply IHform_equiv. apply typing_subst_ext. exact dt.
  - (* FE_Ex *)
    simpl. apply FE_Ex.
    apply IHform_equiv. apply typing_subst_ext. exact dt.
  - (* FE_Eps_Adjoint_Iso *)
    admit. (* HIÁNYZÓ AXIÓMA: Szintaktikus Beck-Chevalley a Skolem konstansokra *)
  - (* FE_Eps_Functorial *)
    admit.
  - (* FE_Pullback_Id *)
    admit.
  - (* FE_Pullback_Comp *)
    admit.
  - (* FE_Pullback_Cong *)
    admit.
Admitted.

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
    - (* ---> ITT JÖN A BÁZIS SZINTAXIS <--- *)
      (* Ide kell beírnod azt a base_equiv konstruktort, ami kimondja, 
         hogy 'b_comp b_fst (b_pair f g) == f'.
         Mivel az f itt b_id, ez adja meg a b_id <-> b_comp b_fst ... kapcsolatot.
         Ha a base_equiv-et regisztráltad a Setoid rewrite-hoz, lehet, 
         hogy a Coq be tudja bizonyítani magától, vagy egy explicit 
         BE_Fst_Pair (vagy aminek elnevezted) konstruktor kell ide. *)
      admit. 
    - exact wf. 
  }
  
 (* Lépés 3: Phi[fst o <id, snd>] <==> (Phi[fst])[<id, snd>] 
     (A subst funktor kompozíciója megőrzi az izomorfizmust) *)
  { apply FE_Sym. 
    eapply FE_Pullback_Comp.
    - (* df: b_fst tipizálása, ami a b_Prod (b_Prod I A) A -ból vetíti vissza a b_Prod I A -t *)
      apply (@BT_Fst Sign (b_Prod I A) A).
    - (* dg: b_pair b_id b_snd tipizálása, ami b_Prod I A -ból megy b_Prod (b_Prod I A) A -ba *)
      apply BT_Pair.
      + apply (@BT_Id Sign (b_Prod I A)).
      + apply (@BT_Snd Sign I A).
    - (* a WellFormed Phi bizonyítás átadása *)
      exact wf. 
  }
Admitted. (* A Qed-hez már csak a bázis egyenlőség admit-ját kell feloldani *)


Lemma eps_implies_ex : forall {Sign : Type} `{SkolemMapping Sign} (I A : b_ty) (Phi : @h_ty Sign),
  h_derivation I [ Phi .[ ε A, Phi ] ]
    (tm_ex_intro (b_const A (skolem_index A Phi)) (tm_var 0))
    (Ty_Ex A Phi).
Proof.
  intros Sign SM I A Phi.
  (* Alkalmazzuk az Egzisztenciális Bevezetést az Epsilon konstanssal. *)
  eapply HD_Ex_Intro.
  - (* A bázis tipizálás bizonyítása: az epszilon konstans A típusú. *)
    apply BT_Const.
  - (* A premissza pontosan megegyezik a lokális kontextussal (0. indexű változó). *)
    apply HD_Var0.
Qed.
  
Lemma ex_implies_eps : forall {Sign : Type} `{SkolemMapping Sign} (I A : b_ty) (Phi : @h_ty Sign),
  h_derivation I [ Ty_Ex A Phi ]
    (tm_ex_elim (tm_var 0) (tm_eps_intro b_snd (tm_var 0)))
    (Phi .[ ε A, Phi ]).
Proof.
  intros Sign SM I A Phi.
  
  (* 1. Felnyitjuk az egzisztenciálist az Ex_Elim szabállyal *)
  eapply HD_Ex_Elim.
  - (* Az egzisztenciális formula a kontextusunk legtetején van (Var0) *)
    apply HD_Var0.
  - (* Most a bázis kontextusunk 'b_Prod I A', és van egy 'Phi' a kontextusunkban.
       A célunk a 'Phi .[ ε A, Phi ]' bizonyítása, de substelve 'b_fst'-tel.
       Mivel a típusok kategóriaelméletileg egyeznek, de szintaktikusan eltérnek, 
       konverziót alkalmazunk. *)
    eapply HD_Conv.
    
    + (* 2. Alkalmazzuk az Epszilon Bevezetést a 'b_snd' projekcióra! *)
      eapply HD_Eps_Intro.
      * (* A bázis bizonyítás: b_snd pontosan 'A' típusú a 'b_Prod I A' kontextusban *)
        apply BT_Snd.
      * (* Be kell bizonyítanunk, hogy 'Phi' igaz a 'b_snd' helyettesítéssel. *)
        eapply HD_Conv.
        { (* Maga a formula ott van a kontextus tetején! *)
          apply HD_Var0. }
        { (* STRUKTURÁLIS LEMMA 1: 
             A Phi formula izomorf a Phi[id, b_snd]-vel a b_Prod I A felett. 
             (Ezt a FE_Pullback_Comp és FE_Pullback_Id lemmákkal lehetne levezetni) *)
          admit. }
          
    + (* STRUKTURÁLIS LEMMA 2:
         Az Epszilon bevezetés eredménye izomorf a célformulánk 'b_fst' substjével.
         Tehát: (Phi[eps])[b_fst] == Phi[b_snd][eps_b_snd] *)
      admit.
Admitted.
