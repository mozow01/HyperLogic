(*Logic/Hyper/Simple/Hyper_Lemmas_Conv.v*)

Require Import List Arith PeanoNat Lia.
Import ListNotations.

Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax_Conv.

(* ================================================================= *)
(* 1. SZINTAKTIKUS MŰVELETEK (LOGIKAI VÁLTOZÓK)                      *)
(* ================================================================= *)

(**
 * Operation: h_lift
 * Description: De Bruijn indexek eltolása a logikai változókhoz.
 * Figyelem: A bázis kifejezéseket (b_tm) NEM érinti, ami a Dual Context 
 * egyik legnagyobb előnye!
 *)
Fixpoint h_lift (n : nat) (k : nat) (t : h_tm) : h_tm :=
  match t with
  (* Propozicionális STLC esetek *)
  | tm_unit => tm_unit
  | tm_var i =>
      if k <=? i then tm_var (n + i) else tm_var i
  | tm_lam Phi t' => tm_lam Phi (h_lift n (S k) t')
  | tm_app t1 t2 => tm_app (h_lift n k t1) (h_lift n k t2)
  | tm_pair t1 t2 => tm_pair (h_lift n k t1) (h_lift n k t2)
  | tm_fst t' => tm_fst (h_lift n k t')
  | tm_snd t' => tm_snd (h_lift n k t')
  | tm_inl B t' => tm_inl B (h_lift n k t')
  | tm_inr A t' => tm_inr A (h_lift n k t')
  | tm_case t t1 t2 => tm_case (h_lift n k t) (h_lift n (S k) t1) (h_lift n (S k) t2)
  | tm_absurd A t' => tm_absurd A (h_lift n k t')
  
  (* --- ÚJ ESETEK: Hyper Kvantorok --- *)
  
  (* A forall_intro önmagában nem köt le új LOGIKAI változót, 
     csak a bázis kontextus nő meg! Így a 'k' nem nő! *)
  | tm_all_intro p => tm_all_intro (h_lift n k p)
  | tm_all_elim p f => tm_all_elim (h_lift n k p) f
  
  | tm_ex_intro f p => tm_ex_intro f (h_lift n k p)
  (* Az ex_elim viszont a 'p2'-ben egy új logikai változót köt 
     (a tanú típusát), így ott a 'k' megnő! *)
  | tm_ex_elim p p2 => tm_ex_elim (h_lift n k p) (h_lift n (S k) p2)
  end.

(**
 * Operation: h_insert_at
 * Description: Beszúr egy logikai formulát (Psi) a kontextusba.
 *)
Fixpoint h_insert_at (n : nat) (Psi : h_ty) (G : h_context) : h_context :=
  match n, G with
  | 0, _       => Psi :: G
  | S n', h :: t => h :: h_insert_at n' Psi t
  | S n', []   => []
  end.

(* ================================================================= *)
(* 2. A LIFTING TULAJDONSÁGAI                                        *)
(* ================================================================= *)

Lemma h_lift_0 : forall t k, h_lift 0 k t = t.
Proof.
  induction t; intros k; simpl; auto.
  - destruct (k <=? n); auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2, IHt3; auto.
  - rewrite IHt; auto.
  (* Kvantorok *)
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
Defined.

Lemma h_lift_add : forall t n m k, h_lift n k (h_lift m k t) = h_lift (n + m) k t.
Proof.
  induction t; intros n0 m0 k0; simpl; auto.
  - destruct (k0 <=? n) eqn:Hk.
    + simpl.
      assert (Hk_inner : k0 <=? m0 + n = true).
      { apply Nat.leb_le in Hk. apply Nat.leb_le. lia. }
      rewrite Hk_inner. f_equal. lia.
    + simpl. rewrite Hk. auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2, IHt3; auto.
  - rewrite IHt; auto.
  (* Kvantorok *)
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
Defined.

(* ================================================================= *)
(* 2.2 WELL-FORMED CONTEXTS                                          *)
(* ================================================================= *)


Lemma wf_ctx_pullback : forall I J f Delta,
  base_typing I f J -> wf_ctx J Delta -> wf_ctx I (ctx_pullback f Delta).
Proof.
  intros I J f Delta Hf Hwf.
  induction Hwf; simpl.
  - apply WFC_nil.
  - apply WFC_cons.
    + eapply wf_pullback. exact Hf. exact w.
    + exact IHHwf.
Qed.

(* ================================================================= *)
(* META-THEOREMS: EXTRACTING WELL-FORMEDNESS FROM DERIVATIONS        *)
(* ================================================================= *)

(* Meta-Theorem: Formula equivalence guarantees both sides are well-formed *)
Lemma form_equiv_wf : forall I Phi Psi,
  form_equiv I Phi Psi -> WellFormed I Phi * WellFormed I Psi.
Proof.
  intros I Phi Psi f. induction f.
  - (* FEQ_Atom: Explicitly provide the base_typing derivations! *)
    split. 
    + eapply WF_Atom. exact d1.
    + eapply WF_Atom. exact d2.
  - split; assumption.
  - destruct IHf; split; assumption.
  - destruct IHf1; destruct IHf2; split; assumption.
  - destruct IHf1; destruct IHf2; split; apply WF_Prod; assumption.
  - destruct IHf1; destruct IHf2; split; apply WF_Sum; assumption.
  - destruct IHf1; destruct IHf2; split; apply WF_Arrow; assumption.
  - destruct IHf; split; apply WF_All; assumption.
  - destruct IHf; split; apply WF_Ex; assumption.
  - split. 
    + eapply wf_pullback. apply BT_Id. exact w.
    + exact w.
  - split.
    + eapply wf_pullback. exact dg. eapply wf_pullback. exact df. exact w.
    + eapply wf_pullback. eapply BT_Comp; eassumption. exact w.
  - split.
    + eapply wf_pullback. exact df. exact w.
    + eapply wf_pullback. exact dg. exact w.
Qed.

(* Meta-Theorem: A valid derivation implies a well-formed context *)
Lemma well_formed_ctx : forall I G p Phi,
  h_derivation I G p Phi -> wf_ctx I G.
Proof.
  intros I G p Phi d.
  induction d.
  - (* 1. HD_Var0 *) apply WFC_cons; assumption.
  - (* 2. HD_VarS *) apply WFC_cons; assumption.
  - (* 3. HD_Unit *) assumption.
  - (* 4. HD_Lam  *) inversion IHd; subst; assumption.
  - (* 5. HD_App  *) assumption.
  - (* 6. HD_Pair *) assumption.
  - (* 7. HD_Fst  *) assumption.
  - (* 8. HD_Snd  *) assumption.
  - (* 9. HD_Inl  *) assumption.
  - (* 10. HD_Inr *) assumption.
  - (* 11. HD_Case*) assumption.
  - (* 12. HD_Absurd *) assumption.
  - (* 13. HD_All_Intro *) assumption. 
  - (* 14. HD_All_Elim *) assumption.
  - (* 15. HD_Ex_Intro *) assumption.
  - (* 16. HD_Ex_Elim *) assumption.
  - (* 17. HD_Conv *) clear d IHd f. induction c; [apply WFC_nil | apply WFC_cons; eauto].
                      apply form_equiv_wf in f. destruct f as [_ Hwf_Psi]. exact Hwf_Psi.
Defined.

(* Meta-Theorem: A valid derivation implies a well-formed target type *)
Lemma well_formed_target : forall I G p Phi,
  h_derivation I G p Phi -> WellFormed I Phi.
Proof.
  intros I G p Phi d.
  induction d.
  - (* 1. HD_Var0 *) assumption.
  - (* 2. HD_VarS *) assumption.
  - (* 3. HD_Unit *) apply WF_Unit.
  - (* 4. HD_Lam  *) 
    apply WF_Arrow. 
    + assert (Hctx : wf_ctx I (Phi :: G)) by eauto using well_formed_ctx.
      inversion Hctx; subst; assumption.
    + assumption.
  - (* 5. HD_App  *) inversion IHd1; subst; assumption.
  - (* 6. HD_Pair *) apply WF_Prod; assumption.
  - (* 7. HD_Fst  *) inversion IHd; subst; assumption.
  - (* 8. HD_Snd  *) inversion IHd; subst; assumption.
  - (* 9. HD_Inl  *) apply WF_Sum; eauto.
  - (* 10. HD_Inr *) apply WF_Sum; eauto. 
  - (* 11. HD_Case*) exact IHd2.
  - (* 12. HD_Absurd *) assumption. 
  - (* 13. HD_All_Intro *) apply WF_All; assumption.
  - (* 14. HD_All_Elim *) 
    inversion IHd; subst. eapply wf_pullback.
    + eapply BT_Pair; [apply BT_Id | exact b].
    + assumption.
  - (* 15. HD_Ex_Intro *) apply WF_Ex; assumption. 
  - (* 16. HD_Ex_Elim *) assumption. 
  - (* 17. HD_Conv *) 
    apply form_equiv_wf in f. destruct f as [_ Hwf_Psi]. exact Hwf_Psi.
Defined.

(* Meta-Theorem: Universal quantifier body is well-formed *)
Lemma well_formed_all_body : forall I G p A Phi,
  h_derivation I G p (Ty_All A Phi) -> WellFormed (b_Prod I A) Phi.
Proof.
  intros I G p A Phi d.
  apply well_formed_target in d.
  inversion d; subst; assumption.
Defined.

(* Meta-Theorem: Existential quantifier body is well-formed *)
Lemma well_formed_ex_body : forall I G p A Phi,
  h_derivation I G p (Ty_Ex A Phi) -> WellFormed (b_Prod I A) Phi.
Proof.
  intros I G p A Phi d.
  apply well_formed_target in d.
  inversion d; subst; assumption.
Defined.


(* ================================================================= *)
(* 2.5 EQUIVALENCE PROOFS (100% Verified, No Axioms!)                *)
(* ================================================================= *)

Lemma form_equiv_refl : forall I Phi, WellFormed I Phi -> form_equiv I Phi Phi.
Proof.
  intros I Phi H. apply FEQ_Refl. exact H.
Qed.

Lemma ctx_equiv_refl : forall I G, wf_ctx I G -> ctx_equiv I G G.
Proof.
  intros I G H. induction H.
  - apply CEQ_nil.
  - apply CEQ_cons. 
    + apply FEQ_Refl. exact w. 
    + exact IHwf_ctx.
Qed.

Lemma ctx_equiv_sym : forall I G Delta,
  ctx_equiv I G Delta -> ctx_equiv I Delta G.
Proof.
  intros I G Delta H. induction H.
  - apply CEQ_nil.
  - apply CEQ_cons.
    + apply FEQ_Sym. exact f.
    + exact IHctx_equiv.
Qed.

Lemma ctx_equiv_insert : forall I n Psi G1 G2,
  WellFormed I Psi ->
  ctx_equiv I G1 G2 -> 
  ctx_equiv I (h_insert_at n Psi G1) (h_insert_at n Psi G2).
Proof.
  intros I n Psi G1 G2 Hwf H.
  generalize dependent n.
  induction H; intros n; destruct n; simpl.
  - apply CEQ_cons. apply FEQ_Refl. exact Hwf. apply CEQ_nil.
  - apply CEQ_nil.
  - apply CEQ_cons. apply FEQ_Refl. exact Hwf. apply CEQ_cons; assumption.
  - apply CEQ_cons. assumption. apply IHctx_equiv.
Qed.

Lemma ctx_equiv_app : forall I G1 G2 Delta,
  ctx_equiv I G1 G2 -> 
  wf_ctx I Delta ->
  ctx_equiv I (G1 ++ Delta) (G2 ++ Delta).
Proof.
  intros I G1 G2 Delta H Hwf.
  induction H; simpl.
  - apply ctx_equiv_refl. exact Hwf.
  - apply CEQ_cons; assumption.
Qed.

(* ================================================================= *)
(* 3. WEAKENING TÉTELEK                                              *)
(* ================================================================= *)

Lemma wf_ctx_insert : forall I n Psi G,
  WellFormed I Psi -> wf_ctx I G -> wf_ctx I (h_insert_at n Psi G).
Proof.
  intros I n Psi G Hwf HG. generalize dependent n.
  induction HG; intros n; destruct n; simpl.
  - apply WFC_cons; [assumption | apply WFC_nil].
  - apply WFC_nil.
  - apply WFC_cons; [assumption | apply WFC_cons; assumption].
  - apply WFC_cons; [assumption | apply IHHG].
Qed.

Lemma wf_ctx_app : forall I G Delta,
  wf_ctx I G -> wf_ctx I Delta -> wf_ctx I (G ++ Delta).
Proof.
  intros I G Delta HG HDelta.
  induction HG; simpl; auto.
  - apply WFC_cons; auto.
Qed.

Lemma ctx_pullback_insert : forall f n Psi G,
  ctx_pullback f (h_insert_at n Psi G) = h_insert_at n (form_pullback f Psi) (ctx_pullback f G).
Proof.
  intros f n Psi G. revert n. induction G; intros n; destruct n; simpl; auto.
  rewrite IHG. reflexivity.
Qed.

Theorem h_weakening_general : forall I G p Phi Psi n,
  WellFormed I Psi ->
  h_typing I G p Phi ->
  h_typing I (h_insert_at n Psi G) (h_lift 1 n p) Phi.
Proof.
  intros I G p Phi Psi n Hwf H.
  revert n Psi Hwf.
  induction H; intros n0 Psi0 Hwf0; simpl.
  - (* 1. HT_Var0 *)
    destruct n0; simpl.
    + apply HT_VarS; [assumption | apply HT_Var0; assumption].
    + apply HT_Var0; [apply wf_ctx_insert; assumption | assumption].
  - (* 2. HT_VarS *)
    destruct n0; simpl.
    + apply HT_VarS; [assumption | apply HT_VarS; assumption].
    + specialize (IHh_typing n0 Psi0 Hwf0).
      destruct (n0 <=? i) eqn:Heq.
      * apply HT_VarS; [assumption | idtac].
        replace (tm_var (S i)) with (h_lift 1 n0 (tm_var i)) by (simpl; rewrite Heq; reflexivity).
        exact IHh_typing.
      * apply HT_VarS; [assumption | idtac].
        replace (tm_var i) with (h_lift 1 n0 (tm_var i)) by (simpl; rewrite Heq; reflexivity).
        exact IHh_typing.
  - (* 3. HT_Unit *) 
    apply HT_Unit. apply wf_ctx_insert; assumption.
  - (* 4. HT_Lam *) 
    apply HT_Lam. apply (IHh_typing (S n0) Psi0 Hwf0).
  - (* 5. HT_App *) 
    eapply HT_App. apply (IHh_typing1 n0 Psi0 Hwf0). apply (IHh_typing2 n0 Psi0 Hwf0).
  - (* 6. HT_Pair *) 
    apply HT_Pair. apply (IHh_typing1 n0 Psi0 Hwf0). apply (IHh_typing2 n0 Psi0 Hwf0).
  - (* 7. HT_Fst *) 
    eapply HT_Fst. apply (IHh_typing n0 Psi0 Hwf0).
  - (* 8. HT_Snd *) 
    eapply HT_Snd. apply (IHh_typing n0 Psi0 Hwf0).
  - (* 9. HT_Inl *) 
    apply HT_Inl; [assumption | apply (IHh_typing n0 Psi0 Hwf0)].
  - (* 10. HT_Inr *) 
    apply HT_Inr; [assumption | apply (IHh_typing n0 Psi0 Hwf0)].
  - (* 11. HT_Case *) 
    eapply HT_Case.
    + apply (IHh_typing1 n0 Psi0 Hwf0).
    + apply (IHh_typing2 (S n0) Psi0 Hwf0).
    + apply (IHh_typing3 (S n0) Psi0 Hwf0).
  - (* 12. HT_Absurd *) 
    apply HT_Absurd; [assumption | apply (IHh_typing n0 Psi0 Hwf0)].
  - (* 13. HT_All_Intro *)
    apply HT_All_Intro; [apply wf_ctx_insert; assumption | idtac].
    rewrite ctx_pullback_insert. apply (IHh_typing n0 (form_pullback b_fst Psi0)).
    eapply wf_pullback; [apply BT_Fst | assumption].
  - (* 14. HT_All_Elim *) 
    eapply HT_All_Elim; [apply (IHh_typing n0 Psi0 Hwf0) | assumption].
  - (* 15. HT_Ex_Intro *) 
    eapply HT_Ex_Intro; [assumption | assumption | apply (IHh_typing n0 Psi0 Hwf0)].
  - (* 16. HT_Ex_Elim *) 
    eapply HT_Ex_Elim; [assumption | apply (IHh_typing1 n0 Psi0 Hwf0) | idtac].
    rewrite ctx_pullback_insert. apply (IHh_typing2 (S n0) (form_pullback b_fst Psi0)).
    eapply wf_pullback; [apply BT_Fst | assumption].
  - (* 17. HT_Conv *)
    eapply HT_Conv.
    + apply ctx_equiv_insert; [assumption | eassumption].
    + eassumption.
    + apply (IHh_typing n0 Psi0 Hwf0).
Defined.


Lemma h_weakening : forall I G p Phi Psi,
  WellFormed I Psi ->
  h_typing I G p Phi ->
  h_typing I (Psi :: G) (h_lift 1 0 p) Phi.
Proof.
  intros I G p Phi Psi Hwf H.
  change (Psi :: G) with (h_insert_at 0 Psi G).
  eapply h_weakening_general. exact Hwf. assumption.
Defined.

Lemma h_weakening_from_nil : forall I G p Phi,
  wf_ctx I G ->
  h_typing I nil p Phi ->
  h_typing I G (h_lift (length G) 0 p) Phi.
Proof.
  intros I G. induction G; intros p0 Phi0 Hwf H.
  - simpl. rewrite h_lift_0. exact H.
  - simpl. inversion Hwf; subst.
    apply IHG in H; auto.
    eapply h_weakening with (Psi:=a) in H; auto.
    rewrite h_lift_add in H.
    replace (1 + length G) with (S (length G)) in H by lia.
    exact H.
Defined.

Lemma h_weakening_append : forall I G Delta p Phi,
  wf_ctx I Delta ->
  h_typing I G p Phi -> h_typing I (G ++ Delta) p Phi.
Proof.
  assert (H_cons_app : forall (T : Type) (l : list T) (a : T), a :: l = [a] ++ l) by (simpl; auto).
  intros I G Delta p Phi Hwf H.
  revert Delta Hwf.
  induction H; intros Delta Hwf;
  try (rewrite H_cons_app; try rewrite <- app_assoc; try rewrite <- H_cons_app).
  - (* 1. HT_Var0 *) apply HT_Var0; [apply wf_ctx_app; assumption | assumption].
  - (* 2. HT_VarS *) apply HT_VarS; [assumption | apply IHh_typing; assumption].
  - (* 3. HT_Unit *) apply HT_Unit; apply wf_ctx_app; [assumption | assumption].
  - (* 4. HT_Lam  *) apply HT_Lam. apply IHh_typing; assumption.
  - (* 5. HT_App  *) eapply HT_App; [apply IHh_typing1; assumption | apply IHh_typing2; assumption].
  - (* 6. HT_Pair *) apply HT_Pair; [apply IHh_typing1; assumption | apply IHh_typing2; assumption].
  - (* 7. HT_Fst  *) eapply HT_Fst; apply IHh_typing; assumption.
  - (* 8. HT_Snd  *) eapply HT_Snd; apply IHh_typing; assumption.
  - (* 9. HT_Inl  *) apply HT_Inl; [assumption | apply IHh_typing; assumption].
  - (* 10. HT_Inr *) apply HT_Inr; [assumption | apply IHh_typing; assumption].
  - (* 11. HT_Case*) eapply HT_Case; [apply IHh_typing1; assumption | apply IHh_typing2; assumption | apply IHh_typing3; assumption].
  - (* 12. HT_Absurd *) apply HT_Absurd; [assumption | apply IHh_typing; assumption].
  - (* 13. HT_All_Intro *) 
    apply HT_All_Intro; [apply wf_ctx_app; assumption | idtac].
    unfold ctx_pullback. rewrite map_app. apply IHh_typing. 
    eapply wf_ctx_pullback; [apply BT_Fst | assumption].
  - (* 14. HT_All_Elim *) 
    eapply HT_All_Elim; [apply IHh_typing; assumption | assumption].
  - (* 15. HT_Ex_Intro *) 
    eapply HT_Ex_Intro; [assumption | assumption | apply IHh_typing; assumption].
  - (* 16. HT_Ex_Elim *) 
    eapply HT_Ex_Elim; [assumption | apply IHh_typing1; assumption | idtac].
    unfold ctx_pullback. rewrite map_app. apply IHh_typing2. 
    eapply wf_ctx_pullback; [apply BT_Fst | assumption].
  - (* 17. HT_Conv *)
    eapply HT_Conv.
    + apply ctx_equiv_app; [eassumption | assumption].
    + eassumption.
    + apply IHh_typing; assumption.
Defined.