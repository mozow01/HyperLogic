Require Import List Arith PeanoNat Lia.
Import ListNotations.

Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.

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
(* 3. WEAKENING TÉTELEK                                              *)
(* ================================================================= *)

(* Ez egy kulcsfontosságú segédlemma: A fibrációs visszahúzás (pullback) 
   és a logikai kontextus-bővítés (insert_at) felcserélhetők! *)
Lemma ctx_pullback_insert : forall f n Psi G,
  ctx_pullback f (h_insert_at n Psi G) = h_insert_at n (form_pullback f Psi) (ctx_pullback f G).
Proof.
  intros f n Psi G. revert n. induction G; intros n; destruct n; simpl; auto.
  rewrite IHG. reflexivity.
Qed.

Theorem h_weakening_general : forall I G p Phi Psi n,
  h_typing I G p Phi ->
  h_typing I (h_insert_at n Psi G) (h_lift 1 n p) Phi.
Proof.
  intros I G p Phi Psi n H.
  revert n Psi.
  induction H; intros n0 Psi0; simpl.
  
  (* --- STLC Esetek --- *)
  - destruct n0; simpl; [apply HT_VarS, HT_Var0 | apply HT_Var0].
  - destruct n0; simpl.
    + apply HT_VarS, HT_VarS. assumption.
    + specialize (IHh_typing n0 Psi0).
      destruct (n0 <=? i) eqn:Heq.
      * apply HT_VarS. 
        replace (h_lift 1 n0 (tm_var i)) with (tm_var (S i)) in IHh_typing by (unfold h_lift; rewrite Heq; auto).
        exact IHh_typing.
      * apply HT_VarS.
        replace (h_lift 1 n0 (tm_var i)) with (tm_var i) in IHh_typing by (unfold h_lift; rewrite Heq; auto).
        exact IHh_typing.
  - apply HT_Unit.
  - apply HT_Lam. apply (IHh_typing (S n0) Psi0).
  - eapply HT_App; eauto.
  - apply HT_Pair; eauto.
  - eapply HT_Fst; eauto.
  - eapply HT_Snd; eauto.
  - apply HT_Inl; auto.
  - apply HT_Inr; auto.
  - eapply HT_Case; eauto.
    + apply (IHh_typing2 (S n0) Psi0).
    + apply (IHh_typing3 (S n0) Psi0).
  - apply HT_Absurd; auto.

  (* --- ÚJ ESETEK: Kvantorok --- *)
  - (* HT_All_Intro *)
    apply HT_All_Intro. 
    (* Trükk: A visszahúzott kontextust alakítjuk át a ctx_pullback_insert lemmával *)
    rewrite ctx_pullback_insert.
    apply (IHh_typing n0 (form_pullback b_fst Psi0)).
    
  - (* HT_All_Elim *)
    eapply HT_All_Elim. apply IHh_typing. assumption.
    
  - (* HT_Ex_Intro *)
    eapply HT_Ex_Intro; eauto.
    
  - (* HT_Ex_Elim *)
    eapply HT_Ex_Elim. 
    + apply IHh_typing1.
    + (* Itt is be kell hozni a ctx_pullback_insert lemmát *)
      rewrite ctx_pullback_insert.
      apply (IHh_typing2 (S n0) (form_pullback b_fst Psi0)).
Defined.

Lemma h_weakening : forall I G p Phi Psi,
  h_typing I G p Phi ->
  h_typing I (Psi :: G) (h_lift 1 0 p) Phi.
Proof.
  intros.
  change (Psi :: G) with (h_insert_at 0 Psi G).
  eapply h_weakening_general. assumption.
Defined.

Lemma h_weakening_from_nil : forall I G p Phi,
  h_typing I nil p Phi ->
  h_typing I G (h_lift (length G) 0 p) Phi.
Proof.
  intros I G. induction G; intros p0 Phi0 H.
  - simpl. rewrite h_lift_0. exact H.
  - simpl. apply IHG in H.
    eapply h_weakening with (Psi:=a) in H.
    rewrite h_lift_add in H.
    replace (1 + length G) with (S (length G)) in H by lia.
    exact H.
Defined.

Lemma h_weakening_append : forall I G Delta p Phi,
  h_typing I G p Phi -> h_typing I (G ++ Delta) p Phi.
Proof.
  assert (H_cons_app : forall (T : Type) (l : list T) (a : T), a :: l = [a] ++ l) by (simpl; auto).
  intros I G Delta p Phi H.
  
  revert Delta. 
  induction H; intros Delta; try (rewrite H_cons_app; try rewrite <- app_assoc; try rewrite <- H_cons_app); eauto.
  
  (* --- STLC Esetek --- *)
  - (* HT_Var0 *) apply HT_Var0.
  - (* HT_VarS *) apply HT_VarS; auto.
  - (* HT_Unit *) apply HT_Unit.
  - (* HT_Lam  *) apply HT_Lam. eauto.
  - (* HT_App  *) eapply HT_App; eauto.
  - (* HT_Pair *) apply HT_Pair; auto.
  - (* HT_Fst  *) eapply HT_Fst; eauto.
  - (* HT_Snd  *) eapply HT_Snd; eauto.
  - (* HT_Inl  *) apply HT_Inl; auto.
  - (* HT_Inr  *) apply HT_Inr; auto.
  - (* HT_Case *) eapply HT_Case; eauto.
  - (* HT_Absurd *) apply HT_Absurd; auto.
  
  (* --- Kvantor Esetek --- *)
  - (* HT_All_Intro *) 
    apply HT_All_Intro. 
    unfold ctx_pullback. rewrite map_app. 
    apply IHh_typing.
    
  - (* HT_All_Elim *) 
    eapply HT_All_Elim; eauto.
    
  - (* HT_Ex_Intro *) 
    eapply HT_Ex_Intro; eauto.
    
  - (* HT_Ex_Elim *) 
    eapply HT_Ex_Elim; eauto. 
    unfold ctx_pullback. rewrite map_app. apply IHh_typing2.
Defined.