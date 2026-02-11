Require Import List Arith PeanoNat Lia.
Import ListNotations.
Require Import STLC_PI_Sum.

Open Scope stlc_scope_sum.

(* ================================================================= *)
(* 1. SYNTAX OPERATIONS                                            *)
(* ================================================================= *)

(**
 * Operation: lift
 * Description: Shifts De Bruijn indices to handle variable binding.
 * Extended for Sums and Void.
 *)
Fixpoint lift (n : nat) (k : nat) (t : tm) : tm :=
  match t with
  | tm_unit => tm_unit
  | tm_var i =>
      if k <=? i then tm_var (n + i) else tm_var i
  | tm_lam A t' =>
      tm_lam A (lift n (S k) t')
  | tm_app t1 t2 =>
      tm_app (lift n k t1) (lift n k t2)
  | tm_pair t1 t2 =>
      tm_pair (lift n k t1) (lift n k t2)
  | tm_fst t' =>
      tm_fst (lift n k t')
  | tm_snd t' =>
      tm_snd (lift n k t')
  
  (* --- New Cases --- *)
  | tm_inl B t' =>
      tm_inl B (lift n k t')
  | tm_inr A t' =>
      tm_inr A (lift n k t')
  | tm_case t t1 t2 =>
      (* t has no new binders.
         t1 binds a variable (the Left case), so we increment k.
         t2 binds a variable (the Right case), so we increment k. *)
      tm_case (lift n k t) (lift n (S k) t1) (lift n (S k) t2)
  | tm_absurd A t' =>
      tm_absurd A (lift n k t')
  end.

(**
 * Operation: insert_at
 * Description: Inserts a type `B` into context `Gamma` at position `n`.
 *)
Fixpoint insert_at (n : nat) (B : ty) (Gamma : context) : context :=
  match n, Gamma with
  | 0, _       => B :: Gamma
  | S n', h :: t => h :: insert_at n' B t
  | S n', []   => []
  end.

(* ================================================================= *)
(* 2. PROPERTIES OF LIFTING                                        *)
(* ================================================================= *)

Lemma lift_0 : forall t k, lift 0 k t = t.
Proof.
  induction t; intros k; simpl; auto.
  - (* tm_var *) destruct (k <=? n); auto.
  - (* tm_lam *) rewrite IHt; auto.
  - (* tm_app *) rewrite IHt1, IHt2; auto.
  - (* tm_pair *) rewrite IHt1, IHt2; auto.
  - (* tm_fst *) rewrite IHt; auto.
  - (* tm_snd *) rewrite IHt; auto.
  (* New cases *)
  - (* tm_inl *) rewrite IHt; auto.
  - (* tm_inr *) rewrite IHt; auto.
  - (* tm_case *) rewrite IHt1, IHt2, IHt3; auto.
  - (* tm_absurd *) rewrite IHt; auto.
Defined.

Lemma lift_add : forall t n m k, lift n k (lift m k t) = lift (n + m) k t.
Proof.
  induction t; intros n0 m0 k0; simpl; auto.
  - (* tm_var *)
    destruct (k0 <=? n) eqn:Hk.
    + simpl.
      assert (Hk_inner : k0 <=? m0 + n = true).
      { apply Nat.leb_le in Hk. apply Nat.leb_le. lia. }
      rewrite Hk_inner. f_equal. lia.
    + simpl. rewrite Hk. auto.
  - (* tm_lam *) rewrite IHt; auto.
  - (* tm_app *) rewrite IHt1, IHt2; auto.
  - (* tm_pair *) rewrite IHt1, IHt2; auto.
  - (* tm_fst *) rewrite IHt; auto.
  - (* tm_snd *) rewrite IHt; auto.
  (* New cases *)
  - (* tm_inl *) rewrite IHt; auto.
  - (* tm_inr *) rewrite IHt; auto.
  - (* tm_case *) rewrite IHt1, IHt2, IHt3; auto.
  - (* tm_absurd *) rewrite IHt; auto.
Defined.

(* ================================================================= *)
(* 3. WEAKENING THEOREMS                                           *)
(* ================================================================= *)

Theorem weakening_general : forall Gamma t A B n,
  Gamma ⊢ t [:] A ->
  (insert_at n B Gamma) ⊢ (lift 1 n t) [:] A.
Proof.
  intros Gamma t A B n H.
  revert n B.
  induction H; intros n0 B0; simpl.

  - (* T_Unit *) apply T_Unit.
  - (* T_Var0 *)
    destruct n0; simpl; [apply T_VarS, T_Var0 | apply T_Var0].
  - (* T_VarS *)
    destruct n0; simpl.
    + apply T_VarS, T_VarS. assumption.
    + specialize (IHtypeability n0 B0).
      destruct (n0 <=? i) eqn:Heq.
      * apply T_VarS.
        replace (lift 1 n0 (tm_var i)) with (tm_var (S i)) in IHtypeability.
        exact IHtypeability.
        unfold lift. rewrite Heq. reflexivity.
      * apply T_VarS.
        replace (lift 1 n0 (tm_var i)) with (tm_var i) in IHtypeability.
        exact IHtypeability.
        unfold lift. rewrite Heq. reflexivity.
  - (* T_Lam *) apply T_Lam. apply (IHtypeability (S n0) B0).
  - (* T_App *) eapply T_App; eauto.
  - (* T_Pair *) apply T_Pair; eauto.
  - (* T_Fst *) eapply T_Fst; eauto.
  - (* T_Snd *) eapply T_Snd; eauto.
  
  (* --- New Cases --- *)
  - (* T_Inl *) apply T_Inl; auto.
  - (* T_Inr *) apply T_Inr; auto.
  - (* T_Case *) 
    eapply T_Case; eauto.
    (* Apply IH to branches. Note that context size increases by 1 in branches,
       so insertion index 'n' becomes 'S n' relative to the binder. *)
    + apply (IHtypeability2 (S n0) B0).
    + apply (IHtypeability3 (S n0) B0).
  - (* T_Absurd *) apply T_Absurd; auto.
Defined.

Lemma weakening : forall Gamma t A B,
  Gamma ⊢ t [:] A ->
  (B :: Gamma) ⊢ (lift 1 0 t) [:] A.
Proof.
  intros.
  change (B :: Gamma) with (insert_at 0 B Gamma).
  apply weakening_general. assumption.
Defined.

Lemma weakening_from_nil : forall Gamma t A,
  nil ⊢ t [:] A ->
  Gamma ⊢ (lift (length Gamma) 0 t) [:] A.
Proof.
  intros Gamma. induction Gamma; intros t0 A0 H.
  - simpl. rewrite lift_0. exact H.
  - simpl. apply IHGamma in H.
    apply weakening with (B:=a) in H.
    rewrite lift_add in H.
    replace (1 + length Gamma) with (S (length Gamma)) in H by lia.
    exact H.
Defined.

Lemma weakening_append : forall Gamma Delta t A,
  Gamma ⊢ t [:] A -> (Gamma ++ Delta) ⊢ t [:] A.
Proof.
  assert (H_cons_app : forall (T : Type) (l : list T) (a : T), a :: l = [a] ++ l).
  { simpl; auto. }
  intros Gamma Delta t A H.
  induction H; try (rewrite H_cons_app; try rewrite <- app_assoc; try rewrite <- H_cons_app); auto.
  - apply T_Unit.
  - apply T_Var0.
  - apply T_VarS; auto.
  - apply T_Lam; auto.
  - eapply T_App; eassumption.
  - apply T_Pair; auto.
  - eapply T_Fst; eassumption.
  - eapply T_Snd; eassumption.
  - apply T_Inl; auto.
  - apply T_Inr; auto.
  - eapply T_Case; eauto.
  - apply T_Absurd; auto.
Defined.