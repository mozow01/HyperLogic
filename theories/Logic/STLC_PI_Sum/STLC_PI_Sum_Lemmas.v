
Require Import List Arith PeanoNat Lia.
Import ListNotations.
Require Import STLC_PI_Sum.

Open Scope stlc_scope_sum.

(** Structural lemmas for de Bruijn lifting with sums. *)

(** [lift] descends through sums and void elimination. *)
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
  
  | tm_inl B t' =>
      tm_inl B (lift n k t')
  | tm_inr A t' =>
      tm_inr A (lift n k t')
  | tm_case t t1 t2 =>
      (* Each case branch binds one variable, so its cutoff is incremented. *)
      tm_case (lift n k t) (lift n (S k) t1) (lift n (S k) t2)
  | tm_absurd A t' =>
      tm_absurd A (lift n k t')
  end.





(** [insert_at n B Gamma] inserts [B] at position [n]. *)
Fixpoint insert_at (n : nat) (B : ty) (Gamma : context) : context :=
  match n, Gamma with
  | 0, _       => B :: Gamma
  | S n', h :: t => h :: insert_at n' B t
  | S n', []   => []
  end.


Lemma lift_0 : forall t k, lift 0 k t = t.
Proof.
  induction t; intros k; simpl; auto.
  -   destruct (k <=? n); auto.
  -   rewrite IHt; auto.
  -   rewrite IHt1, IHt2; auto.
  -   rewrite IHt1, IHt2; auto.
  -   rewrite IHt; auto.
  -   rewrite IHt; auto.
  -   rewrite IHt; auto.
  -   rewrite IHt; auto.
  -   rewrite IHt1, IHt2, IHt3; auto.
  -   rewrite IHt; auto.
Defined.

Lemma lift_add : forall t n m k, lift n k (lift m k t) = lift (n + m) k t.
Proof.
  induction t; intros n0 m0 k0; simpl; auto.
  -
    destruct (k0 <=? n) eqn:Hk.
    + simpl.
      assert (Hk_inner : k0 <=? m0 + n = true).
      { apply Nat.leb_le in Hk. apply Nat.leb_le. lia. }
      rewrite Hk_inner. f_equal. lia.
    + simpl. rewrite Hk. auto.
  -   rewrite IHt; auto.
  -   rewrite IHt1, IHt2; auto.
  -   rewrite IHt1, IHt2; auto.
  -   rewrite IHt; auto.
  -   rewrite IHt; auto.
  -   rewrite IHt; auto.
  -   rewrite IHt; auto.
  -   rewrite IHt1, IHt2, IHt3; auto.
  -   rewrite IHt; auto.
Defined.


Theorem weakening_general : forall Gamma t A B n,
  Gamma ⊢ t [:] A ->
  (insert_at n B Gamma) ⊢ (lift 1 n t) [:] A.
Proof.
  intros Gamma t A B n H.
  revert n B.
  induction H; intros n0 B0; simpl.

  -   apply T_Unit.
  -
    destruct n0; simpl; [apply T_VarS, T_Var0 | apply T_Var0].
  -
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
  -   apply T_Lam. apply (IHtypeability (S n0) B0).
  -   eapply T_App; eauto.
  -   apply T_Pair; eauto.
  -   eapply T_Fst; eauto.
  -   eapply T_Snd; eauto.
  
  -   apply T_Inl; auto.
  -   apply T_Inr; auto.
  -
    eapply T_Case; eauto.
    + apply (IHtypeability2 (S n0) B0).
    + apply (IHtypeability3 (S n0) B0).
  -   apply T_Absurd; auto.
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