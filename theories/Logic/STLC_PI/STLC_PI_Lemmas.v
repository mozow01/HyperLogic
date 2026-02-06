Require Import List Arith PeanoNat Lia.
Import ListNotations.
Require Import HyperLogic.Logic.STLC_PI.STLC_PI.

Open Scope stlc_scope.

(* ================================================================= *)
(* 1. SYNTAX OPERATIONS                                              *)
(* ================================================================= *)

(**
 * Operation: lift
 * Description: Shifts De Bruijn indices to handle variable binding.
 * Usage: `lift n k t` adds `n` to all free variables in `t` (indices >= `k`).
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
(* 2. PROPERTIES OF LIFTING                                          *)
(* ================================================================= *)

(**
 * Lemma: lift_0
 * Statement: lift 0 k t = t
 * Description: Lifting by 0 is the identity operation.
 *)
Lemma lift_0 : forall t k, lift 0 k t = t.
Proof.
  induction t; intros k; simpl; auto.
  - (* tm_var *)
    destruct (k <=? n); auto.
  - (* tm_lam *)  rewrite IHt; auto.
  - (* tm_app *)  rewrite IHt1, IHt2; auto.
  - (* tm_pair *) rewrite IHt1, IHt2; auto.
  - (* tm_fst *)  rewrite IHt; auto.
  - (* tm_snd *)  rewrite IHt; auto.
Defined.
 
(**
 * Lemma: lift_add
 * Statement: lift n k (lift m k t) = lift (n + m) k t
 * Description: Composition of lifting is additive.
 *)
Lemma lift_add : forall t n m k, lift n k (lift m k t) = lift (n + m) k t.
Proof.
  (* Rename variables to avoid clash with De Bruijn index 'n' in tm_var *)
  induction t; intros n0 m0 k0; simpl; auto.

  - (* tm_var *)
    destruct (k0 <=? n) eqn:Hk.
    + (* Case: Index is lifted *)
      simpl.
      (* Prove k0 <= m0 + n to simplify the outer lift condition *)
      assert (Hk_inner : k0 <=? m0 + n = true).
      { apply Nat.leb_le in Hk. apply Nat.leb_le. lia. }
      rewrite Hk_inner.
      f_equal. lia. (* n0 + (m0 + n) = (n0 + m0) + n *)

    + (* Case: Index is not lifted *)
      simpl. rewrite Hk. auto.

  - (* tm_lam *)  rewrite IHt; auto.
  - (* tm_app *)  rewrite IHt1, IHt2; auto.
  - (* tm_pair *) rewrite IHt1, IHt2; auto.
  - (* tm_fst *)  rewrite IHt; auto.
  - (* tm_snd *)  rewrite IHt; auto.
Defined.

(* ================================================================= *)
(* 3. WEAKENING THEOREMS                                             *)
(* ================================================================= *)

(**
 * Theorem: weakening_general
 * Statement: Gamma |- t : A  =>  (insert_at n B Gamma) |- lift 1 n t : A
 * Description: General weakening lemma for insertion at arbitrary position `n`.
 *)
Theorem weakening_general : forall Gamma t A B n,
  Gamma ⊢ t [:] A ->
  (insert_at n B Gamma) ⊢ (lift 1 n t) [:] A.
Proof.
  intros Gamma t A B n H.
  revert n B.
  induction H; intros n0 B0; simpl.

  - (* T_Unit *)
    apply T_Unit.

  - (* T_Var0 *)
    destruct n0 as [|n0].
    + (* Insertion at head *) simpl. apply T_VarS. apply T_Var0.
    + (* Insertion deeper *)  simpl. apply T_Var0.

  - (* T_VarS *)
    destruct n0 as [|n0].
    + (* Insertion at head *)
      simpl. apply T_VarS, T_VarS. assumption.
    + (* Insertion deeper *)
      simpl. specialize (IHtypeability n0 B0).
      destruct (n0 <=? i) eqn:Heq.
      * (* Index >= insertion point: lifted twice *)
        apply T_VarS.
        replace (lift 1 n0 (tm_var i)) with (tm_var (S i)) in IHtypeability.
        exact IHtypeability.
        unfold lift. rewrite Heq. simpl. reflexivity.
      * (* Index < insertion point: unchanged *)
        apply T_VarS.
        replace (lift 1 n0 (tm_var i)) with (tm_var i) in IHtypeability.
        exact IHtypeability.
        unfold lift. rewrite Heq. reflexivity.

  - (* T_Lam *)
    apply T_Lam. apply (IHtypeability (S n0) B0).

  - (* Recursive cases *)
    eapply T_App; eauto.
  - apply T_Pair; eauto.
  - eapply T_Fst; eauto.
  - eapply T_Snd; eauto.
Defined.

(**
 * Lemma: weakening
 * Statement: Gamma |- t : A  =>  (B :: Gamma) |- lift 1 0 t : A
 * Description: Standard weakening at the head of the context.
 *)
Lemma weakening : forall Gamma t A B,
  Gamma ⊢ t [:] A ->
  (B :: Gamma) ⊢ (lift 1 0 t) [:] A.
Proof.
  intros.
  change (B :: Gamma) with (insert_at 0 B Gamma).
  apply weakening_general. assumption.
Defined.

(**
 * Lemma: weakening_from_nil
 * Statement: nil |- t : A  =>  Gamma |- lift |Gamma| 0 t : A
 * Description: Weakening a closed term into an arbitrary context `Gamma`.
 * Requires shifting indices by the length of the new context.
 *)
Lemma weakening_from_nil : forall Gamma t A,
  nil ⊢ t [:] A ->
  Gamma ⊢ (lift (length Gamma) 0 t) [:] A.
Proof.
  intros Gamma. induction Gamma; intros t0 A0 H.

  - (* Base case: Gamma = nil *)
    simpl.
    rewrite lift_0. (* Identity property *)
    exact H.

  - (* Inductive step: Gamma = a :: Gamma *)
    simpl.
    (* IH: Gamma |- lift |Gamma| 0 t0 : A0 *)
    apply IHGamma in H.

    (* Apply standard weakening (shifts by 1) *)
    apply weakening with (B:=a) in H.

    (* We have: lift 1 0 (lift |Gamma| 0 t0) *)
    (* We need: lift (S |Gamma|) 0 t0 *)
    rewrite lift_add in H.
    replace (1 + length Gamma) with (S (length Gamma)) in H by lia.
    exact H.
Defined.