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
Proof. Admitted.

(**
 * Lemma: lift_add
 * Statement: lift n k (lift m k t) = lift (n + m) k t
 * Description: Composition of lifting is additive.
 *)
Lemma lift_add : forall t n m k, lift n k (lift m k t) = lift (n + m) k t.
Proof. Admitted.

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
Proof. Admitted.

(**
 * Lemma: weakening
 * Statement: Gamma |- t : A  =>  (B :: Gamma) |- lift 1 0 t : A
 * Description: Standard weakening at the head of the context.
 *)
Lemma weakening : forall Gamma t A B,
  Gamma ⊢ t [:] A ->
  (B :: Gamma) ⊢ (lift 1 0 t) [:] A.
Proof. Admitted.

(**
 * Lemma: weakening_from_nil
 * Statement: nil |- t : A  =>  Gamma |- lift |Gamma| 0 t : A
 * Description: Weakening a closed term into an arbitrary context `Gamma`.
 * Requires shifting indices by the length of the new context.
 *)
Lemma weakening_from_nil : forall Gamma t A,
  nil ⊢ t [:] A ->
  Gamma ⊢ (lift (length Gamma) 0 t) [:] A.
Proof. Admitted.