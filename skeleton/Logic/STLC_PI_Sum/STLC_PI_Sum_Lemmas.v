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
Proof. Admitted.

Lemma lift_add : forall t n m k, lift n k (lift m k t) = lift (n + m) k t.
Proof. Admitted.

(* ================================================================= *)
(* 3. WEAKENING THEOREMS                                           *)
(* ================================================================= *)

Theorem weakening_general : forall Gamma t A B n,
  Gamma ⊢ t [:] A ->
  (insert_at n B Gamma) ⊢ (lift 1 n t) [:] A.
Proof. Admitted.

Lemma weakening : forall Gamma t A B,
  Gamma ⊢ t [:] A ->
  (B :: Gamma) ⊢ (lift 1 0 t) [:] A.
Proof. Admitted.

Lemma weakening_from_nil : forall Gamma t A,
  nil ⊢ t [:] A ->
  Gamma ⊢ (lift (length Gamma) 0 t) [:] A.
Proof. Admitted.

Lemma weakening_append : forall Gamma Delta t A,
  Gamma ⊢ t [:] A -> (Gamma ++ Delta) ⊢ t [:] A.
Proof. Admitted.