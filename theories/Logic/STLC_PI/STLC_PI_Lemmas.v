Require Import List Arith PeanoNat Lia.
Import ListNotations.
Require Import HyperLogic.Logic.STLC_PI.STLC_PI.

Open Scope stlc_scope.

(* ================================================================= *)
(* 1. LIFTING (Index eltolás)                                        *)
(* ================================================================= *)
(* Csak ez kell a De Bruijn indexek kezeléséhez a Weakening-hez. *)

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

(* Segédfüggvény a kontextus bővítéshez *)
Fixpoint insert_at (n : nat) (B : ty) (Gamma : context) : context :=
  match n, Gamma with
  | 0, _ => B :: Gamma
  | S n', h :: t => h :: insert_at n' B t
  | S n', [] => []
  end.

(* ================================================================= *)
(* 2. WEAKENING (Gyengítés)                                          *)
(* ================================================================= *)

(* Ez az egyetlen komoly lemma, ami kell. *)
Theorem weakening_general : forall Gamma t A B n,
  Gamma ⊢ t [:] A ->
  (insert_at n B Gamma) ⊢ (lift 1 n t) [:] A.
Proof.
  intros Gamma t A B n H.
  revert n B.
  induction H; intros n0 B0; simpl.
  - apply T_Unit.
  - destruct n0 as [|n0].
    + simpl. apply T_VarS. apply T_Var0.
    + simpl. apply T_Var0.
  - destruct n0 as [|n0].
    + simpl. apply T_VarS. apply T_VarS. assumption.
    + simpl. specialize (IHtypeability n0 B0).
      destruct (n0 <=? i) eqn:Heq.
      * apply T_VarS.
        replace (lift 1 n0 (tm_var i)) with (tm_var (S i)) in IHtypeability.
        exact IHtypeability.
        unfold lift. rewrite Heq. simpl. reflexivity.
      * apply T_VarS.
        replace (lift 1 n0 (tm_var i)) with (tm_var i) in IHtypeability.
        exact IHtypeability.
        unfold lift. rewrite Heq. reflexivity.
  - apply T_Lam. apply (IHtypeability (S n0) B0).
  - eapply T_App; eauto.
  - apply T_Pair; eauto.
  - eapply T_Fst; eauto.
  - eapply T_Snd; eauto.
Defined.

(* A standard weakening, amit a Completeness használ: B beszúrása a fejre. *)
Lemma weakening : forall Gamma t A B,
  Gamma ⊢ t [:] A ->
  (B :: Gamma) ⊢ (lift 1 0 t) [:] A.
Proof.
  intros.
  change (B :: Gamma) with (insert_at 0 B Gamma).
  apply weakening_general. assumption.
Qed.