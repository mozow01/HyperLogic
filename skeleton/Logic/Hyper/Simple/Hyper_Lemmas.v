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
Proof. Admitted.

Lemma h_lift_add : forall t n m k, h_lift n k (h_lift m k t) = h_lift (n + m) k t.
Proof. Admitted.

(* ================================================================= *)
(* 3. WEAKENING TÉTELEK                                              *)
(* ================================================================= *)

(* Ez egy kulcsfontosságú segédlemma: A fibrációs visszahúzás (pullback)
   és a logikai kontextus-bővítés (insert_at) felcserélhetők! *)
Lemma ctx_pullback_insert : forall f n Psi G,
  ctx_pullback f (h_insert_at n Psi G) = h_insert_at n (form_pullback f Psi) (ctx_pullback f G).
Proof. Admitted.

Theorem h_weakening_general : forall I G p Phi Psi n,
  h_typing I G p Phi ->
  h_typing I (h_insert_at n Psi G) (h_lift 1 n p) Phi.
Proof. Admitted.

Lemma h_weakening : forall I G p Phi Psi,
  h_typing I G p Phi ->
  h_typing I (Psi :: G) (h_lift 1 0 p) Phi.
Proof. Admitted.

Lemma h_weakening_from_nil : forall I G p Phi,
  h_typing I nil p Phi ->
  h_typing I G (h_lift (length G) 0 p) Phi.
Proof. Admitted.

Lemma h_weakening_append : forall I G Delta p Phi,
  h_typing I G p Phi -> h_typing I (G ++ Delta) p Phi.
Proof. Admitted.