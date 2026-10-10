

Require Import List.
Import ListNotations.

(** Legacy hyperdoctrine syntax and examples. *)
Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.


Notation "'π_1'" := b_fst (at level 0).
Notation "'π_2'" := b_snd (at level 0).
Notation "'S'"  := b_S (at level 0).

(* This precedence keeps predicate application tightly bound. *)
Notation "P '[' t ']'" := (Ty_Atom P t) (at level 10, no associativity).

Notation "Phi /\ Psi" := (Ty_Prod Phi Psi) (at level 80, right associativity).
Notation "Phi \/ Psi" := (Ty_Sum Phi Psi) (at level 85, right associativity).
Notation "Phi ~> Psi" := (Ty_Arrow Phi Psi) (at level 90, right associativity). 
(* [~>] avoids shadowing Coq's function arrow. *)

(* Weak precedence extends a quantifier over the following expression. *)
Notation "'∃' A , Phi" := (Ty_Ex A Phi) (at level 200, right associativity).
Notation "'∀' A , Phi" := (Ty_All A Phi) (at level 200, right associativity).

Variable P : nat.
Variable Q : nat.

Definition bal_oldal_szep := 
  ∃ S , (P[π_2] \/ Q[π_2]).

Definition jobb_oldal_szep := 
  (∃ S , P[π_2]) \/ (∃ S , Q[π_2]).
  


