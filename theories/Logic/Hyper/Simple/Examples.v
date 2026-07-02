(* Logic/Hyper/Simple/Examples.v *)


Require Import List.
Import ListNotations.

(* ================================================================= *)
(* MODUL BEEMELÉSE: BÁZIS SZINTAXIS (Individuumok és Kontextusok)    *)
(* ================================================================= *)
Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.

(* ================================================================= *)
(* HYPER SYNTAX: MATEMATIKAI JELÖLÉSRENDSZER (NOTATIONS)             *)
(* ================================================================= *)

(* 1. Bázis projekciók rövidítései a kényelemért *)
Notation "'π_1'" := b_fst (at level 0).
Notation "'π_2'" := b_snd (at level 0).
Notation "'S'"  := b_S (at level 0).

(* 2. Atomi predikátum alkalmazása (Pullback jelölés: P[t]) *)
(* A 10-es szint biztosítja, hogy ez kössön a legerősebben *)
Notation "P '[' t ']'" := (Ty_Atom P t) (at level 10, no associativity).

(* 3. Logikai Konnektívumok *)
(* Jobbra asszociatívak, a megszokott logikai precedencia-szintekkel *)
Notation "Phi /\ Psi" := (Ty_Prod Phi Psi) (at level 80, right associativity).
Notation "Phi \/ Psi" := (Ty_Sum Phi Psi) (at level 85, right associativity).
Notation "Phi ~> Psi" := (Ty_Arrow Phi Psi) (at level 90, right associativity). 
(* Megj: A sima '->' a Coq beépített függvény-nyila, azt ne írjuk felül, használjuk a '~>'-t! *)

(* 4. Kvantorok *)
(* A 200-as szint (leggyengébb kötés) miatt a kvantor az egész utána lévő kifejezésre vonatkozik *)
Notation "'∃' A , Phi" := (Ty_Ex A Phi) (at level 200, right associativity).
Notation "'∀' A , Phi" := (Ty_All A Phi) (at level 200, right associativity).

Variable P : nat. (* pl. 1 *)
Variable Q : nat. (* pl. 2 *)

Definition bal_oldal_szep := 
  ∃ S , (P[π_2] \/ Q[π_2]).

Definition jobb_oldal_szep := 
  (∃ S , P[π_2]) \/ (∃ S , Q[π_2]).
  


