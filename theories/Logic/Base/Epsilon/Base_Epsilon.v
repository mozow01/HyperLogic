Require Import List. 
Require Import Setoid.
Require Import Morphisms.
Require Import HyperLogic.Logic.Hyper.Epsilon.Epsilon_Syntax.
Import ListNotations.

(* ================================================================= *)
(* 1. DEFINÍCIÓ: Kölcsönös Egyenlőség (Mutual Inductive Eq)          *)
(* ================================================================= *)

(* Előre deklaráljuk a jelölést, hogy a definícióban használhassuk *)
Reserved Notation "t1 '≈' t2" (at level 70).
Reserved Notation "A '≈T' B" (at level 70).

Inductive b_equiv_tm : b_tm -> b_tm -> Prop :=
  (* --- A) EKVIVALENCIA TULAJDONSÁGOK (Refl, Sym, Trans) --- *)
  | BE_Refl  : forall t, t ≈ t
  | BE_Sym   : forall t1 t2, t1 ≈ t2 -> t2 ≈ t1
  | BE_Trans : forall t1 t2 t3, t1 ≈ t2 -> t2 ≈ t3 -> t1 ≈ t3

  (* --- B) KONGRUENCIA (Minden konstruktorra) --- *)
  (* Ha a részek egyenlőek, az egész is egyenlő *)
  
  (* Párok *)
  | BE_Pair_Cong : forall a a' b b', a ≈ a' -> b ≈ b' -> (b_pair a b) ≈ (b_pair a' b')
  | BE_Fst_Cong  : forall t t', t ≈ t' -> (b_fst t) ≈ (b_fst t')
  | BE_Snd_Cong  : forall t t', t ≈ t' -> (b_snd t) ≈ (b_snd t')

  (* EPSZILON (A kritikus pont!) *)
  (* Ha a 'Ty' típusok szerkezetileg egyenlőek, akkor az Epszilonok is. *)
  | BE_Epsilon_Cong : forall A B, A ≈T B -> (b_epsilon A) ≈ (b_epsilon B)

  (* --- C) SZÁMÍTÁSI SZABÁLYOK (Beta & Eta) --- *)
  
  (* Beta: Projekciók egyszerűsítése *)
  | BE_Beta_Fst : forall a b, b_fst (b_pair a b) ≈ a
  | BE_Beta_Snd : forall a b, b_snd (b_pair a b) ≈ b
  
  (* Eta: Surjective Pairing (Ha szétszedem és összerakom, ugyanaz) *)
  | BE_Eta_Pair : forall t, b_pair (b_fst t) (b_snd t) ≈ t

with b_equiv_ty : h_ty -> h_ty -> Prop :=
  (* --- Típus Ekvivalencia --- *)
  | BTE_Refl : forall A, A ≈T A
  | BTE_Sym  : forall A B, A ≈T B -> B ≈T A
  | BTE_Trans: forall A B C, A ≈T B -> B ≈T C -> A ≈T C

  (* --- Típus Kongruencia --- *)
  | BTE_Arr_Cong : forall A A' B B', A ≈T A' -> B ≈T B' -> (Ty_Arr A B) ≈T (Ty_Arr A' B')
  | BTE_Prod_Cong: forall A A' B B', A ≈T A' -> B ≈T B' -> (Ty_Prod A B) ≈T (Ty_Prod A' B')
  
  (* ATOM (Reláció): Itt hivatkozunk vissza a Termekre! *)
  (* Két atom egyenlő, ha a predikátum indexe (p) azonos, 
     és a termek listája (args) elemenként ekvivalens. *)
  | BTE_Atom_Cong : forall p args args',
      Forall2 b_equiv_tm args args' -> (* Lista elemenkénti egyenlősége *)
      (Ty_Atom p args) ≈T (Ty_Atom p args')

where "t1 '≈' t2" := (b_equiv_tm t1 t2)
and   "A '≈T' B"  := (b_equiv_ty A B).

(* ================================================================= *)
(* 2. COQ REGISZTRÁCIÓ (Instances)                                   *)
(* ================================================================= *)

(* Ez teszi lehetővé, hogy a 'rewrite' parancsot használd a bizonyításokban. *)
(* Azt mondjuk a Coq-nak: "Ez a reláció tényleg egy ekvivalencia". *)

Instance b_equiv_Equivalence : Equivalence b_equiv_tm.
Proof.
  constructor.
  - exact BE_Refl.
  - exact BE_Sym.
  - exact BE_Trans.
Qed.

Instance b_equiv_ty_Equivalence : Equivalence b_equiv_ty.
Proof.
  constructor.
  - exact BTE_Refl.
  - exact BTE_Sym.
  - exact BTE_Trans.
Qed.

(* ================================================================= *)
(* 3. PROPER INSTANCE-OK (Hogy működjön a helyettesítés)             *)
(* ================================================================= *)

(* Ezek a bizonyítások biztosítják, hogy ha kicserélsz egy részt 
   egy kifejezésben egy vele egyenlőre, az egész egyenlő marad. *)

Instance b_pair_Proper : Proper (b_equiv_tm ==> b_equiv_tm ==> b_equiv_tm) b_pair.
Proof.
  intros x y H1 z w H2. apply BE_Pair_Cong; assumption.
Qed.

Instance b_fst_Proper : Proper (b_equiv_tm ==> b_equiv_tm) b_fst.
Proof.
  intros x y H. apply BE_Fst_Cong; assumption.
Qed.

Instance b_snd_Proper : Proper (b_equiv_tm ==> b_equiv_tm) b_snd.
Proof.
  intros x y H. apply BE_Snd_Cong; assumption.
Qed.

(* A legfontosabb: Az Epszilon is Proper! *)
Instance b_epsilon_Proper : Proper (b_equiv_ty ==> b_equiv_tm) b_epsilon.
Proof.
  intros A B H. apply BE_Epsilon_Cong; assumption.
Qed.

(* A típus konstruktorok is Proper-ek *)
Instance Ty_Atom_Proper : Proper (eq ==> Forall2 b_equiv_tm ==> b_equiv_ty) Ty_Atom.
Proof.
  intros p p' Hp args args' Hargs.
  rewrite Hp. apply BTE_Atom_Cong. assumption.
Qed.