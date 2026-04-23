Require Import List PeanoNat Arith Lia.
Import ListNotations.
Require Import Coq.Classes.Morphisms.

(* ================================================================= *)
(* TYPES AND TERMS                                *)
(* ================================================================= *)

Inductive ty : Set :=
  | Ty_Atomic : nat -> ty
  | Ty_Unit   : ty
  | Ty_Arrow  : ty -> ty -> ty
  | Ty_Prod   : ty -> ty -> ty.

Inductive tm : Set :=
  | tm_unit : tm
  | tm_var  : nat -> tm
  | tm_lam  : ty -> tm -> tm
  | tm_app  : tm -> tm -> tm
  | tm_pair : tm -> tm -> tm
  | tm_fst  : tm -> tm
  | tm_snd  : tm -> tm.

Definition context := list ty.

(* ================================================================= *)
(* SCOPE DEFINITION                               *)
(* ================================================================= *)

(* Létrehozzuk a saját scope-ot, hogy ne akadjon össze a későbbi nyelvekkel *)
Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.

(* ================================================================= *)
(* TYPING SYSTEM (LOGIC LAYER - Prop)                     *)
(* ================================================================= *)
(* Ez a matematikai definíció, ez kell a Kategóriához és Completenesshez *)

Inductive typeability : context -> tm -> ty -> Prop :=
  | T_Unit : forall Gamma,
      typeability Gamma tm_unit Ty_Unit

  | T_Var0 : forall Gamma A,
      typeability (A :: Gamma) (tm_var 0) A

  | T_VarS : forall Gamma A B i,
      typeability Gamma (tm_var i) A ->
      typeability (B :: Gamma) (tm_var (S i)) A

  | T_Lam : forall Gamma t A B,
      typeability (A :: Gamma) t B ->
      typeability Gamma (tm_lam A t) (Ty_Arrow A B)

  | T_App : forall Gamma t1 t2 A B,
      typeability Gamma t1 (Ty_Arrow A B) ->
      typeability Gamma t2 A ->
      typeability Gamma (tm_app t1 t2) B

  | T_Pair : forall Gamma t1 t2 A B,
      typeability Gamma t1 A ->
      typeability Gamma t2 B ->
      typeability Gamma (tm_pair t1 t2) (Ty_Prod A B)

  | T_Fst : forall Gamma t A B,
      typeability Gamma t (Ty_Prod A B) ->
      typeability Gamma (tm_fst t) A

  | T_Snd : forall Gamma t A B,
      typeability Gamma t (Ty_Prod A B) ->
      typeability Gamma (tm_snd t) B.

(* A notációt az stlc_scope-hoz kötjük *)
Notation "Gamma '⊢' t '[:]' A" := (typeability Gamma t A) (at level 70, no associativity) : stlc_scope.
Notation "'⊢' t '[:]' A" := (typeability nil t A) (at level 70, no associativity) : stlc_scope.
Notation "A ⊃ B" := (Ty_Arrow A B) (at level 70, right associativity) : stlc_scope.

(* Alapértelmezetten megnyitjuk a scope-ot ebben a fájlban *)
Open Scope stlc_scope.

(* ================================================================= *)
(* DERIVATION TREES (DATA LAYER - Set)                      *)
(* ================================================================= *)
(* Ez a Soundness-hez (Computation) kell. Ugyanaz a struktúra, de Set-ben. *)

Inductive derivation : context -> tm -> ty -> Set :=
  | D_Unit : forall Gamma,
      derivation Gamma tm_unit Ty_Unit

  | D_Var0 : forall Gamma A,
      derivation (A :: Gamma) (tm_var 0) A

  | D_VarS : forall Gamma A B i,
      derivation Gamma (tm_var i) A ->
      derivation (B :: Gamma) (tm_var (S i)) A

  | D_Lam : forall Gamma t A B,
      derivation (A :: Gamma) t B ->
      derivation Gamma (tm_lam A t) (Ty_Arrow A B)

  | D_App : forall Gamma t1 t2 A B,
      derivation Gamma t1 (Ty_Arrow A B) ->
      derivation Gamma t2 A ->
      derivation Gamma (tm_app t1 t2) B

  | D_Pair : forall Gamma t1 t2 A B,
      derivation Gamma t1 A ->
      derivation Gamma t2 B ->
      derivation Gamma (tm_pair t1 t2) (Ty_Prod A B)

  | D_Fst : forall Gamma t A B,
      derivation Gamma t (Ty_Prod A B) ->
      derivation Gamma (tm_fst t) A

  | D_Snd : forall Gamma t A B,
      derivation Gamma t (Ty_Prod A B) ->
      derivation Gamma (tm_snd t) B.

(* Híd a Derivation (Set) és Typeability (Prop) között *)
Fixpoint forget_derivation {Gamma t A} (d : derivation Gamma t A) : typeability Gamma t A.
Proof. Admitted.

(* ================================================================= *)
(* PROOF IRRELEVANCE LOGIC                          *)
(* ================================================================= *)

Inductive tm_equiv_rel : tm -> tm -> Prop :=
  | PI_rule : forall Gamma A t s,
      (Gamma ⊢ t [:] A) -> (Gamma ⊢ s [:] A) -> tm_equiv_rel t s.

Definition obj_stlc := ty.

Definition hom_stlc (x y : obj_stlc) := { t : tm | ⊢ t [:] (x ⊃ y)}.

Definition hom_equiv_stlc {x y : obj_stlc} (f g : hom_stlc x y) :=
  tm_equiv_rel (proj1_sig f) (proj1_sig g).

Lemma hom_equiv_stlc_refl : forall {x y} (f : hom_stlc x y), hom_equiv_stlc f f.
Proof. Admitted.

Lemma hom_equiv_stlc_sym : forall {x y} (f g : hom_stlc x y), hom_equiv_stlc f g -> hom_equiv_stlc g f.
Proof. Admitted.

Lemma hom_equiv_stlc_trans : forall {x y} (f g h : hom_stlc x y),
  hom_equiv_stlc f g -> hom_equiv_stlc g h -> hom_equiv_stlc f h.
Proof. Admitted.

Lemma generic_axiom_proof : forall {x y} (f g : hom_stlc x y), hom_equiv_stlc f g.
Proof. Admitted.