(* Logic/Base/Epsilon/Base_Syntax *)

Require Import Setoid.
Require Import Relation_Definitions.
Require Import Morphisms.
Require Import Coq.Classes.RelationClasses.

(* 1. OBJEKTUMOK *)
Inductive b_ty : Type :=
  | b_Unit : b_ty
  | b_S    : b_ty
  | b_Prod : b_ty -> b_ty -> b_ty.

Scheme Equality for b_ty.

(* 1.5 FUNKCIÓJELEK SZIGNATÚRÁJA *)
Class FunctionSignature (Func : Type) : Type := {
  func_dom : Func -> b_ty;
  func_cod : Func -> b_ty
}.

(* 2. NYERS MORFIZMUSOK *)
Inductive b_tm {Sign Func : Type} : Type :=
  | b_id   : b_tm
  | b_comp : b_tm -> b_tm -> b_tm
  | b_unit : b_tm
  | b_pair : b_tm -> b_tm -> b_tm
  | b_fst  : b_tm
  | b_snd  : b_tm
  (* Epszilon-helyőrző. *)
  | b_const : b_ty -> Sign -> b_tm
  (* Valódi algebrai függvényjel. *)
  | b_func : Func -> b_tm.

(* 3. TIPUSOLÁSI SZABÁLYOK *)
Inductive base_typing {Sign Func : Type} `{HFunc : FunctionSignature Func}
  : b_ty -> b_tm (Sign:=Sign) (Func:=Func) -> b_ty -> Type :=
  | BT_Id : forall A, base_typing A b_id A
  | BT_Comp : forall A B C g f,
      base_typing B g C ->
      base_typing A f B ->
      base_typing A (b_comp g f) C
  | BT_Unit : forall A, base_typing A b_unit b_Unit
  | BT_Pair : forall A B C f g,
      base_typing A f B ->
      base_typing A g C ->
      base_typing A (b_pair f g) (b_Prod B C)
  | BT_Fst : forall A B, base_typing (b_Prod A B) b_fst A
  | BT_Snd : forall A B, base_typing (b_Prod A B) b_snd B
  | BT_Const : forall I A (s : Sign), base_typing I (b_const A s) A
  | BT_Func : forall f, base_typing (func_dom f) (b_func f) (func_cod f).

Arguments BT_Id {Sign Func HFunc A}.
Arguments BT_Comp {Sign Func HFunc A B C g f}.
Arguments BT_Unit {Sign Func HFunc A}.
Arguments BT_Pair {Sign Func HFunc A B C f g}.
Arguments BT_Fst {Sign Func HFunc A B}.
Arguments BT_Snd {Sign Func HFunc A B}.
Arguments BT_Const {Sign Func HFunc I A s}.
Arguments BT_Func {Sign Func HFunc f}.

(* 4. BÁZIS-EKVIVALENCIA *)
Inductive base_equiv {Sign Func : Type} `{HFunc : FunctionSignature Func}
  : forall (A B : b_ty) (f g : @b_tm Sign Func),
      @base_typing Sign Func HFunc A f B ->
      @base_typing Sign Func HFunc A g B -> Prop :=

  | BE_Refl : forall A B (f : @b_tm Sign Func)
      (df dg : @base_typing Sign Func HFunc A f B),
      base_equiv A B f f df dg

  | BE_Sym : forall A B (f g : @b_tm Sign Func)
      (df : @base_typing Sign Func HFunc A f B)
      (dg : @base_typing Sign Func HFunc A g B),
      base_equiv A B f g df dg ->
      base_equiv A B g f dg df

  | BE_Trans : forall A B (f g h : @b_tm Sign Func)
      (df : @base_typing Sign Func HFunc A f B)
      (dg : @base_typing Sign Func HFunc A g B)
      (dh : @base_typing Sign Func HFunc A h B),
      base_equiv A B f g df dg ->
      base_equiv A B g h dg dh ->
      base_equiv A B f h df dh

  | BE_CongComp : forall A B C (f f' g g' : @b_tm Sign Func)
      (df : @base_typing Sign Func HFunc A f B)
      (df' : @base_typing Sign Func HFunc A f' B)
      (dg : @base_typing Sign Func HFunc B g C)
      (dg' : @base_typing Sign Func HFunc B g' C),
      base_equiv A B f f' df df' ->
      base_equiv B C g g' dg dg' ->
      base_equiv A C (b_comp g f) (b_comp g' f') (BT_Comp dg df) (BT_Comp dg' df')

  | BE_CongPair : forall A B C (f f' g g' : @b_tm Sign Func)
      (df : @base_typing Sign Func HFunc A f B)
      (df' : @base_typing Sign Func HFunc A f' B)
      (dg : @base_typing Sign Func HFunc A g C)
      (dg' : @base_typing Sign Func HFunc A g' C),
      base_equiv A B f f' df df' ->
      base_equiv A C g g' dg dg' ->
      base_equiv A (b_Prod B C) (b_pair f g) (b_pair f' g') (BT_Pair df dg) (BT_Pair df' dg')

  | BE_Assoc : forall A B C D (f g h : @b_tm Sign Func)
      (df : @base_typing Sign Func HFunc A f B)
      (dg : @base_typing Sign Func HFunc B g C)
      (dh : @base_typing Sign Func HFunc C h D),
      base_equiv A D (b_comp h (b_comp g f)) (b_comp (b_comp h g) f)
        (BT_Comp dh (BT_Comp dg df)) (BT_Comp (BT_Comp dh dg) df)

  | BE_IdL : forall A B (f : @b_tm Sign Func)
      (df : @base_typing Sign Func HFunc A f B),
      base_equiv A B (b_comp b_id f) f (BT_Comp BT_Id df) df

  | BE_IdR : forall A B (f : @b_tm Sign Func)
      (df : @base_typing Sign Func HFunc A f B),
      base_equiv A B (b_comp f b_id) f (BT_Comp df BT_Id) df

  | BE_BetaFst : forall A B C (f g : @b_tm Sign Func)
      (df : @base_typing Sign Func HFunc A f B)
      (dg : @base_typing Sign Func HFunc A g C),
      base_equiv A B (b_comp b_fst (b_pair f g)) f (BT_Comp BT_Fst (BT_Pair df dg)) df

  | BE_BetaSnd : forall A B C (f g : @b_tm Sign Func)
      (df : @base_typing Sign Func HFunc A f B)
      (dg : @base_typing Sign Func HFunc A g C),
      base_equiv A C (b_comp b_snd (b_pair f g)) g (BT_Comp BT_Snd (BT_Pair df dg)) dg

  | BE_EtaPair : forall A B C (h : @b_tm Sign Func)
      (dh : @base_typing Sign Func HFunc A h (b_Prod B C)),
      base_equiv A (b_Prod B C) (b_pair (b_comp b_fst h) (b_comp b_snd h)) h
        (BT_Pair (BT_Comp BT_Fst dh) (BT_Comp BT_Snd dh)) dh

  | BE_EtaUnit : forall A (f : @b_tm Sign Func)
      (df : @base_typing Sign Func HFunc A f b_Unit),
      base_equiv A b_Unit f b_unit df BT_Unit

  | BE_CompPair : forall A B C D (f g h : @b_tm Sign Func)
      (df : @base_typing Sign Func HFunc B f C)
      (dg : @base_typing Sign Func HFunc B g D)
      (dh : @base_typing Sign Func HFunc A h B),
      base_equiv A (b_Prod C D) (b_comp (b_pair f g) h) (b_pair (b_comp f h) (b_comp g h))
        (BT_Comp (BT_Pair df dg) dh) (BT_Pair (BT_Comp df dh) (BT_Comp dg dh)).

Arguments base_equiv {Sign Func HFunc A B f g}.

Definition base_equiv_typed {Sign Func : Type} `{HFunc : FunctionSignature Func}
  (I J : b_ty) (f g : @b_tm Sign Func) : Prop :=
  exists (df : base_typing I f J) (dg : base_typing I g J),
    base_equiv df dg.

Notation "f '≡_[' I ',' J ']' g" := (base_equiv_typed I J f g) (at level 70).

Lemma bet_refl : forall {Sign Func : Type} `{HFunc : FunctionSignature Func}
  {I J : b_ty} {f : @b_tm Sign Func} (df : base_typing I f J),
  base_equiv_typed I J f f.
Proof.
  intros. exists df, df. apply BE_Refl.
Defined.

Lemma bet_sym : forall {Sign Func : Type} `{HFunc : FunctionSignature Func}
  {I J : b_ty} {f g : @b_tm Sign Func},
  base_equiv_typed I J f g -> base_equiv_typed I J g f.
Proof.
  intros Sign Func HFunc I J f g [df [dg H]].
  exists dg, df. apply BE_Sym. exact H.
Defined.

Lemma bet_trans : forall {Sign Func : Type} `{HFunc : FunctionSignature Func}
  {I J : b_ty} {f g h : @b_tm Sign Func},
  base_equiv_typed I J f g -> base_equiv_typed I J g h -> base_equiv_typed I J f h.
Proof.
  intros Sign Func HFunc I J f g h [df [dg1 H1]] [dg2 [dh H2]].
  exists df, dh.
  eapply BE_Trans.
  - exact H1.
  - eapply BE_Trans.
    + apply BE_Refl.
    + exact H2.
Qed.

Instance bet_sym_inst {Sign Func : Type} `{HFunc : FunctionSignature Func} {I J : b_ty}
  : Symmetric (@base_equiv_typed Sign Func HFunc I J).
Proof. exact (@bet_sym Sign Func HFunc I J). Defined.

Instance bet_trans_inst {Sign Func : Type} `{HFunc : FunctionSignature Func} {I J : b_ty}
  : Transitive (@base_equiv_typed Sign Func HFunc I J).
Proof. exact (@bet_trans Sign Func HFunc I J). Defined.

Add Parametric Morphism (Sign Func : Type) (HFunc : FunctionSignature Func) (A B C : b_ty) : (@b_comp Sign Func)
  with signature (@base_equiv_typed Sign Func HFunc B C) ==> (@base_equiv_typed Sign Func HFunc A B) ==> (@base_equiv_typed Sign Func HFunc A C)
  as comp_typed_mor.
Proof.
  intros g g' [dg [dg' Hg]] f f' [df [df' Hf]].
  exists (BT_Comp dg df), (BT_Comp dg' df').
  apply BE_CongComp.
  - exact Hf.
  - exact Hg.
Defined.

Add Parametric Morphism (Sign Func : Type) (HFunc : FunctionSignature Func) (A B C : b_ty) : (@b_pair Sign Func)
  with signature (@base_equiv_typed Sign Func HFunc A B) ==> (@base_equiv_typed Sign Func HFunc A C) ==> (@base_equiv_typed Sign Func HFunc A (b_Prod B C))
  as pair_typed_mor.
Proof.
  intros f f' [df [df' Hf]] g g' [dg [dg' Hg]].
  exists (BT_Pair df dg), (BT_Pair df' dg').
  apply BE_CongPair.
  - exact Hf.
  - exact Hg.
Defined.
