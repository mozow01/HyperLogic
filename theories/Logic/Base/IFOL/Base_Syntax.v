(** The epsilon-free base syntax of intuitionistic first-order logic. *)

Require Import Setoid.
Require Import Relation_Definitions.
Require Import Morphisms.
Require Import Coq.Classes.RelationClasses.

(* Context objects: the terminal object, the individual sort, and products. *)
Inductive b_ty : Type :=
| b_Unit : b_ty
| b_S : b_ty
| b_Prod : b_ty -> b_ty -> b_ty.

Scheme Equality for b_ty.

Class FunctionSignature (Func : Type) : Type := {
  func_dom : Func -> b_ty;
  func_cod : Func -> b_ty
}.

(* Raw arrows.  Primitive function symbols are the only non-cartesian
   generators: iFOL deliberately has no distinguished constants. *)
Inductive b_tm {Func : Type} : Type :=
| b_id : b_tm
| b_comp : b_tm -> b_tm -> b_tm
| b_unit : b_tm
| b_pair : b_tm -> b_tm -> b_tm
| b_fst : b_tm
| b_snd : b_tm
| b_func : Func -> b_tm.

Inductive base_typing {Func : Type} `{FunctionSignature Func}
  : b_ty -> @b_tm Func -> b_ty -> Type :=
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
| BT_Func : forall f, base_typing (func_dom f) (b_func f) (func_cod f).

Arguments BT_Id {Func H A}.
Arguments BT_Comp {Func H A B C g f}.
Arguments BT_Unit {Func H A}.
Arguments BT_Pair {Func H A B C f g}.
Arguments BT_Fst {Func H A B}.
Arguments BT_Snd {Func H A B}.
Arguments BT_Func {Func H f}.

(* The free cartesian equational theory on the function signature. *)
Inductive base_equiv {Func : Type} `{FunctionSignature Func}
  : forall (A B : b_ty) (f g : @b_tm Func),
      @base_typing Func H A f B ->
      @base_typing Func H A g B -> Prop :=
| BE_Refl : forall A B (f : @b_tm Func)
    (df dg : @base_typing Func H A f B),
    base_equiv A B f f df dg
| BE_Sym : forall A B (f g : @b_tm Func)
    (df : @base_typing Func H A f B)
    (dg : @base_typing Func H A g B),
    base_equiv A B f g df dg ->
    base_equiv A B g f dg df
| BE_Trans : forall A B (f g h : @b_tm Func)
    (df : @base_typing Func H A f B)
    (dg : @base_typing Func H A g B)
    (dh : @base_typing Func H A h B),
    base_equiv A B f g df dg ->
    base_equiv A B g h dg dh ->
    base_equiv A B f h df dh
| BE_CongComp : forall A B C (f f' g g' : @b_tm Func)
    (df : @base_typing Func H A f B)
    (df' : @base_typing Func H A f' B)
    (dg : @base_typing Func H B g C)
    (dg' : @base_typing Func H B g' C),
    base_equiv A B f f' df df' ->
    base_equiv B C g g' dg dg' ->
    base_equiv A C (b_comp g f) (b_comp g' f') (BT_Comp dg df) (BT_Comp dg' df')
| BE_CongPair : forall A B C (f f' g g' : @b_tm Func)
    (df : @base_typing Func H A f B)
    (df' : @base_typing Func H A f' B)
    (dg : @base_typing Func H A g C)
    (dg' : @base_typing Func H A g' C),
    base_equiv A B f f' df df' ->
    base_equiv A C g g' dg dg' ->
    base_equiv A (b_Prod B C) (b_pair f g) (b_pair f' g') (BT_Pair df dg) (BT_Pair df' dg')
| BE_Assoc : forall A B C D (f g h : @b_tm Func)
    (df : @base_typing Func H A f B)
    (dg : @base_typing Func H B g C)
    (dh : @base_typing Func H C h D),
    base_equiv A D (b_comp h (b_comp g f)) (b_comp (b_comp h g) f)
      (BT_Comp dh (BT_Comp dg df)) (BT_Comp (BT_Comp dh dg) df)
| BE_IdL : forall A B (f : @b_tm Func) (df : @base_typing Func H A f B),
    base_equiv A B (b_comp b_id f) f (BT_Comp BT_Id df) df
| BE_IdR : forall A B (f : @b_tm Func) (df : @base_typing Func H A f B),
    base_equiv A B (b_comp f b_id) f (BT_Comp df BT_Id) df
| BE_BetaFst : forall A B C (f g : @b_tm Func)
    (df : @base_typing Func H A f B)
    (dg : @base_typing Func H A g C),
    base_equiv A B (b_comp b_fst (b_pair f g)) f (BT_Comp BT_Fst (BT_Pair df dg)) df
| BE_BetaSnd : forall A B C (f g : @b_tm Func)
    (df : @base_typing Func H A f B)
    (dg : @base_typing Func H A g C),
    base_equiv A C (b_comp b_snd (b_pair f g)) g (BT_Comp BT_Snd (BT_Pair df dg)) dg
| BE_EtaPair : forall A B C (h : @b_tm Func)
    (dh : @base_typing Func H A h (b_Prod B C)),
    base_equiv A (b_Prod B C) (b_pair (b_comp b_fst h) (b_comp b_snd h)) h
      (BT_Pair (BT_Comp BT_Fst dh) (BT_Comp BT_Snd dh)) dh
| BE_EtaUnit : forall A (f : @b_tm Func) (df : @base_typing Func H A f b_Unit),
    base_equiv A b_Unit f b_unit df BT_Unit
| BE_CompPair : forall A B C D (f g h : @b_tm Func)
    (df : @base_typing Func H B f C)
    (dg : @base_typing Func H B g D)
    (dh : @base_typing Func H A h B),
    base_equiv A (b_Prod C D) (b_comp (b_pair f g) h) (b_pair (b_comp f h) (b_comp g h))
      (BT_Comp (BT_Pair df dg) dh) (BT_Pair (BT_Comp df dh) (BT_Comp dg dh)).

Arguments base_equiv {Func H A B f g}.

Definition base_equiv_typed {Func : Type} `{FunctionSignature Func}
  (I A : b_ty) (t s : @b_tm Func) : Prop :=
  exists (dt : base_typing I t A) (ds : base_typing I s A), base_equiv dt ds.

Notation "t '≡_[' I ',' A ']' s" := (base_equiv_typed I A t s) (at level 70).

Lemma bet_refl : forall {Func : Type} `{FunctionSignature Func}
  {I A : b_ty} {t : @b_tm Func} (dt : base_typing I t A),
  base_equiv_typed I A t t.
Proof.
  intros. exists dt, dt. apply BE_Refl.
Defined.

Lemma bet_sym : forall {Func : Type} `{FunctionSignature Func}
  {I A : b_ty} {t s : @b_tm Func},
  base_equiv_typed I A t s -> base_equiv_typed I A s t.
Proof.
  intros Func H I A t s [dt [ds Hts]].
  exists ds, dt. now apply BE_Sym.
Defined.

Lemma bet_trans : forall {Func : Type} `{FunctionSignature Func}
  {I A : b_ty} {t s u : @b_tm Func},
  base_equiv_typed I A t s -> base_equiv_typed I A s u -> base_equiv_typed I A t u.
Proof.
  intros Func H I A t s u [dt [ds Hts]] [ds' [du Hsu]].
  exists dt, du. eapply BE_Trans; [exact Hts|].
  eapply BE_Trans; [apply BE_Refl|exact Hsu].
Defined.

Instance bet_sym_inst {Func : Type} `{FunctionSignature Func} {I A : b_ty}
  : Symmetric (@base_equiv_typed Func H I A).
Proof. exact (@bet_sym Func H I A). Defined.

Instance bet_trans_inst {Func : Type} `{FunctionSignature Func} {I A : b_ty}
  : Transitive (@base_equiv_typed Func H I A).
Proof. exact (@bet_trans Func H I A). Defined.

Add Parametric Morphism (Func : Type) (H : FunctionSignature Func) (A B C : b_ty) : (@b_comp Func)
  with signature (@base_equiv_typed Func H B C) ==> (@base_equiv_typed Func H A B) ==> (@base_equiv_typed Func H A C)
  as ifol_comp_typed_mor.
Proof.
  intros g g' [dg [dg' Hgg']] f f' [df [df' Hff']].
  exists (BT_Comp dg df), (BT_Comp dg' df').
  now apply BE_CongComp.
Defined.

Add Parametric Morphism (Func : Type) (H : FunctionSignature Func) (A B C : b_ty) : (@b_pair Func)
  with signature (@base_equiv_typed Func H A B) ==> (@base_equiv_typed Func H A C) ==> (@base_equiv_typed Func H A (b_Prod B C))
  as ifol_pair_typed_mor.
Proof.
  intros f f' [df [df' Hff']] g g' [dg [dg' Hgg']].
  exists (BT_Pair df dg), (BT_Pair df' dg').
  now apply BE_CongPair.
Defined.
