(* Base/Simple/Base_Syntax*)

Require Import Setoid.
Require Import Relation_Definitions.
Require Import Morphisms.

  (* 1. OBJEKTUMOK *)
  Inductive b_ty : Type :=
    | b_Unit : b_ty
    | b_S    : b_ty
    | b_Prod : b_ty -> b_ty -> b_ty.

  (* 2. NYERS MORFIZMUSOK *)
  Inductive b_tm : Type :=
    | b_id   : b_tm
    | b_comp : b_tm -> b_tm -> b_tm
    | b_unit : b_tm
    | b_pair : b_tm -> b_tm -> b_tm
    | b_fst  : b_tm
    | b_snd  : b_tm.

  (* 3. TIPUSOLASI SZABALYOK (B1 |- f : B2) *)
  Inductive base_typing : b_ty -> b_tm -> b_ty -> Set :=
    | BT_Id : forall A,
        base_typing A b_id A
    | BT_Comp : forall A B C g f,
        base_typing B g C -> base_typing A f B ->
        base_typing A (b_comp g f) C
    | BT_Unit : forall A,
        base_typing A b_unit b_Unit
    | BT_Pair : forall A B C f g,
        base_typing A f B -> base_typing A g C ->
        base_typing A (b_pair f g) (b_Prod B C)
    | BT_Fst : forall A B,
        base_typing (b_Prod A B) b_fst A
    | BT_Snd : forall A B,
        base_typing (b_Prod A B) b_snd B.

Require Import Setoid.
Require Import Relation_Definitions.
Require Import Morphisms.

(* --- 1. LÉPÉS: Argumentumok implicitté tétele --- *)
(* Ez mondja meg a Coq-nak, hogy a kapcsos zárójelben lévőket találja ki magától. *)
Arguments BT_Id {A}.
Arguments BT_Comp {A B C g f}.
Arguments BT_Unit {A}.
Arguments BT_Pair {A B C f g}.
Arguments BT_Fst {A B}.
Arguments BT_Snd {A B}.

(* --- 2. LÉPÉS: A tiszta ekvivalencia reláció --- *)
Inductive base_equiv : forall (A B : b_ty) (f g : b_tm),
  base_typing A f B -> base_typing A g B -> Prop :=

    (* --- Ekvivalencia relacio alapjai --- *)
    | BE_Refl : forall A B f (df : base_typing A f B),
        base_equiv A B f f df df

    | BE_Sym : forall A B f g (df : base_typing A f B) (dg : base_typing A g B),
        base_equiv A B f g df dg -> base_equiv A B g f dg df

    | BE_Trans : forall A B f g h (df : base_typing A f B) (dg : base_typing A g B) (dh : base_typing A h B),
        base_equiv A B f g df dg -> base_equiv A B g h dg dh -> base_equiv A B f h df dh

    (* --- Kongruencia --- *)
    | BE_CongComp : forall A B C f f' g g'
        (df : base_typing A f B) (df' : base_typing A f' B)
        (dg : base_typing B g C) (dg' : base_typing B g' C),
        base_equiv A B f f' df df' ->
        base_equiv B C g g' dg dg' ->
        (* Itt most már TÉNYLEG elég a 2 argumentum a BT_Comp-nak! *)
        base_equiv A C (b_comp g f) (b_comp g' f') (BT_Comp dg df) (BT_Comp dg' df')

    | BE_CongPair : forall A B C f f' g g'
        (df : base_typing A f B) (df' : base_typing A f' B)
        (dg : base_typing A g C) (dg' : base_typing A g' C),
        base_equiv A B f f' df df' ->
        base_equiv A C g g' dg dg' ->
        base_equiv A (b_Prod B C) (b_pair f g) (b_pair f' g') (BT_Pair df dg) (BT_Pair df' dg')

    (* --- Kategoria axiomak --- *)
    | BE_Assoc : forall A B C D f g h
        (df: base_typing A f B) (dg: base_typing B g C) (dh: base_typing C h D),
        base_equiv A D (b_comp h (b_comp g f)) (b_comp (b_comp h g) f)
                   (BT_Comp dh (BT_Comp dg df)) (BT_Comp (BT_Comp dh dg) df)

    (* Figyeld meg: eltűnt a (BT_Id B), csak BT_Id maradt! *)
    | BE_IdL : forall A B f (df: base_typing A f B),
        base_equiv A B (b_comp b_id f) f (BT_Comp BT_Id df) df

    | BE_IdR : forall A B f (df: base_typing A f B),
        base_equiv A B (b_comp f b_id) f (BT_Comp df BT_Id) df

    (* --- Cartesian (Beta/Eta) axiomak --- *)
    | BE_BetaFst : forall A B C f g (df: base_typing A f B) (dg: base_typing A g C),
        base_equiv A B (b_comp b_fst (b_pair f g)) f (BT_Comp BT_Fst (BT_Pair df dg)) df

    | BE_BetaSnd : forall A B C f g (df: base_typing A f B) (dg: base_typing A g C),
        base_equiv A C (b_comp b_snd (b_pair f g)) g (BT_Comp BT_Snd (BT_Pair df dg)) dg

    | BE_EtaPair : forall A B C h (dh: base_typing A h (b_Prod B C)),
        base_equiv A (b_Prod B C) (b_pair (b_comp b_fst h) (b_comp b_snd h)) h
                   (BT_Pair (BT_Comp BT_Fst dh) (BT_Comp BT_Snd dh)) dh

    | BE_EtaUnit : forall A f (df: base_typing A f b_Unit),
        base_equiv A b_Unit f b_unit df BT_Unit.

(* --- 5. SETOID ÉS MORFIZMUS REGISZTRÁCIÓ --- *)

(* Először implicitté tesszük a base_equiv paramétereit is,
   hogy a Setoid rendszer csak a két derivációt (df, dg) lássa. *)
Arguments base_equiv {A B f g}.

(* Ekvivalencia reláció regisztrálása *)
Add Parametric Relation (A B : b_ty) (f : b_tm) : (base_typing A f B) (@base_equiv A B f f)
  reflexivity proved by (@BE_Refl A B f)
  symmetry proved by (@BE_Sym A B f f)
  transitivity proved by (@BE_Trans A B f f f)
  as base_equiv_rel.

(* Morfizmus regisztrálása a kompozícióra (hogy lehessen rewrite-olni a b_comp belsejében) *)
Add Parametric Morphism (A B C : b_ty) (f g : b_tm) : (@BT_Comp A B C g f)
  with signature (@base_equiv B C g g) ==> (@base_equiv A B f f) ==> (@base_equiv A C (b_comp g f) (b_comp g f))
  as comp_mor.
Proof. Admitted.

(* Morfizmus regisztrálása a párosításra (hogy lehessen rewrite-olni a b_pair belsejében) *)
Add Parametric Morphism (A B C : b_ty) (f g : b_tm) : (@BT_Pair A B C f g)
  with signature (@base_equiv A B f f) ==> (@base_equiv A C g g) ==> (@base_equiv A (b_Prod B C) (b_pair f g) (b_pair f g))
  as pair_mor.
Proof. Admitted.