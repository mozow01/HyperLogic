(* Logic/Base/Epsilon/Base_Syntax *)

Require Import Setoid.
Require Import Relation_Definitions.
Require Import Morphisms.   
  
(* 1. OBJEKTUMOK (Marad az eredeti) *)
Inductive b_ty : Type :=
  | b_Unit : b_ty
  | b_S    : b_ty
  | b_Prod : b_ty -> b_ty -> b_ty.

(* 2. NYERS MORFIZMUSOK (Bővítve az implicit {Sign} paraméterrel) *)
Inductive b_tm {Sign : Type} : Type :=
  | b_id   : b_tm
  | b_comp : b_tm -> b_tm -> b_tm
  | b_unit : b_tm
  | b_pair : b_tm -> b_tm -> b_tm
  | b_fst  : b_tm
  | b_snd  : b_tm
  (* ÚJ: A rigid konstans hordozója. 
     Tartalmazza a típusát (b_ty) és az azonosítóját (Sign). *)
  | b_const : b_ty -> Sign -> b_tm.

(* 3. TIPUSOLASI SZABALYOK (B1 |- f : B2) *)

(* 3. TIPUSOLASI SZABALYOK (B1 |- f : B2) *)
Inductive base_typing {Sign : Type} : b_ty -> b_tm (Sign:=Sign) -> b_ty -> Type :=
  | BT_Id : forall A, base_typing A b_id A
  | BT_Comp : forall A B C g f, base_typing B g C -> base_typing A f B -> base_typing A (b_comp g f) C
  | BT_Unit : forall A, base_typing A b_unit b_Unit
  | BT_Pair : forall A B C f g, base_typing A f B -> base_typing A g C -> base_typing A (b_pair f g) (b_Prod B C)
  | BT_Fst : forall A B, base_typing (b_Prod A B) b_fst A
  | BT_Snd : forall A B, base_typing (b_Prod A B) b_snd B
  (* ÚJ: A konstans tipizálási szabálya. *)
  | BT_Const : forall I A (s : Sign), base_typing I (b_const A s) A.

(* --- 1. LÉPÉS: Argumentumok implicitté tétele --- *)
(* Mivel bevezettük a {Sign} paramétert a b_tm és base_typing típusokba, 
   ez a paraméter lesz az ELSŐ implicit argumentum minden konstruktornál. *)
Arguments BT_Id {Sign A}.
Arguments BT_Comp {Sign A B C g f}.
Arguments BT_Unit {Sign A}.
Arguments BT_Pair {Sign A B C f g}.
Arguments BT_Fst {Sign A B}.
Arguments BT_Snd {Sign A B}.
Arguments BT_Const {Sign I A s}.

(* --- 2. LÉPÉS: A tiszta ekvivalencia reláció --- *)
(* Ide is bejön a {Sign : Type} explicit implicit paraméterként. *)
Inductive base_equiv {Sign : Type} : forall (A B : b_ty) (f g : @b_tm Sign), 
  @base_typing Sign A f B -> @base_typing Sign A g B -> Prop :=

    (* --- Ekvivalencia relacio alapjai --- *)
    | BE_Refl : forall A B (f : @b_tm Sign) (df : @base_typing Sign A f B),
        base_equiv A B f f df df
        
    | BE_Sym : forall A B (f g : @b_tm Sign) (df : @base_typing Sign A f B) (dg : @base_typing Sign A g B),
        base_equiv A B f g df dg -> base_equiv A B g f dg df
        
    | BE_Trans : forall A B (f g h : @b_tm Sign) (df : @base_typing Sign A f B) (dg : @base_typing Sign A g B) (dh : @base_typing Sign A h B),
        base_equiv A B f g df dg -> base_equiv A B g h dg dh -> base_equiv A B f h df dh

    (* --- Kongruencia --- *)
    | BE_CongComp : forall A B C (f f' g g' : @b_tm Sign)
        (df : @base_typing Sign A f B) (df' : @base_typing Sign A f' B)
        (dg : @base_typing Sign B g C) (dg' : @base_typing Sign B g' C),
        base_equiv A B f f' df df' -> 
        base_equiv B C g g' dg dg' -> 
        base_equiv A C (b_comp g f) (b_comp g' f') (BT_Comp dg df) (BT_Comp dg' df')

    | BE_CongPair : forall A B C (f f' g g' : @b_tm Sign)
        (df : @base_typing Sign A f B) (df' : @base_typing Sign A f' B)
        (dg : @base_typing Sign A g C) (dg' : @base_typing Sign A g' C),
        base_equiv A B f f' df df' -> 
        base_equiv A C g g' dg dg' ->
        base_equiv A (b_Prod B C) (b_pair f g) (b_pair f' g') (BT_Pair df dg) (BT_Pair df' dg')

    (* --- Kategoria axiomak --- *)
    | BE_Assoc : forall A B C D (f g h : @b_tm Sign) 
        (df: @base_typing Sign A f B) (dg: @base_typing Sign B g C) (dh: @base_typing Sign C h D),
        base_equiv A D (b_comp h (b_comp g f)) (b_comp (b_comp h g) f) 
                   (BT_Comp dh (BT_Comp dg df)) (BT_Comp (BT_Comp dh dg) df)

    | BE_IdL : forall A B (f : @b_tm Sign) (df: @base_typing Sign A f B),
        base_equiv A B (b_comp b_id f) f (BT_Comp BT_Id df) df

    | BE_IdR : forall A B (f : @b_tm Sign) (df: @base_typing Sign A f B),
        base_equiv A B (b_comp f b_id) f (BT_Comp df BT_Id) df

    (* --- Cartesian (Beta/Eta) axiomak --- *)
    | BE_BetaFst : forall A B C (f g : @b_tm Sign) (df: @base_typing Sign A f B) (dg: @base_typing Sign A g C),
        base_equiv A B (b_comp b_fst (b_pair f g)) f (BT_Comp BT_Fst (BT_Pair df dg)) df

    | BE_BetaSnd : forall A B C (f g : @b_tm Sign) (df: @base_typing Sign A f B) (dg: @base_typing Sign A g C),
        base_equiv A C (b_comp b_snd (b_pair f g)) g (BT_Comp BT_Snd (BT_Pair df dg)) dg

    | BE_EtaPair : forall A B C (h : @b_tm Sign) (dh: @base_typing Sign A h (b_Prod B C)),
        base_equiv A (b_Prod B C) (b_pair (b_comp b_fst h) (b_comp b_snd h)) h 
                   (BT_Pair (BT_Comp BT_Fst dh) (BT_Comp BT_Snd dh)) dh

    | BE_EtaUnit : forall A (f : @b_tm Sign) (df: @base_typing Sign A f b_Unit),
        base_equiv A b_Unit f b_unit df BT_Unit
        
    | BE_CompPair : forall A B C D (f g h : @b_tm Sign) 
        (df: @base_typing Sign B f C) (dg: @base_typing Sign B g D) (dh: @base_typing Sign A h B),
        base_equiv A (b_Prod C D) (b_comp (b_pair f g) h) (b_pair (b_comp f h) (b_comp g h)) 
                   (BT_Comp (BT_Pair df dg) dh) (BT_Pair (BT_Comp df dh) (BT_Comp dg dh)). 

(* --- 5. SETOID ÉS MORFIZMUS REGISZTRÁCIÓ --- *)

(* Implicitté tesszük a b_equiv Sign paraméterét is. *)
Arguments base_equiv {Sign A B f g}.

(* --- 5. SETOID ÉS MORFIZMUS REGISZTRÁCIÓ --- *)

(* Implicitté tesszük a b_equiv Sign paraméterét is. *)
Arguments base_equiv {Sign A B f g}.

(* Ekvivalencia reláció regisztrálása *)
Add Parametric Relation (Sign : Type) (A B : b_ty) (f : @b_tm Sign) : (@base_typing Sign A f B) (@base_equiv Sign A B f f)
  reflexivity proved by (@BE_Refl Sign A B f)
  symmetry proved by (@BE_Sym Sign A B f f)
  transitivity proved by (@BE_Trans Sign A B f f f)
  as base_equiv_rel.

(* Morfizmus regisztrálása a kompozícióra *)
Add Parametric Morphism (Sign : Type) (A B C : b_ty) (f g : @b_tm Sign) : (@BT_Comp Sign A B C g f)
  with signature (@base_equiv Sign B C g g) ==> (@base_equiv Sign A B f f) ==> (@base_equiv Sign A C (b_comp g f) (b_comp g f))
  as comp_mor.
Proof.
  intros dg dg' Hg df df' Hf.
  apply BE_CongComp; auto.
Defined.

(* Morfizmus regisztrálása a párosításra *)
Add Parametric Morphism (Sign : Type) (A B C : b_ty) (f g : @b_tm Sign) : (@BT_Pair Sign A B C f g)
  with signature (@base_equiv Sign A B f f) ==> (@base_equiv Sign A C g g) ==> (@base_equiv Sign A (b_Prod B C) (b_pair f g) (b_pair f g))
  as pair_mor.
Proof. 
  intros df df' Hf dg dg' Hg.
  apply BE_CongPair; auto.
Defined.