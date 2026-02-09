Require Import List. 
Require Import HyperLogic.Logic.Hyper.Epsilon.Epsilon_Syntax.


Import ListNotations.

(* ================================================================= *)
(* 1. SZIGNATÚRÁK (A Világ Leírása)                                  *)
(* ================================================================= *)

Definition constant_type (c : ConstSym) : b_ty :=
  match c with
  | C_Zero => b_S
  | C_One  => b_S
  end.

Definition function_sig (f : FunSym) : (b_ty * b_ty) :=
  match f with
  | F_Plus => (b_Prod b_S b_S, b_S) 
  | F_Mult => (b_Prod b_S b_S, b_S)
  end.

(* Predikátumok szignatúrája: Milyen típusú argumentumokat várnak? *)
(* Most csak 'nat'-tal indexeljük a predikátumokat az egyszerűség kedvéért *)
(* Pl. 0-ás predikátum jelentheti az Egyenlőséget (Eq), ami két S-t vár. *)
Definition predicate_sig (p : nat) : list b_ty :=
  match p with
  | 0 => [b_S; b_S]  (* Eq(S, S) *)
  | _ => []          (* Egyébként üres *)
  end.

(* ================================================================= *)
(* 2. SEGÉDFÜGGVÉNY                                                  *)
(* ================================================================= *)

Fixpoint get_type (n : nat) (G : b_context) : option b_ty :=
  match G, n with
  | nil, _ => None
  | A :: _, 0 => Some A
  | _ :: G', S n' => get_type n' G'
  end.

(* ================================================================= *)
(* 3. KÖLCSÖNÖS TÍPUSOZÁS (MUTUAL TYPING)                            *)
(* ================================================================= *)

(* Három dolgot kell egyszerre definiálnunk:
   1. base_typing:      Termek helyessége
   2. formula_wf:       Formulák helyessége
   3. check_args:       Argumentumlisták helyessége (Predikátumokhoz) 
*)

Inductive base_typing : b_context -> b_tm -> b_ty -> Prop :=
  
  | BT_Var : forall G n A,
      get_type n G = Some A ->
      base_typing G (b_var n) A

  | BT_Const : forall G c,
      base_typing G (b_const c) (constant_type c)

  | BT_Unit : forall G,
      base_typing G b_unit b_Unit

  | BT_Pair : forall G t1 t2 A B,
      base_typing G t1 A ->
      base_typing G t2 B ->
      base_typing G (b_pair t1 t2) (b_Prod A B)
      
  | BT_Fst : forall G t A B,
      base_typing G t (b_Prod A B) ->
      base_typing G (b_fst t) A
      
  | BT_Snd : forall G t A B,
      base_typing G t (b_Prod A B) ->
      base_typing G (b_snd t) B

  | BT_Fun : forall G f t A B,
      function_sig f = (A, B) ->
      base_typing G t A ->
      base_typing G (b_fun f t) B

  (* --- A LEKÖTÉS (BINDING) --- *)
  (* A formula az (S :: G) kontextusban van, az eredmény a G-ben. *)
  | BT_Epsilon : forall G (A : h_ty),
      formula_wf (b_S :: G) A -> 
      base_typing G (b_epsilon A) b_S

with formula_wf : b_context -> h_ty -> Prop :=
  
  | WF_Unit : forall G,
      formula_wf G Ty_Unit

  | WF_Arr : forall G A B,
      formula_wf G A ->
      formula_wf G B ->
      formula_wf G (Ty_Arr A B)
      
  | WF_Prod : forall G A B,
      formula_wf G A ->
      formula_wf G B ->
      formula_wf G (Ty_Prod A B)

  (* --- ATOMI FORMULA --- *)
  (* P(t1, t2...) *)
  (* Ellenőrizzük, hogy a 'ts' termek típusai megfelelnek a szignatúrának *)
  | WF_Atom : forall G p ts,
      check_args G ts (predicate_sig p) ->
      formula_wf G (Ty_Atom p ts)

with check_args : b_context -> list b_tm -> list b_ty -> Prop :=
  
  | CA_Nil : forall G,
      check_args G [] []

  | CA_Cons : forall G t ts A As,
      base_typing G t A ->       (* A fej típusa stimmel *)
      check_args G ts As ->      (* A farok is stimmel *)
      check_args G (t :: ts) (A :: As).

(* Indukciós sémák generálása a bizonyításokhoz *)
Scheme base_typing_mut := Induction for base_typing Sort Prop
  with formula_wf_mut := Induction for formula_wf Sort Prop
  with check_args_mut := Induction for check_args Sort Prop.

Combined Scheme typing_mut_ind from base_typing_mut, formula_wf_mut, check_args_mut.