Require Import List.
Require Import PeanoNat.
Import ListNotations.

Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Logic.Base.Simple.Base_Typing.
Require Import HyperLogic.Logic.Base.Simple.Base_Equiv.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Substitution.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Typing.

(* Induktív reláció: entails G Phi Psi
   Jelölés: G | Phi |- Psi

   Jelentése: A 'G' bázis-kontextusban (ahol a változók élnek),
   ha a 'Phi' formula igaz, akkor a 'Psi' formula is igaz.

   Ez felel meg a Fiber kategória morfizmusainak.
*)

Inductive entails (G : b_context) : h_ty -> h_ty -> Prop :=

  (* --- 1. Structural Rules (Identity & Cut) --- *)

  | L_Id : forall A,
      formula_wf G A -> (* Csak jól formált formulákon *)
      entails G A A

  | L_Comp : forall A B C,
      entails G A B ->
      entails G B C ->
      entails G A C

  (* --- 2. Propositional Logic (BiCCC Rules) --- *)

  (* TRUE (Top) *)
  | L_Top_Intro : forall A,
      formula_wf G A ->
      entails G A Ty_Unit

  (* FALSE (Bottom) *)
  | L_Bot_Elim : forall A,
      formula_wf G A ->
      entails G Ty_Void A

  (* AND (Product) *)
  | L_And_Intro : forall A B C,
      entails G C A ->
      entails G C B ->
      entails G C (Ty_Prod A B)

  | L_And_E1 : forall A B,
      formula_wf G B ->
      entails G (Ty_Prod A B) A

  | L_And_E2 : forall A B,
      formula_wf G A ->
      entails G (Ty_Prod A B) B

  (* OR (Sum) *)
  | L_Or_Intro1 : forall A B,
      formula_wf G B ->
      entails G A (Ty_Sum A B)

  | L_Or_Intro2 : forall A B,
      formula_wf G A ->
      entails G B (Ty_Sum A B)

  | L_Or_Elim : forall A B C,
      entails G A C ->
      entails G B C ->
      entails G (Ty_Sum A B) C

  (* IMPLICATION (Exponential) *)
  (* Adjungálás: (C /\ A -> B) <==> (C -> (A => B)) *)

  | L_Arr_Intro : forall A B C,
      entails G (Ty_Prod C A) B ->  (* Curry *)
      entails G C (Ty_Arr A B)

  | L_Arr_Elim : forall A B,
      formula_wf G (Ty_Arr A B) ->
      entails G (Ty_Prod (Ty_Arr A B) A) B (* Eval *)

  (* --- 3. Quantifiers (The Typeability Flavor!) --- *)

  (* FORALL (Universal Quantifier) *)
  (* Jobb adjungáltja a Weakening-nek (Shift) *)

  | L_All_Intro : forall A Phi Psi,
      (* Ha kiterjesztett kontextusban (A::G) a 'Psi' (eltolva) implikálja 'Phi'-t... *)
      entails (A :: G) (h_shift 1 0 Psi) Phi ->
      (* ...akkor az alap kontextusban 'Psi' implikálja 'Minden A. Phi'-t *)
      entails G Psi (Ty_All A Phi)

  | L_All_Elim : forall A Phi t,
      (* Typeability Check! 't' legyen érvényes term 'A' típussal G-ben *)
      base_typing G t A ->
      (* All A. Phi |- Phi[t/0] *)
      entails G (Ty_All A Phi) (h_subst 0 t Phi)

  (* EXISTS (Existential Quantifier) *)
  (* Bal adjungáltja a Weakening-nek (Shift) *)

  | L_Ex_Intro : forall A Phi t,
      (* Typeability Check! *)
      base_typing G t A ->
      (* Phi[t/0] |- Ex A. Phi *)
      entails G (h_subst 0 t Phi) (Ty_Ex A Phi)

  | L_Ex_Elim : forall A Phi Psi,
      (* Ha kiterjesztett kontextusban 'Phi' implikálja 'Psi'-t (eltolva)... *)
      entails (A :: G) Phi (h_shift 1 0 Psi) ->
      (* ...akkor 'Ex A. Phi' implikálja 'Psi'-t *)
      entails G (Ty_Ex A Phi) Psi

  (* --- 4. Conversion Rule (Interaction with Base Equality) --- *)

  (* Ha két term egyenlő a Base-ben (pl. beta redukció),
     akkor a rájuk épülő atomi állítások is ekvivalensek. *)
  | L_Cast : forall p ts1 ts2,
      (* Ha a termlisták elemenként egyenlőek... (ezt definiálni kellene, de most egyszerűsítünk) *)
      (* Itt egy egyszerűsített szabály: ha a szintaxisban csere történik *)
      ts1 = ts2 -> (* Ez placeholder a base_equiv listára *)
      entails G (Ty_Atom p ts1) (Ty_Atom p ts2).