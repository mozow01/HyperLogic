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
      
(* ================================================================= *)
(* DERIVATION TREES (DATA LAYER - Set)                               *)
(* ================================================================= *)

Inductive entails_derivation : b_context -> h_ty -> h_ty -> Set :=

  (* --- 1. Structural Rules (Identity & Cut) --- *)
  | LD_Id : forall G A,
      formula_derivation G A -> 
      entails_derivation G A A

  | LD_Comp : forall G A B C,
      formula_derivation G B -> (* ÚJ: A köztes B formula bizonyítása *)
      entails_derivation G A B ->
      entails_derivation G B C ->
      entails_derivation G A C

  (* --- 2. Propositional Logic (BiCCC Rules) --- *)
  | LD_Top_Intro : forall G A,
      formula_derivation G A ->
      entails_derivation G A Ty_Unit

  | LD_Bot_Elim : forall G A,
      formula_derivation G A ->
      entails_derivation G Ty_Void A

  | LD_And_Intro : forall G A B C,
      entails_derivation G C A ->
      entails_derivation G C B ->
      entails_derivation G C (Ty_Prod A B)

  | LD_And_E1 : forall G A B,
      formula_derivation G B -> (* ÚJ: A kidobott B formula bizonyítása *)
      entails_derivation G (Ty_Prod A B) A

  | LD_And_E2 : forall G A B,
      formula_derivation G A -> (* ÚJ: A kidobott A formula bizonyítása *)
      entails_derivation G (Ty_Prod A B) B

  | LD_Or_Intro1 : forall G A B,
      formula_derivation G B -> (* ÚJ: A hozzáadott B formula bizonyítása *)
      entails_derivation G A (Ty_Sum A B)

  | LD_Or_Intro2 : forall G A B,
      formula_derivation G A -> (* ÚJ: A hozzáadott A formula bizonyítása *)
      entails_derivation G B (Ty_Sum A B)

  | LD_Or_Elim : forall G A B C,
      entails_derivation G A C ->
      entails_derivation G B C ->
      entails_derivation G (Ty_Sum A B) C

  | LD_Arr_Intro : forall G A B C,
      entails_derivation G (Ty_Prod C A) B ->
      entails_derivation G C (Ty_Arr A B)

  | LD_Arr_Elim : forall G A B,
      formula_derivation G (Ty_Arr A B) -> (* ÚJ: Az implikáció bizonyítása *)
      entails_derivation G (Ty_Prod (Ty_Arr A B) A) B

  (* --- 3. Quantifiers --- *)
  | LD_All_Intro : forall G A Phi Psi,
      entails_derivation (A :: G) (h_shift 1 0 Psi) Phi ->
      entails_derivation G Psi (Ty_All A Phi)

  | LD_All_Elim : forall G A Phi t,
      base_typing G t A ->
      formula_derivation G (h_subst 0 t Phi) -> (* ÚJ: A helyettesített formula bizonyítása *)
      entails_derivation G (Ty_All A Phi) (h_subst 0 t Phi)

  | LD_Ex_Intro : forall G A Phi t,
      base_typing G t A ->
      formula_derivation G (h_subst 0 t Phi) -> (* ÚJ: A helyettesített formula bizonyítása *)
      entails_derivation G (h_subst 0 t Phi) (Ty_Ex A Phi)

  | LD_Ex_Elim : forall G A Phi Psi,
      formula_derivation G (Ty_Ex A Phi) -> (* ÚJ: Kényelmi okokból *)
      entails_derivation (A :: G) Phi (h_shift 1 0 Psi) ->
      entails_derivation G (Ty_Ex A Phi) Psi

  (* --- 4. Conversion Rule --- *)
  | LD_Cast : forall G p ts1 ts2,
      ts1 = ts2 ->
      args_derivation G ts1 (predicate_sig p) -> (* ÚJ *)
      args_derivation G ts2 (predicate_sig p) -> (* ÚJ *)
      entails_derivation G (Ty_Atom p ts1) (Ty_Atom p ts2).

(* ================================================================= *)
(* BRIDGES (Set -> Prop)                                             *)
(* ================================================================= *)

Fixpoint forget_entails {G Phi Psi} (d : entails_derivation G Phi Psi) : entails G Phi Psi :=
  match d with
  | LD_Id _ A fd => L_Id _ A (forget_formula fd)
  | LD_Comp _ A B C fd d1 d2 => L_Comp _ A B C (forget_entails d1) (forget_entails d2)
  | LD_Top_Intro _ A fd => L_Top_Intro _ A (forget_formula fd)
  | LD_Bot_Elim _ A fd => L_Bot_Elim _ A (forget_formula fd)
  | LD_And_Intro _ A B C d1 d2 => L_And_Intro _ A B C (forget_entails d1) (forget_entails d2)
  | LD_And_E1 _ A B fd => L_And_E1 _ A B (forget_formula fd)
  | LD_And_E2 _ A B fd => L_And_E2 _ A B (forget_formula fd)
  | LD_Or_Intro1 _ A B fd => L_Or_Intro1 _ A B (forget_formula fd)
  | LD_Or_Intro2 _ A B fd => L_Or_Intro2 _ A B (forget_formula fd)
  | LD_Or_Elim _ A B C d1 d2 => L_Or_Elim _ A B C (forget_entails d1) (forget_entails d2)
  | LD_Arr_Intro _ A B C d1 => L_Arr_Intro _ A B C (forget_entails d1)
  | LD_Arr_Elim _ A B fd => L_Arr_Elim _ A B (forget_formula fd)
  | LD_All_Intro _ A Phi Psi d1 => L_All_Intro _ A Phi Psi (forget_entails d1)
  | LD_All_Elim _ A Phi t bt fd_subst => L_All_Elim _ A Phi t bt
  | LD_Ex_Intro _ A Phi t bt fd_subst => L_Ex_Intro _ A Phi t bt
  | LD_Ex_Elim _ A Phi Psi fd_ex d1 => L_Ex_Elim _ A Phi Psi (forget_entails d1)
  | LD_Cast _ p ts1 ts2 eq ad1 ad2 => L_Cast _ p ts1 ts2 eq
  end.