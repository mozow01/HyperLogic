(* theories/Logic/Hyper/Epsilon/Notations.v *)

Require Import HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.

(* Új scope a hagyományos logikai jelölésekhez *)
Declare Scope logic_scope.
Delimit Scope logic_scope with logic.
Open Scope logic_scope.

(* ================================================================= *)
(* 1. BÁZIS ÉS KIFEJEZÉSEK (Termek tipizálása)                       *)
(* ================================================================= *)

(* Kontextus kiterjesztése (Comprehension) *)
Notation "I '▹' D" := (b_Prod I D) (at level 40, left associativity) : logic_scope.

(* Bázis tipizálás: "Az I kontextusban az f kifejezés A típusú" *)
Notation "I '⊢b' f ':' A" := (base_typing I f A) (at level 99, f at next level, no associativity) : logic_scope.

(* ================================================================= *)
(* 1.5. BÁZIS MORFIZMUSOK ÉS EKVIVALENCIA (Kategóriaelméleti szépítés) *)
(* ================================================================= *)

Notation "f '∘' g" := (b_comp f g) (at level 40, left associativity) : logic_scope.
Notation "'⟨' f ',' g '⟩'" := (b_pair f g) (at level 0) : logic_scope.
Notation "'π₁'" := b_fst : logic_scope.
Notation "'π₂'" := b_snd : logic_scope.
Notation "'id'" := b_id : logic_scope.

(* Vizuálisan elválasztjuk a logikai állítást a gépelési bizonyítékoktól *)
Notation "I '⊢b' f '≡' g '⟶' J 'by' df '&' dg" := (@base_equiv _ I J f g df dg)
  (at level 99, f at next level, g at next level, no associativity) : logic_scope.

(* ================================================================= *)
(* 2. LOGIKAI KÖTŐSZAVAK (Propozicionális szint)                     *)
(* ================================================================= *)

Notation "⊤" := Ty_Unit : logic_scope.
Notation "⊥" := Ty_Void : logic_scope.
Notation "A ∧ B" := (Ty_Prod A B) (at level 80, right associativity) : logic_scope.
Notation "A ∨ B" := (Ty_Sum A B) (at level 85, right associativity) : logic_scope.
Notation "A ⇒ B" := (Ty_Arrow A B) (at level 90, right associativity) : logic_scope.

(* ================================================================= *)
(* 3. KVANTOROK ÉS AZ EPSZILON OPERÁTOR                              *)
(* ================================================================= *)

Notation "'∀' D , Phi" := (Ty_All D Phi) (at level 50) : logic_scope.
Notation "'∃' D , Phi" := (Ty_Ex D Phi) (at level 50) : logic_scope.

(* Az Epszilon szimbólum elrejti a Skolem-indexálást és a konstanst *)
Notation "'ε' D , Phi" := (b_const D (skolem_index D Phi)) (at level 50) : logic_scope.

(* ================================================================= *)
(* 4. HELYETTESÍTÉS ÉS GYENGÍTÉS (A fibrációk elrejtése)             *)
(* ================================================================= *)

(* Hagyományos behelyettesítés: Phi[t] a <id, t> pullback helyett *)
Notation "Phi [ t ]" := (form_pullback (b_pair b_id t) Phi) (at level 40, left associativity) : logic_scope.

(* Gyengítés (Lifting/Weakening): Amikor egy új változó kerül a kontextusba *)
Notation "⇑ Phi" := (form_pullback b_fst Phi) (at level 40) : logic_scope.

(* Explicit pullback (ha mégis egy általános f helyettesítés kell) *)
Notation "Phi [ f ]*" := (form_pullback f Phi) (at level 40, left associativity) : logic_scope.

(* ================================================================= *)
(* 5. JÓL-FORMÁLTSÁG (WFF) ÉS EKVIVALENCIA                           *)
(* ================================================================= *)

(* "Az I kontextusban a Phi egy jól formált formula" *)
Notation "I '⊢' Phi 'wff'" := (WellFormed I Phi) (at level 99, no associativity) : logic_scope.

(* Logikai ekvivalencia a bázis felett *)
Notation "I '⊢' Phi '≡' Psi" := (form_equiv I Phi Psi) (at level 99, no associativity) : logic_scope.

(* ================================================================= *)
(* 6. BIZONYÍTHATÓSÁG (A klasszikus Turnstile)                       *)
(* ================================================================= *)

(* I ∙ G ⊢h p : Phi
   Olvasat: Az I bázis kontextusban, a G logikai hipotézisek mellett,
   a p bizonyításterm igazolja a Phi formulát.
*)
Notation "I '∙' G '⊢h' p ':' Phi" := (h_typing I G p Phi) (at level 99, p at next level, no associativity) : logic_scope.