
Require Import HyperLogic.Logic.Base.Simple_Ext.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple_Ext.Hyper_Syntax.

Declare Scope logic_scope.
Delimit Scope logic_scope with logic.
Open Scope logic_scope.


Notation "I '▹' D" := (b_Prod I D) (at level 40, left associativity) : logic_scope.

Notation "I '⊢b' f ':' A" := (base_typing I f A) (at level 99, f at next level, no associativity) : logic_scope.


Notation "f '∘' g" := (b_comp f g) (at level 40, left associativity) : logic_scope.
Notation "'⟨' f ',' g '⟩'" := (b_pair f g) (at level 0) : logic_scope.
Notation "'π₁'" := b_fst : logic_scope.
Notation "'π₂'" := b_snd : logic_scope.
Notation "'id'" := b_id : logic_scope.

Notation "I '⊢b' f '≡' g '⟶' J 'by' df '&' dg" := (@base_equiv _ I J f g df dg) 
  (at level 99, f at next level, g at next level, no associativity) : logic_scope.


Notation "⊤" := Ty_Unit : logic_scope.
Notation "⊥" := Ty_Void : logic_scope.
Notation "A ∧ B" := (Ty_Prod A B) (at level 80, right associativity) : logic_scope.
Notation "A ∨ B" := (Ty_Sum A B) (at level 85, right associativity) : logic_scope.
Notation "A ⇒ B" := (Ty_Arrow A B) (at level 90, right associativity) : logic_scope.

(** Surface notation for the legacy signature-indexed syntax. *)

Notation "'∀' D , Phi" := (Ty_All D Phi) (at level 50) : logic_scope.
Notation "'∃' D , Phi" := (Ty_Ex D Phi) (at level 50) : logic_scope.


(* Formula substitution abbreviates reindexing along the extended map. *)
Notation "Phi [ t ]" := (form_pullback (b_pair b_id t) Phi) (at level 40, left associativity) : logic_scope.

Notation "⇑ Phi" := (form_pullback b_fst Phi) (at level 40) : logic_scope.

Notation "Phi [ f ]*" := (form_pullback f Phi) (at level 40, left associativity) : logic_scope.


Notation "I '⊢' Phi 'wff'" := (WellFormed I Phi) (at level 99, no associativity) : logic_scope.

Notation "I '⊢' Phi '≡' Psi" := (form_equiv I Phi Psi) (at level 99, no associativity) : logic_scope.


(* [I ∙ G ⊢h p : Phi] types [p] under base [I] and hypotheses [G]. *)
Notation "I '∙' G '⊢h' p ':' Phi" := (h_typing I G p Phi) (at level 99, p at next level, no associativity) : logic_scope.