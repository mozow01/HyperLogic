(* ========================================================================= *)
(* Logic/Hyper/Epsilon/Critical_Epsilon_Provable.v                           *)
(* ========================================================================= *)

Require Import HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.

(* Import logical notations *)
Require Import HyperLogic.Logic.Hyper.Epsilon.Notations. 

(* Import substitution lemmas (the "engine room") *)
Require Import HyperLogic.Logic.Hyper.Epsilon.Epsilon_Syntax_Lemmas.

Require Import List.
Import ListNotations.

Open Scope logic_scope.

(* ------------------------------------------------------------------------- *)
(* Terms and Base Morphisms                                                  *)
(* ------------------------------------------------------------------------- *)

(* 'var0' represents the top local variable, which categorically corresponds 
   to the second projection (π₂) *)
Notation "'var0'" := π₂ : logic_scope.

(* ------------------------------------------------------------------------- *)
(* Definition of the "Dual Drinker" Paradox                                  *)
(* ------------------------------------------------------------------------- *)

(* The classic Drinker paradox is: ∃x (D(x) -> ∀y D(y)).
   Its dual is: ∃x ( (∃y D(y)) -> D(x) ).
   
   In our intuitionistic fibered system, the global statement (∃y) must be 
   lifted to the local level (⇑) before it can form an implication with 
   the local formula. 
*)
Definition Dual_Drinker {Sign : Type} `{SkolemMapping Sign} 
  (I D : b_ty) (Phi : @h_ty Sign) : @h_ty Sign :=
  ∃ D , ( (⇑ (∃ D , Phi)) ⇒ Phi ).

(* ------------------------------------------------------------------------- *)
(* Proof Automation Tactics                                                  *)
(* ------------------------------------------------------------------------- *)

(* Tactic to automatically solve well-formedness (wff) goals. *)
Ltac solve_wf :=
  try eassumption; 
  try (eapply WF_Ex; eassumption). 
  
(* Tactic to automatically infer and apply base typing judgments. *)
Ltac solve_bt := 
  eauto using BT_Const, BT_Id, BT_Fst, BT_Snd.

(* ------------------------------------------------------------------------- *)
(* Main Theorem: Provability of the Dual Drinker                             *)
(* ------------------------------------------------------------------------- *)

Lemma dual_drinker_surface_provable {Sign : Type} `{SkolemMapping Sign} 
  (I D : b_ty) (Phi : @h_ty Sign) (wf_Phi : (I ▹ D) ⊢ Phi wff ) : 
  (exists p, I ∙ [] ⊢h p : (Dual_Drinker I D Phi)).
Proof.
  eexists. unfold Dual_Drinker.
  
  (* GOAL: ⊢ ∃x . ( (∃y D(y)) ⇒ D(x) ) 
     INTUITION: Who should be this 'x'? Let it be the Epsilon witness! 
     Epsilon is the magical operator that 'picks an element for which D holds, 
     if such an element exists.' *)
  eapply HT_Ex_Intro with (f := ε D, Phi).
  - solve_bt. (* Categorical typing administration... *)
  
  - (* GOAL: ⊢ (∃y D(y)) ⇒ D(ε y. D(y)) 
       STEP: Assume the left side (Implication introduction). *)
    eapply HT_Lam; fold (@form_pullback Sign).

    (* GOAL: [ ∃y D(y) ] ⊢ D(ε y. D(y))
       STEP: Eliminate the hypothesis! If 'there exists a y who drinks', 
       let's call them 'var0'. From now on, in our local context, 
       we have a specific drinker (var0). *)
    eapply HT_Ex_Elim.
    + (* SUB-GOAL 1: Verify that our premise was indeed [ ∃y D(y) ].
         STEP: Simply recall the hypothesis from the context (HT_Var0). *)
      eapply HT_Conv.
      * apply HT_Var0.
      * (* ... Categorical noise: Prove that pulling back the variable 
           does not change the meaning of the formula (FE_Pullback_Id) ... *)
        eapply FE_Trans.
        1: { eapply FE_Pullback_Comp. - solve_bt. - eapply BT_Pair; solve_bt. - solve_wf. }
        eapply FE_Trans.
        2: { apply FE_Pullback_Id. solve_wf. }
        eapply FE_Pullback_Cong. -- apply (BE_Comp_Pair_Id_Fst_Correct BT_Const). -- solve_wf.

   + (* SUB-GOAL 2: [ D(var0) ] ⊢ D(ε y. D(y))
         INTUITION: This is the heart of the proof! We know var0 drinks. 
         We must show that the person chosen by Epsilon also drinks. 
         STEP: Apply the Epsilon Axiom (HT_Eps_Intro)! This states that if you 
         can provide ANY witness (in this case, var0), then the formula 
         automatically holds for the Epsilon term. *)
      eapply HT_Conv.
      * (* Pass 'var0' as the explicit witness for the Epsilon axiom. *)
        eapply HT_Eps_Intro with (f := var0) (Phi := form_pullback (b_pullback_ext π₁) Phi).
        -- solve_bt.
        -- (* Recall the fact that var0 drinks. *)
           eapply HT_Conv.
           ++ apply HT_Var0.
           ++ (* ... Categorical noise: Substitution cleanup ... *)
              eapply FE_Sym. 
              apply FE_Pullback_Ext_Fst_Snd. solve_wf.

      * (* ... Categorical noise: Beck-Chevalley lifting. Since var0 
           lives in the local context, the formula must be synchronized 
           with the base context. ... *)
        eapply FE_Eps_Lift with (J := I).
        -- solve_bt.
        -- solve_wf.
Defined.