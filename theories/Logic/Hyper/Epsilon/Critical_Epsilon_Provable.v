(** Provability of the dual drinker formula in the epsilon-only calculus. *)

Require Import HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.

Require Import HyperLogic.Logic.Hyper.Epsilon.Notations. 

Require Import HyperLogic.Logic.Hyper.Epsilon.Epsilon_Syntax_Lemmas.

Require Import List.
Import ListNotations.

Open Scope logic_scope.

(* [var0] is the second projection from the extended base context. *)
Notation "'var0'" := π₂ : logic_scope.

(** The dual drinker formula is [exists x, (exists y, D y) -> D x].
    Its existential premise is weakened into the local fiber before forming
    the implication. *)
Definition Dual_Drinker {Sign : Type} `{SkolemMapping Sign} 
  (I D : b_ty) (Phi : @h_ty Sign) : @h_ty Sign :=
  ∃ D , ( (⇑ (∃ D , Phi)) ⇒ Phi ).

Ltac solve_wf :=
  try eassumption; 
  try (eapply WF_Ex; eassumption). 
  
Ltac solve_bt := 
  eauto using BT_Const, BT_Id, BT_Fst, BT_Snd.

Lemma dual_drinker_surface_provable {Sign : Type} `{SkolemMapping Sign} 
  (I D : b_ty) (Phi : @h_ty Sign) (wf_Phi : (I ▹ D) ⊢ Phi wff ) : 
  (exists p, I ∙ [] ⊢h p : (Dual_Drinker I D Phi)).
Proof.
  eexists. unfold Dual_Drinker.
  
  eapply HT_Ex_Intro with (f := ε D, Phi).
  - solve_bt.
  
  -
    eapply HT_Lam; fold (@form_pullback Sign).

    eapply HT_Ex_Elim.
    +
      eapply HT_Conv.
      * apply HT_Var0.
      *
        eapply FE_Trans.
        1: { eapply FE_Pullback_Comp. - solve_bt. - eapply BT_Pair; solve_bt. - solve_wf. }
        eapply FE_Trans.
        2: { apply FE_Pullback_Id. solve_wf. }
        eapply FE_Pullback_Cong. -- apply (BE_Comp_Pair_Id_Fst_Correct BT_Const). -- solve_wf.

   +
      eapply HT_Conv.
      * (* The epsilon rule transfers the explicit witness to the selected term. *)
        eapply HT_Eps_Intro with (f := var0) (Phi := form_pullback (b_pullback_ext π₁) Phi).
        -- solve_bt.
        --
           eapply HT_Conv.
           ++ apply HT_Var0.
           ++
              eapply FE_Sym. 
              apply FE_Pullback_Ext_Fst_Snd. solve_wf.

      *
        eapply FE_Eps_Lift with (J := I).
        -- solve_bt.
        -- solve_wf.
Defined.
