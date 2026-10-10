
Require Import HyperLogic.Logic.Base.Simple_Ext.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple_Ext.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple_Ext.Notations.

(** Legacy well-formedness check for the dual drinker formula. *)
(* Require Import ... *)

Open Scope logic_scope.


Definition Dual_Drinker {Sign : Type} (I D : b_ty) (Phi : @h_ty Sign) : @h_ty Sign :=
  ∃ D , ( (⇑ (∃ D , Phi)) ⇒ Phi ).

Definition P_x {Sign : Type} (I D : b_ty) : @h_ty Sign := Ty_Atom 0 π₂.

Definition DualDrinkerFormula {Sign : Type} (I D : b_ty) : @h_ty Sign :=
  Dual_Drinker I D (P_x I D).


Lemma DualDrinker_WellFormed : forall {Sign : Type} I D, 
  I ⊢ @DualDrinkerFormula Sign I D wff.
Proof.
  intros Sign I D.
  unfold DualDrinkerFormula, Dual_Drinker, P_x.
  apply WF_Ex.
  apply WF_Arrow.
  
  -
    apply WF_Ex.
    eapply WF_Atom.
    
    eapply BT_Comp.
    + eapply BT_Snd.
    +
      unfold b_pullback_ext.
      eapply BT_Pair.
      *
        eapply BT_Comp.
        -- eapply BT_Fst.
        -- eapply BT_Fst.
      *
        apply BT_Snd.
        
  -
    eapply WF_Atom. 
    apply BT_Snd.
Defined.