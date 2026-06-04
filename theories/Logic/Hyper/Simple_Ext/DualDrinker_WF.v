(* ========================================================================= *)
(* Logic/Hyper/Simple_Ext/DualDrinker_WF.v                           *)
(* ========================================================================= *)

Require Import HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple_Ext.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple_Ext.Notations.

(* Természetesen ide be kell importálni az eddigi H5_Pred_Setoid, FinObj 
   és Fin_HyperModel kódjaidat a korábbi DualDrinker fájlból! *)
(* Require Import ... *)

Open Scope logic_scope.

(* ------------------------------------------------------------------------- *)
(* 1. A Dual Drinker Formula (Az új, letisztult szintaxissal!)               *)
(* ------------------------------------------------------------------------- *)

(* Az általános Dual Drinker sémája. 
   Láthatod, milyen gyönyörű és olvasható a Notations_Simple használatával! *)
Definition Dual_Drinker {Sign : Type} (I D : b_ty) (Phi : @h_ty Sign) : @h_ty Sign :=
  ∃ D , ( (⇑ (∃ D , Phi)) ⇒ Phi ).

(* A specifikus P(x) atomi formula behelyettesítése *)
Definition P_x {Sign : Type} (I D : b_ty) : @h_ty Sign := Ty_Atom 0 π₂.

Definition DualDrinkerFormula {Sign : Type} (I D : b_ty) : @h_ty Sign :=
  Dual_Drinker I D (P_x I D).

(* ------------------------------------------------------------------------- *)
(* 2. Jólformáltság (Futtatható Lemma)                                       *)
(* ------------------------------------------------------------------------- *)

Lemma DualDrinker_WellFormed : forall {Sign : Type} I D, 
  I ⊢ @DualDrinkerFormula Sign I D wff.
Proof.
  intros Sign I D.
  unfold DualDrinkerFormula, Dual_Drinker, P_x.
  apply WF_Ex.
  apply WF_Arrow.
  
  - (* BAL OLDAL: ⇑(∃ D, P_x) *)
    (* A pullback bemegy a kvantor mögé, így a kontextus kétszeresen bővül (I ▹ D ▹ D) *)
    apply WF_Ex.
    eapply WF_Atom.
    
    (* A cél most: π₂ ∘ b_pullback_ext π₁ *)
    (* 1. Felbontjuk a kompozíciót *)
    eapply BT_Comp.
    + eapply BT_Snd. (* A legkülső π₂ gépelése *)
    + (* 2. Kibontjuk a b_pullback_ext definícióját (ami egy pár: ⟨f ∘ π₁, π₂⟩) *)
      unfold b_pullback_ext.
      eapply BT_Pair.
      * (* A pár bal oldala: π₁ ∘ π₁ *)
        eapply BT_Comp.
        -- eapply BT_Fst. (* Az eredeti f, ami nálunk π₁ *)
        -- eapply BT_Fst. (* A kiterjesztésből származó belső π₁ *)
      * (* A pár jobb oldala: π₂ *)
        apply BT_Snd.
        
  - (* JOBB OLDAL: P_x *)
    eapply WF_Atom. 
    apply BT_Snd.
Defined.