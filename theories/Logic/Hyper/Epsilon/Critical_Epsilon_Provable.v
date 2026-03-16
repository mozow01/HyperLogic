(* Logic/Hyper/Epsilon/Critical_Epsilon_Provable.v *)
 
Require Import HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.

(* Behúzzuk az új, elegáns logikai jelöléseket *)
Require Import HyperLogic.Logic.Hyper.Epsilon.Notations. 

(* Behúzzuk a "géptermet" (a kategóriaelméleti helyettesítési lemmákat) *)
Require Import HyperLogic.Logic.Hyper.Epsilon.Epsilon_Syntax_Lemmas.

Require Import List.
Import ListNotations.

Open Scope logic_scope.

(* --- TERMEK ÉS BÁZIS MORFIZMUSOK --- *)
(* A 'var0' a legfelső lokális változó, ami kategóriaelméletileg a második projekció (π₂) *)
Notation "'var0'" := π₂ : logic_scope.

(* ================================================================= *)
(* A "DUAL DRINKER" PARADOXON DEFINÍCIÓJA                            *)
(* ================================================================= *)
 
(* A klasszikus Drinker paradoxon: ∃x (D(x) -> ∀y D(y))
   Ennek duálisa: ∃x ( (∃y D(y)) -> D(x) )
   A mi intuicionista fibrációs rendszerünkben a globális állítást (∃y) "fel kell emelnünk"
   a lokális szintre (⇑), mielőtt implikációba tesszük a lokális formulával. 
*)
Definition Dual_Drinker {Sign : Type} `{SkolemMapping Sign} (I D : b_ty) (Phi : @h_ty Sign) : @h_ty Sign :=
  ∃ D , ( (⇑ (∃ D , Phi)) ⇒ Phi ).

(* ================================================================= *)
(* A FŐ TÉTEL: DUAL DRINKER BIZONYÍTHATÓSÁG                          *)
(* ================================================================= *)


Lemma dual_drinker_surface_provable {Sign : Type} `{SkolemMapping Sign} 
  (I D : b_ty) (Phi : @h_ty Sign) (wf_Phi : (I ▹ D) ⊢ Phi wff ) : 
  (exists p, I ∙ [] ⊢h p : (Dual_Drinker I D Phi)).
Proof.
  eexists. unfold Dual_Drinker.
  
  (* Egzisztenciális bevezetés a bázison: A tanú a mi Epszilon konstansunk! *)
  eapply HT_Ex_Intro with (f := ε D, Phi).
  - apply BT_Const.
  - (* 1. LÉPÉS: Lambda (Beteszi a hipotézisek közé a ⇑(∃ D, Phi)-t) *)
    eapply HT_Lam.

    (* 2. LÉPÉS: Egzisztenciális Elimináció (Kibontjuk a ∃ D, Phi hipotézist) *)
    eapply HT_Ex_Elim.
    + (* A premissza letisztítása az epszilon behelyettesítés után *)
      eapply HT_Conv.
      * apply HT_Var0.
      * eapply FE_Trans.
        1: { (* KOMPOZÍCIÓ: Visszahúzás összevonása a helyettesítéssel *)
             eapply FE_Pullback_Comp.
             - apply (@BT_Fst Sign I D). 
             - eapply BT_Pair. { apply BT_Id. } { apply BT_Const. }
             - apply WF_Ex. exact wf_Phi. 
           }
        eapply FE_Trans.
        2: { (* IDENTITÁS: Az eltüntetett identitás morfizmus logikai megfelelője *)
             apply FE_Pullback_Id.
             apply WF_Ex. exact wf_Phi. 
           }
        (* KONGRUENCIA: Itt használjuk a kategóriaelméleti axiómát *)
        eapply FE_Pullback_Cong.
        -- apply (BE_Comp_Pair_Id_Fst_Correct BT_Const).
        -- apply WF_Ex. exact wf_Phi.

    + (* 3. LÉPÉS: A lokális kontextus feldolgozása az Epszilon bevezetéssel *)
      eapply HT_Conv.
      * (* A var0 (lokális x) tanú átadása! A formula kiterjesztve várja! 
         
                  *)
        eapply HT_Eps_Intro with (f := var0) (Phi := ( form_pullback (b_pullback_ext π₁) Phi) ).
        -- apply (@BT_Snd Sign I D).
        -- eapply HT_Conv.
           ++ apply HT_Var0.
           ++ eapply FE_Sym.
              (* VARÁZSLAT: A tegnapi 30 soros kategóriaelméleti daráló helyett ez az egyetlen sor! *)
              apply FE_Pullback_Ext_Fst_Snd. exact wf_Phi.

      * (* 4. LÉPÉS: Beck-Chevalley invariancia (Epszilon Lifting) *)
        eapply FE_Eps_Lift with (J := I).
        -- apply (@BT_Fst Sign I D).
        -- exact wf_Phi.

Unshelve.
  all: try exact (b_Prod I D); auto.
Defined.
