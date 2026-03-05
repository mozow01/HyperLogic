Require Import Coq.Classes.Morphisms.
Require Import List Arith PeanoNat Lia.
Import ListNotations.

(* Kategóriaelméleti alapok *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import HyperLogic.Cat.Fibration.

(* Szintaxis és Bázis Szemantika *)
Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Semantics.Simple.Base_Simple_Soundness.
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Lemmas.
Require Import HyperLogic.Semantics.Simple.Simple_Soundness.


(* =========================================================================
   1. TÁBLÁZAT: SZINTAXIS VS. SZEMANTIKA (HT_All_Intro)
   =========================================================================
   Melyik HyperLogic szintaktikai elem minek felel meg a Fibrációban?

   | Szintaxis (HyperLogic)     | Szemantika (Hiperdoktrína)                   | Magyarázat / Jelentés                                 |
   |----------------------------|----------------------------------------------|-------------------------------------------------------|
   | I, A : b_ty                | I, A ∈ Obj(B)                                | Bázis típusok (Az I a meglévő kontextus, A az új)     |
   | G : h_context              | Γ ∈ Obj(Fiber(I))                            | A feltevéseink (logikai kontextus) az I bázison       |
   | Phi : h_ty                 | Φ ∈ Obj(Fiber(I × A))                        | A bizonyítandó formula (függ I-től és A-tól is)       |
   | b_fst                      | π₁ : I × A → I                               | Bázis projekció (A régi változók megtartása)          |
   | ctx_pullback b_fst G       | π₁^* Γ                                       | A logikai feltevések "felhúzása" az új, tágabb térbe  |
   | Ty_All A Phi               | Π_{π₁} Φ                                     | Univerzális kvantor (A π₁^* jobb adjungáltja)         |
   | HT_All_Intro (maga a tétel)| Hom(π₁^* Γ, Φ) ≅ Hom(Γ, Π_{π₁} Φ)            | Az Adjungálás definíciója (balról jobbra olvasva)     |
   ========================================================================= *)

(* =========================================================================
   2. KOMMUTATÍV DIAGRAM: A KITERJESZTÉS ÉS KVANTIFIKÁLÁS GEOMETRIÁJA
   =========================================================================
   
   BÁZIS KATEGÓRIA (B) - Itt élnek a változók tartományai
   ------------------------------------------------------
               I × A     <-- Az új "bővített" kontextus (a régi I + az új A változó)
                 |
                 | π₁    <-- A projekció, ami eldobja az A-t és visszatér I-be
                 v
                 I       <-- Az eredeti változó-kontextusunk

   SZÁLAK KATEGÓRIÁI (Fibers) - Itt élnek a formulák és a bizonyítások
   -------------------------------------------------------------------
   Fiber(I × A) :     π₁^* Γ -------- p -------> Φ    <-- PREMISSZA: Van egy 'p' bizonyításunk a tágabb térben.
                        ^                        |
                        |                        |
         Visszahúzás    | π₁^* | Π_{π₁} (Jobb adjungált / Kvantor)
         (Weakening)    |                        |
                        |                        v
   Fiber(I)     :       Γ ------ all_intro ----> Π_{π₁} Φ  <-- KONKLÚZIÓ: Ebből kapunk egy bizonyítást a szűkebb térben.
   
   Magyarázat: A π₁^* és a Π_{π₁} adjungált párt alkotnak (π₁^* ⊣ Π_{π₁}). 
   Ez a matematikai törvény garantálja, hogy a fenti két (p és all_intro) nyíl "kicserélhető" egymással!
   ========================================================================= *)


Section Quantifier_Introduction_Explanation.

  Context {C : SetoidCategory} {CC : CartesianCategory C}
          {GF : GoodFibration C}.
          
  (* Bázis típusok: I (ahol most vagyunk) és A (a bevezetendő új változó típusa) *)
  Variable I A : @obj C.
  
  (* ----------------------------------------------------------------- *)
  (* 3. JAVÍTOTT ÉS BIZTONSÁGOS RÖVIDÍTÉSEK (NOTATIONS)                *)
  (* ----------------------------------------------------------------- *)

  (* 1. A π₁ projekció: I x A -> I *)
  Notation "'π₁'" := (@prod_fst C CC I A) (at level 0).

  (* 2. Visszahúzott formula (Weakening). Kifejezetten a formulára (X) alkalmazzuk! *)
  Notation "g '^*' X" := (@fobj _ _ (Pullback g) X) (at level 20, right associativity).

  (* 3. Univerzális Kvantor (Jobb adjungált). Szintén expliciten a formulára (X) alkalmazva! *)
  Notation "'Π_(' g ')' X" := (@right_adj_obj _ _ _ (pullback_has_right_adjoint g) X) (at level 20, right associativity).

  (* ----------------------------------------------------------------- *)
  (* 4. A HT_All_Intro SZEMANTIKAI BIZONYÍTÁSA                         *)
  (* ----------------------------------------------------------------- *)
  
  (* G a logikai kontextusunk (feltevéseink) az eredeti I bázison *)
  Variable G : @obj (Fiber I).
  
  (* Phi a formula, amit be akarunk bizonyítani, de ez már függhet az I-től és az A-tól is! 
     Ezért ez a Fiber(I x A) szálban él. *)
  Variable Phi : @obj (Fiber (prod I A)).

  (* TÉTEL (HT_All_Intro):
     Ha a felhúzott kontextusból (Weakening) tudjuk bizonyítani a Phi-t az I x A felett, 
     akkor az eredeti kontextusból tudjuk bizonyítani a ∀A. Φ-t az I felett.
  *)
  Lemma semantic_All_Intro : 
    (* Premissza: A felhúzott kontextus implikálja a Formulát az I x A szálban *)
    hom (π₁ ^* G) Phi -> 
    
    (* Konklúzió: Az eredeti kontextus implikálja a kvantált formulát az I szálban *)
    hom G (Π_(π₁) Phi).
  Proof.
    Admitted.

End Quantifier_Introduction_Explanation.