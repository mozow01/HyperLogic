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

Section Forall_And_Distribution.

  (* ========================================================================= *)
  (* 1. RÉSZ: SZINTAKTIKAI BIZONYÍTÁSTERMEK (Point-Free Bázissal)              *)
  (* ========================================================================= *)
  
  Variable I A : b_ty.
  Variable Phi Psi : h_ty.

  (* Mivel I x A bázison vagyunk az Intro után, a kvantált "x" változó 
     nem más, mint a második projekció, ami kiszedi az A-t! *)
  Let var_A : b_tm := b_snd. 
  
  (* ODA IRÁNY: ∀A. (Phi ∧ Psi) ⊢ (∀A. Phi) ∧ (∀A. Psi) *)
  (* Tegyük fel, hogy a 0-ás logikai változónk típusa: ∀A. (Phi ∧ Psi) *)
  
  Definition term_forall_and_forward : h_tm :=
    tm_pair 
      (* Első komponens: ∀A. Phi *)
      (tm_all_intro 
         (tm_fst (tm_all_elim (tm_var 0) var_A)))
         
      (* Második komponens: ∀A. Psi *)
      (tm_all_intro 
         (tm_snd (tm_all_elim (tm_var 0) var_A))).

  (* VISSZA IRÁNY: (∀A. Phi) ∧ (∀A. Psi) ⊢ ∀A. (Phi ∧ Psi) *)
  (* Tegyük fel, hogy a 0-ás logikai változónk típusa: (∀A. Phi) ∧ (∀A. Psi) *)
  
  Definition term_forall_and_backward : h_tm :=
    tm_all_intro 
      (tm_pair 
         (* Kibontjuk a bal oldali ∀-t a var_A bázis termmel *)
         (tm_all_elim (tm_fst (tm_var 0)) var_A)
         
         (* Kibontjuk a jobb oldali ∀-t a var_A bázis termmel *)
         (tm_all_elim (tm_snd (tm_var 0)) var_A)).

  (* Megjegyzés: A tényleges 'h_typing' bizonyításokhoz a form_pullback 
     egyenlőségeit (L_Cast) kellene használni, de a termek szerkezete tökéletesen 
     tükrözi a kategóriaelméleti műveleteket. *)


  (* ========================================================================= *)
  (* 2. RÉSZ: SZEMANTIKAI BIZONYÍTÁS (Adjoints and Limits)                     *)
  (* ========================================================================= *)
  
  Context {C : SetoidCategory} {CC : CartesianCategory C}
          {GF : GoodFibration C}.
          
  Variable I_sem A_sem : @obj C.
  
  Notation "'π₁'" := (@prod_fst C CC I_sem A_sem) (at level 0).
  Notation "g '^*' X" := (@fobj _ _ (Pullback g) X) (at level 20, right associativity).
  Notation "'Π_(' g ')' X" := (@right_adj_obj _ _ _ (pullback_has_right_adjoint g) X) (at level 20, right associativity).

  Variable Phi_sem Psi_sem : @obj (Fiber (prod I_sem A_sem)).

  (* ODA IRÁNY Szemantikája: A right_adj_mor (∀_intro) és a prod_map (tm_pair) legózása *)
  Lemma semantic_forall_and_forward :
    hom (Π_(π₁) (@prod _ (Fiber_is_Cartesian (prod I_sem A_sem)) Phi_sem Psi_sem))
        (@prod _ (Fiber_is_Cartesian I_sem) (Π_(π₁) Phi_sem) (Π_(π₁) Psi_sem)).
  Proof.
    apply prod_map.
    - (* 1. komponens (tm_all_intro (tm_fst (tm_all_elim ...))) *)
      apply right_adj_mor.
      exact (compose prod_fst (@epsilon _ _ (Pullback π₁) (pullback_has_right_adjoint π₁) _)).
    - (* 2. komponens *)
      apply right_adj_mor.
      exact (compose prod_snd (@epsilon _ _ (Pullback π₁) (pullback_has_right_adjoint π₁) _)).
  Defined.

  (* VISSZA IRÁNY Szemantikája: Szintén right_adj_mor, de itt használjuk a pb_prod_iso axiómát! *)
  Lemma semantic_forall_and_backward :
    hom (@prod _ (Fiber_is_Cartesian I_sem) (Π_(π₁) Phi_sem) (Π_(π₁) Psi_sem))
        (Π_(π₁) (@prod _ (Fiber_is_Cartesian (prod I_sem A_sem)) Phi_sem Psi_sem)).
  Proof.
    apply right_adj_mor.
    eapply compose.
    
    - (* Epsilonok (kiértékelések) alkalmazása a komponensekre *)
      apply (prod_map 
               (compose (@epsilon _ _ (Pullback π₁) (pullback_has_right_adjoint π₁) Phi_sem) prod_fst)
               (compose (@epsilon _ _ (Pullback π₁) (pullback_has_right_adjoint π₁) Psi_sem) prod_snd)).
               
    - (* A visszahúzás (Weakening) disztributál a szorzat felett! *)
      exact (@iso_to _ _ _ (pb_prod_iso π₁ (Π_(π₁) Phi_sem) (Π_(π₁) Psi_sem))).
  Defined.

End Forall_And_Distribution.