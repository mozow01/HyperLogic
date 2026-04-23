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
   1. TÁBLÁZAT: SZINTAXIS VS. SZEMANTIKA (Szótár)
   =========================================================================
   Melyik HyperLogic szintaktikai elem minek felel meg a Fibrációban?

   | Szintaxis (HyperLogic)     | Szemantika (Hiperdoktrína)                   | Magyarázat / Jelentés                                 |
   |----------------------------|----------------------------------------------|-------------------------------------------------------|
   | I, A : b_ty                | I, A ∈ Obj(B)                                | Bázis típusok (Individuumok tartományai)              |
   | Gamma, Phi : h_ty          | Γ, Φ ∈ Obj(Fiber(I))                         | Formulák / Logikai kontextusok az adott szálban       |
   | b_fst                      | π₁ : I × A → I                               | Bázis projekció (Weakening/gyengítés morfizmusa)      |
   | ctx_pullback b_fst G       | π₁^* Γ                                       | A kontextus felhúzása (Weakening funktor)             |
   | Ty_All A Phi               | Π_{π₁} Φ                                     | Univerzális kvantor (A π₁^* jobb adjungáltja)         |
   | f : I -> A (base_typing)   | f : I → A                                    | Bázis morfizmus (Egy konkrét behelyettesítendő term)  |
   | b_pair b_id f              | ⟨id_I, f⟩ : I → I × A                        | A behelyettesítés gráf-morfizmusa a bázisban          |
   | form_pullback <id, f> Phi  | ⟨id_I, f⟩^* Φ                                | Szintaktikus behelyettesítés: Φ[f/A]                  |
   | HT_All_Intro               | Hom(π₁^* Γ, Φ) ≅ Hom(Γ, Π_{π₁} Φ)            | Adjungálás (Bizonyítás felhúzott kontextusból)        |
   | HT_All_Elim                | ε : π₁^* Π_{π₁} Φ → Φ  (+ Pullback)          | Kvantor elimináció (A Counit / Kiértékelés)           |
   ========================================================================= *)

(* =========================================================================
   2. KOMMUTATÍV DIAGRAM: A BEHELYETTESÍTÉS GEOMETRIÁJA
   =========================================================================

   BÁZIS KATEGÓRIA (B) - Itt élnek a változók és a termek
   ------------------------------------------------------
               I × A
              /  ^
         π₁  /    \  ⟨id_I, f⟩  <-- Ez a "f" term behelyettesítése!
            /      \
           v        \
           I <------- I
               id_I

   (Megjegyzés: π₁ ∘ ⟨id_I, f⟩ = id_I, azaz a behelyettesítés után a bázis nem változik)

   SZÁLAK KATEGÓRIÁI (Fibers) - Itt élnek a formulák és a bizonyítások
   -------------------------------------------------------------------
   Fiber(I × A) :     π₁^* Γ                Φ      <-- Az "∀ Intro" premisszája
                        |                   ^
                        | π₁^* | π₁^*
                        v                   |
   Fiber(I)     :       Γ -----------> Π_{π₁} Φ    <-- Maga a kvantált formula (∀A. Φ)
                                  \
                                   \ ⟨id_I, f⟩^* (Visszahúzás = Behelyettesítés)
                                    v
                               ⟨id_I, f⟩^* Φ       <-- A konklúzió: Φ[f/A]
   ========================================================================= *)

Section Quantifier_Elimination_Explanation.

  Context {C : SetoidCategory} {CC : CartesianCategory C}
          {GF : GoodFibration C}.

  (* Bázis típusok: I (ahol most vagyunk) és A (a kvantált változó típusa) *)
  Variable I A : @obj C.

  (* ----------------------------------------------------------------- *)
  (* 3. PLASZTIKUS RÖVIDÍTÉSEK (NOTATIONS)                             *)
  (* ----------------------------------------------------------------- *)

  (* 1. A π₁ projekció: I x A -> I *)
  Notation "'π₁'" := (@prod_fst C CC I A) (at level 0).

 (* A HELYES VISSZAHÚZÁS: Egyértelműen meghívja az 'fobj'-t a Pullback funktoron *)
  Notation "g '^*' X" := (@fobj _ _ (Pullback g) X) (at level 20, right associativity).

  (* Kvantált formula *)
  Notation "'Π_(' g ')' X" := (@right_adj_obj _ _ _ (pullback_has_right_adjoint g) X) (at level 20, right associativity).

  Notation "'⟨' g ',' h '⟩'" := (@prod_map C CC _ _ _ g h) (at level 0).

  (* ================================================================= *)
  (* BIZONYÍTÁS                                                        *)
  (* ================================================================= *)

  Variable G : @obj (Fiber I).
  Variable Phi : @obj (Fiber (prod I A)).
  Variable f : hom I A.

  (*
  Ahhoz, hogy a Φ formulában az A helyére betehesd az f-et, egy olyan morfizmust kell építened, amely az I-ből csinál egy I×A inputot a formula számára. Ezt csinálja a ⟨idI​,f⟩ párképzés:

    Az első komponense az idI​: "A meglévő kontextust (a korábbi változókat) hagyd békén, passzold tovább változatlanul."

    A második komponense az f: "Az új, A típusú változó helyére pedig számold ki és tedd be az f termet."
  *)
  Let subst_f : hom I (prod I A) := ⟨id I, f⟩.

  Lemma semantic_All_Elim :
    (* Premissza: G ⊢ Π_{π₁} Φ *)
    hom G (Π_(π₁) Phi) ->

    (* Konklúzió: G ⊢ Φ[f/A] *)
    (* A Coq most már garantáltan (fobj (Pullback subst_f) Phi)-ként értelmezi! *)
    hom G (subst_f ^* Phi).
  Proof. Admitted.
End Quantifier_Elimination_Explanation.