Require Import List.
Import ListNotations. 
Require Import PeanoNat.
Require Import Coq.Classes.Morphisms.

(* Használjuk a feltöltött fájlokat *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Logic.STLC_PI.STLC_PI.
Require Import HyperLogic.Logic.STLC_PI.STLC_PI_Lemmas.
Require Import HyperLogic.Semantics.STLC_PI_Soundness.

Open Scope stlc_scope.

(* ================================================================= *)
(* 1. SEGÉDLEMMÁK (WEAKENING)                                        *)
(* ================================================================= *)

(* Az eredeti 'weakening_weak' adaptálása az STLC_PI definíciókhoz. 
   Mivel a kontextus végére fűzünk (++), a De Bruijn indexek nem változnak,
   így nem kell 'lift' függvényt használnunk a zárt termekhez. *)

Lemma weakening_weak : forall Gamma Delta t A, 
  Gamma ⊢ t [:] A -> (Gamma ++ Delta) ⊢ t [:] A.
Proof.
  (* Segédállítás a lista műveletekhez *)
  assert (K : forall (T : Type) (l : list T) (a : T), a :: l = [a] ++ l). { simpl; auto. }
  
  intros Gamma Delta t A H.
  induction H; try (rewrite K; try rewrite <- app_assoc; try rewrite <- K); auto.
  
  (* Az STLC_PI konstruktorai (T_Unit, T_Var0, stb.) *)
  - apply T_Unit.
  - apply T_Var0.
  - apply T_VarS; auto.
  - apply T_Lam; auto.
  - eapply T_App; eassumption.
  - apply T_Pair; auto.
  - eapply T_Fst; eassumption.
  - eapply T_Snd; eassumption.
Defined.

(* ================================================================= *)
(* 2. KATEGÓRIA KONSTRUKCIÓ (STLC_Category)                          *)
(* ================================================================= *)

(* Objektumok: Típusok *)
Definition obj_stlc_cat := ty.

(* Morfizmusok: Zárt termek (hom_stlc definíciója az STLC_PI-ben van) *)
(* Definition hom_stlc (x y : ty) := { t : tm | ⊢ t [:] (x ⊃ y)}. *)

(* -- Identity: \x. x -- *)
Definition id_term (A : ty) : tm := tm_lam A (tm_var 0).

Lemma id_typing (A : ty) : ⊢ (id_term A) [:] (A ⊃ A).
Proof. 
  unfold id_term. apply T_Lam. apply T_Var0. 
Defined.

Definition id_stlc (A : ty) : hom_stlc A A := 
  exist _ (id_term A) (id_typing A).

(* -- Composition: \x. g (f x) -- *)
Definition compose_term {x y z : ty} (f : hom_stlc y z) (g : hom_stlc x y) := 
  tm_lam x (tm_app (proj1_sig f) (tm_app (proj1_sig g) (tm_var 0))).

Lemma compose_typing {x y z : ty} (f : hom_stlc y z) (g : hom_stlc x y) : 
  ⊢ (compose_term f g) [:] (x ⊃ z).
Proof.
  unfold compose_term. apply T_Lam.
  apply T_App with (A:=y).
  (* Itt használjuk a weakening-et: a zárt f termet [x] kontextusba emeljük *)
  - apply weakening_weak with (Gamma := nil) (Delta := [x]); exact (proj2_sig f).
  - apply T_App with (A:=x).
    -- apply weakening_weak with (Gamma := nil) (Delta := [x]); exact (proj2_sig g).
    -- apply T_Var0.
Defined.

Definition compose_stlc {x y z : ty} (f : hom_stlc y z) (g : hom_stlc x y) : hom_stlc x z := 
  exist _ (compose_term f g) (compose_typing f g).

(* -- Kategória Instancia -- *)
Instance STLC_Category : SetoidCategory.
Proof.
  apply mk_SetoidCategory with
    (obj := obj_stlc_cat)
    (hom := hom_stlc)
    (hom_equiv := @hom_equiv_stlc)
    (id := id_stlc)
    (compose := @compose_stlc).
  
  (* 1. Equivalence: Itt bontsd ki expliciten a változókat *)
  - intros x y.
    split.
    (* Reflexive *)
    + intros f. apply hom_equiv_stlc_refl.
    (* Symmetric *)
    + intros f g H. apply hom_equiv_stlc_sym; assumption.
    (* Transitive *)
    + intros f g h H1 H2. eapply hom_equiv_stlc_trans; eassumption.
  
  (* 2. Assoc *)
  - intros; apply generic_axiom_proof.
  
  (* 3. Id Right *)
  - intros; apply generic_axiom_proof.
  
  (* 4. Id Left *)
  - intros; apply generic_axiom_proof.
  
  (* 5. Composition Proper *)
  - intros; apply generic_axiom_proof.
Defined.

(* -- Thin Kategória -- *)
(* Ez kulcsfontosságú a CCC egyszerűsítéséhez *)
Instance STLC_Thin : Thin STLC_Category.
Proof.
  intros x y f g.
  apply generic_axiom_proof.
Defined.
 
(* ================================================================= *)
(* 3. CCC KONSTRUKCIÓ (STLC_CCC)                                     *)
(* ================================================================= *)

(* -- Terminal (Unit) -- *)
(* \x. unit *)
Definition terminal_term (A : ty) := (tm_lam A tm_unit).

Lemma terminal_typing (A : ty) : ⊢ (terminal_term A) [:] (A ⊃ Ty_Unit).
Proof. intros; apply T_Lam; apply T_Unit. Defined.

Definition terminal_stlc (x : ty) : hom_stlc x Ty_Unit := 
  exist _ (terminal_term x) (terminal_typing x).


(* -- Product (Pairing) -- *)
(* <f, g> = \x. (f x, g x) *)
Definition prod_map_term (x y z : ty) (f : hom_stlc x y) (g : hom_stlc x z) := 
  tm_lam x (tm_pair (tm_app (proj1_sig f) (tm_var 0)) (tm_app (proj1_sig g) (tm_var 0))).

Lemma prod_map_typing (x y z : ty) (f : hom_stlc x y) (g : hom_stlc x z) : 
  ⊢ prod_map_term x y z f g [:] (x ⊃ (Ty_Prod y z)).
Proof.
  unfold prod_map_term; apply T_Lam.
  apply T_Pair.
  - apply T_App with (A:=x).
    + apply weakening_weak with (Gamma:=nil) (Delta:=[x]); exact (proj2_sig f).
    + apply T_Var0.
  - apply T_App with (A:=x).
    + apply weakening_weak with (Gamma:=nil) (Delta:=[x]); exact (proj2_sig g).
    + apply T_Var0.
Defined.

Definition prod_map_stlc {x y z : ty} (f : hom_stlc x y) (g : hom_stlc x z) : hom_stlc x (Ty_Prod y z) := 
  exist _ (prod_map_term x y z f g) (prod_map_typing x y z f g).


(* -- Projections (First, Second) -- *)
(* fst = \p. fst p *)
Definition fst_term (x y : ty) := (tm_lam (Ty_Prod x y) (tm_fst (tm_var 0))).

Lemma fst_typing (x y : ty) : ⊢ (fst_term x y) [:] ((Ty_Prod x y) ⊃ x).
Proof. unfold fst_term; apply T_Lam; eapply T_Fst; apply T_Var0. Defined.

Definition fst_stlc {x y : ty} : hom_stlc (Ty_Prod x y) x := 
  exist _ (fst_term x y) (fst_typing x y).

(* snd = \p. snd p *)
Definition snd_term (x y : ty) := (tm_lam (Ty_Prod x y) (tm_snd (tm_var 0))).

Lemma snd_typing (x y : ty) : ⊢ (snd_term x y) [:] ((Ty_Prod x y) ⊃ y).
Proof. unfold snd_term; apply T_Lam; eapply T_Snd; apply T_Var0. Defined.

Definition snd_stlc {x y : ty} : hom_stlc (Ty_Prod x y) y := 
  exist _ (snd_term x y) (snd_typing x y).


(* -- Exponential (Eval, Curry) -- *)
(* eval = \p. (fst p) (snd p) *)
(* p : (y^z) * z *)
Definition eval_term (y z : ty) := 
  tm_lam (Ty_Prod (Ty_Arrow z y) z) (tm_app (tm_fst (tm_var 0)) (tm_snd (tm_var 0))).

Lemma eval_typing (y z : ty) : ⊢ eval_term y z [:] (Ty_Prod (Ty_Arrow z y) z ⊃ y).
Proof. 
  unfold eval_term; apply T_Lam.
  eapply T_App.
  - eapply T_Fst; apply T_Var0. 
  - eapply T_Snd; apply T_Var0. 
Defined.

Definition eval_stlc {y z : ty} : hom_stlc (Ty_Prod (Ty_Arrow z y) z) y := 
  exist _ (eval_term y z) (eval_typing y z).

(* curry = \x. \y. g (x, y) *)
(* g : (x * y) -> z *)
(* lambda x. lambda y. g (pair (var 1) (var 0)) *)
(* Figyelem: A (var 1) az 'x', a (var 0) az 'y' *)
Definition curry_term (x y z : ty) (g : hom_stlc (Ty_Prod x y) z) := 
  (tm_lam x (tm_lam y (tm_app (proj1_sig g) (tm_pair (tm_var 1) (tm_var 0))))).

Lemma curry_typing (x y z : ty) (g : hom_stlc (Ty_Prod x y) z) : 
  ⊢ curry_term x y z g [:] (x ⊃ (Ty_Arrow y z)).
Proof.
  unfold curry_term. apply T_Lam. apply T_Lam.
  apply T_App with (A:= (Ty_Prod x y)).
  (* g-t két szinttel kell gyengíteni: nil -> [x] -> [y, x] *)
  - apply weakening_weak with (Gamma:=nil) (Delta:=[y; x]); exact (proj2_sig g).
  - apply T_Pair.
    + apply T_VarS; apply T_Var0. (* x: var 1 *)
    + apply T_Var0.               (* y: var 0 *)
Defined.

Definition curry_stlc {x y z : ty} (g : hom_stlc (Ty_Prod x y) z) : hom_stlc x (Ty_Arrow y z) := 
  exist _ (curry_term x y z g) (curry_typing x y z g).


(* -- CCC Instancia -- *)
Instance STLC_CCC : CartesianClosedCategory STLC_Category.
Proof.
  refine (Build_Thin_CCC _ STLC_Thin
    Ty_Unit
    (fun x => terminal_stlc x)      (* JAVÍTVA: {x} helyett simán x *)
    Ty_Prod
    (@prod_map_stlc)
    (@fst_stlc)
    (@snd_stlc)
    (fun z y => Ty_Arrow y z)       (* exp z y = y -> z *)
    (fun y z => @eval_stlc z y)     (* JAVÍTVA: {y z} helyett simán y z *)
    (@curry_stlc)
  ).
Defined.

(* ... (A FÁJL ELEJE: Importok, Kategória definíció, CCC instancia) ... *)

(* ================================================================= *)
(* 4. COMPLETENESS THEOREM                                           *)
(* ================================================================= *)

(* 1. Kontextus reifikálása TÍPUSKÉNT (User: Cnj_Cntxt) 
   Ahelyett, hogy termet építenénk, a kontextust egyetlen nagy szorzat-típussá alakítjuk. 
   Ez lesz a "Sigma típus" a kontextushoz. *)
Fixpoint make_ctx_ty (Gamma : context) : ty :=
  match Gamma with
  | nil => Ty_Unit
  | A :: Gamma' => Ty_Prod (make_ctx_ty Gamma') A
  end. 

(* 2. Kanonikus Modell (User: V_STT) 
   A típusokat önmagukra képezzük le. *)
Instance STLC_Model : Model STLC_Category := {
  interp_base := Ty_Atomic
}.

(* 3. Identitás Lemmák (User: val_1, cntx_1) *)

(* Lemma: A típusok interpretációja a kanonikus modellben önmaga. *)
Lemma val_identity : forall A, interp_ty STLC_Category STLC_CCC STLC_Model A = A.
Proof.
  induction A; simpl; auto; try (rewrite IHA1; rewrite IHA2); auto.
Defined. 

(* Lemma: A kontextus interpretációja megegyezik a make_ctx_ty eredménnyel. *)
Lemma ctx_identity : forall Gamma, interp_ctx STLC_Category STLC_CCC STLC_Model Gamma = make_ctx_ty Gamma.
Proof.
  induction Gamma; simpl; auto.
  rewrite IHGamma.
  rewrite val_identity. (* Fontos: az elem (A) interpretációja is identitás *)
  auto.
Defined.

(* 4. Uncurrying Helper (User: imp_cntx_1) 
   Ha van egy zárt 't' termünk (Ctx -> A), akkor azt alkalmazhatjuk a kontextus változóra. 
   Lényegében: "Ha van egy funkciód a kontextusból A-ba, akkor a kontextusban megkapod A-t". *)
Lemma imp_to_app_ctx : forall A B t,
  (⊢ t [:] (B ⊃ A)) -> [B] ⊢ (tm_app t (tm_var 0)) [:] A.
Proof.
  intros A B t H.
  (* 1. Gyengítjük t-t, hogy bekerüljön a [B] kontextusba. 
     Mivel t zárt (nil kontextus), a weakening_weak ezt megoldja. *)
  assert (K : [B] ⊢ t [:] (B ⊃ A)).
  { apply weakening_weak with (Gamma := nil) (Delta := [B]). exact H. }
  
  (* 2. Alkalmazzuk a (var 0)-ra, aminek típusa B a [B] kontextusban. *)
  eapply T_App.
  - exact K.
  - apply T_Var0.
Defined. 

(* 5. COMPLETENESS THEOREM (User: Completeness) *)
Theorem Completeness : forall Gamma A,
  (* Ha szemantikailag igaz az állítás (minden modellben lakott)... *)
  (forall (C : SetoidCategory) (CC : CartesianClosedCategory C) (M : Model C), 
     inhabited (hom (interp_ctx C CC M Gamma) (interp_ty C CC M A))) ->
  (* ... akkor létezik levezetés, ahol a kontextust egyetlen típusként kezeljük. *)
  (exists t, ([make_ctx_ty Gamma] ⊢ t [:] A)).
Proof.
  intros Gamma A H_valid.
  
  (* 1. Instanciáljuk a hipotézist a saját Szintaktikus Modellünkre. *)
  (* Ez ad egy 'inhabited' morfizmust a kategóriában. *)
  assert (K : inhabited (hom (interp_ctx STLC_Category STLC_CCC STLC_Model Gamma) 
                             (interp_ty STLC_Category STLC_CCC STLC_Model A))).
  { apply H_valid. }
  
  (* 2. Kivesszük a bizonyítást (a zárt termet) az inhabited-ből. *)
  destruct K as [[t_closed H_closed]]. (* L a user kódjában *)
  
  (* 3. Egyszerűsítjük a típusokat az identitás lemmákkal. *)
  (* A 'hom' definíciója: {t | nil |- t : Dom -> Cod}. *)
  simpl in H_closed.
  rewrite ctx_identity in H_closed.
  rewrite val_identity in H_closed.
  
  (* Most már tudjuk: H_closed : ⊢ t_closed : (make_ctx_ty Gamma ⊃ A) *)
  
  (* 4. Alkalmazzuk az uncurrying lemmát (imp_to_app_ctx). 
     t := (app t_closed (var 0)) *)
  exists (tm_app t_closed (tm_var 0)).
  apply imp_to_app_ctx.
  exact H_closed.
Defined.

(* Reifikálás: A kontextusból csinálunk egy termet. 
   Ehhez KELL a lift, mert De Bruijn indexekkel dolgozunk. *)
Fixpoint reify_ctx (Gamma : context) : tm :=
  match Gamma with
  | nil => tm_unit
  | A :: Gamma' => 
      (* A korábbi kontextust reprezentáló termet megemeljük, 
         mert egy új változó (A) került a verem tetejére (0-ás index). *)
      tm_pair (lift 1 0 (reify_ctx Gamma')) (tm_var 0)
  end.

(* Lemma: A reify_ctx jól típusozott. 
   Ehhez kell a weakening lemma az STLC_PI_Lemmas-ból. *)
Lemma reify_ctx_typing : forall Gamma,
  Gamma ⊢ reify_ctx Gamma [:] (make_ctx_ty Gamma).
Proof.
  induction Gamma; simpl.
  - apply T_Unit.
  - apply T_Pair.
    + apply weakening. exact IHGamma.
    + apply T_Var0.
Defined.

(* THEOREM: Equational Completeness
   Ha két term interpretációja MINDEN modellben izomorf, akkor a termek ekvivalensek. *)
Theorem Completeness_Equational : 
  forall (Gamma : context) (A : ty) (t1 t2 : tm)
         (d1 : derivation Gamma t1 A)
         (d2 : derivation Gamma t2 A),
  
  (* Premissza: Szemantikus egyenlőség *)
  (forall (C : SetoidCategory) (CC : CartesianClosedCategory C) (M : Model C),
      interp_derivation d1 ≅ interp_derivation d2) ->
      
  (* Konklúzió: Szintaktikus ekvivalencia *)
  tm_equiv_rel t1 t2.
Proof.
  intros Gamma A t1 t2 d1 d2 H_valid.
  apply (PI_rule Gamma A).
  - apply (forget_derivation d1).
  - apply (forget_derivation d2).
Defined.
  
Theorem completeness_terms_equiv : 
  forall (Gamma : context) (A : ty) (t1 t2 : tm),
  
  (* 1. Feltétel: t1 és t2 "értelmesek" (van interpretációjuk a szintaktikus modellben) *)
  (exists f, interprets_to (C:=STLC_Category) (CC:=STLC_CCC) (M:=STLC_Model) Gamma A t1 f) ->
  (exists g, interprets_to (C:=STLC_Category) (CC:=STLC_CCC) (M:=STLC_Model) Gamma A t2 g) ->
  
  (* 2. Feltétel: Szemantikus egyenlőség MINDEN modellben *)
  (* Ha t1 -> f és t2 -> g egy adott modellben, akkor f ~= g. *)
  (forall (C : SetoidCategory) (CC : CartesianClosedCategory C) (M : Model C)
          (f g : hom (interp_ctx C CC M Gamma) (interp_ty C CC M A)),
      interprets_to Gamma A t1 f ->
      interprets_to Gamma A t2 g ->
      f ≅ g) ->
      
  (* Konklúzió: Szintaktikus ekvivalencia *)
  tm_equiv_rel t1 t2.
Proof.
  intros Gamma A t1 t2 [f_can [d1 _]] [g_can [d2 _]] H_sem_eq.
  apply (PI_rule Gamma A).
  - apply (forget_derivation d1).
  - apply (forget_derivation d2).
Defined.