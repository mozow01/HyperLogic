(* theories/Semantics/Epsilon_Adjoint/Epsilon_Adjoint_Completeness.v *)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Equality.
Require Import List.
Import ListNotations.
 
(* Kategóriaelméleti alapok *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Fibration.

(* Szintaxis és Fibráció (Epsilon Adjoint) *)
Require Import HyperLogic.Logic.Base.Epsilon_Adjoint.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon_Adjoint.Hyper_Syntax.
Require Import HyperLogic.Semantics.Epsilon_Adjoint.Base_Epsilon_Completeness.
Require Import HyperLogic.Semantics.Epsilon_Adjoint.Epsilon_Adjoint_Fibration.

(* ================================================================= *)
(* 1. A SZINTAKTIKUS SZÁL KATEGÓRIA (FIBER CATEGORY)                 *)
(* ================================================================= *)
 
(* ÚJ hom_fiber: Üres kontextus és Ty_Arrow (pont mint az STLC-ben!) *)
Class hom_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) (Phi Psi : @h_ty Sign) : Type := mk_hom_fiber {
  h_tm_of : @h_tm Sign;
  h_deriv_of : h_derivation I [] h_tm_of (Ty_Arrow Phi Psi)
}.

Arguments h_tm_of {Sign SM I Phi Psi} _.
Arguments h_deriv_of {Sign SM I Phi Psi} _.

Definition fiber_equiv {Sign : Type} {SM : SkolemMapping Sign} {I : b_ty} {Phi Psi : @h_ty Sign} 
  (f g : @hom_fiber Sign SM I Phi Psi) : Prop := True.

Global Instance fiber_equiv_equivalence {Sign SM I Phi Psi} : Equivalence (@fiber_equiv Sign SM I Phi Psi).
Proof. constructor; red; intros; unfold fiber_equiv; constructor. Qed.

(* IDENTITÁS: Pont mint az STLC id_term *)
Definition id_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) (Phi : @h_ty Sign) : @hom_fiber Sign SM I Phi Phi.
Proof.
  refine (@mk_hom_fiber Sign SM I Phi Phi (tm_lam Phi (tm_var 0)) _).
  apply HD_Lam. apply HD_Var0.
Defined.

(* KOMPOZÍCIÓ Zárt Kombinátorral: \f. \g. \x. f (g x) *)
Definition comp_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {Phi Psi Chi : @h_ty Sign} 
  (f : @hom_fiber Sign SM I Psi Chi) (g : @hom_fiber Sign SM I Phi Psi) : @hom_fiber Sign SM I Phi Chi.
Proof.
  refine (@mk_hom_fiber Sign SM I Phi Chi 
    (tm_app (tm_app 
       (* A COMP kombinátor: *)
       (tm_lam (Ty_Arrow Psi Chi) 
         (tm_lam (Ty_Arrow Phi Psi) 
           (tm_lam Phi 
             (tm_app (tm_var 2) (tm_app (tm_var 1) (tm_var 0))))))
       (* Alkalmazva f-re: *)
       (h_tm_of f)) 
       (* Alkalmazva g-re: *)
    (h_tm_of g)) _).
  
  (* Bizonyítás: Csupa beépített szabállyal, weakening lemma nélkül! *)
  apply HD_App with (Phi := Ty_Arrow Phi Psi).
  - apply HD_App with (Phi := Ty_Arrow Psi Chi).
    + (* A kombinátor típusolása *)
      apply HD_Lam. apply HD_Lam. apply HD_Lam.
      apply HD_App with (Phi := Psi).
      * (* tm_var 2 (f) lekérése a kontextus aljáról *)
        apply HD_VarS. apply HD_VarS. apply HD_Var0.
      * (* tm_app 1 0 kiértékelése *)
        apply HD_App with (Phi := Phi).
        -- (* tm_var 1 (g) lekérése *)
           apply HD_VarS. apply HD_Var0.
        -- (* tm_var 0 (x) lekérése *)
           apply HD_Var0.
    + (* f típusolása (üres kontextusból!) *)
      exact (h_deriv_of f).
  - (* g típusolása (üres kontextusból!) *)
    exact (h_deriv_of g).
Defined.

(* Maga a Fiber SetoidCategory példányosítása *)
Instance Fiber_SetoidCategory {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) : SetoidCategory.
Proof.
  refine (mk_SetoidCategory 
    (@h_ty Sign) 
    (@hom_fiber Sign SM I) 
    (fun X => @id_fiber Sign SM I X)
    (fun X Y Z f g => @comp_fiber Sign SM I X Y Z f g)
    (fun X Y f g => @fiber_equiv Sign SM I X Y f g)
    _ _ _ _ _).
  
  (* Mivel a hom_equiv_equivalence-t a Coq automatikusan megoldotta, 
     az összes maradék kategória axiómát (comp_assoc, id_left, stb.)
     egyszerre kilőjük, hiszen mindegyik csak egy True állítás! *)
  Unshelve.
  all: intros; unfold fiber_equiv; constructor.
Defined.

(* Be is bizonyítjuk, hogy Vékony (Thin) *)
Instance Fiber_Thin {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) : Thin (Fiber_SetoidCategory I).
Proof.
  intros x y f g. unfold fiber_equiv; constructor.
Defined.

(* ================================================================= *)
(* 2. FIBER CARTESIAN CATEGORY (Unit, Prod)                          *)
(* ================================================================= *)

(* --- TERMINAL (Unit) --- *)
Definition term_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) (X : @h_ty Sign) : @hom_fiber Sign SM I X Ty_Unit.
Proof.
  refine (@mk_hom_fiber Sign SM I X Ty_Unit (tm_lam X tm_unit) _).
  apply HD_Lam. apply HD_Unit.
Defined.

(* --- PRODUCT (And) --- *)
(* Kombinátor: \f. \g. \x. (f x, g x) *)
Definition prod_map_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X Y Z : @h_ty Sign} 
  (f : @hom_fiber Sign SM I X Y) (g : @hom_fiber Sign SM I X Z) : @hom_fiber Sign SM I X (Ty_Prod Y Z).
Proof.
  refine (@mk_hom_fiber Sign SM I X (Ty_Prod Y Z)
    (tm_app (tm_app
      (tm_lam (Ty_Arrow X Y)
        (tm_lam (Ty_Arrow X Z)
          (tm_lam X
            (tm_pair (tm_app (tm_var 2) (tm_var 0)) (tm_app (tm_var 1) (tm_var 0))))))
      (h_tm_of f)) (h_tm_of g)) _).
      
  (* JAVÍTÁS: Először a 'g' típusát (X Z) adjuk meg, utána az 'f' típusát (X Y) *)
  apply HD_App with (Phi := Ty_Arrow X Z).
  - apply HD_App with (Phi := Ty_Arrow X Y).
    + apply HD_Lam. apply HD_Lam. apply HD_Lam. apply HD_Pair.
      * apply HD_App with (Phi := X).
        -- apply HD_VarS. apply HD_VarS. apply HD_Var0.
        -- apply HD_Var0.
      * apply HD_App with (Phi := X).
        -- apply HD_VarS. apply HD_Var0.
        -- apply HD_Var0.
    + exact (h_deriv_of f).
  - exact (h_deriv_of g).
Defined.

Definition fst_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X Y : @h_ty Sign} : @hom_fiber Sign SM I (Ty_Prod X Y) X.
Proof.
  refine (@mk_hom_fiber Sign SM I (Ty_Prod X Y) X (tm_lam (Ty_Prod X Y) (tm_fst (tm_var 0))) _).
  apply HD_Lam. eapply HD_Fst. apply HD_Var0.
Defined.

Definition snd_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X Y : @h_ty Sign} : @hom_fiber Sign SM I (Ty_Prod X Y) Y.
Proof.
  refine (@mk_hom_fiber Sign SM I (Ty_Prod X Y) Y (tm_lam (Ty_Prod X Y) (tm_snd (tm_var 0))) _).
  apply HD_Lam. eapply HD_Snd. apply HD_Var0.
Defined.

Instance Fiber_CartesianCategory {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) : CartesianCategory (Fiber_SetoidCategory I).
Proof.
  apply (Build_Thin_CC _ (Fiber_Thin I)
    Ty_Unit (fun X => @term_fiber Sign SM I X)
    Ty_Prod (fun X Y Z f g => @prod_map_fiber Sign SM I X Y Z f g)
    (fun X Y => @fst_fiber Sign SM I X Y)
    (fun X Y => @snd_fiber Sign SM I X Y)
  ).
Defined.
 
(* ================================================================= *)
(* 3. FIBER CARTESIAN CLOSED CATEGORY (Arrow)                        *)
(* ================================================================= *)

(* --- EXPONENTIAL (Implies) --- *)
(* Eval/Apply: \p. (fst p) (snd p) *)
(* JAVÍTÁS: Y a bemenet (domain), Z a kimenet (codomain) *)
Definition eval_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {Y Z : @h_ty Sign} : @hom_fiber Sign SM I (Ty_Prod (Ty_Arrow Y Z) Y) Z.
Proof.
  refine (@mk_hom_fiber Sign SM I _ _
    (tm_lam (Ty_Prod (Ty_Arrow Y Z) Y) (tm_app (tm_fst (tm_var 0)) (tm_snd (tm_var 0)))) _).
  apply HD_Lam. apply HD_App with (Phi := Y).
  - eapply HD_Fst. apply HD_Var0.
  - eapply HD_Snd. apply HD_Var0.
Defined.

(* Curry kombinátor: \f. \x. \y. f (x, y) *)
Definition curry_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X Y Z : @h_ty Sign} (g : @hom_fiber Sign SM I (Ty_Prod X Y) Z) : @hom_fiber Sign SM I X (Ty_Arrow Y Z).
Proof.
  refine (@mk_hom_fiber Sign SM I X (Ty_Arrow Y Z)
    (tm_app
      (tm_lam (Ty_Arrow (Ty_Prod X Y) Z)
        (tm_lam X
          (tm_lam Y
            (tm_app (tm_var 2) (tm_pair (tm_var 1) (tm_var 0))))))
      (h_tm_of g)) _).
  apply HD_App with (Phi := Ty_Arrow (Ty_Prod X Y) Z).
  - apply HD_Lam. apply HD_Lam. apply HD_Lam.
    apply HD_App with (Phi := Ty_Prod X Y).
    + eapply HD_VarS. apply HD_VarS. apply HD_Var0.
    + eapply HD_Pair.
      * apply HD_VarS. apply HD_Var0.
      * apply HD_Var0.
  - exact (h_deriv_of g).
Defined.

Instance Fiber_CartesianClosedCategory {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) : CartesianClosedCategory (Fiber_SetoidCategory I).
Proof.
  refine (Build_Thin_CCC _ (Fiber_Thin I)
    (* JAVÍTÁS ITT IS: Megfordítjuk a változókat, ahogy az STLC_CCC-ben is volt! *)
    (fun Z Y => Ty_Arrow Y Z)
    (fun Y Z => @eval_fiber Sign SM I Y Z)
    (fun X Y Z g => @curry_fiber Sign SM I X Y Z g)
  ).
Defined.

(* ================================================================= *)
(* 4. FIBER BiCARTESIAN CLOSED CATEGORY (Void, Sum)                  *)
(* ================================================================= *)

(* --- INITIAL (Void) --- *)
Definition init_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X : @h_ty Sign} : @hom_fiber Sign SM I Ty_Void X.
Proof.
  refine (@mk_hom_fiber Sign SM I Ty_Void X (tm_lam Ty_Void (tm_absurd X (tm_var 0))) _).
  apply HD_Lam. apply HD_Absurd. apply HD_Var0.
Defined.

(* --- COPRODUCT (Or) --- *)
Definition inl_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X Y : @h_ty Sign} : @hom_fiber Sign SM I X (Ty_Sum X Y).
Proof.
  refine (@mk_hom_fiber Sign SM I X (Ty_Sum X Y) (tm_lam X (tm_inl Y (tm_var 0))) _).
  apply HD_Lam. apply HD_Inl. apply HD_Var0.
Defined.

Definition inr_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X Y : @h_ty Sign} : @hom_fiber Sign SM I Y (Ty_Sum X Y).
Proof.
  refine (@mk_hom_fiber Sign SM I Y (Ty_Sum X Y) (tm_lam Y (tm_inr X (tm_var 0))) _).
  apply HD_Lam. apply HD_Inr. apply HD_Var0.
Defined.

(* Coprod kombinátor: \f. \g. \c. case c of inl x => f x | inr y => g y *)
Definition coprod_map_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X Y Z : @h_ty Sign} 
  (f : @hom_fiber Sign SM I X Z) (g : @hom_fiber Sign SM I Y Z) : @hom_fiber Sign SM I (Ty_Sum X Y) Z.
Proof.
  refine (@mk_hom_fiber Sign SM I (Ty_Sum X Y) Z
    (tm_app (tm_app
      (tm_lam (Ty_Arrow X Z)
        (tm_lam (Ty_Arrow Y Z)
          (tm_lam (Ty_Sum X Y)
            (tm_case (tm_var 0)
              (tm_app (tm_var 3) (tm_var 0))
              (tm_app (tm_var 2) (tm_var 0))))))
      (h_tm_of f)) (h_tm_of g)) _).
      
  (* JAVÍTÁS ITT IS: Először a 'g' típusát (Y Z), utána az 'f' típusát (X Z) adjuk meg! *)
  apply HD_App with (Phi := Ty_Arrow Y Z).
  - apply HD_App with (Phi := Ty_Arrow X Z).
    + apply HD_Lam. apply HD_Lam. apply HD_Lam.
      apply HD_Case with (Phi := X) (Psi := Y).
      * apply HD_Var0.
      * apply HD_App with (Phi := X).
        -- apply HD_VarS. apply HD_VarS. apply HD_VarS. apply HD_Var0.
        -- apply HD_Var0.
      * apply HD_App with (Phi := Y).
        -- apply HD_VarS. apply HD_VarS. apply HD_Var0.
        -- apply HD_Var0.
    + exact (h_deriv_of f).
  - exact (h_deriv_of g).
Defined. 

Instance Fiber_BiCartesianClosedCategory {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) : BiCartesianClosedCategory (Fiber_CartesianClosedCategory I).
Proof.
  apply (Build_Thin_BiCCC (Fiber_SetoidCategory I) (Fiber_CartesianClosedCategory I) (Fiber_Thin I)
    Ty_Void (fun X => @init_fiber Sign SM I X)
    Ty_Sum (fun X Y => @inl_fiber Sign SM I X Y) (fun X Y => @inr_fiber Sign SM I X Y)
    (fun X Y Z f g => @coprod_map_fiber Sign SM I X Y Z f g)
  ).
Defined.

(* ================================================================= 
(* 5. SYNTACTIC HYPERDOCTRINE & ADJUNCTIONS (Axiomatizált váz)       *)
(* ================================================================= *)
(* Felépítjük a Fibrációs struktúrát a Base és a Fiber kategóriák között.
   Mivel a Fiber_SetoidCategory Thin, a kategóriaelméleti egyenlőségek (koherencia)
   triviálisak. A funktorok szintaktikus működését axiomatizáljuk a vázlat kedvéért. *)

Axiom Syntactic_GoodFibration : forall {Sign} {SM : SkolemMapping Sign}, GoodFibration (Base_SetoidCategory Sign).
Axiom Syntactic_StrictGoodFibration : forall {Sign} {SM : SkolemMapping Sign}, StrictGoodFibration (Base_SetoidCategory Sign) Syntactic_GoodFibration.
Axiom Syntactic_EpsilonHyperModel : forall {Sign} {SM : SkolemMapping Sign}, EpsilonHyperModel Syntactic_StrictGoodFibration.
Axiom Syntactic_AdjointEpsilonFibration : forall {Sign} {SM : SkolemMapping Sign}, 
  @AdjointEpsilonFibration Sign SM (Base_SetoidCategory Sign) (Base_CartesianCategory Sign) (Base_TwoSortCategory Sign) (Base_SyntacticEpsilonModel Sign) Syntactic_GoodFibration Syntactic_StrictGoodFibration Syntactic_EpsilonHyperModel.

(* A Soundness tétel szignatúrája megkövetelte, hogy a Bázis kategória is BCCC legyen.
   Bár a bázisunk tisztán Descartes-i (nyilak nélkül), a teljességi példányosításhoz 
   adunk neki egy dummy axiomatizált BCCC-t. *)
Axiom Dummy_Base_CCC : forall {Sign : Type}, 
  CartesianClosedCategory (Base_SetoidCategory Sign).

Axiom Dummy_Base_BCCC : forall {Sign : Type}, 
  BiCartesianClosedCategory (@Dummy_Base_CCC Sign).
(* ================================================================= *)
(* 6. HYPER COMPLETENESS THEOREM                                     *)
(* ================================================================= *)

(* A kontextus "összecsukása" egyetlen formulává (pont mint az STLC-ben a make_ctx_ty) *)
Fixpoint make_h_ctx {Sign : Type} (G : @h_context Sign) : @h_ty Sign :=
  match G with
  | nil => Ty_Unit
  | Phi :: G' => Ty_Prod (make_h_ctx G') Phi
  end.

(* Kontextus reifikálása bizonyítástermmé (dummy lifttel a vázlat kedvéért) *)
Fixpoint reify_h_ctx {Sign : Type} (G : @h_context Sign) : @h_tm Sign :=
  match G with
  | nil => tm_unit
  | Phi :: G' => tm_pair (reify_h_ctx G') (tm_var 0) 
  end.

(* Szintaktikus azonosságok: A szintaktikus modellben a formulák és kontextusok 
   interpretációja önmagukba (illetve az összecsukott formulába) tér vissza. *)
Axiom interp_h_ty_id : forall {Sign} {SM : SkolemMapping Sign} (I : b_ty) (Phi : @h_ty Sign),
  @interp_h_ty Sign (Base_SetoidCategory Sign) (Base_CartesianCategory Sign) 
    (Base_TwoSortCategory Sign) (Base_SyntacticEpsilonModel Sign) 
    (Fiber_SetoidCategory) (@Syntactic_GoodFibration Sign SM) 
    (@Syntactic_StrictGoodFibration Sign SM) (@Syntactic_EpsilonHyperModel Sign SM) I Phi = Phi.
    
Axiom interp_h_ctx_id : forall {Sign} {SM : SkolemMapping Sign} (I : b_ty) (G : @h_context Sign),
  @interp_h_ctx Sign (Base_SetoidCategory Sign) (Base_CartesianCategory Sign) (Base_TwoSortCategory Sign) (Base_SyntacticEpsilonModel Sign) Syntactic_GoodFibration Syntactic_StrictGoodFibration Syntactic_EpsilonHyperModel I G = make_h_ctx G.

(* --- A NAGY TELJESSÉGI TÉTEL --- *)
Theorem hyper_completeness_inhabitational : 
  forall {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) (G : @h_context Sign) (Phi : @h_ty Sign),
  
  (* PREMISSZA: A formula igaz MINDEN érvényes hiperdoktrínában *)
  (forall (C : SetoidCategory) (CC : CartesianCategory C)
          (BCCC : CartesianClosedCategory C) (BiCCC : BiCartesianClosedCategory BCCC)
          (TSC : TwoSortCategory C) (BEM : BaseEpsilonModel)
          (GF : GoodFibration C) (SGF : StrictGoodFibration C GF)
          (EHM : EpsilonHyperModel SGF)
          (AdEHM : @AdjointEpsilonFibration Sign SM C CC TSC BEM GF SGF EHM),
     inhabited (hom (interp_h_ctx I G) (interp_h_ty I Phi))) ->
     
  (* KONKLÚZIÓ: Akkor létezik hozzá szintaktikus levezetésünk is! *)
  exists (p : @h_tm Sign), inhabited (h_derivation I G p Phi).
Proof.
  intros Sign SM I G Phi H_sem.

  (* 1. PÉLDÁNYOSÍTÁS: Bedobjuk a szintaktikus modellünket a tételbe *)
  pose proof (H_sem 
    (Base_SetoidCategory Sign) 
    (Base_CartesianCategory Sign) 
    Dummy_Base_CCC 
    Dummy_Base_BCCC 
    (Base_TwoSortCategory Sign) 
    (Base_SyntacticEpsilonModel Sign) 
    Syntactic_GoodFibration 
    Syntactic_StrictGoodFibration 
    Syntactic_EpsilonHyperModel 
    Syntactic_AdjointEpsilonFibration) as [f_hom].

  (* 2. TÍPUS VISSZAFORDÍTÁS: Szemantikai típusokról Szintaktikai típusokra *)
  rewrite interp_h_ctx_id in f_hom.
  rewrite interp_h_ty_id in f_hom.

  (* f_hom típusa most már: hom (make_h_ctx G) Phi *)
  (* Ami a mi Fiber_SetoidCategory-nkben pontosan: hom_fiber I (make_h_ctx G) Phi *)
  destruct f_hom as [p_term p_deriv].

  (* 3. A TERM KINYERÉSE: 
     p_deriv egy levezetés üres kontextusban: I | [] |- p_term : (make_h_ctx G) -> Phi 
     Pont, mint az STLC-ben, ezt applikáljuk a reifikált kontextusra! *)
  exists (tm_app p_term (reify_h_ctx G)).
  constructor.
  
  (* Az applikáció és a weakening levezetése *)
  apply HD_App with (Phi := make_h_ctx G).
  - (* A p_term áthozása a nyitott kontextusba *)
    admit. 
  - (* A reifikált kontextus tipizálása *)
    admit.
Admitted.
*)
