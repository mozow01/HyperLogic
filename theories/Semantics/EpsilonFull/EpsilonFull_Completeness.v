(* theories/Semantics/EpsilonFull/EpsilonFull_Completeness.v  *)

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
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.

(* Szintaxis és Fibráció (Epsilon Adjoint) *)
Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax_Lemmas.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax_Lemmas.


Require Import HyperLogic.Semantics.EpsilonFull.Base_EpsilonFull_Completeness.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_Fibration.
Require Import HyperLogic.Semantics.EpsilonFull.Base_EpsilonFull_Completeness.

(* ================================================================= *)
(* 1. A SZINTAKTIKUS SZÁL KATEGÓRIA (FIBER CATEGORY)                 *)
(* ================================================================= *)

(* AZ ÚJ OBJEKTUM: Szigma-típus (Formula + Jólformáltság bizonyítása) *)
Definition wf_ty {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred} (I : b_ty) := 
  { Phi : @h_ty Sign Func Pred & WellFormed I Phi }.

(* ÚJ hom_fiber: Már wf_ty objektumokat köt össze. 
   A levezetés maga marad az üres kontextusban, de a formulákat 
   a projT1 (első elem) segítségével nyerjük ki. *)
Class hom_fiber {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} {I : b_ty} (A B : wf_ty I) : Type := mk_hom_fiber {
  h_tm_of : @h_tm Sign Func Pred;
  h_deriv_of : h_derivation I [] h_tm_of (Ty_Arrow (projT1 A) (projT1 B))
}.

Arguments hom_fiber {Sign Func Pred _ _ SM I} A B.
Arguments mk_hom_fiber {Sign Func Pred _ _ SM I A B} h_tm_of h_deriv_of.
Arguments h_tm_of {Sign Func Pred _ _ SM I A B} _.
Arguments h_deriv_of {Sign Func Pred _ _ SM I A B} _.

(* MORFIZMUS EGYENLŐSÉG: Továbbra is True, hiszen a bizonyítástermek 
   egyenlősége a Vékony (Thin) kategória miatt irreleváns. *)
Definition fiber_equiv {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} {I : b_ty} {A B : wf_ty I} 
  (f g : hom_fiber A B) : Prop := True.

Global Instance fiber_equiv_equivalence
  {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred}
  {SM : SkolemMapping Sign Func Pred} {I : b_ty} {A B : wf_ty I}
  : Equivalence (@fiber_equiv Sign Func Pred _ _ SM I A B).
Proof. constructor; red; intros; unfold fiber_equiv; constructor. Defined.

(* ================================================================= *)
(* KATEGÓRIA KROMBINÁTOROK                                           *)
(* ================================================================= *)

(* IDENTITÁS: Pont mint az STLC id_term *)
Definition id_fiber {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} (I : b_ty) (A : wf_ty I) : hom_fiber A A.
Proof.
  refine (@mk_hom_fiber Sign Func Pred _ _ SM I A A (tm_lam (projT1 A) (tm_var 0)) _).
  apply HD_Lam. 
  apply HD_Var0.
  
  (* Bizonyítjuk a kontextus jólformáltságát a Szigma-típus 2. eleméből *)
  apply AWF_Cons.
  - exact (projT2 A).
  - apply AWF_Nil.
Defined.

(* KOMPOZÍCIÓ Zárt Kombinátorral: \f. \g. \x. f (g x) *)
Definition comp_fiber {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} (I : b_ty) {A B C : wf_ty I} 
  (f : hom_fiber B C) (g : hom_fiber A B) : hom_fiber A C.
Proof.
  refine (@mk_hom_fiber Sign Func Pred _ _ SM I A C 
    (tm_app (tm_app 
       (* A COMP kombinátor: *)
       (tm_lam (Ty_Arrow (projT1 B) (projT1 C)) 
         (tm_lam (Ty_Arrow (projT1 A) (projT1 B)) 
           (tm_lam (projT1 A) 
             (tm_app (tm_var 2) (tm_app (tm_var 1) (tm_var 0))))))
       (* Alkalmazva f-re: *)
       (h_tm_of f)) 
       (* Alkalmazva g-re: *)
    (h_tm_of g)) _).
  
  (* Bizonyítás: *)
  apply HD_App with (Phi := Ty_Arrow (projT1 A) (projT1 B)).
  - apply HD_App with (Phi := Ty_Arrow (projT1 B) (projT1 C)).
    + (* A kombinátor típusolása *)
      apply HD_Lam. apply HD_Lam. apply HD_Lam.
      apply HD_App with (Phi := projT1 B).
      
      * (* tm_var 2 (f) lekérése a kontextus aljáról *)
        apply HD_VarS. 
        -- exact (projT2 A). (* 1. átugrás: a 0. indexű projT1 A jólformált *)
        -- apply HD_VarS.
           ++ apply WF_Arrow; [exact (projT2 A) | exact (projT2 B)]. (* 2. átugrás: az 1. indexű A->B jólformált *)
           ++ apply HD_Var0.
              (* Megérkeztünk a 2. indexhez! Bizonyítjuk a maradék kontextust *)
              apply AWF_Cons.
              ** apply WF_Arrow; [exact (projT2 B) | exact (projT2 C)].
              ** apply AWF_Nil.
              
      * (* tm_app 1 0 kiértékelése *)
        apply HD_App with (Phi := projT1 A).
        -- (* tm_var 1 (g) lekérése *)
           apply HD_VarS.
           ++ exact (projT2 A).
           ++ apply HD_Var0.
              apply AWF_Cons.
              ** apply WF_Arrow; [exact (projT2 A) | exact (projT2 B)].
              ** apply AWF_Cons.
                 --- apply WF_Arrow; [exact (projT2 B) | exact (projT2 C)].
                 --- apply AWF_Nil.
                 
        -- (* tm_var 0 (x) lekérése *)
           apply HD_Var0.
           apply AWF_Cons.
           ++ exact (projT2 A).
           ++ apply AWF_Cons.
              ** apply WF_Arrow; [exact (projT2 A) | exact (projT2 B)].
              ** apply AWF_Cons.
                 --- apply WF_Arrow; [exact (projT2 B) | exact (projT2 C)].
                 --- apply AWF_Nil.
                 
    + (* f típusolása (üres kontextusból!) *)
      exact (h_deriv_of f).
  - (* g típusolása (üres kontextusból!) *)
    exact (h_deriv_of g).
Defined.

(* ================================================================= *)
(* SETOIDCATEGORY PÉLDÁNYOSÍTÁS                                      *)
(* ================================================================= *)

(* Maga a Fiber SetoidCategory példányosítása *)
Instance Fiber_SetoidCategory {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} (I : b_ty) : SetoidCategory.
Proof.
  refine (mk_SetoidCategory 
    (wf_ty I) (* AZ OBJEKTUMOK ITT MÁR A SZIGMA-TÍPUSOK! *)
    (@hom_fiber Sign Func Pred _ _ SM I) 
    (fun X => @id_fiber Sign Func Pred _ _ SM I X)
    (fun X Y Z f g => @comp_fiber Sign Func Pred _ _ SM I X Y Z f g)
    (fun X Y f g => @fiber_equiv Sign Func Pred _ _ SM I X Y f g)
    _ _ _ _ _).
  
  Unshelve.
  all: intros; unfold fiber_equiv; constructor.
Defined.

(* Be is bizonyítjuk, hogy Vékony (Thin) *)
Instance Fiber_Thin {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} (I : b_ty) : Thin (Fiber_SetoidCategory I).
Proof.
  intros x y f g. unfold fiber_equiv; constructor.
Defined.

(* ================================================================= *)
(* 2. FIBER CARTESIAN CATEGORY (Unit, Prod)                          *)
(* ================================================================= *)

(* --- OBJEKTUMOK CSOMAGOLÁSA --- *)
(* A Unit típus jólformáltságának csomagolása Szigma-típusba *)
Definition fiber_unit {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred} (I : b_ty) : wf_ty I :=
  existT _ Ty_Unit (WF_Unit I). (* <--- Itt kapta meg az I-t expliciten! *)

(* A Szorzat típus (And) jólformáltságának csomagolása Szigma-típusba *)
Definition fiber_prod {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred} {I : b_ty} (Y Z : wf_ty I) : wf_ty I :=
  existT _ (Ty_Prod (projT1 Y) (projT1 Z)) (WF_Prod I (projT1 Y) (projT1 Z) (projT2 Y) (projT2 Z)). (* <--- A WF_Prod is megkapja az I-t! *)

(* --- TERMINAL (Unit) --- *)
Definition term_fiber {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} (I : b_ty) (X : wf_ty I) : @hom_fiber Sign Func Pred _ _ SM I X (fiber_unit I).
Proof.
  refine (@mk_hom_fiber Sign Func Pred _ _ SM I X (fiber_unit I) (tm_lam (projT1 X) tm_unit) _).
  apply HD_Lam. 
  apply HD_Unit.
  (* A HD_Unit immár jólformált kontextust vár! *)
  apply AWF_Cons.
  - exact (projT2 X).
  - apply AWF_Nil.
Defined.

(* --- PRODUCT (And) --- *)
(* Kombinátor: \f. \g. \x. (f x, g x) *)
Definition prod_map_fiber {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} (I : b_ty) {X Y Z : wf_ty I} 
  (f : @hom_fiber Sign Func Pred _ _ SM I X Y) (g : @hom_fiber Sign Func Pred _ _ SM I X Z) : @hom_fiber Sign Func Pred _ _ SM I X (fiber_prod Y Z).
Proof.
  refine (@mk_hom_fiber Sign Func Pred _ _ SM I X (fiber_prod Y Z)
    (tm_app (tm_app
      (tm_lam (Ty_Arrow (projT1 X) (projT1 Y))
        (tm_lam (Ty_Arrow (projT1 X) (projT1 Z))
          (tm_lam (projT1 X)
            (tm_pair (tm_app (tm_var 2) (tm_var 0)) (tm_app (tm_var 1) (tm_var 0))))))
      (h_tm_of f)) (h_tm_of g)) _).
      
  (* JAVÍTÁS: Először a 'g' típusát (X Z) adjuk meg, utána az 'f' típusát (X Y) *)
  apply HD_App with (Phi := Ty_Arrow (projT1 X) (projT1 Z)).
  - apply HD_App with (Phi := Ty_Arrow (projT1 X) (projT1 Y)).
    + apply HD_Lam. apply HD_Lam. apply HD_Lam. apply HD_Pair.
      * apply HD_App with (Phi := projT1 X).
        -- (* tm_var 2 (f) lekérése eltolt veremből *)
           apply HD_VarS. 
           ++ exact (projT2 X).
           ++ apply HD_VarS.
              ** apply WF_Arrow; [exact (projT2 X) | exact (projT2 Z)].
              ** apply HD_Var0.
                 apply AWF_Cons.
                 --- apply WF_Arrow; [exact (projT2 X) | exact (projT2 Y)].
                 --- apply AWF_Nil.
        -- (* tm_var 0 (x) lekérése *)
           apply HD_Var0.
           apply AWF_Cons. exact (projT2 X).
           apply AWF_Cons. apply WF_Arrow; [exact (projT2 X) | exact (projT2 Z)].
           apply AWF_Cons. apply WF_Arrow; [exact (projT2 X) | exact (projT2 Y)].
           apply AWF_Nil.
           
      * apply HD_App with (Phi := projT1 X).
        -- (* tm_var 1 (g) lekérése eltolt veremből *)
           apply HD_VarS.
           ++ exact (projT2 X).
           ++ apply HD_Var0.
              apply AWF_Cons.
              ** apply WF_Arrow; [exact (projT2 X) | exact (projT2 Z)].
              ** apply AWF_Cons.
                 --- apply WF_Arrow; [exact (projT2 X) | exact (projT2 Y)].
                 --- apply AWF_Nil.
        -- (* tm_var 0 (x) lekérése megint *)
           apply HD_Var0.
           apply AWF_Cons. exact (projT2 X).
           apply AWF_Cons. apply WF_Arrow; [exact (projT2 X) | exact (projT2 Z)].
           apply AWF_Cons. apply WF_Arrow; [exact (projT2 X) | exact (projT2 Y)].
           apply AWF_Nil.
           
    + exact (h_deriv_of f).
  - exact (h_deriv_of g).
Defined.

Definition fst_fiber {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} (I : b_ty) {X Y : wf_ty I} : @hom_fiber Sign Func Pred _ _ SM I (fiber_prod X Y) X.
Proof.
  refine (@mk_hom_fiber Sign Func Pred _ _ SM I (fiber_prod X Y) X (tm_lam (projT1 (fiber_prod X Y)) (tm_fst (tm_var 0))) _).
  apply HD_Lam. 
  eapply HD_Fst. 
  apply HD_Var0.
  (* Bizonyítjuk a Prod jólformáltságát a kontextusban *)
  apply AWF_Cons.
  - apply WF_Prod; [exact (projT2 X) | exact (projT2 Y)].
  - apply AWF_Nil.
Defined.

Definition snd_fiber {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} (I : b_ty) {X Y : wf_ty I} : @hom_fiber Sign Func Pred _ _ SM I (fiber_prod X Y) Y.
Proof.
  refine (@mk_hom_fiber Sign Func Pred _ _ SM I (fiber_prod X Y) Y (tm_lam (projT1 (fiber_prod X Y)) (tm_snd (tm_var 0))) _).
  apply HD_Lam. 
  eapply HD_Snd. 
  apply HD_Var0.
  (* Bizonyítjuk a Prod jólformáltságát a kontextusban *)
  apply AWF_Cons.
  - apply WF_Prod; [exact (projT2 X) | exact (projT2 Y)].
  - apply AWF_Nil.
Defined.

Instance Fiber_CartesianCategory {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} (I : b_ty) : CartesianCategory (Fiber_SetoidCategory I).
Proof.
  apply (Build_Thin_CC _ (Fiber_Thin I)
    (fiber_unit I) (fun X => @term_fiber Sign Func Pred _ _ SM I X)
    (fun X Y => fiber_prod X Y) (fun X Y Z f g => @prod_map_fiber Sign Func Pred _ _ SM I X Y Z f g)
    (fun X Y => @fst_fiber Sign Func Pred _ _ SM I X Y)
    (fun X Y => @snd_fiber Sign Func Pred _ _ SM I X Y)
  ).
Defined.

(* ================================================================= *)
(* 3. FIBER CARTESIAN CLOSED CATEGORY (Arrow)                        *)
(* ================================================================= *)

(* --- OBJEKTUM CSOMAGOLÁSA --- *)
(* Az Exponenciális típus (Arrow) jólformáltságának csomagolása Szigma-típusba *)
Definition fiber_arrow {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred} {I : b_ty} (Y Z : wf_ty I) : wf_ty I :=
  existT _ (Ty_Arrow (projT1 Y) (projT1 Z)) (WF_Arrow I (projT1 Y) (projT1 Z) (projT2 Y) (projT2 Z)).

(* --- EXPONENTIAL (Implies) --- *)
(* Eval/Apply: \p. (fst p) (snd p) *)
Definition eval_fiber {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} (I : b_ty) {Y Z : wf_ty I} : @hom_fiber Sign Func Pred _ _ SM I (fiber_prod (fiber_arrow Y Z) Y) Z.
Proof.
  refine (@mk_hom_fiber Sign Func Pred _ _ SM I _ _
    (tm_lam (projT1 (fiber_prod (fiber_arrow Y Z) Y)) (tm_app (tm_fst (tm_var 0)) (tm_snd (tm_var 0)))) _).
  apply HD_Lam. 
  apply HD_App with (Phi := projT1 Y).
  - eapply HD_Fst. apply HD_Var0.
    (* Bizonyítjuk a (Y->Z)*Y szorzat jólformáltságát *)
    apply AWF_Cons.
    + apply (WF_Prod I). 
      * apply (WF_Arrow I); [exact (projT2 Y) | exact (projT2 Z)].
      * exact (projT2 Y).
    + apply AWF_Nil.
  - eapply HD_Snd. apply HD_Var0.
    (* Bizonyítjuk a (Y->Z)*Y szorzat jólformáltságát ugyanitt *)
    apply AWF_Cons.
    + apply (WF_Prod I). 
      * apply (WF_Arrow I); [exact (projT2 Y) | exact (projT2 Z)].
      * exact (projT2 Y).
    + apply AWF_Nil.
Defined.

(* Curry kombinátor: \f. \x. \y. f (x, y) *)
Definition curry_fiber {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} (I : b_ty) {X Y Z : wf_ty I} (g : @hom_fiber Sign Func Pred _ _ SM I (fiber_prod X Y) Z) : @hom_fiber Sign Func Pred _ _ SM I X (fiber_arrow Y Z).
Proof.
  refine (@mk_hom_fiber Sign Func Pred _ _ SM I X (fiber_arrow Y Z)
    (tm_app
      (tm_lam (Ty_Arrow (projT1 (fiber_prod X Y)) (projT1 Z))
        (tm_lam (projT1 X)
          (tm_lam (projT1 Y)
            (tm_app (tm_var 2) (tm_pair (tm_var 1) (tm_var 0))))))
      (h_tm_of g)) _).
      
  apply HD_App with (Phi := Ty_Arrow (projT1 (fiber_prod X Y)) (projT1 Z)).
  - apply HD_Lam. apply HD_Lam. apply HD_Lam.
    apply HD_App with (Phi := projT1 (fiber_prod X Y)).
    + (* tm_var 2 lekérése (el kell tolni Y-on és X-en keresztül) *)
      apply HD_VarS. exact (projT2 Y).
      apply HD_VarS. exact (projT2 X).
      apply HD_Var0.
      apply AWF_Cons.
      * apply (WF_Arrow I).
        -- apply (WF_Prod I); [exact (projT2 X) | exact (projT2 Y)].
        -- exact (projT2 Z).
      * apply AWF_Nil.
      
    + eapply HD_Pair.
      * (* tm_var 1 (X) lekérése (el kell tolni Y-on keresztül) *)
        apply HD_VarS. exact (projT2 Y).
        apply HD_Var0.
        apply AWF_Cons. exact (projT2 X).
        apply AWF_Cons. 
        -- apply (WF_Arrow I).
           ++ apply (WF_Prod I); [exact (projT2 X) | exact (projT2 Y)].
           ++ exact (projT2 Z).
        -- apply AWF_Nil.
        
      * (* tm_var 0 (Y) lekérése *)
        apply HD_Var0.
        apply AWF_Cons. exact (projT2 Y).
        apply AWF_Cons. exact (projT2 X).
        apply AWF_Cons. 
        -- apply (WF_Arrow I).
           ++ apply (WF_Prod I); [exact (projT2 X) | exact (projT2 Y)].
           ++ exact (projT2 Z).
        -- apply AWF_Nil.
        
  - exact (h_deriv_of g).
Defined.

Instance Fiber_CartesianClosedCategory {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} (I : b_ty) : CartesianClosedCategory (Fiber_SetoidCategory I).
Proof.
  refine (Build_Thin_CCC _ (Fiber_Thin I)
    (* Az exponenciális objektumképző fv-nél immár az új fiber_arrow-t használjuk! *)
    (fun Z Y => fiber_arrow Y Z)
    (fun Y Z => @eval_fiber Sign Func Pred _ _ SM I Y Z)
    (fun X Y Z g => @curry_fiber Sign Func Pred _ _ SM I X Y Z g)
  ).
Defined.

(* ================================================================= *)
(* 4. FIBER BiCARTESIAN CLOSED CATEGORY (Void, Sum)                  *)
(* ================================================================= *)

(* --- OBJEKTUMOK CSOMAGOLÁSA --- *)
(* A Void típus jólformáltságának csomagolása Szigma-típusba *)
Definition fiber_void {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred} (I : b_ty) : wf_ty I :=
  existT _ Ty_Void (WF_Void I). 

(* A Sum típus (Or) jólformáltságának csomagolása Szigma-típusba *)
Definition fiber_sum {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred} {I : b_ty} (X Y : wf_ty I) : wf_ty I :=
  existT _ (Ty_Sum (projT1 X) (projT1 Y)) (WF_Sum I (projT1 X) (projT1 Y) (projT2 X) (projT2 Y)).

Definition init_fiber {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} (I : b_ty) {X : wf_ty I} : @hom_fiber Sign Func Pred _ _ SM I (fiber_void I) X.
Proof.
  refine (@mk_hom_fiber Sign Func Pred _ _ SM I (fiber_void I) X (tm_lam Ty_Void (tm_absurd (projT1 X) (tm_var 0))) _).
  apply HD_Lam. 
  apply HD_Absurd. 
  - (* ÚJ CÉL: A cél-típus (motive) jólformáltsága *)
    exact (projT2 X).
  - (* RÉGI CÉL: A Ty_Void levezetése a kontextusból *)
    apply HD_Var0.
    (* Bizonyítjuk a Void kontextus jólformáltságát *)
    apply AWF_Cons.
    + apply WF_Void.
    + apply AWF_Nil.
Defined.

(* --- COPRODUCT (Or) --- *)
Definition inl_fiber {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} (I : b_ty) {X Y : wf_ty I} : @hom_fiber Sign Func Pred _ _ SM I X (fiber_sum X Y).
Proof.
  refine (@mk_hom_fiber Sign Func Pred _ _ SM I X (fiber_sum X Y) (tm_lam (projT1 X) (tm_inl (projT1 Y) (tm_var 0))) _).
  apply HD_Lam. 
  apply HD_Inl. 
  - (* ÚJ CÉL: A jobb oldal (Y) jólformáltsága *)
    exact (projT2 Y).
  - (* RÉGI CÉL: A bal oldal (X) levezetése *)
    apply HD_Var0.
    apply AWF_Cons. exact (projT2 X). apply AWF_Nil.
Defined.

Definition inr_fiber {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} (I : b_ty) {X Y : wf_ty I} : @hom_fiber Sign Func Pred _ _ SM I Y (fiber_sum X Y).
Proof.
  refine (@mk_hom_fiber Sign Func Pred _ _ SM I Y (fiber_sum X Y) (tm_lam (projT1 Y) (tm_inr (projT1 X) (tm_var 0))) _).
  apply HD_Lam. 
  apply HD_Inr. 
  - (* ÚJ CÉL: A bal oldal (X) jólformáltsága *)
    exact (projT2 X).
  - (* RÉGI CÉL: A jobb oldal (Y) levezetése *)
    apply HD_Var0.
    apply AWF_Cons. exact (projT2 Y). apply AWF_Nil.
Defined.

(* Coprod kombinátor: \f. \g. \c. case c of inl x => f x | inr y => g y *)
Definition coprod_map_fiber {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} (I : b_ty) {X Y Z : wf_ty I} 
  (f : @hom_fiber Sign Func Pred _ _ SM I X Z) (g : @hom_fiber Sign Func Pred _ _ SM I Y Z) : @hom_fiber Sign Func Pred _ _ SM I (fiber_sum X Y) Z.
Proof.
  refine (@mk_hom_fiber Sign Func Pred _ _ SM I (fiber_sum X Y) Z
    (tm_app (tm_app
      (tm_lam (Ty_Arrow (projT1 X) (projT1 Z))
        (tm_lam (Ty_Arrow (projT1 Y) (projT1 Z))
          (tm_lam (Ty_Sum (projT1 X) (projT1 Y))
            (tm_case (tm_var 0)
              (tm_app (tm_var 3) (tm_var 0))
              (tm_app (tm_var 2) (tm_var 0))))))
      (h_tm_of f)) (h_tm_of g)) _).
      
  (* JAVÍTÁS ITT IS: Először a 'g' típusát (Y Z), utána az 'f' típusát (X Z) adjuk meg! *)
  apply HD_App with (Phi := Ty_Arrow (projT1 Y) (projT1 Z)).
  - apply HD_App with (Phi := Ty_Arrow (projT1 X) (projT1 Z)).
    + apply HD_Lam. apply HD_Lam. apply HD_Lam.
      apply HD_Case with (Phi := projT1 X) (Psi := projT1 Y).
      * (* A case vizsgált kifejezése: c lekérése (var 0) *)
        apply HD_Var0.
        apply AWF_Cons. apply (WF_Sum I); [exact (projT2 X) | exact (projT2 Y)].
        apply AWF_Cons. apply (WF_Arrow I); [exact (projT2 Y) | exact (projT2 Z)].
        apply AWF_Cons. apply (WF_Arrow I); [exact (projT2 X) | exact (projT2 Z)].
        apply AWF_Nil.
        
      * (* inl x => f x *)
        apply HD_App with (Phi := projT1 X).
        -- (* tm_var 3 (f) lekérése eltolva az X-en keresztül *)
           apply HD_VarS. exact (projT2 X).
           apply HD_VarS. apply (WF_Sum I); [exact (projT2 X) | exact (projT2 Y)].
           apply HD_VarS. apply (WF_Arrow I); [exact (projT2 Y) | exact (projT2 Z)].
           apply HD_Var0.
           apply AWF_Cons. apply (WF_Arrow I); [exact (projT2 X) | exact (projT2 Z)].
           apply AWF_Nil.
        -- (* tm_var 0 (x) lekérése *)
           apply HD_Var0.
           apply AWF_Cons. exact (projT2 X).
           apply AWF_Cons. apply (WF_Sum I); [exact (projT2 X) | exact (projT2 Y)].
           apply AWF_Cons. apply (WF_Arrow I); [exact (projT2 Y) | exact (projT2 Z)].
           apply AWF_Cons. apply (WF_Arrow I); [exact (projT2 X) | exact (projT2 Z)].
           apply AWF_Nil.
           
      * (* inr y => g y *)
        apply HD_App with (Phi := projT1 Y).
        -- (* tm_var 2 (g) lekérése eltolva az Y-on keresztül *)
           apply HD_VarS. exact (projT2 Y).
           apply HD_VarS. apply (WF_Sum I); [exact (projT2 X) | exact (projT2 Y)].
           apply HD_Var0.
           apply AWF_Cons. apply (WF_Arrow I); [exact (projT2 Y) | exact (projT2 Z)].
           apply AWF_Cons. apply (WF_Arrow I); [exact (projT2 X) | exact (projT2 Z)].
           apply AWF_Nil.
        -- (* tm_var 0 (y) lekérése *)
           apply HD_Var0.
           apply AWF_Cons. exact (projT2 Y).
           apply AWF_Cons. apply (WF_Sum I); [exact (projT2 X) | exact (projT2 Y)].
           apply AWF_Cons. apply (WF_Arrow I); [exact (projT2 Y) | exact (projT2 Z)].
           apply AWF_Cons. apply (WF_Arrow I); [exact (projT2 X) | exact (projT2 Z)].
           apply AWF_Nil.
           
    + exact (h_deriv_of f).
  - exact (h_deriv_of g).
Defined. 

Instance Fiber_BiCartesianClosedCategory {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} (I : b_ty) : BiCartesianClosedCategory (Fiber_CartesianClosedCategory I).
Proof.
  apply (Build_Thin_BiCCC (Fiber_SetoidCategory I) (Fiber_CartesianClosedCategory I) (Fiber_Thin I)
    (fiber_void I) (fun X => @init_fiber Sign Func Pred _ _ SM I X)
    (fun X Y => fiber_sum X Y) (fun X Y => @inl_fiber Sign Func Pred _ _ SM I X Y) (fun X Y => @inr_fiber Sign Func Pred _ _ SM I X Y)
    (fun X Y Z f g => @coprod_map_fiber Sign Func Pred _ _ SM I X Y Z f g)
  ).
Defined.

(* Szükségünk lesz a List map függvényére a kontextus helyettesítéséhez *)
Require Import Coq.Lists.List.

(* Lemma az All_Elim és Ex_Intro konverziójához *)
Lemma form_equiv_subst_comm_elim : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred}
  {I J A : b_ty} (t : @b_tm Sign Func) (f : @b_tm Sign Func) (Phi : @h_ty Sign Func Pred)
  (dt : base_typing I t J) (df : base_typing J f A),
  WellFormed (b_Prod J A) Phi ->
  form_equiv I
    (form_subst (b_pair b_id (b_comp f t)) (form_subst (b_subst_ext t) Phi))
    (form_subst t (form_subst (b_pair b_id f) Phi)).
Proof.
intros Sign Func Pred HFunc HPred SM I J A t f Phi dt df Hwf.
  eapply FE_Trans.
  - (* 1. Lépés: (Phi.[b_subst_ext t]).[<id, f o t>] ≡ Phi.[b_subst_ext t o <id, f o t>] *)
    eapply FE_Pullback_Comp.
    + (* A Coq először a BELSŐ helyettesítést kéri: b_subst_ext t *)
      eapply typing_subst_ext. exact dt.
    + (* Aztán a KÜLSŐ helyettesítést: <id, f o t> *)
      eapply BT_Pair.
      * apply BT_Id.
      * eapply BT_Comp; eassumption.
    + exact Hwf.
  - eapply FE_Trans.
    + (* 2. Lépés: A Bázis Kommutálás (ext t o <id, f o t> ≡ <id, f> o t) *)
      eapply FE_Pullback_Cong.
      * unfold b_subst_ext.
        (* Közös nevező bevezetése automatikusan: < t, f o t > *)
        eapply BE_Trans. 
        
        -- (* BAL OLDAL: <t o fst, snd> o <id, f o t> ≡ <t, f o t> *)
           eapply BE_Trans.
           ++ (* 1. Bevisszük a kompozíciót a párba *)
              apply BE_CompPair. 
           ++ (* 2. Tagonként redukálunk *)
              eapply BE_CongPair.
              ** (* Első tag: (t o fst) o <id, f o t> ≡ t *)
                 eapply BE_Trans.
                 --- eapply BE_Sym. apply BE_Assoc. (* <-- ITT A JAVÍTÁS: Szimmetria! *)
                 --- eapply BE_Trans.
                     +++ eapply BE_CongComp. 
                         *** apply BE_BetaFst. (* A belső tag: fst o <id, ..> ≡ id *)
                         *** apply BE_Refl.    (* A külső tag: t ≡ t *)
                     +++ apply BE_IdR.         
              ** (* Második tag: snd o <id, f o t> ≡ f o t *)
                 apply BE_BetaSnd.
                 
        -- (* JOBB OLDAL: <id, f> o t ≡ <t, f o t> inverze *)
           eapply BE_Sym. 
           eapply BE_Trans.
           ++ (* 1. Bevisszük a kompozíciót a párba *)
              apply BE_CompPair.
           ++ (* 2. Tagonként redukálunk *)
              eapply BE_CongPair.
              ** (* Első tag: id o t ≡ t *)
                 apply BE_IdL.
              ** (* Második tag: (f o t) ≡ (f o t) *)
                 apply BE_Refl.
                 
      * exact Hwf.
  + (* 3. Lépés: Phi.[<id, f> o t] ≡ (Phi.[<id, f>]).[t] inverze *)
      eapply FE_Sym. eapply FE_Pullback_Comp.
      * (* A BELSŐ helyettesítés: <id, f> *)
        eapply BT_Pair.
        -- apply BT_Id.
        -- exact df.
      * (* A KÜLSŐ helyettesítés: t *)
        exact dt.
      * exact Hwf.

  (* --- A POLC LESÖPRÉSE (Unshelve Magic) --- *)
  Unshelve.
  all: repeat match goal with
  | |- base_typing _ _ _ => eapply BT_Comp || eapply BT_Pair || apply BT_Id || eapply BT_Fst || eapply BT_Snd || apply typing_subst_ext || eassumption
  end.
Defined.   


(* Lemma az Ex_Elim és Eps_Elim premisszájához (fst kommutálás) *)
Lemma form_equiv_subst_comm_fst : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred}
  {I J A : b_ty} (t : @b_tm Sign Func) (Chi : @h_ty Sign Func Pred)
  (dt : base_typing I t J),
  WellFormed J Chi ->
  form_equiv (b_Prod I A)
    (form_subst (b_subst_ext t) (form_subst b_fst Chi))
    (form_subst b_fst (form_subst t Chi)).
Proof.
  intros Sign Func Pred HFunc HPred SM I J A t Chi dt Hwf.
  eapply FE_Trans.
  - (* 1. (Chi.[fst]).[b_subst_ext t] ≡ Chi.[fst o b_subst_ext t] *)
    eapply FE_Pullback_Comp.
    + eapply BT_Fst.
    + apply typing_subst_ext. exact dt.
    + exact Hwf.
  - eapply FE_Trans.
    + (* 2. fst o b_subst_ext t ≡ t o fst *)
      eapply FE_Pullback_Cong.
      * unfold b_subst_ext. apply BE_BetaFst.
      * exact Hwf.
    + (* 3. Chi.[t o fst] ≡ (Chi.[t]).[fst] inverze *)
      eapply FE_Sym. eapply FE_Pullback_Comp.
      * exact dt.
      * apply BT_Fst.
      * exact Hwf.

  Unshelve.
  all: repeat match goal with
  | |- base_typing _ _ _ => eapply BT_Comp || apply BT_Fst || apply BT_Snd || apply typing_subst_ext || eassumption
  end.
Defined.

Lemma ctx_subst_ext_comm : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred} 
  {I J A : b_ty} (t : @b_tm Sign Func) (dt : base_typing I t J) (G : @h_context Sign Func Pred),
  All_WellFormed J G ->
  ctx_equiv (b_Prod I A) 
            (ctx_subst (b_subst_ext t) (ctx_subst b_fst G)) 
            (ctx_subst b_fst (ctx_subst t G)).
Proof.
  intros Sign Func Pred HFunc HPred SM I J A t dt G Hwf.
  induction Hwf.
  - (* AWF_Nil *)
    simpl. apply CEq_Nil.
  - (* AWF_Cons *)
    simpl. apply CEq_Cons.
    + eapply FE_Trans.
      * (* 1. (Phi.[fst]).[b_subst_ext t] ≡ Phi.[fst o (b_subst_ext t)] *)
        eapply FE_Pullback_Comp.
        -- eapply BT_Fst.
        -- apply typing_subst_ext. exact dt.
        -- assumption. (* A belső WellFormed bizonyítás! *)
      * eapply FE_Trans.
        -- (* 2. A bázis kompozíciók ekvivalenciája (A Béta-redukció mágiája) *)
           eapply FE_Pullback_Cong.
           ++ unfold b_subst_ext. apply BE_BetaFst.
           ++ eapply w.
        -- (* 3. Phi.[t o fst] ≡ (Phi.[t]).[fst] inverze *)
           eapply FE_Sym. eapply FE_Pullback_Comp.
           ++ exact dt.
           ++ apply BT_Fst.
           ++ assumption.
    + exact IHHwf.
    Unshelve.
  all: repeat match goal with
  | |- base_typing _ _ _ => eapply BT_Comp || apply BT_Fst || apply BT_Snd || apply typing_subst_ext || eassumption || typeclasses eauto
  end.
Defined.


(* ================================================================= *)
(* ÁLTALÁNOS HELYETTESÍTÉSI LEMMA                    *)
(* ================================================================= *)

(* Az Általános Inverz Helyettesítési Lemma: 
   Ha egy f-fel helyettesített formula jólformált, és f érvényes morfizmus, 
   akkor az eredeti formula is jólformált volt. *)
Lemma form_wf_subst_inv : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} {I J : b_ty} 
  (f : @b_tm Sign Func) (df : base_typing I f J) (Phi : @h_ty Sign Func Pred),
  WellFormed I (form_subst f Phi) -> WellFormed J Phi.
Proof.
  intros Sign Func Pred HFunc HPred SM I J f df Phi.
  (* Fontos: a kontextusokat generalizáljuk, hogy az IH a b_subst_ext-re is működjön *)
  generalize dependent J. generalize dependent I. generalize dependent f.
  
  (* Indukció a formula (Phi) szerkezetén! 
     JAVÍTÁS: Helyes sorrend az intros-ban (f, I, J, df) *)
  induction Phi; intros f I J df Hwf; simpl in Hwf; inversion Hwf; subst.
  
  - (* Ty_Unit *) apply WF_Unit.
  - (* Ty_Void *) apply WF_Void.
  - (* Ty_Prod *) apply WF_Prod; [eapply IHPhi1 | eapply IHPhi2]; eassumption.
  - (* Ty_Sum  *) apply WF_Sum;  [eapply IHPhi1 | eapply IHPhi2]; eassumption.
  - (* Ty_Arrow*) apply WF_Arrow;[eapply IHPhi1 | eapply IHPhi2]; eassumption.
  
  - (* Ty_Atom *) 
    match goal with
    | [ H_typ : base_typing _ (b_comp _ _) _ |- _ ] => inversion H_typ; subst
    end.
    (* A base_typing_unique lemmáddal bebizonyítjuk, hogy a közbülső B típus egyezik J-vel! *)
    assert (H_eq : J = B). { eapply base_typing_unique. exact df. eassumption. }
    subst B.
    eapply WF_Atom. eassumption.
    
  - (* Ty_All *) 
    apply WF_All.
    eapply IHPhi. 2: eassumption.
    (* A b_subst_ext tipizálása kézzel felépítve *)
    unfold b_subst_ext.
    eapply BT_Pair.
    + eapply BT_Comp. exact df. apply BT_Fst.
    + apply BT_Snd.
    
  - (* Ty_Ex *) 
    apply WF_Ex.
    eapply IHPhi. 2: eassumption.
    unfold b_subst_ext.
    eapply BT_Pair.
    + eapply BT_Comp. exact df. apply BT_Fst.
    + apply BT_Snd.
Defined.



(* Step 2: Structural Inversion Lemma for Formulas pulled back along the first projection. *)
Lemma form_wf_fst_inv : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} {I A : b_ty} {Phi : @h_ty Sign Func Pred},
  WellFormed (b_Prod I A) (form_subst b_fst Phi) -> WellFormed I Phi.
Proof.
  intros Sign Func Pred HFunc HPred SM I A Phi Hwf.
  eapply form_wf_subst_inv.
  - eapply BT_Fst. (* A 'f' morfizmusunk itt a b_fst *)
  - exact Hwf.
Defined.
(* Step 3: Structural Inversion Lemma for Contexts pulled back along the first projection. *)
Lemma ctx_wf_fst_inv : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} {I A : b_ty} {G : @h_context Sign Func Pred},
  All_WellFormed (b_Prod I A) (ctx_subst b_fst G) -> All_WellFormed I G.
Proof.
  intros Sign Func Pred HFunc HPred SM I A G H.
  induction G.
  - (* Case: G is nil *)
    simpl in H. inversion H. apply AWF_Nil.
  - (* Case: G is a :: G' *)
    simpl in H. 
    (* JAVÍTÁS: A helyes minta [| formula kontextus fej_biz farok_biz] *)
    inversion H as [| ? ? H_head H_tail]; subst.
    apply AWF_Cons.
    + (* Prove WellFormed for the head of the list *)
      eapply form_wf_fst_inv. exact H_head.
    + (* Prove All_WellFormed for the tail of the list *)
      apply IHG. exact H_tail.
Defined.

Lemma meta_ctx_wf : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} {I : b_ty} 
  {G : @h_context Sign Func Pred} {p : @h_tm Sign Func Pred} {Phi : @h_ty Sign Func Pred},
  h_derivation I G p Phi -> @All_WellFormed Sign Func Pred _ _ I G.
Proof.
intros Sign Func Pred HFunc HPred SM I G p Phi Hderiv.
  induction Hderiv.
  - (* HD_Var0 *)  
    exact a.
  - (* HD_VarS *) 
    apply AWF_Cons; assumption.
  - (* HD_Unit *) 
    exact a.
  - (* HD_Conv *) 
    exact IHHderiv.
  - (* HD_Ctx_Conv *)
    eapply ctx_equiv_wf_right.
    + exact c.         (* Ez a ctx_equiv I G1 G2 *)
    + exact IHHderiv.  (* Ez pedig a All_WellFormed I G1 *) 
    
  - (* HD_Lam *) 
    (* A Lam bevezetésnél a kontextus (Phi :: G). Az inverzió leveszi a fejet. *)
    inversion IHHderiv; subst; assumption.
  - (* HD_App *) 
    exact IHHderiv1.
  - (* HD_Pair *) 
    exact IHHderiv1.
  - (* HD_Fst *) 
    exact IHHderiv.
  - (* HD_Snd *) 
    exact IHHderiv.
  - (* HD_Inl *) 
    exact IHHderiv.
  - (* HD_Inr *) 
    exact IHHderiv.
  - (* HD_Case *) 
    exact IHHderiv1.
  - (* HD_Absurd *) 
    exact IHHderiv.
  - (* HD_All_Intro *) 
    (* ITT A MÁGIA: A tegnap megírt inverziós lemmánk egyből megoldja a kontextus eltolást! *)
    apply ctx_wf_fst_inv in IHHderiv. 
    exact IHHderiv.
  - (* HD_All_Elim *) 
    exact IHHderiv.
  - (* HD_Ex_Intro *) 
    exact IHHderiv.
  - (* HD_Ex_Elim *) 
     exact IHHderiv1.
  - (* HD_Eps_Intro *) 
    exact IHHderiv.
  - (* HD_Eps_Elim *) 
    exact IHHderiv1.
Defined.



(* Strukturális Metatétel (Context Regularity): 
   Ha egy kontextusból le lehet vezetni valamit, akkor az a kontextus jólformált.
   ESKÜ: Ezt a projekt végén egy standard strukturális indukcióval lemmává alakítjuk! *)
Lemma meta_ctx_wf_base : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} {I A : b_ty} 
  {G : @h_context Sign Func Pred} {p : @h_tm Sign Func Pred} {Phi : @h_ty Sign Func Pred},
  h_derivation (b_Prod I A) (ctx_subst b_fst G) p Phi -> All_WellFormed I G.
Proof.
  intros Sign Func Pred HFunc HPred SM I A G p Phi H.
  (* Step 1 (from plan): Apply the general context regularity lemma. *)
  apply meta_ctx_wf in H.
  (* Step 2 & 3 (from plan): Apply the context inversion lemma to get the result for the original context. *)
  apply ctx_wf_fst_inv in H.
  (* Step 4 (from plan): The goal is now exactly the hypothesis. *)
  exact H.
Defined.

Lemma meta_type_wf : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} {I : b_ty} 
  {G : @h_context Sign Func Pred} {p : @h_tm Sign Func Pred} {Phi : @h_ty Sign Func Pred},
  h_derivation I G p Phi -> WellFormed I Phi.
Proof.
  intros Sign Func Pred HFunc HPred SM I G p Phi Hderiv.
  induction Hderiv; simpl.
  - (* HD_Var0 *) inversion a; subst; assumption.
  - (* HD_VarS *) assumption.
  - (* HD_Unit *) apply WF_Unit.
  - (* HD_Conv *) 
    (* A form_equiv_wf lemma visszaadja a Phi és Psi jólformáltságát egy párban.
       Nekünk csak a második (Psi) kell. *)
    destruct (form_equiv_wf I Phi Psi f) as [_ Hwf_Psi].
    exact Hwf_Psi.
  - (* HD_Ctx_Conv *) assumption.
  - (* HD_Lam *) 
    apply WF_Arrow.
    + (* Itt kell a meta_ctx_wf a premisszára! *)
      apply meta_ctx_wf in Hderiv. inversion Hderiv; subst. assumption.
    + assumption.
  - (* HD_App *) inversion IHHderiv1; subst; assumption.
  - (* HD_Pair *) apply WF_Prod; assumption.
  - (* HD_Fst *) inversion IHHderiv; subst; assumption.
  - (* HD_Snd *) inversion IHHderiv; subst; assumption.
  - (* HD_Inl *) apply WF_Sum; assumption.
  - (* HD_Inr *) apply WF_Sum; assumption.
  - (* HD_Case *) assumption.
  - (* HD_Absurd *)
    exact w. 
  - (* HD_All_Intro *) apply WF_All. apply IHHderiv.
  - (* HD_All_Elim *) 
    eapply wf_subst.
    + (* Konstruáljuk meg a <id, f> tipizálását! *)
      eapply BT_Pair.
      * apply BT_Id.   (* Az id tipizálása: I -> I *)
      * exact b.       (* Az f tipizálása: I -> A *)
    + (* A maradék ugyanaz *)
      inversion IHHderiv; subst; assumption.
  - (* HD_Ex_Intro *)
    apply WF_Ex.
    (* Visszanyerjük a mag (Phi) jólformáltságát a helyettesített verzióból *)
    eapply form_wf_subst_inv.
    + (* 1. A helyettesítés (<id, f>) típushelyességének bizonyítása *)
      eapply BT_Pair.
      * apply BT_Id.
      * exact b.
    + (* 2. A helyettesített formula jólformáltsága (ezt adja az IH) *)
      exact IHHderiv.
  - (* HD_Ex_Elim *)
    apply form_wf_fst_inv in IHHderiv2.
    exact IHHderiv2.
  - (* HD_Eps_Intro *)
    eapply wf_subst.
    + eapply BT_Pair. apply BT_Id. apply BT_Const.
    + (* Visszanyerjük a mag (Phi) jólformáltságát a Phi.[f] helyettesített verzióból *)
      eapply form_wf_subst_inv.
      * eapply BT_Pair.
        -- apply BT_Id.
        -- exact b.
      * exact IHHderiv.
  - (* HD_Eps_Elim *)
    apply form_wf_fst_inv in IHHderiv2.
    exact IHHderiv2.
Defined.

Lemma meta_all_body_wf : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} {I A : b_ty} 
  {G : @h_context Sign Func Pred} {p : @h_tm Sign Func Pred} {Phi : @h_ty Sign Func Pred},
  h_derivation I G p (Ty_All A Phi) -> WellFormed (b_Prod I A) Phi.
Proof.
intros Sign Func Pred HFunc HPred SM I A G p Phi Hderiv.
  (* 1. Rászabadítjuk a Mester Lemmát a levezetésre *)
  apply meta_type_wf in Hderiv.
  (* 2. Az inverzió lehámozza a Forall kvantort *)
  inversion Hderiv; subst.
  (* 3. Készen is vagyunk! *)
  assumption.
Defined.

(* Strukturális Metatétel: A helyettesítés megtartja a jólformáltságot *)
Lemma meta_subst_wf : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} {I J : b_ty} 
  (t : @b_tm Sign Func) (dt : base_typing I t J) (Phi : @h_ty Sign Func Pred),
  @WellFormed Sign Func Pred _ _ J Phi -> @WellFormed Sign Func Pred _ _ I (form_subst t Phi).
Proof.
intros Sign Func Pred HFunc HPred SM I J t dt Phi Hwf.
  eapply wf_subst.
  - exact dt.
  - exact Hwf.
Defined.

(* Strukturális Metatétel: Az Ex magja jólformált (A helyettesített verzió) *)
Lemma meta_ex_body_wf : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} {I A : b_ty} 
  {G : @h_context Sign Func Pred} {p : @h_tm Sign Func Pred} {Phi : @h_ty Sign Func Pred} {f : @b_tm Sign Func},
  base_typing I f A -> h_derivation I G p (form_subst (b_pair b_id f) Phi) -> @WellFormed Sign Func Pred _ _ (b_Prod I A) Phi.
Proof.
intros Sign Func Pred HFunc HPred SM I A G p Phi f dt Hderiv.
  (* 1. A levezetésből kinyerjük a helyettesített formula jólformáltságát *)
  apply meta_type_wf in Hderiv.
  
  (* 2. A form_wf_subst_inv lemmával visszafejtjük az eredeti formulát *)
  eapply form_wf_subst_inv.
  - (* A helyettesítés (<id, f>) típushelyességének bizonyítása *)
    eapply BT_Pair.
    + apply BT_Id.
    + exact dt.
  - (* A helyettesített formula jólformáltsága *)
    exact Hderiv.
Defined.

(* Strukturális Metatétel: Az Ex magja jólformált (Az alap verzió) *)
Lemma meta_ex_body_wf_base : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} {I A : b_ty} 
  {G : @h_context Sign Func Pred} {p : @h_tm Sign Func Pred} {Phi : @h_ty Sign Func Pred},
  h_derivation I G p (Ty_Ex A Phi) -> @WellFormed Sign Func Pred _ _ (b_Prod I A) Phi.
Proof.
intros Sign Func Pred HFunc HPred SM I A G p Phi Hderiv.
  (* 1. A levezetés kimenete garantáltan jólformált *)
  apply meta_type_wf in Hderiv.
  (* 2. Felnyitjuk az Ex kvantort, ami megadja a belső formula jólformáltságát *)
  inversion Hderiv; subst.
  (* 3. Készen is vagyunk! *)
  assumption.
Defined.

(* Strukturális Metatétel: A Case (Ex_Elim) visszatérési típusa jólformált *)
Lemma meta_ex_elim_chi_wf : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} {I A : b_ty} 
  {G : @h_context Sign Func Pred} {p1 p2 : h_tm} {Phi Chi : @h_ty Sign Func Pred},
  h_derivation I G p1 (Ty_Ex A Phi) ->
  h_derivation (b_Prod I A) (Phi :: ctx_subst b_fst G) p2 (form_subst b_fst Chi) ->
  @WellFormed Sign Func Pred _ _ I Chi.
Proof.
intros Sign Func Pred HFunc HPred SM I A G p1 p2 Phi Chi H1 H2.
  (* 1. A második levezetésből kinyerjük a helyettesített Chi jólformáltságát *)
  apply meta_type_wf in H2.
  
  (* 2. A form_wf_fst_inv lemmával lehámozzuk a fst eltolást *)
  eapply form_wf_fst_inv.
  exact H2.
Defined.


(* Strukturális Metatétel: Az Epszilon magja jólformált *)
Lemma meta_eps_body_wf : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} {I A : b_ty} 
  {G : @h_context Sign Func Pred} {p : @h_tm Sign Func Pred} {Phi : @h_ty Sign Func Pred} {f : @b_tm Sign Func},
  base_typing I f A -> h_derivation I G p (Phi .[ f ]) -> @WellFormed Sign Func Pred _ _ (b_Prod I A) Phi.
Proof.
intros Sign Func Pred HFunc HPred SM I A G p Phi f dt Hderiv.
  (* 1. A levezetésből kinyerjük a helyettesített formula jólformáltságát *)
  apply meta_type_wf in Hderiv.
  
  (* 2. A form_wf_subst_inv lemmával visszafejtjük az eredeti formulát *)
  eapply form_wf_subst_inv.
  - eapply BT_Pair.
    + apply BT_Id.
    + exact dt.
  - exact Hderiv.
Defined.

(* Kategóriaelméleti Axióma (Beck-Chevalley az Epszilonra): 
   A visszahúzás (helyettesítés) kommutál az Epszilon-képzéssel. 
   Ezt a szemantikában az Adjoint Epsilon Fibration garantálja! *)
Lemma meta_eps_bc : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} {I J A : b_ty} 
  (t : @b_tm Sign Func) (dt : base_typing I t J) (Phi : @h_ty Sign Func Pred),
  @WellFormed Sign Func Pred _ _ (b_Prod J A) Phi ->
  form_equiv I 
    ((form_subst (b_subst_ext t) Phi) .[ ε A, form_subst (b_subst_ext t) Phi ])
    (form_subst t (Phi .[ ε A, Phi ])).
Proof.
  intros Sign Func Pred HFunc HPred SM I J A t dt Phi wf.
  (* Mivel betettük a szintaxisba, ez most már egyetlen lépés! *)
  eapply FE_Eps_BC.
  - exact dt.
  - exact wf.
Defined.

Lemma meta_eps_elim_body_wf : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} {I A : b_ty} 
  {G : @h_context Sign Func Pred} {p : @h_tm Sign Func Pred} {Phi : @h_ty Sign Func Pred},
  h_derivation I G p (Phi .[ ε A, Phi ]) -> @WellFormed Sign Func Pred _ _ (b_Prod I A) Phi.
Proof.
intros Sign Func Pred HFunc HPred SM I A G p Phi Hderiv.
  (* 1. A levezetésből kinyerjük a helyettesített formula jólformáltságát *)
  apply meta_type_wf in Hderiv.
  
  (* 2. A form_wf_subst_inv lemmával visszafejtjük az eredeti formulát *)
  eapply form_wf_subst_inv.
  - (* A helyettesítés (<id, ε A, Phi>) típushelyességének bizonyítása *)
    eapply BT_Pair.
    + apply BT_Id.
    + eapply BT_Const. (* Az epszilon-term tipizálása *)
  - (* A helyettesített formula jólformáltsága *)
    exact Hderiv.
Defined.

Lemma meta_eps_elim_chi_wf : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} {I A : b_ty} 
  {G : @h_context Sign Func Pred} {p1 p2 : h_tm} {Phi Chi : @h_ty Sign Func Pred},
  h_derivation I G p1 (Phi .[ ε A, Phi ]) ->
  h_derivation (b_Prod I A) (Phi :: ctx_subst b_fst G) p2 (form_subst b_fst Chi) ->
  @WellFormed Sign Func Pred _ _ I Chi.
Proof.
intros Sign Func Pred HFunc HPred SM I A G p1 p2 Phi Chi H1 H2.
  (* 1. A második levezetésből kinyerjük az eltolt Chi jólformáltságát *)
  apply meta_type_wf in H2.
  
  (* 2. A form_wf_fst_inv lemmával visszanyerjük az alap Chi-t *)
  eapply form_wf_fst_inv.
  exact H2.
Defined.

(* Lemma: A helyettesítés megőrzi a kontextus jólformáltságát *)
Lemma ctx_wf_subst : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} {I J : b_ty} 
  (t : @b_tm Sign Func) (dt : base_typing I t J) (G : @h_context Sign Func Pred),
  All_WellFormed J G -> All_WellFormed I (ctx_subst t G).
Proof.
  intros Sign Func Pred HFunc HPred SM I J t dt G Hwf.
  induction Hwf.
  - (* Nil eset *)
    simpl. apply AWF_Nil.
  - (* Cons eset *)
    simpl. apply AWF_Cons.
    + eapply wf_subst; eassumption.
    + exact IHHwf.
Defined.

Lemma h_derivation_subst_general : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} 
  {I J : b_ty} (t : @b_tm Sign Func) (dt : base_typing I t J) (G : @h_context Sign Func Pred) (Phi : @h_ty Sign Func Pred) (p : @h_tm Sign Func Pred),
  h_derivation J G p Phi -> 
  h_derivation I (ctx_subst t G) (tm_subst t p) (form_subst t Phi).
Proof.
  intros Sign Func Pred HFunc HPred SM I J t dt G Phi p Hderiv.
  revert I t dt.
  induction Hderiv; intros I0 t0 dt0.
  - (* HD_Var0 *)
    simpl. apply HD_Var0.
    (* Szétszedjük a meglévő kontextus jólformáltságát *)
    inversion a; subst.
    apply AWF_Cons.
    + (* A formula megőrzi a jólformáltságát a helyettesítés után *)
      eapply wf_subst. eassumption. exact X.
    + (* A maradék kontextus is megőrzi a jólformáltságát *)
      eapply ctx_wf_subst. eassumption. exact X0.
  - (* HD_VarS *)
    simpl. apply HD_VarS.
    + eapply wf_subst. exact dt0. exact w.
    + (* 2. Cél: A maradék levezetésre alkalmazzuk az indukciós hipotézist *)
      apply IHHderiv. exact dt0. 
  - (* HD_Unit *)
    simpl. (* tm_subst t0 tm_unit-ból tm_unit lesz *)
    apply HD_Unit.
    (* Itt kéri a kontextus jólformáltságát: All_WellFormed I0 (ctx_subst t0 G) *)
    eapply ctx_wf_subst.
    + exact dt0. (* A bázis típusozás: t0 : I0 -> I *)
    + exact a.   (* Az eredeti kontextus jólformáltsága, ami ott van a környezetedben! *) 
  - (* HD_Conv *)
    eapply HD_Conv.
    + (* 1. Levezetés: itt van az IHHderiv! *)
      apply IHHderiv. exact dt0.
    + (* 2. Ekvivalencia: form_equiv (Phi.[t]) (Psi.[t]) *)
      (* Ide NEM wf_subst kell, hanem form_equiv_subst! *)
      eapply form_equiv_subst.
      * exact dt0.  
      * exact f.
  - (* HD_Ctx_Conv *)
    eapply HD_Ctx_Conv.
    + eapply ctx_equiv_subst. exact dt0. exact c.
    + apply IHHderiv. exact dt0.
  - (* HD_Lam *)
    simpl. apply HD_Lam. apply IHHderiv. exact dt0.
  - (* HD_App *)
    simpl. eapply HD_App.
    + apply IHHderiv1. exact dt0.
    + apply IHHderiv2. exact dt0.
  - (* HD_Pair *)
    simpl. apply HD_Pair.
    + apply IHHderiv1. exact dt0.
    + apply IHHderiv2. exact dt0.
  - (* HD_Fst *)
    simpl. eapply HD_Fst. apply IHHderiv. exact dt0.
  - (* HD_Snd *)
    simpl. eapply HD_Snd. apply IHHderiv. exact dt0.
  - (* HD_Inl *)
    simpl. apply HD_Inl.
    + (* 1. gól: A Psi jólformáltsága a helyettesítés után *)
      eapply wf_subst.
      * exact dt0.
      * exact w.
    + (* 2. gól: A Phi levezetése (Indukciós Hipotézis) *)
      apply IHHderiv.
      exact dt0.
  - (* HD_Inr *)
    simpl. apply HD_Inr.
    + (* 1. cél: A bal oldal (Phi) jólformáltsága a helyettesítés után *)
      eapply wf_subst.
      * exact dt0.
      * exact w.
    + (* 2. cél: A jobb oldal (Psi) levezetése az IH segítségével *)
      apply IHHderiv.
      exact dt0.
  - (* HD_Case *)
    simpl. eapply HD_Case.
    + apply IHHderiv1. exact dt0.
    + apply IHHderiv2. exact dt0.
    + apply IHHderiv3. exact dt0.
  - (* HD_Absurd *)
    simpl. apply HD_Absurd.
    + (* 1. cél: A motive (Phi) jólformáltsága a helyettesítés után *)
      eapply wf_subst.
      * exact dt0.
      * exact w.
    + (* 2. cél: A Void levezetése (Indukciós Hipotézis) *)
      (* Megjegyzés: (form_subst t0 Ty_Void) az egyszerűen Ty_Void *)
      apply IHHderiv.
      exact dt0.
  
  - (* HD_All_Intro *)
    simpl. apply HD_All_Intro.
    eapply HD_Ctx_Conv.
    + (* 1. Premissza: A kontextusok ekvivalenciája *)
      eapply ctx_subst_ext_comm. 
      * exact dt0.
      * eapply meta_ctx_wf_base. exact Hderiv. (* Itt a pontosított axióma! *)
    + (* 2. Premissza: Az Indukciós Hipotézis *)
      apply IHHderiv. 
      apply typing_subst_ext. exact dt0.

  - (* HD_All_Elim *)
    simpl. eapply HD_Conv.
    + eapply HD_All_Elim.
      * apply IHHderiv. exact dt0.
      * eapply BT_Comp. eassumption. exact dt0.
    + (* AZ ADMIT HELYE: Itt aratjuk le az előző lemmánk gyümölcsét! *)
      eapply form_equiv_subst_comm_elim.
      * exact dt0.
      * exact b. (* A 'b' változó a célodban pontosan az 'f' tipizálása! *)
      * eapply meta_all_body_wf. exact Hderiv.

  - (* HD_Ex_Intro *)
    simpl. eapply HD_Ex_Intro.
    + eapply BT_Comp. eassumption. exact dt0.
    + eapply HD_Conv. (* A premisszán belül konvertálunk! *)
      * apply IHHderiv. exact dt0.
      * (* AZ ADMIT HELYE: Szimmetria + az előző lemmánk! *)
        eapply FE_Sym. 
        eapply form_equiv_subst_comm_elim.
        -- exact dt0.
        -- exact b.
        -- eapply meta_ex_body_wf. exact b. exact Hderiv.

  - (* HD_Ex_Elim *)
    simpl. eapply HD_Ex_Elim.
    + apply IHHderiv1. exact dt0.
    + eapply HD_Conv. 
      * eapply HD_Ctx_Conv.
        -- apply CEq_Cons. 
           ++ (* 1. Admit kilövése: A kiterjesztett Phi jólformált *)
              apply FE_Refl. 
              eapply meta_subst_wf. 
              ** eapply typing_subst_ext. exact dt0.
              ** eapply meta_ex_body_wf_base. exact Hderiv1.
           ++ (* A Bullet hiba javítása: Hderiv1 bizonyítja a kontextust *)
              eapply ctx_subst_ext_comm. 
              ** exact dt0.
              ** eapply meta_ctx_wf. exact Hderiv1. 
        -- apply IHHderiv2. apply typing_subst_ext. exact dt0.
      * (* 2. Admit kilövése: A hiányzó Fst kommutációs lemmánk! *)
        eapply form_equiv_subst_comm_fst. 
        -- exact dt0.
        -- eapply meta_ex_elim_chi_wf. exact Hderiv1. exact Hderiv2.


  - (* HD_Eps_Intro *)
    simpl. eapply HD_Conv.
    + eapply HD_Eps_Intro.
      * eapply BT_Comp. eassumption. exact dt0.
      * eapply HD_Conv. 
        -- apply IHHderiv. exact dt0.
        -- (* 1. Admit kilövése: A kommutációs lemmánk szimmetrikusan! *)
           eapply FE_Sym. 
           eapply form_equiv_subst_comm_elim.
           ++ exact dt0.
           ++ exact b.
           ++ eapply meta_eps_body_wf. exact b. exact Hderiv.
    + (* 2. Admit kilövése: A Beck-Chevalley Axióma *)
      eapply meta_eps_bc.
      * exact dt0.
      * eapply meta_eps_body_wf. exact b. exact Hderiv.

  - (* HD_Eps_Elim *)
    simpl. eapply HD_Eps_Elim.
    + eapply HD_Conv.
      * apply IHHderiv1. exact dt0.
      * (* 1. Admit kilövése: Beck-Chevalley szimmetrikusan megfordítva! *)
        eapply FE_Sym. 
        eapply meta_eps_bc.
        -- exact dt0.
        -- eapply meta_eps_elim_body_wf. exact Hderiv1.
    + eapply HD_Conv.
      * eapply HD_Ctx_Conv.
        -- apply CEq_Cons.
           ++ apply FE_Refl. 
              (* 2. Admit: Jólformáltság a kiterjesztett Phi-re *)
              eapply meta_subst_wf. 
              ** eapply typing_subst_ext. exact dt0.
              ** eapply meta_eps_elim_body_wf. exact Hderiv1.
           ++ (* Bullet hiba javítása: G jólformáltsága *)
              eapply ctx_subst_ext_comm. 
              ** exact dt0.
              ** eapply meta_ctx_wf. exact Hderiv1.
        -- apply IHHderiv2. apply typing_subst_ext. exact dt0.
      * (* 3. Admit kilövése: A Fst kommutációs lemmánk! *)
        eapply form_equiv_subst_comm_fst. 
        -- exact dt0.
        -- eapply meta_eps_elim_chi_wf. exact Hderiv1. exact Hderiv2.
Defined.

(* 2. A HELYETTESÍTÉSI FUNKTOR OBJEKTUM-RÉSZE A TERM MODELLBEN *)

Definition subst_functor_obj {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} 
  {I J : b_ty} (t : @b_tm Sign Func) (dt : base_typing I t J)
  (Phi : wf_ty J) : wf_ty I.
Proof.
  (* 1. Felbontjuk a Szigma-típust formulára és a jólformáltsági bizonyításra *)
  destruct Phi as [phi Hwf].
  
  (* 2. A kimenet a helyettesített formula lesz *)
  exists (form_subst t phi).
  
  (* 3. Bizonyítjuk, hogy ez jólformált *)
  eapply meta_subst_wf.
  - exact dt.
  - exact Hwf.
Defined.

Definition subst_functor_hom {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} 
  {I J : b_ty} (t : @b_tm Sign Func) (dt : base_typing I t J)
  (Phi Psi : wf_ty J)
  (f : hom_fiber Phi Psi) : hom_fiber (subst_functor_obj t dt Phi) (subst_functor_obj t dt Psi).
Proof.
  (* 1. Fel kell bontanunk a Szigma-típusokat, különben a 'subst_functor_obj' beragad! *)
  destruct Phi as [phi Hwf_phi].
  destruct Psi as [psi Hwf_psi].
  
  (* 2. Bontsuk ki a morfizmust *)
  destruct f as [p Hderiv].
  
  (* 3. Az új morfizmus a helyettesített term lesz *)
  exists (tm_subst t p).
  
  (* 4. Most már a Coq tud egyszerűsíteni, mert látja a belső formulákat (phi, psi) *)
  change (h_derivation I (ctx_subst t []) (tm_subst t p) 
         (form_subst t (Ty_Arrow phi psi))).
         
  (* 5. Jöhet a tegnapi Mester Lemma! *)
  eapply h_derivation_subst_general.
  - exact dt.
  - exact Hderiv.
Defined.

(* 3. A HELYETTESÍTÉSI FUNKTOR PÉLDÁNYOSÍTÁSA *)

Instance subst_functor {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} 
  {I J : b_ty} (t : @b_tm Sign Func) (dt : base_typing I t J) :
  Functor (Fiber_SetoidCategory J) (Fiber_SetoidCategory I).
Proof.
  refine (mk_Functor 
    (Fiber_SetoidCategory J) 
    (Fiber_SetoidCategory I)
    (fun Phi => subst_functor_obj t dt Phi)
    (fun Phi Psi f => subst_functor_hom t dt Phi Psi f)
    _ _ _).
Unshelve.
  (* A három Funktor-axióma (Proper, Id, Comp) a Thin tulajdonság miatt triviálisan True! *)
  all: intros; unfold fiber_equiv; constructor.
Defined.

(* ================================================================= *)
(* 3. AZ EGZISZTENCIÁLIS KVANTOR (BAL ADJUNKT) BLOKK                 *)
(* ================================================================= *)

(* 1. Objektum képzés *)
Definition ex_functor_obj {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} 
  (I A : b_ty) (Phi : wf_ty (b_Prod I A)) : wf_ty I.
Proof. 
  destruct Phi as [phi Hwf].
  exists (Ty_Ex A phi).
  apply WF_Ex. exact Hwf.
Defined.

(* 2. Az Adjunkció Unit-ja (Eta): Y -> Pullback (Ex Y) *)
Definition ex_subst_unit {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred} (I A : b_ty) (Y : wf_ty (b_Prod I A)) :
  hom_fiber Y (subst_functor_obj b_fst BT_Fst (ex_functor_obj I A Y)).
Proof.
  destruct Y as [y Hy].
  exists (tm_lam y (tm_ex_intro b_snd (tm_var 0))).
  apply HD_Lam.
  simpl.
  eapply HD_Ex_Intro.
  - apply BT_Snd.
  - eapply HD_Conv.
    + apply HD_Var0. apply AWF_Cons; auto. apply AWF_Nil.
    + eapply FE_Trans.
      { eapply FE_Sym. eapply FE_Pullback_Id. exact Hy. }
      eapply FE_Trans.
      { eapply FE_Pullback_Cong.
        - eapply BE_Trans. { eapply BE_Sym. apply BE_EtaPair. }
          eapply BE_Sym. eapply BE_Trans. { apply BE_CompPair. }
          eapply BE_CongPair.
          + eapply BE_Trans. { eapply BE_Sym. apply BE_Assoc. }
            eapply BE_CongComp. apply BE_BetaFst. apply BE_Refl.
          + eapply BE_Trans. { apply BE_BetaSnd. } eapply BE_Sym. apply BE_IdR.
        - exact Hy.
      }
      { apply FE_Sym. eapply FE_Pullback_Comp.
        - eapply typing_subst_ext. eapply BT_Fst.
        - apply BT_Pair. apply BT_Id. apply BT_Snd.
        - exact Hy.
      }
Unshelve.
  all: repeat match goal with
  | |- base_typing _ _ _ => eapply BT_Comp || eapply BT_Pair || apply BT_Id || eapply BT_Fst || eapply BT_Snd || apply typing_subst_ext || eassumption
  | |- _ => auto
  end.
Defined.

(* 3. A Bal Adjunkt Morfizmus-képző: Y -> Pullback X  =>  Ex Y -> X *)
Definition ex_subst_left_adj_mor {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred} (I A : b_ty) 
  (Y : wf_ty (b_Prod I A)) (X : wf_ty I)
  (g : hom_fiber Y (subst_functor_obj b_fst BT_Fst X)) : 
  hom_fiber (ex_functor_obj I A Y) X.
Proof.
  destruct Y as [y Hy]. destruct X as [x Hx].
  destruct g as [p Hderiv].
  
  exists (tm_lam (Ty_Ex A y) (tm_ex_elim (tm_var 0) (tm_app p (tm_var 0)))).
  
  apply HD_Lam.
  eapply HD_Ex_Elim.
  - apply HD_Var0. apply AWF_Cons. apply WF_Ex. exact Hy. apply AWF_Nil.
  - simpl.
    eapply (HD_App _ _ _ _ y (form_subst b_fst x)).
    + change (h_derivation (b_Prod I A) ([] ++ [y; Ty_Ex A (form_subst (b_subst_ext b_fst) y)]) p (Ty_Arrow y (form_subst b_fst x))).
      eapply h_derivation_append.
      * exact Hderiv.
      * apply AWF_Cons; try assumption.
        apply AWF_Cons; try assumption.
        apply WF_Ex. eapply wf_subst; try assumption.
        eapply typing_subst_ext. apply BT_Fst.
        exact Hy.
        apply AWF_Nil.
    + apply HD_Var0. 
      apply AWF_Cons; try assumption.
      apply AWF_Cons; try assumption.
      apply WF_Ex. eapply wf_subst; try assumption.
      eapply typing_subst_ext. apply BT_Fst.
      exact Hy.
      apply AWF_Nil.
Defined.

(* 4. Az IsRightAdjoint Adjunkció Példányosítása *)
Instance TermModel_Pullback_IsRightAdjoint {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred} (I A : b_ty) :
  IsRightAdjoint (subst_functor b_fst BT_Fst (I:=b_Prod I A) (J:=I)).
Proof.
  refine (mk_IsRightAdjoint 
    (Fiber_SetoidCategory I)
    (Fiber_SetoidCategory (b_Prod I A))
    (subst_functor b_fst BT_Fst (I:=b_Prod I A) (J:=I))
    (fun Y => ex_functor_obj I A Y)
    (fun Y => ex_subst_unit I A Y)
    (fun Y X g => ex_subst_left_adj_mor I A Y X g)
    _ _ _).
Unshelve.
  all: intros; unfold fiber_equiv; constructor.
Defined.

(* ================================================================= *)
(* 4. AZ UNIVERZÁLIS ADJUNKCIÓ (RIGHT ADJOINT)                       *)
(* ================================================================= *)

(* 1. A Forall (Jobb Adjunkt) Objektum Képzése *)
Definition all_functor_obj {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred} (I A : b_ty) 
  (Phi : wf_ty (b_Prod I A)) : wf_ty I.
Proof. 
  destruct Phi as [phi Hwf].
  exists (Ty_All A phi).
  apply WF_All. exact Hwf.
Defined.

(* 2. A Counit (Epsilon) természetes transzformáció: (All A. X)[fst] -> X *)
(* 2. A Counit (Epsilon) természetes transzformáció: (All A. X)[fst] -> X *)
Definition all_subst_counit {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred} (I A : b_ty) 
  (X : wf_ty (b_Prod I A)) :
  hom_fiber (subst_functor_obj b_fst BT_Fst (all_functor_obj I A X)) X.
Proof.
  destruct X as [x Hx].
  (* A morfizmus: \x. all_elim x snd *)
  exists (tm_lam (form_subst b_fst (Ty_All A x)) (tm_all_elim (tm_var 0) b_snd)).
  
  apply HD_Lam.
  eapply HD_Conv.
  - eapply HD_All_Elim.
    + apply HD_Var0. apply AWF_Cons. 
      (* Ez a rész már sikeresen lefutott nálad: *)
      change (WellFormed (b_Prod I A) (form_subst b_fst (Ty_All A x))).
      eapply wf_subst. 
      * apply BT_Fst. 
      * apply WF_All. exact Hx. 
      * apply AWF_Nil.
    + apply BT_Snd.
  - (* BÁZIS MÁGIA JAVÍTÁSA: Megfordítjuk a célt, így egyezni fog a transzformációs lánccal! *)
    eapply FE_Sym.
    eapply FE_Trans.
    { eapply FE_Sym. eapply FE_Pullback_Id. exact Hx. }
    eapply FE_Trans.
    { eapply FE_Pullback_Cong.
      - eapply BE_Trans. { eapply BE_Sym. apply BE_EtaPair. }
        eapply BE_Sym. eapply BE_Trans. { apply BE_CompPair. }
        eapply BE_CongPair.
        + eapply BE_Trans. { eapply BE_Sym. apply BE_Assoc. }
          eapply BE_CongComp. apply BE_BetaFst. apply BE_Refl.
        + eapply BE_Trans. { apply BE_BetaSnd. } eapply BE_Sym. apply BE_IdR.
      - exact Hx.
    }
    { apply FE_Sym. eapply FE_Pullback_Comp.
      - eapply typing_subst_ext. eapply BT_Fst.
      - apply BT_Pair. apply BT_Id. apply BT_Snd.
      - exact Hx.
    }
Unshelve.
  all: repeat match goal with
  | |- base_typing _ _ _ => eapply BT_Comp || eapply BT_Pair || apply BT_Id || eapply BT_Fst || eapply BT_Snd || apply typing_subst_ext || eassumption
  end.
Defined.

(* 3. A Jobb Adjunkt Morfizmusképző: Y[fst] -> X  =>  Y -> All A. X *)
Definition all_subst_right_adj_mor {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred} (I A : b_ty) 
  (Y : wf_ty I) (X : wf_ty (b_Prod I A))
  (f : hom_fiber (subst_functor_obj b_fst BT_Fst Y) X) : 
  hom_fiber Y (all_functor_obj I A X).
Proof.
  destruct Y as [y Hy]. destruct X as [x Hx].
  destruct f as [p Hderiv].
  
  (* A morfizmus: \y. all_intro (p y) *)
  exists (tm_lam y (tm_all_intro (tm_app p (tm_var 0)))).
  
  apply HD_Lam.
  apply HD_All_Intro.
  
  (* 1. LÉPÉS: Kisöpörjük a projT1 és ctx_subst zajt a célból! *)
  simpl.
  
  (* 2. LÉPÉS: Explicit megadjuk a típusokat a HD_App-nak, elkerülve a ?Phi evar csapdát *)
  eapply (HD_App _ _ _ _ (form_subst b_fst y) x).
  - (* Első cél: h_derivation ... p (Ty_Arrow (form_subst b_fst y) x) *)
    (* Most már a change tökéletesen működik, mert tiszta a kontextus és nincs evar! *)
    change (h_derivation (b_Prod I A) ([] ++ [form_subst b_fst y]) p (Ty_Arrow (form_subst b_fst y) x)).
    
    eapply h_derivation_append.
    + exact Hderiv.
    + apply AWF_Cons. eapply wf_subst. apply BT_Fst. exact Hy. apply AWF_Nil.
  - (* Második cél: a változó levezetése *)
    apply HD_Var0. 
    apply AWF_Cons. eapply wf_subst. apply BT_Fst. exact Hy. apply AWF_Nil.
Defined.
 

Instance TermModel_Pullback_IsLeftAdjoint {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred} (I A : b_ty) :
  IsLeftAdjoint (subst_functor b_fst BT_Fst (I:=b_Prod I A) (J:=I)).
Proof.
  (* JAVÍTÁS: Itt a mk_IsLeftAdjoint paraméterezése miatt C jön előre, D hátra! *)
  refine (mk_IsLeftAdjoint 
    (Fiber_SetoidCategory (b_Prod I A))
    (Fiber_SetoidCategory I)
    (subst_functor b_fst BT_Fst (I:=b_Prod I A) (J:=I))
    (fun X => all_functor_obj I A X)
    (fun X => all_subst_counit I A X)
    (fun Y X f => all_subst_right_adj_mor I A Y X f)
    _ _ _).
Unshelve.
  all: intros; unfold fiber_equiv; constructor.
Defined.


(* ================================================================= *)
(* 5. AZ EPSZILON FIBRÁCIÓ PÉLDÁNYOSÍTÁSA (A FINÁLÉ)                 *)
(* ================================================================= *)

(* Segédlemma: Közvetlenül az Unshelve alatt építjük fel a két morfizmust *)
Lemma form_equiv_to_iso {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred} (I : b_ty) 
  (X Y : wf_ty I) :
  form_equiv I (projT1 X) (projT1 Y) -> @Iso (Fiber_SetoidCategory I) X Y.
Proof.
  intros Heq.
  destruct X as [x Hx]. destruct Y as [y Hy]. simpl in Heq.
  
  (* 1. Először leütjük a kategóriaelméleti axiómákat *)
  econstructor.
  - unfold fiber_equiv; constructor.
  - unfold fiber_equiv; constructor.
    
  (* 2. FINÁLÉ: Leemeljük a polcról a két morfizmus-célt, és helyben felépítjük őket *)
  Unshelve.
  * (* 1. cél: Oda irányú morfizmus (x -> y) *)
    exists (tm_lam x (tm_var 0)).
    apply HD_Lam. eapply HD_Conv.
    + apply HD_Var0. apply AWF_Cons; auto. apply AWF_Nil.
    + exact Heq.
    
  * (* 2. cél: Vissza irányú morfizmus (y -> x) *)
    exists (tm_lam y (tm_var 0)).
    apply HD_Lam. eapply HD_Conv.
    + apply HD_Var0. apply AWF_Cons; auto. apply AWF_Nil.
    + apply FE_Sym. exact Heq.
Defined.


(* ================================================================= *)
(* KANONIKUS MODELL: GOOD FIBRATION                                  *)
(* ================================================================= *)

Instance TermModel_GoodFibration {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} : 
  GoodFibration (Base_SetoidCategory Sign Func).
Proof.
  refine (@mk_GoodFibration 
    (Base_SetoidCategory Sign Func) 
    (Base_CartesianCategory Sign Func)
    (fun I => Fiber_SetoidCategory I)
    (fun I => Fiber_Thin I)
    (fun I => Fiber_CartesianCategory I)
    (fun I => Fiber_CartesianClosedCategory I)
    (fun I => Fiber_BiCartesianClosedCategory I)
    
    (* ITT A MEGOLDÁS: Saját vetítőkkel egyből kinyerjük a termet és a típust! *)
    (fun I J f => subst_functor (tm_of f) (deriv_of f))
    
    (* A 7 darab trivializálódó izomorfizmus *)
    _ _ _ _ _ _ _ 
    
    (* A kvantorok adjunkciói, amik most már TÖKÉLETESEN unifikálódnak! *)
    (fun I A => TermModel_Pullback_IsRightAdjoint I A)
    (fun I A => TermModel_Pullback_IsLeftAdjoint I A)
    
    (* A maradék 3 izomorfizmus *)
    _ _ _
  ).
  
  - (* 1. pullback_id_iso *)
    intros I A. destruct A as [phi Hwf]. apply form_equiv_to_iso. simpl.
    eapply FE_Pullback_Id. exact Hwf.
    
  - (* 2. pullback_comp_iso *)
    intros I J K g f A. destruct A as [phi Hwf]. apply form_equiv_to_iso. simpl.
    (* MEGOLDÁS: Megfordítjuk az egyenlőséget, hogy illeszkedjen a lemmára! *)
    eapply FE_Sym. 
    eapply FE_Pullback_Comp.
    + exact (deriv_of g).
    + exact (deriv_of f).
    + exact Hwf.
    
  - (* 3. pb_term_iso *)
    intros I J f. apply form_equiv_to_iso. simpl. apply FE_Refl. apply WF_Unit.
    
  - (* 4. pb_prod_iso *)
    intros I J f A B. destruct A as [phiA HwfA]. destruct B as [phiB HwfB]. 
    apply form_equiv_to_iso. simpl. apply FE_Refl.
    (* Jólformáltság bizonyítása szorzatra: *)
    apply WF_Prod.
    + eapply meta_subst_wf. exact (deriv_of f). exact HwfA.
    + eapply meta_subst_wf. exact (deriv_of f). exact HwfB.
    
  - (* 5. pb_init_iso *)
    intros I J f. apply form_equiv_to_iso. simpl. apply FE_Refl.
    apply WF_Void.
    
  - (* 6. pb_coprod_iso *)
    intros I J f A B. destruct A as [phiA HwfA]. destruct B as [phiB HwfB]. 
    apply form_equiv_to_iso. simpl. apply FE_Refl.
    (* Jólformáltság bizonyítása összegre: *)
    apply WF_Sum.
    + eapply meta_subst_wf. exact (deriv_of f). exact HwfA.
    + eapply meta_subst_wf. exact (deriv_of f). exact HwfB.
    
  - (* 7. pb_exp_iso *)
    intros I J f A B. destruct A as [phiA HwfA]. destruct B as [phiB HwfB]. 
    apply form_equiv_to_iso. simpl. apply FE_Refl.
    (* Jólformáltság bizonyítása nyílra: *)
    apply WF_Arrow.
    + eapply meta_subst_wf. exact (deriv_of f). exact HwfB.
    + eapply meta_subst_wf. exact (deriv_of f). exact HwfA.
    
  - (* 8. beck_chevalley_sigma *)
    intros I J K f A. destruct A as [phi Hwf]. apply form_equiv_to_iso. simpl. apply FE_Refl.
    (* Jólformáltság bizonyítása egzisztenciális kvantorra: *)
    apply WF_Ex.
    eapply meta_subst_wf. exact (deriv_of ((f ∘ prod_fst) ∏ prod_snd)). exact Hwf.
    
  - (* 9. beck_chevalley_pi *)
    intros I J K f A. destruct A as [phi Hwf]. apply form_equiv_to_iso. simpl. apply FE_Refl.
    (* Jólformáltság bizonyítása univerzális kvantorra: *)
    apply WF_All.
    eapply meta_subst_wf. exact (deriv_of ((f ∘ prod_fst) ∏ prod_snd)). exact Hwf.
  - (* 10. pb_iso (A morfizmusok kongruenciája) *)
    intros I J f g Heq A. destruct A as [phi Hwf]. apply form_equiv_to_iso. simpl.
    eapply FE_Pullback_Cong.
    + exact Heq.
    + exact Hwf.
Defined.

(* ================================================================= *)
(* KANONIKUS MODELL: STRICT GOOD FIBRATION                           *)
(* ================================================================= *)

Instance TermModel_StrictGoodFibration {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} : 
  StrictGoodFibration (Base_SetoidCategory Sign Func) TermModel_GoodFibration.
Proof.
  constructor.
  intros X Y M1 M2 Heq.
  
  (* Mivel nem tudom, hogyan definiáltad a TotalHom_equiv-et a 
     függvénytáradban, kezdd azzal, hogy kibontod. 
     Általában ez csak a bázis-egyenlőség (Heq) továbbadása. *)
  unfold TotalHom_equiv. 
(* Bizonyítjuk a szimmetrikus bázis-egyenlőséget *)
  assert (Hsym : h_base M2 ≅ h_base M1). {
    symmetry. exact Heq.
  }
  
  (* Ezt az egyenlőséget adjuk meg az egzisztenciális (exists) célnak *)
  exists Hsym.
  
  (* A maradék cél a szálkategória morfizmusainak egyenlősége.
     Mivel a szálkategóriád Thin, ez teljesen automatikusan megoldódik! *)
  unfold fiber_equiv; constructor.
Defined.

  
(* ================================================================= *)
(* KANONIKUS MODELL: EPSILON HYPER MODEL                             *)
(* ================================================================= *)

  
Definition term_model_i_atom {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} 
  (p : Pred) (t : @b_tm Sign Func) (I : b_ty) : 
  (* EXPLICITEN kikényszerítjük az interp_ty I hívást, minden kategóriával *)
  wf_ty (@interp_ty (Base_SetoidCategory Sign Func)
                    (Base_CartesianCategory Sign Func)
                    (Base_TwoSortCategory Sign Func) I).
Proof.
  (* A VARÁZSLAT: A rewrite lecseréli az "interp_ty I"-t sima "I"-re a célban! *)
  rewrite (interp_ty_id Sign Func I).
  
  (* Most már a cél tisztán wf_ty I, jöhet a szintaktikai eldönthetőség: *)
  destruct (decide_base_typing I t) as [[A dt] | Hbad].
  - (* FŐÁG: Ha a term típusos *)
    destruct (b_ty_eq_dec A (pred_dom p)) as [HA | Hneq].
    + subst A.
      exists (Ty_Atom p t).
      eapply WF_Atom.
      exact dt.
    + exists Ty_Unit.
      apply WF_Unit.
  - (* HIBÁS ÁG: Ha a term hibás *)
    exists Ty_Unit.
    apply WF_Unit.
Defined.

(* ================================================================= *)
(* SEGÉDLEMMÁK: A függő típusok "lehámozása" a tiszta szintaxisról   *)
(* ================================================================= *)

(* 1. A Pullback funktor és a projT1 felcserélhetősége (Karakterre illeszkedik a gólhoz!) *)
Lemma projT1_pullback : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} {I J : @obj (Base_SetoidCategory Sign Func)} 
  (f : @hom (Base_SetoidCategory Sign Func) I J) (Phi : wf_ty J),
  projT1 (@fobj _ _ (Pullback f) Phi) = form_subst (tm_of f) (projT1 Phi).
Proof.
  intros. destruct Phi. reflexivity.
Defined.

(* 2. Az eq_rect_r eltüntetése a tiszta szintaxisról (obj típussal a pontos egyezésért!) *)
Lemma projT1_eq_rect_r_wf : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} {I J : @obj (Base_SetoidCategory Sign Func)} 
  (e : I = J) (Phi : wf_ty J),
  projT1 (eq_rect_r (fun o : @obj (Base_SetoidCategory Sign Func) => wf_ty o) Phi e) = projT1 Phi.
Proof.
  intros. destruct e. reflexivity.
Defined.

(* ================================================================= *)
(* KANONIKUS MODELL: EPSILON HYPER MODEL                             *)
(* ================================================================= *)

Instance TermModel_EpsilonHyperModel {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} : 
  EpsilonHyperModel TermModel_StrictGoodFibration.
Proof.
  refine (@Build_EpsilonHyperModel Sign Func Pred H H0
    (Base_SetoidCategory Sign Func) 
    (Base_CartesianCategory Sign Func) 
    (Base_TwoSortCategory Sign Func) 
    (Base_SyntacticEpsilonFullModel Sign Func)
    TermModel_GoodFibration 
    TermModel_StrictGoodFibration 
    term_model_i_atom
    _ 
    _).

  - (* 1. cél (i_atom_pb): *)
    intros p t I A f df.
    apply form_equiv_to_iso. 
    unfold term_model_i_atom.
    
    (* 1. A VARÁZSLAT: Lehámozzuk a Pullback funktort és az eq_rect_r casteket a gólról! *)
    (* Nincs több 'change' és típus-ütközés, a lemmák karakterre pontosan illeszkednek! *)
    rewrite projT1_pullback.
    rewrite projT1_eq_rect_r_wf.
    rewrite projT1_eq_rect_r_wf.
    
    (* MOST MÁR A GÓL 100%-IG TISZTA SZINTAXIS! Eltűnt minden dependent type! *)
    (* 2. Jöhet a te helyettesítési lemmád, ami most már csont nélkül lefut: *)
    rewrite (interp_tm_term I A f df).
    
    (* 3. Kiszámoljuk a belső match-ek projT1-ét is *)
    cbn [projT1].
    
    (* 4. Innentől a tiszta eldönthetőségi logika *)
    destruct (decide_base_typing A t) as [[B dt_t] | Hbad_t].
    + destruct (b_ty_eq_dec B (pred_dom p)) as [HB | HB].
      * subst B.
        destruct (decide_base_typing I (b_comp t f)) as [[B' dcomp] | Hbad_comp].
        -- assert (HB' : B' = pred_dom p).
           { eapply base_typing_unique.
             - exact dcomp.
             - exact (BT_Comp dt_t df).
           }
           subst B'.
           destruct (b_ty_eq_dec (pred_dom p) (pred_dom p)) as [Heq_dom | Hcontra].
           2: exfalso; apply Hcontra; reflexivity.
           dependent destruction Heq_dom.
           repeat rewrite projT1_eq_rect_r_wf.
           cbn [projT1 form_subst].
           rewrite (interp_ty_id Sign Func I).
           apply FE_Refl.
           eapply WF_Atom.
           exact dcomp.
        -- destruct (Hbad_comp (pred_dom p) (BT_Comp dt_t df)).
      * destruct (decide_base_typing I (b_comp t f)) as [[B' dcomp] | Hbad_comp].
        -- assert (HB' : B' = B).
           { inversion dcomp; subst.
             match goal with
             | [ Ht : base_typing ?Mid t B', Hf : base_typing I f ?Mid |- _ ] =>
                 assert (HM : Mid = A) by (eapply base_typing_unique; [exact Hf | exact df]);
                 subst Mid;
                 eapply base_typing_unique; [exact Ht | exact dt_t]
             end.
           }
           subst B'.
           destruct (b_ty_eq_dec B (pred_dom p)) as [Hcontra | _].
           { contradiction. }
           rewrite (interp_ty_id Sign Func I).
           apply FE_Refl.
           apply WF_Unit.
        -- rewrite (interp_ty_id Sign Func I).
           apply FE_Refl.
           apply WF_Unit.
    + destruct (decide_base_typing I (b_comp t f)) as [[B' dcomp] | Hbad_comp].
      * inversion dcomp; subst.
        match goal with
        | [ Ht : base_typing ?Mid t _, Hf : base_typing I f ?Mid |- _ ] =>
            assert (HM : Mid = A) by (eapply base_typing_unique; [exact Hf | exact df]);
            subst Mid;
            destruct (Hbad_t B' Ht)
        end.
      * rewrite (interp_ty_id Sign Func I).
        apply FE_Refl.
        apply WF_Unit.

  - (* 2. cél (i_atom_cong_global): *)
    intros p I A t1 t2 d1 d2 Heq.
    apply form_equiv_to_iso.
    unfold term_model_i_atom.
    
    (* Itt is csak le kell hámozni az eq_rect_r casteket a cékról *)
    rewrite projT1_eq_rect_r_wf.
    rewrite projT1_eq_rect_r_wf.
    
    cbn [projT1].
    
    destruct (decide_base_typing I t1) as [[B1 dt1] | Hbad1].
    + destruct (decide_base_typing I t2) as [[B2 dt2] | Hbad2].
      * assert (HB1 : B1 = A) by (eapply base_typing_unique; [exact dt1 | exact d1]).
        assert (HB2 : B2 = A) by (eapply base_typing_unique; [exact dt2 | exact d2]).
        subst B1 B2.
        destruct (b_ty_eq_dec A (pred_dom p)) as [HA | HA].
        -- subst A.
           destruct (b_ty_eq_dec (pred_dom p) (pred_dom p)) as [Heq_dom | Hcontra].
           2: exfalso; apply Hcontra; reflexivity.
           dependent destruction Heq_dom.
           repeat rewrite projT1_eq_rect_r_wf.
           cbn [projT1].
           rewrite (interp_ty_id Sign Func I).
           eapply FE_Atom.
           exact Heq.
        -- rewrite (interp_ty_id Sign Func I).
           apply FE_Refl.
           apply WF_Unit.
      * destruct (Hbad2 A d2).
    + destruct (Hbad1 A d1).
Defined.

(* ================================================================= *)
(* KANONIKUS MODELL: ADJOINT EPSILON FIBRATION                       *)
(* ================================================================= *)

(* 1. Megmutatja a Coq-nak, hogy a projT1 hogyan szabadítja fel az ex_functor_obj-ból a Ty_Ex-et *)
Lemma projT1_ex_functor_obj : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred} (I A : b_ty) (Y : wf_ty (b_Prod I A)),
  projT1 (ex_functor_obj I A Y) = Ty_Ex A (projT1 Y).
Proof. intros. destruct Y. reflexivity. Defined.

(* Ez a lemma igazolja, hogy a Term Modellben a formulák (h_ty) 
   szemantikai interpretációja (interp_h_ty) valójában identitásként 
   viselkedik, és megegyezik magával a tiszta szintaktikai formulával. 
   Az explicit @ jel garantálja, hogy a Coq felismerje a Szigma-típust. *)

Lemma term_model_interp_id : forall {Sign Func Pred : Type} `{HFunc : FunctionSignature Func} `{HPred : PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} (ctx : b_ty) (X : @h_ty Sign Func Pred), 
  WellFormed ctx X -> (* <--- Ez a pajzs védi meg a lemmát az ill-formált atomoktól! *)
  projT1 (@interp_h_ty Sign Func Pred HFunc HPred
            (Base_SetoidCategory Sign Func)
            (Base_CartesianCategory Sign Func)
            (Base_TwoSortCategory Sign Func)
            (Base_SyntacticEpsilonFullModel Sign Func)
            TermModel_GoodFibration
            TermModel_StrictGoodFibration
            (@TermModel_EpsilonHyperModel Sign Func Pred HFunc HPred SM)
            ctx X) = X.
Proof. 
  intros Sign Func Pred HFunc HPred SM ctx X Hwf.
  generalize dependent ctx.
  
  (* Elindítjuk az indukciót, pont mint az előbb *)
  induction X; intros ctx Hwf; simpl.

  - (* 1/8 gól: Ty_Unit *)
    reflexivity.
    
  - (* 2/8 gól: Ty_Void *)
    reflexivity.
    
  - (* 3/8 gól: Ty_Prod *)
    inversion Hwf; subst. 
    simpl. rewrite IHX1, IHX2; auto.
    
  - (* 4/8 gól: Ty_Sum *)
    inversion Hwf; subst. 
    simpl. rewrite IHX1, IHX2; auto.
    
  - (* 5/8 gól: Ty_Arrow *)
    inversion Hwf; subst. 
    simpl. rewrite IHX1, IHX2; auto.
    
  - (* 6/8 gól: Ty_Atom *)
    (* 1. Invertáljuk a jólformáltságot, megkapjuk a base_typing fát *)
    inversion Hwf; subst.
    
    (* 2. KIFEJEZETTEN KINYITJUK a definíciót, hogy a Coq meglássa az eq_rect_r-t! *)
    unfold term_model_i_atom.
    
    (* 3. Most már ott van a mintázat, csont nélkül lefut a törlés: *)
    rewrite projT1_eq_rect_r_wf.
    
    (* 4. Szétbontjuk az eldöntést inl/inr ágakra *)
    destruct (decide_base_typing ctx b) as [[A0 b0] | Hbad].
    + (* inl ág: Jól-tipizált, reflexivitás kész! *)
      assert (HA0 : A0 = pred_dom p).
      { eapply base_typing_unique; [exact b0 | exact X]. }
      subst A0.
      destruct (b_ty_eq_dec (pred_dom p) (pred_dom p)) as [Heq_dom | Hcontra].
      2: exfalso; apply Hcontra; reflexivity.
      dependent destruction Heq_dom.
      repeat rewrite projT1_eq_rect_r_wf.
      simpl.
      reflexivity.
    + (* inr ág: Ellentmondás! Az inversion (Hwf) adott egy X : base_typing-ot *)
      match goal with
      | [ H_bt : base_typing ctx b ?A_mid |- _ ] => destruct (Hbad A_mid H_bt)
      end.
    
 - (* 7/8: Ty_All *)
    inversion Hwf; subst. 
    match goal with
    | [ H : WellFormed (b_Prod ctx b) X |- _ ] => specialize (IHX (b_Prod ctx b) H)
    end.
    destruct (interp_h_ty (b_Prod ctx b) X) as [phi Hwf_phi] in *.
    simpl in IHX. subst phi.
    
    cbn [all_functor_obj projT1].
    
    (* A MEGOLDÁS: A fold helyett f_equal-t használunk! 
       Ez lehúzza a Ty_All-t mindkét oldalról. *)
    f_equal.
    apply (interp_ty_id Sign Func b).
    
  - (* 8/8: Ty_Ex (Egzisztenciális kvantor) *)
    inversion Hwf; subst.
    match goal with
    | [ H : WellFormed (b_Prod ctx b) X |- _ ] => specialize (IHX (b_Prod ctx b) H)
    end.
    destruct (interp_h_ty (b_Prod ctx b) X) as [phi Hwf_phi] in *.
    simpl in IHX. subst phi.
    
    cbn [ex_functor_obj projT1].
    
    (* Ugyanez a trükk itt is! *)
    f_equal.
    apply (interp_ty_id Sign Func b).
Defined.



Instance TermModel_AdjointEpsilonFullFibration {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred} : 
  @AdjointEpsilonFullFibration Sign Func Pred H H0 SM
    (Base_SetoidCategory Sign Func) 
    (Base_CartesianCategory Sign Func) 
    (Base_TwoSortCategory Sign Func) 
    (Base_SyntacticEpsilonFullModel Sign Func) 
    TermModel_GoodFibration 
    TermModel_StrictGoodFibration 
    TermModel_EpsilonHyperModel.
Proof.
  constructor.

- (* 1. eps_is_left_adj_obj *) 
    (* AZ ÚJÍTÁS: Behozzuk a környezetbe a Coq által felkínált jólformáltságot! *)
    intros I A Phi Hwf_Phi.
    
    apply form_equiv_to_iso.
    
    (* 1. Felszíni kategóriaelméleti absztrakciók kibontása *)
    cbn [left_adj_obj pullback_has_left_adjoint TermModel_GoodFibration TermModel_Pullback_IsRightAdjoint].
    
    (* 2. A FINÁLÉ MÁGIÁJA 1/2: Dependent Type csapdák kilövése *)
    destruct (interp_h_ty (b_Prod I A) Phi) as [phi Hwf_phi] eqn:Heq_phi.
    destruct (interp_h_ty I (Phi .[ ε A, Phi ])) as [psi Hwf_psi] eqn:Heq_psi.
    cbn [ex_functor_obj projT1].
    
    (* 3. A FINÁLÉ MÁGIÁJA 2/2: Fixpontok visszacsomagolása *)
    change (_ (Base_SetoidCategory Sign Func) (Base_CartesianCategory Sign Func) (Base_TwoSortCategory Sign Func) I) 
      with (@interp_ty (Base_SetoidCategory Sign Func) (Base_CartesianCategory Sign Func) (Base_TwoSortCategory Sign Func) I).
    change (_ (Base_SetoidCategory Sign Func) (Base_CartesianCategory Sign Func) (Base_TwoSortCategory Sign Func) A) 
      with (@interp_ty (Base_SetoidCategory Sign Func) (Base_CartesianCategory Sign Func) (Base_TwoSortCategory Sign Func) A).
      
    (* 4. Helyreállítjuk phi és psi értékét a tiszta identitás lemmáddal *)
    assert (H_phi : phi = Phi).
    {
      (* FIGYELD: Nincs több admit! A Hwf_Phi itt van a kezünkben! *)
      generalize (term_model_interp_id (b_Prod I A) Phi Hwf_Phi).
      rewrite Heq_phi. cbn [projT1]. auto.
    }
    subst phi.
    
    assert (H_psi : psi = Phi .[ ε A, Phi ]).
    {
      (* Nincs admit! A helyettesítés jólformáltságát a kész wf_subst lemmáddal igazoljuk! *)
      assert (Hwf_Psi : WellFormed I (Phi .[ ε A, Phi ])).
      {
        eapply wf_subst.
        - eapply BT_Pair. apply BT_Id. apply BT_Const.
        - exact Hwf_Phi.
      }
      generalize (term_model_interp_id I (Phi .[ ε A, Phi ]) Hwf_Psi).
      rewrite Heq_psi. cbn [projT1]. auto.
    }
    subst psi.
    
    (* 5. GÓL: form_equiv (interp_ty I) (Ty_Ex (interp_ty A) Phi) (Phi .[ ε A, Phi ]) *)
    (* A csúnya 'change' helyett a tiszta identitás lemmáddal lehúzzuk az interp_ty-t: *)
    rewrite (interp_ty_id Sign Func I).
    rewrite (interp_ty_id Sign Func A).
     
    (* 6. GÓL MOST MÁR: form_equiv I (Ty_Ex A Phi) (Phi .[ ε A, Phi ]) *)
    apply FE_Eps_Adjoint_Iso.  
    exact Hwf_Phi.  
- (* 2. eps_functorial *)
    intros I A Phi Psi Hwf_Phi Hwf_Psi H_iso.
    destruct H_iso as [f g Hfg Hgf].
    
    pose (L := LeftAdjointFunctor 
                 (Pullback (@interp_tm Sign Func H
                              (Base_SetoidCategory Sign Func)
                              (Base_CartesianCategory Sign Func)
                              (Base_TwoSortCategory Sign Func)
                              (Base_SyntacticEpsilonFullModel Sign Func)
                              _ _ _
                              (BT_Fst (Sign:=Sign) (A:=I) (B:=A)))) 
                 pullback_has_left_adjoint).

    match type of f with
    | hom ?dPhi ?dPsi =>
        pose (DomPhi := dPhi);
        pose (DomPsi := dPsi)
    end.
    
    match goal with
    | |- ?cPhi ≅O ?cPsi =>
        pose (CodPhi := cPhi);
        pose (CodPsi := cPsi)
    end.

    (* AZ ELSŐ IZOMORFIZMUS *)
    assert (Iso_Phi : fobj L DomPhi ≅O CodPhi). 
    {
      apply form_equiv_to_iso.

      unfold L.
      destruct DomPhi as [phi Hwf_phi] eqn:Heq_phi.
      destruct CodPhi as [psi Hwf_psi] eqn:Heq_psi.
      
      unfold fobj, LeftAdjointFunctor.

      (* Itt a lényeg: a left_adj_obj-ot is kibontjuk, nem kézzel gyártunk existT-t. *)
      cbn [left_adj_obj
           pullback_has_left_adjoint
           TermModel_GoodFibration
           TermModel_Pullback_IsRightAdjoint].

      cbn [ex_functor_obj projT1].

      (* Ugyanaz a fixpont-visszacsomagolás, mint az első ágban. *)
      change (_ (Base_SetoidCategory Sign Func)
                (Base_CartesianCategory Sign Func)
                (Base_TwoSortCategory Sign Func)
                I)
        with (@interp_ty
                (Base_SetoidCategory Sign Func)
                (Base_CartesianCategory Sign Func)
                (Base_TwoSortCategory Sign Func)
                I).

      change (_ (Base_SetoidCategory Sign Func)
                (Base_CartesianCategory Sign Func)
                (Base_TwoSortCategory Sign Func)
                A)
        with (@interp_ty
                (Base_SetoidCategory Sign Func)
                (Base_CartesianCategory Sign Func)
                (Base_TwoSortCategory Sign Func)
                A).

      assert (H_phi : phi = Phi).
      {
        pose proof (term_model_interp_id (b_Prod I A) Phi Hwf_Phi) as H_interp_phi.
        unfold DomPhi in Heq_phi.
        rewrite Heq_phi in H_interp_phi.
        cbn [projT1] in H_interp_phi.
        exact H_interp_phi.
      }
      subst phi.
      
      assert (H_psi : psi = Phi .[ ε A, Phi ]).
      {
        assert (Hwf_EpsPhi : WellFormed I (Phi .[ ε A, Phi ])).
        {
          eapply wf_subst.
          - eapply BT_Pair.
            + apply BT_Id.
            + apply BT_Const.
          - exact Hwf_Phi.
        }

        pose proof (term_model_interp_id I (Phi .[ ε A, Phi ]) Hwf_EpsPhi) as H_interp_eps_phi.
        unfold CodPhi in Heq_psi.
        rewrite Heq_psi in H_interp_eps_phi.
        cbn [projT1] in H_interp_eps_phi.
        exact H_interp_eps_phi.
      }
      subst psi.

      rewrite (interp_ty_id Sign Func I).
      rewrite (interp_ty_id Sign Func A).

      apply FE_Eps_Adjoint_Iso.
      exact Hwf_Phi.
    }

    (* A MÁSODIK IZOMORFIZMUS *)
    assert (Iso_Psi : fobj L DomPsi ≅O CodPsi).
    {
      apply form_equiv_to_iso.

      unfold L.
      destruct DomPsi as [psi_in Hwf_psi_in] eqn:Heq_psi_in.
      destruct CodPsi as [psi_out Hwf_psi_out] eqn:Heq_psi_out.
      
      unfold fobj, LeftAdjointFunctor.

      cbn [left_adj_obj
           pullback_has_left_adjoint
           TermModel_GoodFibration
           TermModel_Pullback_IsRightAdjoint].

      cbn [ex_functor_obj projT1].

      change (_ (Base_SetoidCategory Sign Func)
                (Base_CartesianCategory Sign Func)
                (Base_TwoSortCategory Sign Func)
                I)
        with (@interp_ty
                (Base_SetoidCategory Sign Func)
                (Base_CartesianCategory Sign Func)
                (Base_TwoSortCategory Sign Func)
                I).

      change (_ (Base_SetoidCategory Sign Func)
                (Base_CartesianCategory Sign Func)
                (Base_TwoSortCategory Sign Func)
                A)
        with (@interp_ty
                (Base_SetoidCategory Sign Func)
                (Base_CartesianCategory Sign Func)
                (Base_TwoSortCategory Sign Func)
                A).

      assert (H_psi_in : psi_in = Psi).
      {
        pose proof (term_model_interp_id (b_Prod I A) Psi Hwf_Psi) as H_interp_psi.
        unfold DomPsi in Heq_psi_in.
        rewrite Heq_psi_in in H_interp_psi.
        cbn [projT1] in H_interp_psi.
        exact H_interp_psi.
      }
      subst psi_in.
      
      assert (H_psi_out : psi_out = Psi .[ ε A, Psi ]).
      {
        assert (Hwf_EpsPsi : WellFormed I (Psi .[ ε A, Psi ])).
        {
          eapply wf_subst.
          - eapply BT_Pair.
            + apply BT_Id.
            + apply BT_Const.
          - exact Hwf_Psi.
        }

        pose proof (term_model_interp_id I (Psi .[ ε A, Psi ]) Hwf_EpsPsi) as H_interp_eps_psi.
        unfold CodPsi in Heq_psi_out.
        rewrite Heq_psi_out in H_interp_eps_psi.
        cbn [projT1] in H_interp_eps_psi.
        exact H_interp_eps_psi.
      }
      subst psi_out.

      rewrite (interp_ty_id Sign Func I).
      rewrite (interp_ty_id Sign Func A).

      apply FE_Eps_Adjoint_Iso.
      exact Hwf_Psi.
    }

    (* Kinyerjük a morfizmusokat a kész izomorfizmusokból. *)
    destruct Iso_Phi as [to_Phi from_Phi _ _].
    destruct Iso_Psi as [to_Psi from_Psi _ _].

    change (CodPhi ≅O CodPsi).

    refine {|
      iso_to :=
        @compose (Fiber (interp_ty I))
          CodPhi
          (fobj L DomPsi)
          CodPsi
          to_Psi
          (@compose (Fiber (interp_ty I))
             CodPhi
             (fobj L DomPhi)
             (fobj L DomPsi)
             (@fmap _ _ L DomPhi DomPsi f)
             from_Phi);

      iso_from :=
        @compose (Fiber (interp_ty I))
          CodPsi
          (fobj L DomPhi)
          CodPhi
          to_Phi
          (@compose (Fiber (interp_ty I))
             CodPsi
             (fobj L DomPsi)
             (fobj L DomPhi)
             (@fmap _ _ L DomPsi DomPhi g)
             from_Psi)
    |}.
    + unfold fiber_equiv; constructor.
    + unfold fiber_equiv; constructor.
Defined.

(* ================================================================= *)
(*                      COMPLETENESS THEOREMS                        *)
(* ================================================================= *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

Fixpoint h_lift {Sign Func Pred : Type} (shift cutoff : nat) (p : @h_tm Sign Func Pred) : @h_tm Sign Func Pred :=
  match p with
  | tm_unit => tm_unit

  | tm_var i =>
      if cutoff <=? i then tm_var (shift + i) else tm_var i

  | tm_lam Phi p' =>
      tm_lam Phi (h_lift shift (Datatypes.S cutoff) p')

  | tm_app p1 p2 =>
      tm_app (h_lift shift cutoff p1) (h_lift shift cutoff p2)

  | tm_pair p1 p2 =>
      tm_pair (h_lift shift cutoff p1) (h_lift shift cutoff p2)

  | tm_fst p' =>
      tm_fst (h_lift shift cutoff p')

  | tm_snd p' =>
      tm_snd (h_lift shift cutoff p')

  | tm_inl Psi p' =>
      tm_inl Psi (h_lift shift cutoff p')

  | tm_inr Phi p' =>
      tm_inr Phi (h_lift shift cutoff p')

  | tm_case p0 p1 p2 =>
      tm_case
        (h_lift shift cutoff p0)
        (h_lift shift (Datatypes.S cutoff) p1)
        (h_lift shift (Datatypes.S cutoff) p2)

  | tm_absurd Phi p' =>
      tm_absurd Phi (h_lift shift cutoff p')

  | tm_all_intro p' =>
      tm_all_intro (h_lift shift cutoff p')

  | tm_all_elim p' t =>
      tm_all_elim (h_lift shift cutoff p') t

  | tm_ex_intro t p' =>
      tm_ex_intro t (h_lift shift cutoff p')

  | tm_ex_elim p1 p2 =>
      tm_ex_elim
        (h_lift shift cutoff p1)
        (h_lift shift (Datatypes.S cutoff) p2)

  | tm_eps_intro t p' =>
      tm_eps_intro t (h_lift shift cutoff p')

  | tm_eps_elim p1 p2 =>
      tm_eps_elim
        (h_lift shift cutoff p1)
        (h_lift shift (Datatypes.S cutoff) p2)
  end.
  
Fixpoint h_insert_at {Sign Func Pred : Type}
  (n : nat) (Psi : @h_ty Sign Func Pred) (G : @h_context Sign Func Pred) : @h_context Sign Func Pred :=
  match n, G with
  | Datatypes.O, _ => Psi :: G
  | Datatypes.S n', nil => Psi :: nil
  | Datatypes.S n', Phi :: G' => Phi :: h_insert_at n' Psi G'
  end.
  
Lemma All_WellFormed_insert : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
  (I : b_ty) (G : @h_context Sign Func Pred) (Psi : @h_ty Sign Func Pred) (n : nat),
  WellFormed I Psi ->
  All_WellFormed I G ->
  All_WellFormed I (h_insert_at n Psi G).
Proof.
  intros Sign Func Pred HFunc HPred SM I G Psi n HwfPsi HwfG.
  revert n.
  induction HwfG; intros n; destruct n; simpl.
  - (* G = nil, n = 0 *)
    apply AWF_Cons.
    + exact HwfPsi.
    + apply AWF_Nil.

  - (* G = nil, n = S n *)
    apply AWF_Cons.
    + exact HwfPsi.
    + apply AWF_Nil.

  - (* G = A :: G, n = 0 *)
    apply AWF_Cons.
    + exact HwfPsi.
    + apply AWF_Cons; assumption.

  - (* G = A :: G, n = S n *)
    apply AWF_Cons.
    + assumption.
    + apply IHHwfG.
Defined.

Lemma ctx_subst_insert : forall {Sign Func Pred : Type}
  (f : @b_tm Sign Func) (n : nat) (Psi : @h_ty Sign Func Pred) (G : @h_context Sign Func Pred),
  ctx_subst f (h_insert_at n Psi G)
  =
  h_insert_at n (form_subst f Psi) (ctx_subst f G).
Proof.
  intros Sign Func Pred f n Psi G.
  revert n.
  induction G as [|Phi G IH]; intros n; destruct n; simpl; auto.
  rewrite IH.
  reflexivity.
Defined.

Lemma ctx_equiv_insert : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
  (I : b_ty) (G1 G2 : @h_context Sign Func Pred) (Psi : @h_ty Sign Func Pred) (n : nat),
  WellFormed I Psi ->
  ctx_equiv I G1 G2 ->
  ctx_equiv I (h_insert_at n Psi G1) (h_insert_at n Psi G2).
Proof.
  intros Sign Func Pred HFunc HPred SM I G1 G2 Psi n HwfPsi Heq.
  revert n.
  induction Heq; intros n; destruct n; simpl.
  - apply CEq_Cons.
    + apply FE_Refl. exact HwfPsi.
    + apply CEq_Nil.
  - apply CEq_Cons.
    + apply FE_Refl. exact HwfPsi.
    + apply CEq_Nil.
  - apply CEq_Cons.
    + apply FE_Refl. exact HwfPsi.
    + apply CEq_Cons; assumption.
  - apply CEq_Cons.
    + exact f.
    + apply IHHeq.
Defined.

Theorem hd_weakening_general : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
  (I : b_ty) (G : @h_context Sign Func Pred) (p : @h_tm Sign Func Pred) (Phi Psi : @h_ty Sign Func Pred) (n : nat),
  WellFormed I Psi ->
  h_derivation I G p Phi ->
  h_derivation I (h_insert_at n Psi G) (h_lift 1 n p) Phi.
Proof.
  intros Sign Func Pred HFunc HPred SM I G p Phi Psi n HwfPsi d.
  revert n Psi HwfPsi.
  induction d; intros n0 Psi0 Hwf0; simpl.

    - (* HD_Var0 *)
    destruct n0; simpl.
    + apply HD_VarS.
      * exact Hwf0.
      * apply HD_Var0. exact a.

    + inversion a; subst.
      apply HD_Var0.
      apply AWF_Cons.
      * assumption.
      * apply All_WellFormed_insert; assumption.

    - (* HD_VarS *)
    destruct n0; simpl.
    + apply HD_VarS.
      * exact Hwf0.
      * apply HD_VarS; assumption.

    + destruct (n0 <=? n) eqn:Heq.
      * apply HD_VarS.
        -- exact w.
        -- replace (@tm_var Sign Func Pred (Datatypes.S n))
             with (@h_lift Sign Func Pred 1 n0 (@tm_var Sign Func Pred n)).
           ++ apply IHd. exact Hwf0.
           ++ simpl. rewrite Heq. reflexivity.

      * apply HD_VarS.
        -- exact w.
        -- replace (@tm_var Sign Func Pred n)
             with (@h_lift Sign Func Pred 1 n0 (@tm_var Sign Func Pred n)).
           ++ apply IHd. exact Hwf0.
           ++ simpl. rewrite Heq. reflexivity.
           
  - (* HD_Unit *)
    apply HD_Unit.
    apply All_WellFormed_insert; assumption.

  - (* HD_Conv *)
    eapply HD_Conv.
    + apply IHd. exact Hwf0.
    + exact f.

  - (* HD_Ctx_Conv *)
    eapply HD_Ctx_Conv.
    + eapply ctx_equiv_insert. exact Hwf0. exact c.
    + apply IHd. exact Hwf0.

    - (* HD_Lam *)
    apply HD_Lam.
    exact (IHd (Datatypes.S n0) Psi0 Hwf0).

  - (* HD_App *)
    eapply HD_App.
    + apply IHd1. exact Hwf0.
    + apply IHd2. exact Hwf0.

  - (* HD_Pair *)
    apply HD_Pair.
    + apply IHd1. exact Hwf0.
    + apply IHd2. exact Hwf0.

  - (* HD_Fst *)
    eapply HD_Fst.
    apply IHd.
    exact Hwf0.

  - (* HD_Snd *)
    eapply HD_Snd.
    apply IHd.
    exact Hwf0.

  - (* HD_Inl *)
    apply HD_Inl.
    + exact w.
    + apply IHd. exact Hwf0.

  - (* HD_Inr *)
    apply HD_Inr.
    + exact w.
    + apply IHd. exact Hwf0.

    - (* HD_Case *)
    eapply HD_Case.
    + apply IHd1.
      exact Hwf0.

    + change (h_derivation I
                (h_insert_at (Datatypes.S n0) Psi0 (Phi :: G))
                (@h_lift Sign Func Pred 1 (Datatypes.S n0) p1)
                Chi).
      apply IHd2.
      exact Hwf0.

    + change (h_derivation I
                (h_insert_at (Datatypes.S n0) Psi0 (Psi :: G))
                (@h_lift Sign Func Pred 1 (Datatypes.S n0) p2)
                Chi).
      apply IHd3.
      exact Hwf0.

  - (* HD_Absurd *)
    apply HD_Absurd.
    + exact w.
    + apply IHd. exact Hwf0.

  - (* HD_All_Intro *)
    apply HD_All_Intro.
    rewrite ctx_subst_insert.
    apply IHd.
    eapply wf_subst.
    + apply BT_Fst.
    + exact Hwf0.

  - (* HD_All_Elim *)
    eapply HD_All_Elim.
    + apply IHd. exact Hwf0.
    + exact b.

  - (* HD_Ex_Intro *)
    eapply HD_Ex_Intro.
    + exact b.
    + apply IHd. exact Hwf0.

   - (* HD_Ex_Elim *)
    eapply HD_Ex_Elim.
    + apply IHd1.
      exact Hwf0.

    + simpl.
      rewrite ctx_subst_insert.

      change (h_derivation (b_Prod I A)
                (h_insert_at
                   (Datatypes.S n0)
                   (form_subst b_fst Psi0)
                   (Phi :: ctx_subst b_fst G))
                (@h_lift Sign Func Pred 1 (Datatypes.S n0) p2)
                (form_subst b_fst Chi)).

      apply IHd2.

      eapply wf_subst.
      * apply BT_Fst.
      * exact Hwf0.

  - (* HD_Eps_Intro *)
    eapply HD_Eps_Intro.
    + exact b.
    + apply IHd. exact Hwf0.

   - (* HD_Eps_Elim *)
    eapply HD_Eps_Elim.
    + apply IHd1.
      exact Hwf0.

    + simpl.
      rewrite ctx_subst_insert.

      change (h_derivation (b_Prod I A)
                (h_insert_at
                   (Datatypes.S n0)
                   (form_subst b_fst Psi0)
                   (Phi :: ctx_subst b_fst G))
                (@h_lift Sign Func Pred 1 (Datatypes.S n0) p2)
                (form_subst b_fst Chi)).

      apply IHd2.

      eapply wf_subst.
      * apply BT_Fst.
      * exact Hwf0.
Defined.

Lemma hd_weakening : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
  (I : b_ty) (G : @h_context Sign Func Pred) (A : @h_ty Sign Func Pred) (p : @h_tm Sign Func Pred) (Phi : @h_ty Sign Func Pred),
  All_WellFormed I (A :: G) ->
  h_derivation I G p Phi ->
  h_derivation I (A :: G) (h_lift 1 0 p) Phi.
Proof.
  intros Sign Func Pred HFunc HPred SM I G A p Phi HwfCtx d.
  assert (HwfA : WellFormed I A).
  {
    inversion HwfCtx; subst.
    assumption.
  }
  exact (hd_weakening_general I G p Phi A 0 HwfA d).
Defined.

Fixpoint h_make_ctx_ty {Sign Func Pred : Type} (G : @h_context Sign Func Pred) : @h_ty Sign Func Pred :=
  match G with
  | nil => Ty_Unit
  | A :: G' => Ty_Prod (h_make_ctx_ty G') A
  end.

Fixpoint h_reify_ctx {Sign Func Pred : Type} (G : @h_context Sign Func Pred) : @h_tm Sign Func Pred :=
  match G with
  | nil => tm_unit
  | A :: G' => tm_pair (h_lift 1 0 (h_reify_ctx G')) (tm_var 0)
  end.
  
Lemma h_reify_ctx_typing : forall {Sign Func Pred : Type} `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
  (I : b_ty) (G : @h_context Sign Func Pred),
  All_WellFormed I G ->
  h_derivation I G (h_reify_ctx G) (h_make_ctx_ty G).
Proof.
  intros Sign Func Pred HFunc HPred SM I G HwfG.
  induction HwfG as [|A G HwfA HwfG IH]; simpl.
  - apply HD_Unit.
    apply AWF_Nil.
  - apply HD_Pair.
    + eapply hd_weakening.
      * apply AWF_Cons; assumption.
      * exact IH.
    + apply HD_Var0.
      apply AWF_Cons; assumption.
Defined.

Lemma term_model_interp_ctx_id : forall {Sign Func Pred : Type} `{HFunc : FunctionSignature Func} `{HPred : PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
  (I : b_ty) (G : @h_context Sign Func Pred),
  All_WellFormed I G ->
  projT1
    (@interp_h_ctx Sign Func Pred HFunc HPred
       (Base_SetoidCategory Sign Func)
       (Base_CartesianCategory Sign Func)
       (Base_TwoSortCategory Sign Func)
       (Base_SyntacticEpsilonFullModel Sign Func)
       TermModel_GoodFibration
       TermModel_StrictGoodFibration
       (@TermModel_EpsilonHyperModel Sign Func Pred HFunc HPred SM)
       I G)
  = h_make_ctx_ty G.
Proof.
  intros Sign Func Pred HFunc HPred SM I G HwfG.
  induction HwfG as [|Phi G HwfPhi HwfG IH]; simpl.
  - reflexivity.
  - cbn [projT1].
    f_equal.
    + exact IH.
    + apply term_model_interp_id.
      exact HwfPhi.
Defined.

Lemma term_model_inhabited_to_derivation :
  forall {Sign Func Pred : Type}
    `{HFunc : FunctionSignature Func} `{HPred : PredicateSignature Pred}
    {SM : SkolemMapping Sign Func Pred}
    {I : b_ty} {G : @h_context Sign Func Pred}
    {Phi : @h_ty Sign Func Pred}
    (wfc : All_WellFormed I G)
    (wf_Phi : WellFormed I Phi),
  inhabited
    (@hom
      (@Fiber
        (Base_SetoidCategory Sign Func)
        (Base_CartesianCategory Sign Func)
        (@TermModel_GoodFibration Sign Func Pred HFunc HPred SM)
        (@interp_ty
          (Base_SetoidCategory Sign Func)
          (Base_CartesianCategory Sign Func)
          (Base_TwoSortCategory Sign Func) I))
      (@interp_h_ctx Sign Func Pred HFunc HPred
        (Base_SetoidCategory Sign Func)
        (Base_CartesianCategory Sign Func)
        (Base_TwoSortCategory Sign Func)
        (Base_SyntacticEpsilonFullModel Sign Func)
        TermModel_GoodFibration
        TermModel_StrictGoodFibration
        (@TermModel_EpsilonHyperModel Sign Func Pred HFunc HPred SM)
        I G)
      (@interp_h_ty Sign Func Pred HFunc HPred
        (Base_SetoidCategory Sign Func)
        (Base_CartesianCategory Sign Func)
        (Base_TwoSortCategory Sign Func)
        (Base_SyntacticEpsilonFullModel Sign Func)
        TermModel_GoodFibration
        TermModel_StrictGoodFibration
        (@TermModel_EpsilonHyperModel Sign Func Pred HFunc HPred SM)
        I Phi)) ->
  exists p : @h_tm Sign Func Pred,
    inhabited (h_derivation I G p Phi).
Proof.
  intros Sign Func Pred HFunc HPred SM I G Phi wfc wf_Phi H_term.
  destruct H_term as [m_syn].
  destruct m_syn as [p_syn dp_syn].

  assert (H_ctx :
    projT1
      (@interp_h_ctx Sign Func Pred HFunc HPred
        (Base_SetoidCategory Sign Func)
        (Base_CartesianCategory Sign Func)
        (Base_TwoSortCategory Sign Func)
        (Base_SyntacticEpsilonFullModel Sign Func)
        TermModel_GoodFibration
        TermModel_StrictGoodFibration
        (@TermModel_EpsilonHyperModel Sign Func Pred HFunc HPred SM)
        I G)
    = h_make_ctx_ty G).
  {
    apply term_model_interp_ctx_id.
    exact wfc.
  }

  assert (H_phi :
    projT1
      (@interp_h_ty Sign Func Pred HFunc HPred
        (Base_SetoidCategory Sign Func)
        (Base_CartesianCategory Sign Func)
        (Base_TwoSortCategory Sign Func)
        (Base_SyntacticEpsilonFullModel Sign Func)
        TermModel_GoodFibration
        TermModel_StrictGoodFibration
        (@TermModel_EpsilonHyperModel Sign Func Pred HFunc HPred SM)
        I Phi)
    = Phi).
  {
    apply term_model_interp_id.
    exact wf_Phi.
  }

  rewrite H_ctx in dp_syn.
  rewrite H_phi in dp_syn.
  rewrite (interp_ty_id Sign Func I) in dp_syn.

  assert (H_fun :
    h_derivation I G p_syn (Ty_Arrow (h_make_ctx_ty G) Phi)).
  {
    change (h_derivation I (nil ++ G) p_syn
      (Ty_Arrow (h_make_ctx_ty G) Phi)).
    eapply (@h_derivation_append Sign Func Pred HFunc HPred SM
      I nil G p_syn (Ty_Arrow (h_make_ctx_ty G) Phi)).
    - exact dp_syn.
    - exact wfc.
  }

  exists (tm_app p_syn (h_reify_ctx G)).
  constructor.
  eapply HD_App.
  - exact H_fun.
  - apply h_reify_ctx_typing.
    exact wfc.
Defined.

Theorem epsilon_adjoint_completeness_inhabitational_gen :
  forall {Sign Func Pred : Type} `{HFunc : FunctionSignature Func} `{HPred : PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
         {I : b_ty} {G : @h_context Sign Func Pred} {Phi : @h_ty Sign Func Pred}
         (wfc : All_WellFormed I G)
         (wf_Phi : WellFormed I Phi),
  (forall (C : SetoidCategory) (CC : CartesianCategory C)
          (TSC : TwoSortCategory C)
          (BEM : @BaseEpsilonFullModel Sign Func HFunc C CC TSC)
          (GF : GoodFibration C)
          (SGF : StrictGoodFibration C GF)
          (EHM : @EpsilonHyperModel Sign Func Pred HFunc HPred C CC TSC BEM GF SGF)
          (AEF : @AdjointEpsilonFullFibration Sign Func Pred HFunc HPred SM C CC TSC BEM GF SGF EHM),
     inhabited
       (@hom (Fiber (interp_ty I))
             (@interp_h_ctx Sign Func Pred HFunc HPred C CC TSC BEM GF SGF EHM I G)
             (@interp_h_ty  Sign Func Pred HFunc HPred C CC TSC BEM GF SGF EHM I Phi))) ->
  exists (p : @h_tm Sign Func Pred),
    inhabited (h_derivation I G p Phi).
Proof.
  intros Sign Func Pred HFunc HPred SM I G Phi wfc wf_Phi H_univ.

  (* 1. Példányosítjuk az univerzális hipotézist a szintaktikus termmodellel. *)
  pose proof
    (H_univ
       (Base_SetoidCategory Sign Func)
       (Base_CartesianCategory Sign Func)
       (Base_TwoSortCategory Sign Func)
       (Base_SyntacticEpsilonFullModel Sign Func)
       TermModel_GoodFibration
       TermModel_StrictGoodFibration
       TermModel_EpsilonHyperModel
       TermModel_AdjointEpsilonFullFibration) as H_term.
  eapply term_model_inhabited_to_derivation.
  - exact wfc.
  - exact wf_Phi.
  - exact H_term.
Defined.   
