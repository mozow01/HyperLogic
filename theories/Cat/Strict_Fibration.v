Require Import HyperLogic.Cat.Core. 
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import Coq.Classes.Morphisms.

(* ================================================================= *)
(* THIN GOOD FIBRATION (Biztonságos, gyakorlatias Coq verzió)        *)
(* ================================================================= *)

Class ThinGoodFibration (B : SetoidCategory) {CB : CartesianCategory B} := mk_ThinGoodFibration {

  Fiber : @obj B -> SetoidCategory;
  
  (* A szálak Lokálisan Proof Irrelevantek *)
  fiber_is_thin : forall (I : @obj B), Thin (Fiber I);

  Fiber_is_Cartesian : forall (I : @obj B), CartesianCategory (Fiber I);
  Fiber_is_Closed    : forall (I : @obj B), @CartesianClosedCategory (Fiber I) (Fiber_is_Cartesian I);
  Fiber_is_BiClosed  : forall (I : @obj B), @BiCartesianClosedCategory (Fiber I) (Fiber_is_Cartesian I) (Fiber_is_Closed I);
  
  Pullback : forall {I J : @obj B}, (hom I J) -> Functor (Fiber J) (Fiber I);
  
  pullback_id_iso : forall {I : @obj B} (A : @obj (Fiber I)),
      (@fobj _ _ (Pullback (id I)) A) ≅O A;
  pullback_comp_iso : forall {I J K : @obj B} (g : hom J K) (f : hom I J) (A : @obj (Fiber K)),
      (@fobj _ _ (Pullback (compose g f)) A) ≅O
      (@fobj _ _ (Pullback f) (@fobj _ _ (Pullback g) A));

  (* VISSZATÉVE: A kényelmi izomorfizmusok a gyors rewrite-hoz! *)
  pb_term_iso : forall {I J : @obj B} (f : hom I J),
      (@fobj _ _ (Pullback f) (@terminal _ (Fiber_is_Cartesian J))) ≅O
      (@terminal _ (Fiber_is_Cartesian I));
  pb_prod_iso : forall {I J : @obj B} (f : hom I J) (A B : @obj (Fiber J)),
      (@fobj _ _ (Pullback f) (@prod _ (Fiber_is_Cartesian J) A B)) ≅O
      (@prod _ (Fiber_is_Cartesian I) (@fobj _ _ (Pullback f) A) (@fobj _ _ (Pullback f) B));
  pb_init_iso : forall {I J : @obj B} (f : hom I J),
      (@fobj _ _ (Pullback f) (@initial _ _ (Fiber_is_Closed J) (Fiber_is_BiClosed J))) ≅O
      (@initial _ _ (Fiber_is_Closed I) (Fiber_is_BiClosed I));
  pb_coprod_iso : forall {I J : @obj B} (f : hom I J) (A B : @obj (Fiber J)),
      (@fobj _ _ (Pullback f) (@coprod _ _ (Fiber_is_Closed J) (Fiber_is_BiClosed J) A B)) ≅O
      (@coprod _ _ (Fiber_is_Closed I) (Fiber_is_BiClosed I) (@fobj _ _ (Pullback f) A) (@fobj _ _ (Pullback f) B));
  pb_exp_iso : forall {I J : @obj B} (f : hom I J) (A B : @obj (Fiber J)),
      (@fobj _ _ (Pullback f) (@exp _ _ (Fiber_is_Closed J) A B)) ≅O
      (@exp _ _ (Fiber_is_Closed I) (@fobj _ _ (Pullback f) A) (@fobj _ _ (Pullback f) B));

  (* Kvantorok és Beck-Chevalley *)
  pullback_has_left_adjoint : forall {I J : @obj B} (f : hom I J), IsRightAdjoint (Pullback f);
  pullback_has_right_adjoint : forall {I J : @obj B} (f : hom I J), IsLeftAdjoint (Pullback f);
  
  beck_chevalley_sigma : forall {I J K : @obj B} (f : hom K I) (A : @obj (Fiber (@prod B CB I J))),
      (@fobj _ _ (Pullback f) (@left_adj_obj _ _ _ (pullback_has_left_adjoint (@prod_fst B CB I J)) A)) ≅O
      (@left_adj_obj _ _ _ (pullback_has_left_adjoint (@prod_fst B CB K J))
          (@fobj _ _ (Pullback (@prod_map B CB (prod K J) I J (compose f (@prod_fst B CB K J)) (@prod_snd B CB K J))) A));
          
  beck_chevalley_pi : forall {I J K : @obj B} (f : hom K I) (A : @obj (Fiber (@prod B CB I J))),
      (@fobj _ _ (Pullback f) (@right_adj_obj _ _ _ (pullback_has_right_adjoint (@prod_fst B CB I J)) A)) ≅O
      (@right_adj_obj _ _ _ (pullback_has_right_adjoint (@prod_fst B CB K J))
          (@fobj _ _ (Pullback (@prod_map B CB (prod K J) I J (compose f (@prod_fst B CB K J)) (@prod_snd B CB K J))) A));

  pb_iso : forall {I J : @obj B} (f g : hom I J),
      f ≅ g -> forall (A : @obj (Fiber J)), (@fobj _ _ (Pullback f) A) ≅O (@fobj _ _ (Pullback g) A)
}.

(* --- Instance regisztráció --- *)
Global Instance TGF_Fiber_CC
  {B : SetoidCategory} {CB : CartesianCategory B} {TGF : ThinGoodFibration B} (I : @obj B)
  : CartesianCategory (Fiber I) := Fiber_is_Cartesian I.

Global Instance TGF_Fiber_CCC
  {B : SetoidCategory} {CB : CartesianCategory B} {TGF : ThinGoodFibration B} (I : @obj B)
  : CartesianClosedCategory (Fiber I) := Fiber_is_Closed I.

Global Instance TGF_Fiber_BCCC
  {B : SetoidCategory} {CB : CartesianCategory B} {TGF : ThinGoodFibration B} (I : @obj B)
  : BiCartesianClosedCategory (TGF_Fiber_CCC I) := Fiber_is_BiClosed I.

Global Instance TGF_Fiber_Thin
  {B : SetoidCategory} {CB : CartesianCategory B} {TGF : ThinGoodFibration B} (I : @obj B)
  : Thin (Fiber I) := fiber_is_thin I.


(* ================================================================= *)
(* TOTAL CATEGORY A THIN FIBRÁCIÓRA                                  *)
(* ================================================================= *)

Class ThinTotalObj {B : SetoidCategory} {CB : CartesianCategory B} (TGF : ThinGoodFibration B) := mk_ThinTotalObj {
  t_base : @obj B;
  t_fib  : @obj (Fiber t_base)
}.
Arguments t_base {_ _ _} _.
Arguments t_fib {_ _ _} _.

Class ThinTotalHom {B : SetoidCategory} {CB : CartesianCategory B} {TGF : ThinGoodFibration B} (X Y : ThinTotalObj TGF) := mk_ThinTotalHom {
  h_base : hom (t_base X) (t_base Y);
  h_fib  : hom (t_fib X) (@fobj _ _ (Pullback h_base) (t_fib Y))
}.
Arguments h_base {_ _ _ _ _} _.
Arguments h_fib {_ _ _ _ _} _.

Definition ThinTotalHom_equiv {B : SetoidCategory} {CB : CartesianCategory B} {TGF : ThinGoodFibration B} 
                          {X Y : ThinTotalObj TGF} (M1 M2 : ThinTotalHom X Y) : Prop :=
  exists (H_base : h_base M2 ≅ h_base M1),
    h_fib M1 ≅ 
    compose (@iso_to _ _ _ (pb_iso (h_base M2) (h_base M1) H_base (t_fib Y))) (h_fib M2).


(* ================================================================= *)
(* STRICT THIN GOOD FIBRATION (A Globális PI)                        *)
(* ================================================================= *)

Class StrictThinGoodFibration (B : SetoidCategory) {CB : CartesianCategory B} (TGF : ThinGoodFibration B) := {
  global_pi : forall (X Y : ThinTotalObj TGF) (M1 M2 : ThinTotalHom X Y),
    h_base M1 ≅ h_base M2 -> 
    ThinTotalHom_equiv M1 M2
}.


(* ================================================================= *)
(* A TOTAL KATEGÓRIA STRUKTÚRÁJA ÉS BIZONYÍTÁSAI                     *)
(* ================================================================= *)

Definition thin_total_id {B : SetoidCategory} {CB : CartesianCategory B} {TGF : ThinGoodFibration B} 
                    (X : ThinTotalObj TGF) : ThinTotalHom X X :=
  @mk_ThinTotalHom B CB TGF X X 
    (id (t_base X)) 
    (@iso_from _ _ _ (pullback_id_iso (t_fib X))).

Definition thin_total_comp {B : SetoidCategory} {CB : CartesianCategory B} {TGF : ThinGoodFibration B} 
                      {X Y Z : ThinTotalObj TGF} 
                      (M2 : ThinTotalHom Y Z) (M1 : ThinTotalHom X Y) : ThinTotalHom X Z :=
  @mk_ThinTotalHom B CB TGF X Z 
    (compose (h_base M2) (h_base M1))
    (compose 
       (@iso_from _ _ _ (pullback_comp_iso (h_base M2) (h_base M1) (t_fib Z)))
       (compose 
          (@fmap (Fiber (t_base Y)) (Fiber (t_base X)) (Pullback (h_base M1)) 
                 (t_fib Y) (@fobj _ _ (Pullback (h_base M2)) (t_fib Z)) (h_fib M2))
          (h_fib M1))).

Instance ThinTotalHom_Equivalence {B : SetoidCategory} {CB : CartesianCategory B} 
  {TGF : ThinGoodFibration B} {STGF : StrictThinGoodFibration B TGF} {X Y : ThinTotalObj TGF} 
  : Equivalence (@ThinTotalHom_equiv B CB TGF X Y).
Proof.
  split.
  - intros M. apply global_pi. reflexivity.
  - intros M1 M2 H. apply global_pi. destruct H as [Hb _]. exact Hb.
  - intros M1 M2 M3 H1 H2. apply global_pi. 
    destruct H1 as [Hb1 _]. destruct H2 as [Hb2 _]. 
    symmetry in Hb1. symmetry in Hb2. transitivity (h_base M2). all: assumption. 
Defined.

Instance ThinTotalCategory {B : SetoidCategory} {CB : CartesianCategory B} 
  (TGF : ThinGoodFibration B) (STGF : StrictThinGoodFibration B TGF) : SetoidCategory.
Proof.
  refine {|
    obj := ThinTotalObj TGF;
    hom := @ThinTotalHom B CB TGF;
    id := @thin_total_id B CB TGF;
    compose := @thin_total_comp B CB TGF;
    hom_equiv := @ThinTotalHom_equiv B CB TGF;
    hom_equiv_equivalence := @ThinTotalHom_Equivalence B CB TGF STGF;
    
    comp_assoc := _;
    id_right := _;
    id_left := _;
    comp_proper := _
  |}.
  
  - intros X Y Z W f g h. apply global_pi. apply comp_assoc.
  - intros X Y f. apply global_pi. apply id_right.
  - intros X Y f. apply global_pi. apply id_left.
  - intros X Y Z f g h i Hf Hh. apply global_pi.
    destruct Hf as [Hfb _]. destruct Hh as [Hhb _].
    apply comp_proper. symmetry in Hfb. exact Hfb.
    symmetry in Hhb. exact Hhb.
Defined.


(* ================================================================= *)
(* KVANTOROK KONSTRUKCIÓJA (Sigma és Pi)                             *)
(* ================================================================= *)

Definition Thin_Sigma_f {B : SetoidCategory} {CB : CartesianCategory B} {TGF : ThinGoodFibration B} {I J : @obj B} (f : hom I J)
  : Functor (Fiber I) (Fiber J) :=
  LeftAdjointFunctor (Pullback f) (@pullback_has_left_adjoint B CB TGF I J f).

Definition Thin_Pi_f {B : SetoidCategory} {CB : CartesianCategory B} {TGF : ThinGoodFibration B} {I J : @obj B} (f : hom I J)
  : Functor (Fiber I) (Fiber J) :=
  RightAdjointFunctor (Pullback f) (@pullback_has_right_adjoint B CB TGF I J f).

(* ================================================================= *)
(* BASE LOGIC (Individuumok)                                         *)
(* ================================================================= *)

Class ThinTwoSortCategory (B : SetoidCategory) {CB : CartesianCategory B} := mk_ThinTwoSortCategory {
  S : @obj B;
  S_is_not_Terminal : S <> terminal 
}.
Arguments S {_ _} _.

Definition thin_bang (B : SetoidCategory) {CB : CartesianCategory B} {TSC : ThinTwoSortCategory B} : hom (@S B CB TSC) terminal :=
  terminal_map.

(* ================================================================= *)
(* LOGIKAI KVANTOROK (Exists / Forall)                               *)
(* ================================================================= *)

Definition Thin_ExistsQuantifier (B : SetoidCategory) {CB : CartesianCategory B} {TGF : ThinGoodFibration B} {TSC : ThinTwoSortCategory B}
  : Functor (Fiber (@S B CB TSC)) (Fiber terminal) :=
  @Thin_Sigma_f B CB TGF (@S B CB TSC) terminal (thin_bang B).

Definition Thin_ForallQuantifier (B : SetoidCategory) {CB : CartesianCategory B} {TGF : ThinGoodFibration B} {TSC : ThinTwoSortCategory B}
  : Functor (Fiber (@S B CB TSC)) (Fiber terminal) :=
  @Thin_Pi_f B CB TGF (@S B CB TSC) terminal (thin_bang B).