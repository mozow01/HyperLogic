Require Import HyperLogic.Cat.Core. 
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import Coq.Classes.Morphisms.

(* ================================================================= *)
(* GOOD FIBRATION DEFINITION                                         *)
(* ================================================================= *)

(* A Base kategóriának (B) Cartesian-nak kell lennie {CB},
   hogy tudjuk kezelni a kontextusokat (szorzatokat). *)
Class GoodFibration (B : SetoidCategory) {CB : CartesianCategory B} := mk_GoodFibration {

  Fiber : @obj B -> SetoidCategory;
  Fiber_is_Cartesian : forall (I : @obj B), CartesianCategory (Fiber I);
  Fiber_is_Closed    : forall (I : @obj B), @CartesianClosedCategory (Fiber I) (Fiber_is_Cartesian I);
  Fiber_is_BiClosed  : forall (I : @obj B), @BiCartesianClosedCategory (Fiber I) (Fiber_is_Cartesian I) (Fiber_is_Closed I);
  
  Pullback : forall {I J : @obj B}, (hom I J) -> Functor (Fiber J) (Fiber I);
  
  pullback_id_iso : forall {I : @obj B} (A : @obj (Fiber I)),
      (@fobj _ _ (Pullback (id I)) A) ≅O A;
  pullback_comp_iso : forall {I J K : @obj B} (g : hom J K) (f : hom I J) (A : @obj (Fiber K)),
      (@fobj _ _ (Pullback (compose g f)) A) ≅O
      (@fobj _ _ (Pullback f) (@fobj _ _ (Pullback g) A));

 
  (* A PULLBACK FUNKTOR MEGŐRZI A LOGIKAI (BiCCC) STRUKTÚRÁT   *)
 
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

  
  (* KVANTOR ADJUNGÁLTAK ÉS BECK-CHEVALLEY FELTÉTELEK          *)
  

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

  (* Pullback tiszteli a bázis morfizmusok egyenlőségét *)
  pb_iso : forall {I J : @obj B} (f g : hom I J),
      f ≅ g -> forall (A : @obj (Fiber J)), (@fobj _ _ (Pullback f) A) ≅O (@fobj _ _ (Pullback g) A);
}.

(* --- Instance regisztráció --- *)
Global Instance GF_Fiber_CC
  {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} (I : @obj B)
  : CartesianCategory (Fiber I) := Fiber_is_Cartesian I.

Global Instance GF_Fiber_CCC
  {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} (I : @obj B)
  : CartesianClosedCategory (Fiber I) := Fiber_is_Closed I.

Global Instance GF_Fiber_BCCC
  {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} (I : @obj B)
  : BiCartesianClosedCategory (GF_Fiber_CCC I) := Fiber_is_BiClosed I.



(* ================================================================= *)
(* TOTAL CATEGORY (Grothendieck Konstrukció / Teljes Tér: E)         *)
(* ================================================================= *)

Class TotalObj {B : SetoidCategory} {CB : CartesianCategory B} (GF : GoodFibration B) := mk_TotalObj {
  t_base : @obj B;
  t_fib  : @obj (Fiber t_base)
}.
(* A Class kulcsszó miatt a Coq a példányt implicitnek veszi. 
   Ezekkel a sorokkal visszakapcsoljuk explicitre, mint a Recordnál! *)
Arguments t_base {_ _ _} _.
Arguments t_fib {_ _ _} _.

Class TotalHom {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} (X Y : TotalObj GF) := mk_TotalHom {
  h_base : hom (t_base X) (t_base Y);
  h_fib  : hom (t_fib X) (@fobj _ _ (Pullback h_base) (t_fib Y))
}.
(* Itt is kikényszerítjük, hogy a morfizmus paraméter explicit maradjon. *)
Arguments h_base {_ _ _ _ _} _.
Arguments h_fib {_ _ _ _ _} _.

Definition TotalHom_equiv {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} 
                          {X Y : TotalObj GF} (M1 M2 : TotalHom X Y) : Prop :=
  exists (H_base : h_base M2 ≅ h_base M1),
    h_fib M1 ≅ 
    (* Itt a varázslat: @iso_to _ _ _ (példány) *)
    compose (@iso_to _ _ _ (pb_iso (h_base M2) (h_base M1) H_base (t_fib Y))) (h_fib M2).

(* ================================================================= *)
(* STRICT GOOD FIBRATION (A Valódi Globális PI)                      *)
(* ================================================================= *)

Class StrictGoodFibration (B : SetoidCategory) {CB : CartesianCategory B} (GF : GoodFibration B) := {
  fiber_is_thin : forall (I : @obj B), Thin (Fiber I);
  
  global_pi : forall (X Y : TotalObj GF) (M1 M2 : TotalHom X Y),
    h_base M1 ≅ h_base M2 -> 
    TotalHom_equiv M1 M2
}.

Global Instance SGF_Fiber_Thin
  {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {SGF : StrictGoodFibration B GF} (I : @obj B)
  : Thin (Fiber I) := fiber_is_thin I.


(* ================================================================= *)
(* A TOTAL KATEGÓRIA STRUKTÚRÁJA (Identitás és Kompozíció)           *)
(* ================================================================= *)

Definition total_id {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} 
                    (X : TotalObj GF) : TotalHom X X :=
  (* Kőkemény explicit hívás a @ operátorral: minden paramétert mi adunk meg! *)
  @mk_TotalHom B CB GF X X 
    (id (t_base X)) 
    (@iso_from _ _ _ (pullback_id_iso (t_fib X))).

Definition total_comp {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} 
                      {X Y Z : TotalObj GF} 
                      (M2 : TotalHom Y Z) (M1 : TotalHom X Y) : TotalHom X Z :=
  (* Itt is @mk_TotalHom-ot használunk az egyértelműség kedvéért *)
  @mk_TotalHom B CB GF X Z 
    (compose (h_base M2) (h_base M1))
    (compose 
       (@iso_from _ _ _ (pullback_comp_iso (h_base M2) (h_base M1) (t_fib Z)))
       (compose 
          (@fmap (Fiber (t_base Y)) (Fiber (t_base X)) (Pullback (h_base M1)) 
                 (t_fib Y) (@fobj _ _ (Pullback (h_base M2)) (t_fib Z)) (h_fib M2))
          (h_fib M1))).

(* ================================================================= *)
(* BIZONYÍTÁSOK ÉS KATEGÓRIA INSTANCE                                *)
(* ================================================================= *)

Instance TotalHom_Equivalence {B : SetoidCategory} {CB : CartesianCategory B} 
  {GF : GoodFibration B} {SGF : StrictGoodFibration B GF} {X Y : TotalObj GF} 
  : Equivalence (@TotalHom_equiv B CB GF X Y).
Proof.
  split.
  - intros M. apply global_pi. reflexivity.
  - intros M1 M2 H. apply global_pi. destruct H as [Hb _]. exact Hb.
  - intros M1 M2 M3 H1 H2. apply global_pi. 
    destruct H1 as [Hb1 _]. destruct H2 as [Hb2 _]. 
    symmetry in Hb1. symmetry in Hb2. transitivity (h_base M2). all: assumption.
Qed.

(* A Teljes Tér MINT Setoid Kategória - "Program" kulcsszó nélkül, inline Ltac-kal! *)
(* A Teljes Tér MINT Setoid Kategória - Kifejtett Proof-fal a soronkénti debugoláshoz! *)
Instance TotalCategory {B : SetoidCategory} {CB : CartesianCategory B} 
  (GF : GoodFibration B) (SGF : StrictGoodFibration B GF) : SetoidCategory.
Proof.
  (* A refine segítségével megadjuk a struktúrát, és '_' jelet teszünk oda, 
     amit bizonyítani akarunk. Így a Coq 4 tiszta célt (subgoal) generál. *)
  refine {|
    obj := TotalObj GF;
    hom := @TotalHom B CB GF;
    id := @total_id B CB GF;
    compose := @total_comp B CB GF;
    hom_equiv := @TotalHom_equiv B CB GF;
    hom_equiv_equivalence := @TotalHom_Equivalence B CB GF SGF;
    
    comp_assoc := _;
    id_right := _;
    id_left := _;
    comp_proper := _
  |}.
  
  - (* 1. Cél: comp_assoc *)
    intros X Y Z W f g h.
    apply global_pi.
    apply comp_assoc.
    
  - (* 2. Cél: id_right *)
    intros X Y f.
    apply global_pi.
    apply id_right.
    
  - (* 3. Cél: id_left *)
    intros X Y f.
    apply global_pi.
    apply id_left.
    
  - (* 4. Cél: comp_proper *)
    intros X Y Z f g h i Hf Hh.
    apply global_pi.
    destruct Hf as [Hfb _].
    destruct Hh as [Hhb _].
    apply comp_proper. symmetry in Hfb. exact Hfb.  symmetry in Hhb. exact Hhb.
Defined.

(* ================================================================= *)
(* KVANTOROK KONSTRUKCIÓJA (Sigma és Pi)                             *)
(* ================================================================= *)

Definition Sigma_f {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {I J : @obj B} (f : hom I J)
  : Functor (Fiber I) (Fiber J) :=
  (* Közvetlen definíció: megadjuk a funktort és az Adjoint példányt expliciten *)
  LeftAdjointFunctor (Pullback f) (@pullback_has_left_adjoint B CB GF I J f).

Definition Pi_f {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {I J : @obj B} (f : hom I J)
  : Functor (Fiber I) (Fiber J) :=
  RightAdjointFunctor (Pullback f) (@pullback_has_right_adjoint B CB GF I J f).

(* ================================================================= *)
(* BASE LOGIC (Individuumok)                                         *)
(* ================================================================= *)

Class TwoSortCategory (B : SetoidCategory) {CB : CartesianCategory B} := mk_TwoSortCategory {
  (* A 'One' (terminális) már jön a CB-ből, itt csak az S-t (Individuum típus) definiáljuk *)
  S : @obj B;
  S_is_not_Terminal : S <> terminal 
}.
(* Kívülről kikapcsoljuk az S typeclass-függő implicit feloldását *)
Arguments S {_ _} _.

(* A "bang" morfizmus: S -> 1 (terminális leképezés) *)
(* Itt már expliciten hivatkozunk az S-re az @ operátorral, hogy a Coq ne tévedjen el *)
Definition bang (B : SetoidCategory) {CB : CartesianCategory B} {TSC : TwoSortCategory B} : hom (@S B CB TSC) terminal :=
  terminal_map.

(* ================================================================= *)
(* LOGIKAI KVANTOROK (Exists / Forall)                               *)
(* ================================================================= *)

(** Exisztenciális kvantor: Sigma a bang mentén (S -> 1) *)
Definition ExistsQuantifier (B : SetoidCategory) {CB : CartesianCategory B} {GF : GoodFibration B} {TSC : TwoSortCategory B}
  : Functor (Fiber (@S B CB TSC)) (Fiber terminal) :=
  (* Mindent expliciten átadunk a Sigma_f-nek *)
  @Sigma_f B CB GF (@S B CB TSC) terminal (bang B).

(** Univerzális kvantor: Pi a bang mentén (S -> 1) *)
Definition ForallQuantifier (B : SetoidCategory) {CB : CartesianCategory B} {GF : GoodFibration B} {TSC : TwoSortCategory B}
  : Functor (Fiber (@S B CB TSC)) (Fiber terminal) :=
  @Pi_f B CB GF (@S B CB TSC) terminal (bang B).