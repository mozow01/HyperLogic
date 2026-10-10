Require Import HyperLogic.Cat.Core. 
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.

(** [GoodFibration] packages thin BiCCC fibers, reindexing, chosen
    preservation isomorphisms, projection adjoints, and Beck-Chevalley laws. *)

Class GoodFibration (B : SetoidCategory) {CB : CartesianCategory B} := mk_GoodFibration {
  
  Fiber : @obj B -> SetoidCategory;
  
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

  (** Chosen preservation maps make reindexing laws directly available to rewriting. *)
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

  (** Quantifiers are adjoints only to reindexing along projections. *)
  pullback_has_left_adjoint : forall {I A : @obj B}, IsRightAdjoint (Pullback (@prod_fst B CB I A));
  pullback_has_right_adjoint : forall {I A : @obj B}, IsLeftAdjoint (Pullback (@prod_fst B CB I A));

  beck_chevalley_sigma : forall {I J K : @obj B} (f : hom K I) (A : @obj (Fiber (@prod B CB I J))),
      (@fobj _ _ (Pullback f) (@left_adj_obj _ _ _ pullback_has_left_adjoint A)) ≅O
      (@left_adj_obj _ _ _ pullback_has_left_adjoint
          (@fobj _ _ (Pullback (@prod_map B CB (prod K J) I J (compose f (@prod_fst B CB K J)) (@prod_snd B CB K J))) A));
          
  beck_chevalley_pi : forall {I J K : @obj B} (f : hom K I) (A : @obj (Fiber (@prod B CB I J))),
      (@fobj _ _ (Pullback f) (@right_adj_obj _ _ _ pullback_has_right_adjoint A)) ≅O
      (@right_adj_obj _ _ _ pullback_has_right_adjoint
          (@fobj _ _ (Pullback (@prod_map B CB (prod K J) I J (compose f (@prod_fst B CB K J)) (@prod_snd B CB K J))) A));

  pb_iso : forall {I J : @obj B} (f g : hom I J),
      f ≅ g -> forall (A : @obj (Fiber J)), (@fobj _ _ (Pullback f) A) ≅O (@fobj _ _ (Pullback g) A)
}.

Global Instance GF_Fiber_CC
  {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} (I : @obj B)
  : CartesianCategory (Fiber I) := Fiber_is_Cartesian I.

Global Instance GF_Fiber_CCC
  {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} (I : @obj B)
  : CartesianClosedCategory (Fiber I) := Fiber_is_Closed I.

Global Instance GF_Fiber_BCCC
  {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} (I : @obj B)
  : BiCartesianClosedCategory (GF_Fiber_CCC I) := Fiber_is_BiClosed I.

Global Instance GF_Fiber_Thin
  {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} (I : @obj B)
  : Thin (Fiber I) := fiber_is_thin I.

(** A BiCCC-valued view of a fibration. *)

(** [Iso] is Type-valued, while [SetoidCategory] expects Prop-valued
    hom-equivalences.  This wrapper is the Prop-valued reading of object
    isomorphism used below. *)
Inductive IsoProp {C : SetoidCategory} (A B : @obj C) : Prop :=
| iso_prop_intro : A ≅O B -> IsoProp A B.

Definition OppositeCategory (C : SetoidCategory) : SetoidCategory.
Proof.
  refine {|
    obj := @obj C;
    hom := fun x y => @hom C y x;
    id := fun x => @id C x;
    compose := fun x y z f g => @compose C z y x g f;
    hom_equiv := fun x y f g => @hom_equiv C y x f g;
    hom_equiv_equivalence := fun x y => @hom_equiv_equivalence C y x;

    comp_assoc := _;
    id_right := _;
    id_left := _;
    comp_proper := _
  |}.
  - intros x y z w f g h. symmetry. apply comp_assoc.
  - intros x y f. apply id_left.
  - intros x y f. apply id_right.
  - intros x y z f g h i Hfg Hhi.
    apply comp_proper; [exact Hhi | exact Hfg].
Defined.

Record BiCCCObject := mk_BiCCCObject {
  biccc_cat : SetoidCategory;
  biccc_cartesian : CartesianCategory biccc_cat;
  biccc_closed : @CartesianClosedCategory biccc_cat biccc_cartesian;
  biccc_biclosed : @BiCartesianClosedCategory biccc_cat biccc_cartesian biccc_closed
}.

Record BiCCCFunctor (X Y : BiCCCObject) := mk_BiCCCFunctor {
  biccc_functor : Functor (biccc_cat X) (biccc_cat Y);

  biccc_pres_terminal :
    @fobj _ _ biccc_functor (@terminal (biccc_cat X) (biccc_cartesian X)) ≅O
    @terminal (biccc_cat Y) (biccc_cartesian Y);

  biccc_pres_prod : forall (A B : @obj (biccc_cat X)),
    @fobj _ _ biccc_functor (@prod (biccc_cat X) (biccc_cartesian X) A B) ≅O
    @prod (biccc_cat Y) (biccc_cartesian Y)
      (@fobj _ _ biccc_functor A)
      (@fobj _ _ biccc_functor B);

  biccc_pres_initial :
    @fobj _ _ biccc_functor
      (@initial (biccc_cat X) (biccc_cartesian X) (biccc_closed X) (biccc_biclosed X)) ≅O
    @initial (biccc_cat Y) (biccc_cartesian Y) (biccc_closed Y) (biccc_biclosed Y);

  biccc_pres_coprod : forall (A B : @obj (biccc_cat X)),
    @fobj _ _ biccc_functor
      (@coprod (biccc_cat X) (biccc_cartesian X) (biccc_closed X) (biccc_biclosed X) A B) ≅O
    @coprod (biccc_cat Y) (biccc_cartesian Y) (biccc_closed Y) (biccc_biclosed Y)
      (@fobj _ _ biccc_functor A)
      (@fobj _ _ biccc_functor B);

  biccc_pres_exp : forall (A B : @obj (biccc_cat X)),
    @fobj _ _ biccc_functor
      (@exp (biccc_cat X) (biccc_cartesian X) (biccc_closed X) A B) ≅O
    @exp (biccc_cat Y) (biccc_cartesian Y) (biccc_closed Y)
      (@fobj _ _ biccc_functor A)
      (@fobj _ _ biccc_functor B)
}.

Arguments biccc_functor {X Y} _.
Arguments biccc_pres_terminal {X Y} _.
Arguments biccc_pres_prod {X Y} _ _ _.
Arguments biccc_pres_initial {X Y} _.
Arguments biccc_pres_coprod {X Y} _ _ _.
Arguments biccc_pres_exp {X Y} _ _ _.

Definition BiCCCFunctor_equiv {X Y : BiCCCObject}
  (F G : BiCCCFunctor X Y) : Prop :=
  forall A : @obj (biccc_cat X),
    IsoProp (@fobj _ _ (biccc_functor F) A)
            (@fobj _ _ (biccc_functor G) A).

Instance BiCCCFunctor_equiv_equivalence {X Y : BiCCCObject}
  : Equivalence (@BiCCCFunctor_equiv X Y).
Proof.
  split.
  - intros F A. constructor. reflexivity.
  - intros F G HFG A.
    destruct (HFG A) as [HI].
    constructor. symmetry. exact HI.
  - intros F G H HFG HGH A.
    destruct (HFG A) as [HI1].
    destruct (HGH A) as [HI2].
    constructor.
    transitivity (@fobj _ _ (biccc_functor G) A).
    + exact HI1.
    + exact HI2.
Defined.

Definition BiCCC_id (X : BiCCCObject) : BiCCCFunctor X X.
Proof.
  refine (mk_BiCCCFunctor X X (IdFunctor (biccc_cat X)) _ _ _ _ _);
  simpl; try intros; reflexivity.
Defined.

Definition BiCCC_comp {X Y Z : BiCCCObject}
  (G : BiCCCFunctor Y Z) (F : BiCCCFunctor X Y) : BiCCCFunctor X Z.
Proof.
  refine (mk_BiCCCFunctor X Z
    (ComposeFunctors (biccc_functor G) (biccc_functor F))
    _ _ _ _ _).
  - exact (iso_trans
      (functor_iso_cong (biccc_functor G) (biccc_pres_terminal F))
      (biccc_pres_terminal G)).
  - intros A B0.
    exact (iso_trans
      (functor_iso_cong (biccc_functor G) (biccc_pres_prod F A B0))
      (biccc_pres_prod G (@fobj _ _ (biccc_functor F) A) (@fobj _ _ (biccc_functor F) B0))).
  - exact (iso_trans
      (functor_iso_cong (biccc_functor G) (biccc_pres_initial F))
      (biccc_pres_initial G)).
  - intros A B0.
    exact (iso_trans
      (functor_iso_cong (biccc_functor G) (biccc_pres_coprod F A B0))
      (biccc_pres_coprod G (@fobj _ _ (biccc_functor F) A) (@fobj _ _ (biccc_functor F) B0))).
  - intros A B0.
    exact (iso_trans
      (functor_iso_cong (biccc_functor G) (biccc_pres_exp F A B0))
      (biccc_pres_exp G (@fobj _ _ (biccc_functor F) A) (@fobj _ _ (biccc_functor F) B0))).
Defined.

(** [SetoidCategory] is monomorphic in this development, so the literal
    category of all BiCCCs is one universe too large.  This small coded version
    is enough for ordinary functors: choose a small type of codes and decode
    each code as a BiCCC object. *)
Definition BiCCC_SetoidCategory_on
  (ObjCode : Type) (decode : ObjCode -> BiCCCObject) : SetoidCategory.
Proof.
  refine {|
    obj := ObjCode;
    hom := fun X Y => BiCCCFunctor (decode X) (decode Y);
    id := fun X => BiCCC_id (decode X);
    compose := fun X Y Z G F => BiCCC_comp G F;
    hom_equiv := fun X Y => @BiCCCFunctor_equiv (decode X) (decode Y);
    hom_equiv_equivalence := fun X Y => @BiCCCFunctor_equiv_equivalence (decode X) (decode Y);

    comp_assoc := _;
    id_right := _;
    id_left := _;
    comp_proper := _
  |}.
  - intros X Y Z W F G H A. constructor. simpl. reflexivity.
  - intros X Y F A. constructor. simpl. reflexivity.
  - intros X Y F A. constructor. simpl. reflexivity.
  - intros X Y Z F G H I HFG HHI A.
    destruct (HFG (@fobj _ _ (biccc_functor H) A)) as [HI1].
    destruct (HHI A) as [HI2].
    constructor. simpl.
    eapply iso_trans.
    + exact HI1.
    + apply functor_iso_cong. exact HI2.
Defined.

Definition Fiber_BiCCCObject
  {B : SetoidCategory} {CB : CartesianCategory B}
  {GF : GoodFibration B} (I : @obj B) : BiCCCObject :=
  mk_BiCCCObject
    (Fiber I)
    (Fiber_is_Cartesian I)
    (Fiber_is_Closed I)
    (Fiber_is_BiClosed I).

Definition Pullback_BiCCCFunctor
  {B : SetoidCategory} {CB : CartesianCategory B}
  {GF : GoodFibration B} {I J : @obj B} (f : hom I J)
  : BiCCCFunctor (Fiber_BiCCCObject J) (Fiber_BiCCCObject I).
Proof.
  refine (@mk_BiCCCFunctor
    (Fiber_BiCCCObject J)
    (Fiber_BiCCCObject I)
    (Pullback f) _ _ _ _ _).
  - exact (pb_term_iso f).
  - intros A B0. exact (pb_prod_iso f A B0).
  - exact (pb_init_iso f).
  - intros A B0. exact (pb_coprod_iso f A B0).
  - intros A B0. exact (pb_exp_iso f A B0).
Defined.

Definition Fiber_BiCCC_SetoidCategory
  {B : SetoidCategory} {CB : CartesianCategory B}
  {GF : GoodFibration B} : SetoidCategory :=
  BiCCC_SetoidCategory_on (@obj B) (@Fiber_BiCCCObject B CB GF).

Definition Fiber_ContravariantFunctor
  {B : SetoidCategory} {CB : CartesianCategory B}
  {GF : GoodFibration B}
  : Functor (OppositeCategory B) (@Fiber_BiCCC_SetoidCategory B CB GF).
Proof.
  refine (mk_Functor
    (OppositeCategory B)
    (@Fiber_BiCCC_SetoidCategory B CB GF)
    (fun I => I)
    (fun I J f => @Pullback_BiCCCFunctor B CB GF J I f)
    _ _ _).
  - intros I J f g Hfg A.
    constructor. exact (@pb_iso B CB GF J I f g Hfg A).
  - intros I A.
    constructor. exact (@pullback_id_iso B CB GF I A).
  - intros I J K f g A.
    constructor. exact (@pullback_comp_iso B CB GF K J I f g A).
Defined.


(** The total category is the Grothendieck construction of [GoodFibration].
    Explicit projection arguments prevent dependent typeclass inference from
    hiding the target objects. *)

Class TotalObj {B : SetoidCategory} {CB : CartesianCategory B} (GF : GoodFibration B) := mk_TotalObj {
  t_base : @obj B;
  t_fib  : @obj (Fiber t_base)
}.
Arguments t_base {_ _ _} _.
Arguments t_fib {_ _ _} _.

Class TotalHom {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} (X Y : TotalObj GF) := mk_TotalHom {
  h_base : hom (t_base X) (t_base Y);
  h_fib  : hom (t_fib X) (@fobj _ _ (Pullback h_base) (t_fib Y))
}.
Arguments h_base {_ _ _ _ _} _.
Arguments h_fib {_ _ _ _ _} _.

Definition TotalHom_equiv {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} 
                          {X Y : TotalObj GF} (M1 M2 : TotalHom X Y) : Prop :=
  exists (H_base : h_base M2 ≅ h_base M1),
    h_fib M1 ≅ 
    compose (@iso_to _ _ _ (pb_iso (h_base M2) (h_base M1) H_base (t_fib Y))) (h_fib M2).

(** In thin fibers, equivalence of total morphisms is determined by their base
    components.  The required transport is supplied by [pb_iso], and the two
    resulting fiber arrows are equivalent by thinness. *)
Lemma global_pi {B : SetoidCategory} {CB : CartesianCategory B}
  {GF : GoodFibration B} (X Y : TotalObj GF) (M1 M2 : TotalHom X Y) :
  h_base M1 ≅ h_base M2 -> TotalHom_equiv M1 M2.
Proof.
  intro Hbase.
  unfold TotalHom_equiv.
  assert (Hback : h_base M2 ≅ h_base M1).
  { symmetry. exact Hbase. }
  exists Hback.
  exact (@thin_unique
    (@Fiber B CB GF (t_base X))
    (@fiber_is_thin B CB GF (t_base X)) _ _ _ _).
Defined.


(** Explicit annotations keep unification from choosing the wrong fiber
    arguments; [global_pi] then reduces category laws to their base maps. *)

Definition total_id {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} 
                    (X : TotalObj GF) : TotalHom X X :=
  @mk_TotalHom B CB GF X X 
    (id (t_base X)) 
    (@iso_from _ _ _ (pullback_id_iso (t_fib X))).

Definition total_comp {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} 
                      {X Y Z : TotalObj GF} 
                      (M2 : TotalHom Y Z) (M1 : TotalHom X Y) : TotalHom X Z :=
  @mk_TotalHom B CB GF X Z 
    (compose (h_base M2) (h_base M1))
    (compose 
       (@iso_from _ _ _ (pullback_comp_iso (h_base M2) (h_base M1) (t_fib Z)))
       (compose 
          (@fmap (Fiber (t_base Y)) (Fiber (t_base X)) (Pullback (h_base M1)) 
                 (t_fib Y) (@fobj _ _ (Pullback (h_base M2)) (t_fib Z)) (h_fib M2))
          (h_fib M1))).

Instance TotalHom_Equivalence {B : SetoidCategory} {CB : CartesianCategory B} 
  {GF : GoodFibration B} {X Y : TotalObj GF}
  : Equivalence (@TotalHom_equiv B CB GF X Y).
Proof.
  split.
  - intros M. apply global_pi. reflexivity.
  - intros M1 M2 H. apply global_pi. destruct H as [Hb _]. exact Hb.
  - intros M1 M2 M3 H1 H2. apply global_pi. 
    destruct H1 as [Hb1 _]. destruct H2 as [Hb2 _]. 
    symmetry in Hb1. symmetry in Hb2. transitivity (h_base M2). all: assumption. 
Defined.

Instance TotalCategory {B : SetoidCategory} {CB : CartesianCategory B} 
  (GF : GoodFibration B) : SetoidCategory.
Proof.
  refine {|
    obj := TotalObj GF;
    hom := @TotalHom B CB GF;
    id := @total_id B CB GF;
    compose := @total_comp B CB GF;
    hom_equiv := @TotalHom_equiv B CB GF;
    hom_equiv_equivalence := @TotalHom_Equivalence B CB GF;
    
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


(** A base with the terminal sort and a distinct individual sort [S]. *)
Class TwoSortCategory (B : SetoidCategory) {CB : CartesianCategory B} := mk_TwoSortCategory {
  S : @obj B;
  S_is_not_Terminal : S <> terminal 
}.
Arguments S {B CB}.

Definition bang (B : SetoidCategory) {CB : CartesianCategory B} {TSC : TwoSortCategory B} : hom (@S B CB TSC) terminal :=
  terminal_map.

Lemma pi_iso_cong :
  forall {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B}
         {I A : @obj B} (X Y : @obj (Fiber (@prod B CB I A))),
  X ≅O Y ->
  @right_adj_obj _ _ _ (@pullback_has_right_adjoint B CB GF I A) X ≅O
  @right_adj_obj _ _ _ (@pullback_has_right_adjoint B CB GF I A) Y.
Proof.
  intros B CB GF I A X Y H.
  refine {|
    iso_to := @right_adj_mor _ _ _ (@pullback_has_right_adjoint B CB GF I A) _ _
                (@compose (Fiber (@prod B CB I A)) _ _ _ (@iso_to _ _ _ H) (@epsilon _ _ _ (@pullback_has_right_adjoint B CB GF I A) X));
    iso_from := @right_adj_mor _ _ _ (@pullback_has_right_adjoint B CB GF I A) _ _
                  (@compose (Fiber (@prod B CB I A)) _ _ _ (@iso_from _ _ _ H) (@epsilon _ _ _ (@pullback_has_right_adjoint B CB GF I A) Y))
  |}.
  - apply (fiber_is_thin I).
  - apply (fiber_is_thin I).
Defined.

Lemma sigma_iso_cong :
  forall {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B}
         {I A : @obj B} (X Y : @obj (Fiber (@prod B CB I A))),
  X ≅O Y ->
  @left_adj_obj _ _ _ (@pullback_has_left_adjoint B CB GF I A) X ≅O
  @left_adj_obj _ _ _ (@pullback_has_left_adjoint B CB GF I A) Y.
Proof.
  intros B CB GF I A X Y H.
  refine {|
    iso_to := @left_adj_mor _ _ _ (@pullback_has_left_adjoint B CB GF I A) _ _
                (@compose (Fiber (@prod B CB I A)) _ _ _ (@unit _ _ _ (@pullback_has_left_adjoint B CB GF I A) Y) (@iso_to _ _ _ H));
    iso_from := @left_adj_mor _ _ _ (@pullback_has_left_adjoint B CB GF I A) _ _
                  (@compose (Fiber (@prod B CB I A)) _ _ _ (@unit _ _ _ (@pullback_has_left_adjoint B CB GF I A) X) (@iso_from _ _ _ H))
  |}.
  - apply (fiber_is_thin I).
  - apply (fiber_is_thin I).
Defined.

Lemma sigma_adjoints_unique_pointwise :
  forall {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B}
         {I A : @obj B}
         (RA2 : IsRightAdjoint (Pullback (@prod_fst B CB I A)))
         (X : @obj (Fiber (@prod B CB I A))),
    @left_adj_obj _ _ _ (@pullback_has_left_adjoint B CB GF I A) X ≅O
    @left_adj_obj _ _ _ RA2 X.
Proof.
  intros B CB GF I A RA2 X.
  exact (@left_adjoints_unique_pointwise
           (Fiber I)
           (Fiber (@prod B CB I A))
           (Pullback (@prod_fst B CB I A))
           (@pullback_has_left_adjoint B CB GF I A)
           RA2
           X).
Defined.

Lemma sigma_adjoints_beck_chevalley_transfer :
  forall {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B}
         {I J K : @obj B}
         (f : hom K I)
         (RA_IJ : IsRightAdjoint (Pullback (@prod_fst B CB I J)))
         (RA_KJ : IsRightAdjoint (Pullback (@prod_fst B CB K J)))
         (X : @obj (Fiber (@prod B CB I J))),
    @fobj _ _ (Pullback f)
      (@left_adj_obj _ _ _ RA_IJ X)
    ≅O
    @left_adj_obj _ _ _ RA_KJ
      (@fobj _ _ (Pullback (@prod_map B CB (prod K J) I J
                              (compose f (@prod_fst B CB K J))
                              (@prod_snd B CB K J))) X).
Proof.
  intros B CB GF I J K f RA_IJ RA_KJ X.
  eapply iso_trans.
  - apply functor_iso_cong.
    apply iso_sym.
    apply sigma_adjoints_unique_pointwise.
  - eapply iso_trans.
    + apply beck_chevalley_sigma.
    + apply sigma_adjoints_unique_pointwise.
Defined.
