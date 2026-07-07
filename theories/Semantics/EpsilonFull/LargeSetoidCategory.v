(* theories/Semantics/EpsilonFull/LargeSetoidCategory.v *)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.

Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_ModelCategory.

Set Universe Polymorphism.

Polymorphic Class LargeSetoidCategory := mk_LargeSetoidCategory {
  lobj : Type;
  lhom : lobj -> lobj -> Type;

  lid : forall x, lhom x x;
  lcompose : forall {x y z}, lhom y z -> lhom x y -> lhom x z;

  lhom_equiv : forall {x y}, lhom x y -> lhom x y -> Prop;
  lhom_equiv_equivalence : forall {x y}, Equivalence (@lhom_equiv x y);

  lcomp_assoc :
    forall x y z w (f : lhom z w) (g : lhom y z) (h : lhom x y),
      lhom_equiv (lcompose f (lcompose g h))
        (lcompose (lcompose f g) h);

  lid_right :
    forall x y (f : lhom x y),
      lhom_equiv (lcompose f (lid x)) f;

  lid_left :
    forall x y (f : lhom x y),
      lhom_equiv (lcompose (lid y) f) f;

  lcomp_proper :
    forall {x y z} (f g : lhom y z) (h i : lhom x y),
      lhom_equiv f g ->
      lhom_equiv h i ->
      lhom_equiv (lcompose f h) (lcompose g i)
}.

Polymorphic Class LargeEndofunctor (C : LargeSetoidCategory) :=
  mk_LargeEndofunctor {
    large_fobj : @lobj C -> @lobj C;
    large_fmap :
      forall {x y : @lobj C},
        @lhom C x y -> @lhom C (large_fobj x) (large_fobj y);

    large_fmap_proper :
      forall x y (f g : @lhom C x y),
        @lhom_equiv C x y f g ->
        @lhom_equiv C (large_fobj x) (large_fobj y)
          (large_fmap f) (large_fmap g);

    large_fmap_id :
      forall x,
        @lhom_equiv C (large_fobj x) (large_fobj x)
          (large_fmap (@lid C x)) (@lid C (large_fobj x));

    large_fmap_comp :
      forall x y z (g : @lhom C y z) (f : @lhom C x y),
        @lhom_equiv C (large_fobj x) (large_fobj z)
          (large_fmap (@lcompose C x y z g f))
          (@lcompose C (large_fobj x) (large_fobj y) (large_fobj z)
            (large_fmap g) (large_fmap f))
  }.

Polymorphic Class LargeIsomorphism
  {C : LargeSetoidCategory} (x y : @lobj C) :=
  mk_LargeIsomorphism {
    large_iso_to : @lhom C x y;
    large_iso_from : @lhom C y x;

    large_iso_from_to :
      @lhom_equiv C x x
        (@lcompose C x y x large_iso_from large_iso_to)
        (@lid C x);

    large_iso_to_from :
      @lhom_equiv C y y
        (@lcompose C y x y large_iso_to large_iso_from)
        (@lid C y)
  }.

Add Parametric Relation
  (C : LargeSetoidCategory) (x y : @lobj C)
  : (@lhom C x y) (@lhom_equiv C x y)
  reflexivity proved by (@Equivalence_Reflexive _ _ (@lhom_equiv_equivalence C x y))
  symmetry proved by (@Equivalence_Symmetric _ _ (@lhom_equiv_equivalence C x y))
  transitivity proved by (@Equivalence_Transitive _ _ (@lhom_equiv_equivalence C x y))
  as large_hom_equiv_rel.

Global Instance lcompose_proper_instance
  {C : LargeSetoidCategory} {x y z : @lobj C}
  : Proper
      (@lhom_equiv C y z ==> @lhom_equiv C x y ==> @lhom_equiv C x z)
      (@lcompose C x y z).
Proof.
  do 2 red.
  intros f g Hfg h i Hhi.
  apply lcomp_proper; assumption.
Defined.

Class LargeInitial {C : LargeSetoidCategory} (I : @lobj C) :=
  mk_LargeInitial {
    large_initial_arrow : forall X, @lhom C I X;
    large_initial_unique :
      forall X (f g : @lhom C I X), @lhom_equiv C I X f g
  }.

Class LargeWeakInitial {C : LargeSetoidCategory} (I : @lobj C) :=
  mk_LargeWeakInitial {
    large_weak_initial_arrow : forall X, @lhom C I X
  }.

Section EpsilonFullLargeSetoidCategory.

Context {Sign Func Pred : Type}.
Context `{HFunc : FunctionSignature Func}.
Context `{HPred : PredicateSignature Pred}.
Context {SM : SkolemMapping Sign Func Pred}.

Instance EpsilonFullModel_LargeSetoidCategory : LargeSetoidCategory.
Proof.
  refine {|
    lobj := @EpsilonFullModel Sign Func Pred HFunc HPred SM;
    lhom := @EpsilonFullModelHom Sign Func Pred HFunc HPred SM;
    lid := @EpsilonFullModel_id Sign Func Pred HFunc HPred SM;
    lcompose := fun M N P G F =>
      @EpsilonFullModel_comp Sign Func Pred HFunc HPred SM M N P G F;
    lhom_equiv := @EpsilonFullModelHom_equiv Sign Func Pred HFunc HPred SM;
    lhom_equiv_equivalence := fun M N =>
      @EpsilonFullModelHom_equiv_equivalence
        Sign Func Pred HFunc HPred SM M N;
    lcomp_assoc := fun M N P Q H G F =>
      @EpsilonFullModel_comp_assoc
        Sign Func Pred HFunc HPred SM M N P Q H G F;
    lid_right := fun M N F =>
      @EpsilonFullModel_id_right
        Sign Func Pred HFunc HPred SM M N F;
    lid_left := fun M N F =>
      @EpsilonFullModel_id_left
        Sign Func Pred HFunc HPred SM M N F;
    lcomp_proper := fun M N P G G' F F' HGG' HFF' =>
      @EpsilonFullModel_comp_proper
        Sign Func Pred HFunc HPred SM M N P G G' F F' HGG' HFF'
  |}.
Defined.

Instance TermModel_LargeWeakInitial
  : @LargeWeakInitial
      EpsilonFullModel_LargeSetoidCategory
      TermModel_EpsilonFullModel.
Proof.
  constructor.
  intro M.
  exact (TermModel_to M).
Defined.

Instance TermModel_LargeInitial
  : @LargeInitial
      EpsilonFullModel_LargeSetoidCategory
      TermModel_EpsilonFullModel.
Proof.
  constructor.
  - intro M.
    exact (TermModel_to M).
  - intros M F G.
    apply TermModel_initial_unique.
Defined.

Definition TermModel_large_initial_unique
  (M : @lobj EpsilonFullModel_LargeSetoidCategory)
  (F G : @lhom EpsilonFullModel_LargeSetoidCategory
           TermModel_EpsilonFullModel M)
  : @lhom_equiv EpsilonFullModel_LargeSetoidCategory
      TermModel_EpsilonFullModel M F G :=
  TermModel_initial_unique M F G.

End EpsilonFullLargeSetoidCategory.
