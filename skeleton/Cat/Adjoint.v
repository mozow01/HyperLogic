Require Import List.
Import ListNotations.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.Functor.

Class IsRightAdjoint {C D : SetoidCategory} (G : Functor C D) := mk_IsRightAdjoint {
  left_adj_obj : @obj D -> @obj C;

  unit : forall (Y : @obj D), @hom D Y (@fobj C D G (left_adj_obj Y));

  left_adj_mor : forall {Y : @obj D} {X : @obj C} (g : @hom D Y (@fobj C D G X)),
    @hom C (left_adj_obj Y) X;

  left_adj_mor_proper : forall {Y : @obj D} {X : @obj C},
    Proper (@hom_equiv D Y (@fobj C D G X) ==> @hom_equiv C (left_adj_obj Y) X) left_adj_mor;

  lambek_1_dual : forall {Y : @obj D} {X : @obj C} (g : @hom D Y (@fobj C D G X)),
    @hom_equiv D Y (@fobj C D G X)
      (@compose D Y (@fobj C D G (left_adj_obj Y)) (@fobj C D G X)
         (@fmap C D G (left_adj_obj Y) X (left_adj_mor g))
         (unit Y))
      g;

  lambek_2_dual : forall {Y : @obj D} {X : @obj C} (f : @hom C (left_adj_obj Y) X),
    @hom_equiv C (left_adj_obj Y) X
      (left_adj_mor
        (@compose D Y (@fobj C D G (left_adj_obj Y)) (@fobj C D G X)
           (@fmap C D G (left_adj_obj Y) X f)
           (unit Y)))
      f
}.

Existing Instance left_adj_mor_proper.

Class IsLeftAdjoint {C D : SetoidCategory} (F : Functor D C) := mk_IsLeftAdjoint {
  right_adj_obj : @obj C -> @obj D;

  epsilon : forall (X : @obj C), @hom C (@fobj D C F (right_adj_obj X)) X;

  right_adj_mor : forall {Y : @obj D} {X : @obj C} (f : @hom C (@fobj D C F Y) X),
    @hom D Y (right_adj_obj X);

  right_adj_mor_proper : forall {Y : @obj D} {X : @obj C},
    Proper (@hom_equiv C (@fobj D C F Y) X ==> @hom_equiv D Y (right_adj_obj X)) right_adj_mor;

  lambek_1 : forall {Y : @obj D} {X : @obj C} (f : @hom C (@fobj D C F Y) X),
    @hom_equiv C (@fobj D C F Y) X
      (@compose C (@fobj D C F Y) (@fobj D C F (right_adj_obj X)) X
         (epsilon X)
         (@fmap D C F Y (right_adj_obj X) (right_adj_mor f)))
      f;

  lambek_2 : forall {Y : @obj D} {X : @obj C} (g : @hom D Y (right_adj_obj X)),
    @hom_equiv D Y (right_adj_obj X)
      (right_adj_mor
        (@compose C (@fobj D C F Y) (@fobj D C F (right_adj_obj X)) X
           (epsilon X)
           (@fmap D C F Y (right_adj_obj X) g)))
      g
}.

Existing Instance right_adj_mor_proper.

(* If LA is a left adjoint, then the right component gives rise of a functor *)
Definition RightAdjointFunctor {C D : SetoidCategory} (F : Functor D C) (LA : IsLeftAdjoint F)
  : Functor C D.
Proof. Admitted.

(* If RA (with G : C -> D) is a right adjoint structure, then it is constructed a functor F : D -> C *)
Definition LeftAdjointFunctor {C D : SetoidCategory} (G : Functor C D) (RA : IsRightAdjoint G)
  : Functor D C.
Proof. Admitted.