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

(** A left-adjoint structure determines its right-adjoint functor. *)
Definition RightAdjointFunctor {C D : SetoidCategory} (F : Functor D C) (LA : IsLeftAdjoint F) 
  : Functor C D.
Proof.
  refine (mk_Functor C D
    (fun x => @right_adj_obj C D F LA x)
    
    (fun x y f => @right_adj_mor C D F LA _ _ 
       (@compose C 
          (@fobj D C F (@right_adj_obj C D F LA x)) 
          x                                         
          y                                         
          f                                         
          (@epsilon C D F LA x)))
    _ _ _).

  -
    intros x y f g H.
    apply (@right_adj_mor_proper C D F LA).
    apply comp_proper.
    + assumption.
    + reflexivity.

  -
    intros x.
    rewrite <- (@lambek_2 C D F LA _ _ (@id D (@right_adj_obj C D F LA x))).
    apply (@right_adj_mor_proper C D F LA).
    rewrite (id_left).
    rewrite (@fmap_id D C F).
    rewrite (id_right).
    reflexivity.

  -
    intros x y z f g.
    
    rewrite <- (@lambek_2 C D F LA _ _ 
       (@compose D (@right_adj_obj C D F LA x) (@right_adj_obj C D F LA y) (@right_adj_obj C D F LA z)
          (@right_adj_mor C D F LA _ _ (@compose C _ _ _ g (@epsilon C D F LA y)))
          (@right_adj_mor C D F LA _ _ (@compose C _ _ _ f (@epsilon C D F LA x))))).

    apply (@right_adj_mor_proper C D F LA).
    
    rewrite (@fmap_comp D C F).
    
    rewrite (comp_assoc). 
    
    rewrite (@lambek_1 C D F LA _ _ (@compose C _ _ _ g (@epsilon C D F LA y))). 
    
    rewrite <- (comp_assoc).
    
    rewrite <- (comp_assoc).
    
    apply comp_proper.
    
    +
      reflexivity.
      
    +
      symmetry.
      apply (@lambek_1 C D F LA).
Defined.

(** A right-adjoint structure determines its left-adjoint functor. *)
Definition LeftAdjointFunctor {C D : SetoidCategory} (G : Functor C D) (RA : IsRightAdjoint G)
  : Functor D C.
Proof.
  refine (mk_Functor D C
    (fun x => @left_adj_obj C D G RA x)
    
    (fun x y f => @left_adj_mor C D G RA _ _
       (@compose D x y (@fobj C D G (@left_adj_obj C D G RA y))
          (@unit C D G RA y)
          f))
    _ _ _).

  -
    intros x y f g H.
    apply (@left_adj_mor_proper C D G RA).
    apply comp_proper.
    + reflexivity.
    + assumption.

  -
    intros x.
    rewrite (id_right). 
    rewrite <- (@lambek_2_dual C D G RA _ _ (@id C (@left_adj_obj C D G RA x))).
    apply (@left_adj_mor_proper C D G RA).
    rewrite (@fmap_id C D G).
    rewrite (id_left).
    reflexivity.

  -
    intros x y z f g.
    
    rewrite <- (@lambek_2_dual C D G RA _ _
       (@compose C (@left_adj_obj C D G RA x) (@left_adj_obj C D G RA y) (@left_adj_obj C D G RA z)
          (@left_adj_mor C D G RA _ _ (@compose D _ _ _ (@unit C D G RA z) g))
          (@left_adj_mor C D G RA _ _ (@compose D _ _ _ (@unit C D G RA y) f)))).

    apply (@left_adj_mor_proper C D G RA).
    
    rewrite (@fmap_comp C D G).
    
    rewrite <- (comp_assoc).
    
    rewrite (@lambek_1_dual C D G RA). 
    
    rewrite (comp_assoc). 
    
    rewrite (comp_assoc).
    
    apply comp_proper.
    
    +
      symmetry.
      apply (@lambek_1_dual C D G RA).
      
    +
      reflexivity.
Defined.

Lemma left_adjoints_unique_pointwise
  {C D : SetoidCategory}
  (G : Functor C D)
  (RA1 RA2 : IsRightAdjoint G) :
  forall (Y : @obj D),
    @left_adj_obj C D G RA1 Y ≅O
    @left_adj_obj C D G RA2 Y.
Proof.
  intro Y.
  refine {|
    iso_to := @left_adj_mor C D G RA1 Y (@left_adj_obj C D G RA2 Y)
                (@unit C D G RA2 Y);
    iso_from := @left_adj_mor C D G RA2 Y (@left_adj_obj C D G RA1 Y)
                  (@unit C D G RA1 Y)
  |}.
  - eapply (@RelationClasses.Equivalence_Transitive
              _ _
              (@hom_equiv_equivalence C
                 (@left_adj_obj C D G RA2 Y)
                 (@left_adj_obj C D G RA2 Y)))
      with (y := @left_adj_mor C D G RA2 Y (@left_adj_obj C D G RA2 Y)
                  (@compose D Y
                     (@fobj C D G (@left_adj_obj C D G RA2 Y))
                     (@fobj C D G (@left_adj_obj C D G RA2 Y))
                     (@fmap C D G
                        (@left_adj_obj C D G RA2 Y)
                        (@left_adj_obj C D G RA2 Y)
                        (@compose C
                           (@left_adj_obj C D G RA2 Y)
                           (@left_adj_obj C D G RA1 Y)
                           (@left_adj_obj C D G RA2 Y)
                           (@left_adj_mor C D G RA1 Y (@left_adj_obj C D G RA2 Y)
                              (@unit C D G RA2 Y))
                           (@left_adj_mor C D G RA2 Y (@left_adj_obj C D G RA1 Y)
                              (@unit C D G RA1 Y))))
                     (@unit C D G RA2 Y))).
    + eapply (@RelationClasses.Equivalence_Symmetric
                _ _
                (@hom_equiv_equivalence C
                   (@left_adj_obj C D G RA2 Y)
                   (@left_adj_obj C D G RA2 Y))).
      apply (@lambek_2_dual C D G RA2).
    + eapply (@RelationClasses.Equivalence_Transitive
                _ _
                (@hom_equiv_equivalence C
                   (@left_adj_obj C D G RA2 Y)
                   (@left_adj_obj C D G RA2 Y)))
        with (y := @left_adj_mor C D G RA2 Y (@left_adj_obj C D G RA2 Y)
                    (@unit C D G RA2 Y)).
      * apply (@left_adj_mor_proper C D G RA2).
        rewrite (@fmap_comp C D G).
        rewrite <- (comp_assoc).
        rewrite (@lambek_1_dual C D G RA2).
        apply (@lambek_1_dual C D G RA1).
      * rewrite <- (@lambek_2_dual C D G RA2 Y
                     (@left_adj_obj C D G RA2 Y)
                     (@id C (@left_adj_obj C D G RA2 Y))).
        apply (@left_adj_mor_proper C D G RA2).
        rewrite (@fmap_id C D G).
        rewrite (id_left).
        reflexivity.
  - eapply (@RelationClasses.Equivalence_Transitive
              _ _
              (@hom_equiv_equivalence C
                 (@left_adj_obj C D G RA1 Y)
                 (@left_adj_obj C D G RA1 Y)))
      with (y := @left_adj_mor C D G RA1 Y (@left_adj_obj C D G RA1 Y)
                  (@compose D Y
                     (@fobj C D G (@left_adj_obj C D G RA1 Y))
                     (@fobj C D G (@left_adj_obj C D G RA1 Y))
                     (@fmap C D G
                        (@left_adj_obj C D G RA1 Y)
                        (@left_adj_obj C D G RA1 Y)
                        (@compose C
                           (@left_adj_obj C D G RA1 Y)
                           (@left_adj_obj C D G RA2 Y)
                           (@left_adj_obj C D G RA1 Y)
                           (@left_adj_mor C D G RA2 Y (@left_adj_obj C D G RA1 Y)
                              (@unit C D G RA1 Y))
                           (@left_adj_mor C D G RA1 Y (@left_adj_obj C D G RA2 Y)
                              (@unit C D G RA2 Y))))
                     (@unit C D G RA1 Y))).
    + eapply (@RelationClasses.Equivalence_Symmetric
                _ _
                (@hom_equiv_equivalence C
                   (@left_adj_obj C D G RA1 Y)
                   (@left_adj_obj C D G RA1 Y))).
      apply (@lambek_2_dual C D G RA1).
    + eapply (@RelationClasses.Equivalence_Transitive
                _ _
                (@hom_equiv_equivalence C
                   (@left_adj_obj C D G RA1 Y)
                   (@left_adj_obj C D G RA1 Y)))
        with (y := @left_adj_mor C D G RA1 Y (@left_adj_obj C D G RA1 Y)
                    (@unit C D G RA1 Y)).
      * apply (@left_adj_mor_proper C D G RA1).
        rewrite (@fmap_comp C D G).
        rewrite <- (comp_assoc).
        rewrite (@lambek_1_dual C D G RA1).
        apply (@lambek_1_dual C D G RA2).
      * rewrite <- (@lambek_2_dual C D G RA1 Y
                     (@left_adj_obj C D G RA1 Y)
                     (@id C (@left_adj_obj C D G RA1 Y))).
        apply (@left_adj_mor_proper C D G RA1).
        rewrite (@fmap_id C D G).
        rewrite (id_left).
        reflexivity.
Defined.
