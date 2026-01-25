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
Proof.
  refine (mk_Functor C D
    (* Object: X |-> G(X) *)
    (fun x => @right_adj_obj C D F LA x)
    
    (* Morphism: f |-> right_adj_mor (f o epsilon) *)
    (fun x y f => @right_adj_mor C D F LA _ _ 
       (@compose C 
          (@fobj D C F (@right_adj_obj C D F LA x)) 
          x                                         
          y                                         
          f                                         
          (@epsilon C D F LA x)))
    _ _ _).

  - (* Proper *)
    intros x y f g H.
    apply (@right_adj_mor_proper C D F LA).
    apply comp_proper.
    + assumption.
    + reflexivity.

  - (* Identity *)
    intros x.
    rewrite <- (@lambek_2 C D F LA _ _ (@id D (@right_adj_obj C D F LA x))).
    apply (@right_adj_mor_proper C D F LA).
    rewrite (id_left).
    rewrite (@fmap_id D C F).
    rewrite (id_right).
    reflexivity.

  - (* Composition *)
    intros x y z f g.
    
    (* 1. under right_adj_mor *)
    rewrite <- (@lambek_2 C D F LA _ _ 
       (@compose D (@right_adj_obj C D F LA x) (@right_adj_obj C D F LA y) (@right_adj_obj C D F LA z)
          (@right_adj_mor C D F LA _ _ (@compose C _ _ _ g (@epsilon C D F LA y)))
          (@right_adj_mor C D F LA _ _ (@compose C _ _ _ f (@epsilon C D F LA x))))).

    apply (@right_adj_mor_proper C D F LA).
    
    (* 2. F(Gg o Gf) ~ F(Gg) o F(Gf) *)
    rewrite (@fmap_comp D C F).
    
    (* 3.  epsilon o (FGg o FGf) ~ (epsilon o FGg) o FGf *)
    rewrite (comp_assoc). 
    
    (* 4. Lambek_1: (epsilon o FGg) ~ g o epsilon *)
    rewrite (@lambek_1 C D F LA _ _ (@compose C _ _ _ g (@epsilon C D F LA y))). 
    
    (* 5. Assoc g o (epsilon o F...) *)
    rewrite <- (comp_assoc).
    
    (* 6. LHS: (g o f) o epsilon --> g o (f o epsilon) *)
    rewrite <- (comp_assoc).
    
    (* 7. Congruence *)
    apply comp_proper.
    
    + (* g ~ g *)
      reflexivity.
      
    + (* f o epsilon ~ epsilon o F(...) *)
      symmetry.
      apply (@lambek_1 C D F LA).
Defined.

(* If RA (with G : C -> D) is a right adjoint structure, then it is constructed a functor F : D -> C *)
Definition LeftAdjointFunctor {C D : SetoidCategory} (G : Functor C D) (RA : IsRightAdjoint G)
  : Functor D C.
Proof.
  refine (mk_Functor D C
    (* Object: X |-> F(X) *)
    (fun x => @left_adj_obj C D G RA x)
    
    (* Morphism: f |-> left_adj_mor (unit o f) *)
    (fun x y f => @left_adj_mor C D G RA _ _
       (@compose D x y (@fobj C D G (@left_adj_obj C D G RA y))
          (@unit C D G RA y)
          f))
    _ _ _).

  - (* Proper *)
    intros x y f g H.
    apply (@left_adj_mor_proper C D G RA).
    apply comp_proper.
    + reflexivity.
    + assumption.

  - (* Identity *)
    intros x.
    rewrite (id_right). 
    rewrite <- (@lambek_2_dual C D G RA _ _ (@id C (@left_adj_obj C D G RA x))).
    apply (@left_adj_mor_proper C D G RA).
    rewrite (@fmap_id C D G).
    rewrite (id_left).
    reflexivity.

  - (* Composition *)
    intros x y z f g.
    
    (* Right side yanking *)
    rewrite <- (@lambek_2_dual C D G RA _ _
       (@compose C (@left_adj_obj C D G RA x) (@left_adj_obj C D G RA y) (@left_adj_obj C D G RA z)
          (@left_adj_mor C D G RA _ _ (@compose D _ _ _ (@unit C D G RA z) g))
          (@left_adj_mor C D G RA _ _ (@compose D _ _ _ (@unit C D G RA y) f)))).

    apply (@left_adj_mor_proper C D G RA).
    
    (* G under map *)
    rewrite (@fmap_comp C D G).
    
    (* Assoc: G(..) o (unit o f) *)
    rewrite <- (comp_assoc).
    
    (* Lambek_1_dual: G(F f) o unit ~ unit o f *)
    rewrite (@lambek_1_dual C D G RA). 
    
    (* Assoc: (G(F g) o unit) o f *)
    rewrite (comp_assoc). 
    
    (* Assoc: (unit o g) o f *)
    rewrite (comp_assoc).
    
    (* Congruence *)
    apply comp_proper.
    
    + (* 1. unit o g ~ G(F g) o unit *)
      symmetry.
      apply (@lambek_1_dual C D G RA).
      
    + (* 2. f ~ f *)
      reflexivity.
Defined.