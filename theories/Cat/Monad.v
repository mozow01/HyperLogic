Require Import Coq.Classes.Morphisms.

Require Import Core.
Require Import Functor.
Require Import Adjoint.

(** Monads and comonads on setoid categories. *)

Class Monad {C : SetoidCategory} (M : Functor C C) := mk_monad {
  return_op : forall {A}, @hom C A (@fobj C C M A);
  join_op : forall {A}, @hom C (@fobj C C M (@fobj C C M A)) (@fobj C C M A);

  monad_law_left_unit : forall {A},
    @compose C (@fobj C C M A) (@fobj C C M (@fobj C C M A)) (@fobj C C M A)
      (@join_op A) 
      (@fmap C C M A (@fobj C C M A) (@return_op A)) 
    ≅ @id C (@fobj C C M A);

  monad_law_right_unit : forall {A},
    @compose C (@fobj C C M A) (@fobj C C M (@fobj C C M A)) (@fobj C C M A)
      (@join_op A) 
      (@return_op (@fobj C C M A)) 
    ≅ @id C (@fobj C C M A);

  monad_law_assoc : forall {A},
    @compose C (@fobj C C M (@fobj C C M (@fobj C C M A))) (@fobj C C M (@fobj C C M A)) (@fobj C C M A)
      (@join_op A) 
      (@fmap C C M _ _ (@join_op A)) 
    ≅ 
    @compose C (@fobj C C M (@fobj C C M (@fobj C C M A))) (@fobj C C M (@fobj C C M A)) (@fobj C C M A)
      (@join_op A)
      (@join_op (@fobj C C M A))
}.

Class Comonad {C : SetoidCategory} (W : Functor C C) := mk_comonad {
  extract : forall {A}, @hom C (@fobj C C W A) A;
  duplicate : forall {A}, @hom C (@fobj C C W A) (@fobj C C W (@fobj C C W A));

  comonad_law_left_unit : forall {A},
    @compose C (@fobj C C W A) (@fobj C C W (@fobj C C W A)) (@fobj C C W A)
      (@fmap C C W _ _ (@extract A)) 
      (@duplicate A) 
    ≅ @id C (@fobj C C W A);

  comonad_law_right_unit : forall {A},
    @compose C (@fobj C C W A) (@fobj C C W (@fobj C C W A)) (@fobj C C W A)
      (@extract (@fobj C C W A)) 
      (@duplicate A) 
    ≅ @id C (@fobj C C W A);

  comonad_law_assoc : forall {A},
    @compose C (@fobj C C W A) (@fobj C C W (@fobj C C W A)) (@fobj C C W (@fobj C C W (@fobj C C W A)))
      (@fmap C C W _ _ (@duplicate A)) 
      (@duplicate A) 
    ≅ 
    @compose C (@fobj C C W A) (@fobj C C W (@fobj C C W A)) (@fobj C C W (@fobj C C W (@fobj C C W A)))
      (@duplicate (@fobj C C W A)) 
      (@duplicate A)
}.

(** Bind and extend presentations. *)

Class Monad_Bind_Style {Cat : SetoidCategory} (M : Functor Cat Cat) := mk_Monad_Bind_Style {
  return_b : forall {A}, @hom Cat A (@fobj Cat Cat M A);
  bind_b : forall {A B}, (@hom Cat A (@fobj Cat Cat M B)) -> (@hom Cat (@fobj Cat Cat M A) (@fobj Cat Cat M B));
  
  bind_law1 : forall {A B} (f : @hom Cat A (@fobj Cat Cat M B)), 
    (@compose Cat A (@fobj Cat Cat M A) (@fobj Cat Cat M B) (bind_b f) return_b) ≅ f;
    
  bind_law2 : forall {A}, bind_b (@return_b A) ≅ @id Cat (@fobj Cat Cat M A);
  
  bind_law3 : forall {A B C} (f : @hom Cat A (@fobj Cat Cat M B)) (g : @hom Cat B (@fobj Cat Cat M C)),
    @compose Cat (@fobj Cat Cat M A) (@fobj Cat Cat M B) (@fobj Cat Cat M C) (bind_b g) (bind_b f) 
    ≅ bind_b (@compose Cat A (@fobj Cat Cat M B) (@fobj Cat Cat M C) (bind_b g) f)
}.

Class CoMonad_Extend_Style {Cat : SetoidCategory} (W : Functor Cat Cat) := mk_CoMonad_Extend_Style {
  extract_b : forall {A}, @hom Cat (@fobj Cat Cat W A) A;
  extend_b : forall {A B}, (@hom Cat (@fobj Cat Cat W B) A) -> (@hom Cat (@fobj Cat Cat W B) (@fobj Cat Cat W A));
  
  extend_law1: forall {A B} (f : @hom Cat (@fobj Cat Cat W B) A), 
    (@compose Cat (@fobj Cat Cat W B) (@fobj Cat Cat W A) A extract_b (extend_b f)) ≅ f;
    
  extend_law2: forall {A}, extend_b (@extract_b A) ≅ @id Cat (@fobj Cat Cat W A);
  
  extend_law3: forall {A B C} (f : @hom Cat (@fobj Cat Cat W C) B) (g : @hom Cat (@fobj Cat Cat W B) A),
    @compose Cat (@fobj Cat Cat W C) (@fobj Cat Cat W B) (@fobj Cat Cat W A) (extend_b g) (extend_b f) 
    ≅ extend_b (@compose Cat (@fobj Cat Cat W C) (@fobj Cat Cat W B) A g (extend_b f))
}.

(** Conversions between the two presentations. *)

Definition bind_from_join {Cat : SetoidCategory} {M : Functor Cat Cat} {MJ : Monad M} {A B}
  (f : @hom Cat A (@fobj Cat Cat M B)) : @hom Cat (@fobj Cat Cat M A) (@fobj Cat Cat M B) :=
  @compose Cat (@fobj Cat Cat M A) (@fobj Cat Cat M (@fobj Cat Cat M B)) (@fobj Cat Cat M B)
    (@join_op Cat M MJ B) 
    (@fmap Cat Cat M A (@fobj Cat Cat M B) f).

Definition join_from_bind {Cat : SetoidCategory} {M : Functor Cat Cat}  {MB : Monad_Bind_Style M} {A}
  : @hom Cat (@fobj Cat Cat M (@fobj Cat Cat M A)) (@fobj Cat Cat M A) :=
  @bind_b Cat M MB (@fobj Cat Cat M A) A (@id Cat (@fobj Cat Cat M A)).


(** Every adjunction [F ⊣ G] induces a monad [G ∘ F]. *)
Instance AdjFuncMonad (C D : SetoidCategory) (G : Functor C D) (RA : IsRightAdjoint G): 
  Monad_Bind_Style (ComposeFunctors (C:=D) (D:=C) (E:=D) G (LeftAdjointFunctor G RA)).
Proof.
  (* Explicit types keep the adjoint functor's direction unambiguous. *)
  set (F := @LeftAdjointFunctor C D G RA).
  
  apply mk_Monad_Bind_Style with
  (return_b := fun (A : @obj D) => @unit C D G RA A)
  (bind_b := fun (A B : @obj D) (f : @hom D A (@fobj D D (ComposeFunctors G F) B)) =>
     @fmap C D G (@fobj D C F A) (@fobj D C F B) (@left_adj_mor C D G RA A (@fobj D C F B) f)).
  
  - intros A B f.
    simpl.
    apply (@lambek_1_dual C D G RA).
    
  - intros A.
    simpl.
    assert (H: @left_adj_mor C D G RA A (@fobj D C F A) (@unit C D G RA A) ≅ @id C (@fobj D C F A)).
    {
       rewrite <- (@lambek_2_dual C D G RA A (@fobj D C F A) (@id C (@fobj D C F A))).
       apply (@left_adj_mor_proper C D G RA).
       simpl. rewrite fmap_id. rewrite id_left. reflexivity.
    }
    transitivity (@fmap C D G _ _ (@id C (@fobj D C F A))).
    { 
      apply (@fmap_proper C D G).
      exact H. 
    }

    apply fmap_id.
    
  - intros X Y Z f g.
    simpl.
    rewrite <- fmap_comp.
    apply fmap_proper.
   transitivity (@left_adj_mor C D G RA X (@fobj D C F Z)
       (@compose D X (@fobj C D G (@fobj D C F X)) (@fobj C D G (@fobj D C F Z))
          (@fmap C D G (@fobj D C F X) (@fobj D C F Z)
             (@compose C (@fobj D C F X) (@fobj D C F Y) (@fobj D C F Z)
                (@left_adj_mor C D G RA Y (@fobj D C F Z) g)
                (@left_adj_mor C D G RA X (@fobj D C F Y) f)))
          (@unit C D G RA X))).
    {
      rewrite <- (@lambek_2_dual C D G RA X (@fobj D C F Z)).
      reflexivity.
    }

    apply (@left_adj_mor_proper C D G RA).

    rewrite fmap_comp.

    rewrite <- comp_assoc.

    apply comp_proper.
    + reflexivity. 
    +
      apply (@lambek_1_dual C D G RA).
Defined.


(** Every adjunction [F ⊣ G] induces a comonad [F ∘ G]. *)
Instance AdjFuncCoMonad (C D : SetoidCategory) (F : Functor D C) (LA : IsLeftAdjoint F): 
  CoMonad_Extend_Style (ComposeFunctors (C:=C) (D:=D) (E:=C) F (RightAdjointFunctor F LA)).
Proof.
  (* Explicit types keep the adjoint functor's direction unambiguous. *)
  set (G := @RightAdjointFunctor C D F LA).

  apply mk_CoMonad_Extend_Style with
  (extract_b := fun (A : @obj C) => @epsilon C D F LA A)
  (extend_b := fun (A B : @obj C) (f : @hom C (@fobj C C (ComposeFunctors F G) B) A) =>
     @fmap D C F (@right_adj_obj C D F LA B) (@right_adj_obj C D F LA A) 
        (@right_adj_mor C D F LA (@right_adj_obj C D F LA B) A f)).

  - intros A B f.
    simpl.
    apply (@lambek_1 C D F LA).

  - intros A.
    simpl.
    assert (H: @right_adj_mor C D F LA (@right_adj_obj C D F LA A) A 
               (@epsilon C D F LA A) ≅ @id D (@right_adj_obj C D F LA A)).
    {
      rewrite <- (@lambek_2 C D F LA (@right_adj_obj C D F LA A) A (@id D _)).
      apply (@right_adj_mor_proper C D F LA).
      simpl. rewrite fmap_id. rewrite id_right. reflexivity.
    }
    
    transitivity (@fmap D C F _ _ (@id D (@right_adj_obj C D F LA A))).
    { apply (@fmap_proper D C F). exact H. }

    apply fmap_id.

  - intros X Y Z f g.
    simpl.
    
    rewrite <- fmap_comp.
    apply fmap_proper.


    transitivity (@right_adj_mor C D F LA (@right_adj_obj C D F LA Z) X
       (@compose C (@fobj D C F (@right_adj_obj C D F LA Z)) (@fobj D C F (@right_adj_obj C D F LA X)) X
          (@epsilon C D F LA X)
          (@fmap D C F (@right_adj_obj C D F LA Z) (@right_adj_obj C D F LA X)
             (@compose D (@right_adj_obj C D F LA Z) (@right_adj_obj C D F LA Y) (@right_adj_obj C D F LA X)
                (@right_adj_mor C D F LA (@right_adj_obj C D F LA Y) X g)
                (@right_adj_mor C D F LA (@right_adj_obj C D F LA Z) Y f)
             )))).
    {
       rewrite <- (@lambek_2 C D F LA (@right_adj_obj C D F LA Z) X) at 1.
       reflexivity.
    }

    apply (@right_adj_mor_proper C D F LA).

    rewrite fmap_comp.
    rewrite comp_assoc.
    
    apply comp_proper.
    +
      apply (@lambek_1 C D F LA).
    + reflexivity.
Defined.
