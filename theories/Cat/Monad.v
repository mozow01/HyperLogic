Require Import Coq.Classes.Morphisms.

Require Import Core.
Require Import Functor.
Require Import Adjoint.

(** * Monads and Comonads *)

(** ** Definitions *)

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

(** ** Bind/Extend Style definitions *)

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

(** ** Conversions *)

Definition bind_from_join {Cat : SetoidCategory} {M : Functor Cat Cat} {MJ : Monad M} {A B}
  (f : @hom Cat A (@fobj Cat Cat M B)) : @hom Cat (@fobj Cat Cat M A) (@fobj Cat Cat M B) :=
  @compose Cat (@fobj Cat Cat M A) (@fobj Cat Cat M (@fobj Cat Cat M B)) (@fobj Cat Cat M B)
    (@join_op Cat M MJ B) 
    (@fmap Cat Cat M A (@fobj Cat Cat M B) f).

Definition join_from_bind {Cat : SetoidCategory} {M : Functor Cat Cat}  {MB : Monad_Bind_Style M} {A}
  : @hom Cat (@fobj Cat Cat M (@fobj Cat Cat M A)) (@fobj Cat Cat M A) :=
  @bind_b Cat M MB (@fobj Cat Cat M A) A (@id Cat (@fobj Cat Cat M A)).


(** ** Adjunctions generate Monads and Comonads *)

(* Every Adjunction G -| F (where G:C->D is Right Adjoint) induces a Monad on D.
   T = G o F
*)
Instance AdjFuncMonad (C D : SetoidCategory) (G : Functor C D) (RA : IsRightAdjoint G): 
  Monad_Bind_Style (ComposeFunctors (C:=D) (D:=C) (E:=D) G (LeftAdjointFunctor G RA)).
Proof.
  (* Explicitly define F with explicit types to ensure F : D -> C *)
  set (F := @LeftAdjointFunctor C D G RA).
  
  apply mk_Monad_Bind_Style with
  (* 1. Unit (Return) *)
  (return_b := fun (A : @obj D) => @unit C D G RA A)
  (* 2. Bind *)
  (bind_b := fun (A B : @obj D) (f : @hom D A (@fobj D D (ComposeFunctors G F) B)) =>
     (* f : A -> G(F(B)) *)
     (* left_adj_mor f : F(A) -> F(B) *)
     (* G (left_adj_mor f) : G(F(A)) -> G(F(B)) *)
     @fmap C D G (@fobj D C F A) (@fobj D C F B) (@left_adj_mor C D G RA A (@fobj D C F B) f)).
  
  - intros A B f. (* bind_law1 *)
    simpl.
    apply (@lambek_1_dual C D G RA).
    
  - intros A. (* bind_law2 *)
    simpl.
    assert (H: @left_adj_mor C D G RA A (@fobj D C F A) (@unit C D G RA A) ≅ @id C (@fobj D C F A)).
    {
       rewrite <- (@lambek_2_dual C D G RA A (@fobj D C F A) (@id C (@fobj D C F A))).
       apply (@left_adj_mor_proper C D G RA).
       simpl. rewrite fmap_id. rewrite id_left. reflexivity.
    }
    (* Explicitly Step 1: Replace the LHS with fmap(id) using the Proper instance *)
    transitivity (@fmap C D G _ _ (@id C (@fobj D C F A))).
    { 
      apply (@fmap_proper C D G).
      exact H. 
    }

    (* Explicitly Step 2: Simplify fmap(id) to id *)
    apply fmap_id.
    
  - intros X Y Z f g. (* bind_law3 *)
    simpl.
    rewrite <- fmap_comp.
    apply fmap_proper.
    (* 1. Use transitivity to introduce the Lambek form for (L g ∘ L f) *)
    (* We want to show: (L g ∘ L f) ≅ L (G (L g ∘ L f) ∘ unit) *)
   transitivity (@left_adj_mor C D G RA X (@fobj D C F Z)
       (@compose D X (@fobj C D G (@fobj D C F X)) (@fobj C D G (@fobj D C F Z))
          (* Part 1: G (L g ∘ L f) *)
          (@fmap C D G (@fobj D C F X) (@fobj D C F Z)
             (@compose C (@fobj D C F X) (@fobj D C F Y) (@fobj D C F Z)
                (@left_adj_mor C D G RA Y (@fobj D C F Z) g)
                (@left_adj_mor C D G RA X (@fobj D C F Y) f)))
          (* Part 2: unit *)
          (@unit C D G RA X))).
    {
      (* This direction is exactly lambek_2_dual applied to the composition (L g ∘ L f) *)
      rewrite <- (@lambek_2_dual C D G RA X (@fobj D C F Z)).
      reflexivity.
    }

    (* Now peel off the outer L *)
    apply (@left_adj_mor_proper C D G RA).

    (* Distribute G over composition: G (L g ∘ L f) ≅ G (L g) ∘ G (L f) *)
    rewrite fmap_comp.

    (* Re-associate: (G (L g) ∘ G (L f)) ∘ unit ≅ G (L g) ∘ (G (L f) ∘ unit) *)
    rewrite <- comp_assoc.

    (* Focus on the right side: G (L f) ∘ unit *)
    apply comp_proper.
    + reflexivity. 
    + (* Apply lambek_1_dual: G (L f) ∘ unit ≅ f *)
      apply (@lambek_1_dual C D G RA).
Defined.


(* Every Adjunction F -| G (where F:D->C is Left Adjoint) induces a Comonad on D.
   W = F o G
*)
Instance AdjFuncCoMonad (C D : SetoidCategory) (F : Functor D C) (LA : IsLeftAdjoint F): 
  CoMonad_Extend_Style (ComposeFunctors (C:=C) (D:=D) (E:=C) F (RightAdjointFunctor F LA)).
Proof.
  (* Explicitly define G to ensure G : C -> D *)
  set (G := @RightAdjointFunctor C D F LA).

  apply mk_CoMonad_Extend_Style with
  (* 1. Counit (Extract) *)
  (extract_b := fun (A : @obj C) => @epsilon C D F LA A)
  (* 2. Extend *)
  (extend_b := fun (A B : @obj C) (f : @hom C (@fobj C C (ComposeFunctors F G) B) A) =>
     (* f : F(G(B)) -> A *)
     (* Pass G(B) as the domain in D *)
     @fmap D C F (@right_adj_obj C D F LA B) (@right_adj_obj C D F LA A) 
        (@right_adj_mor C D F LA (@right_adj_obj C D F LA B) A f)).

  - intros A B f. (* extend_law1 *)
    simpl.
    apply (@lambek_1 C D F LA).

  - intros A. (* extend_law2 *)
    simpl.
    (* Assert R(epsilon) = id *)
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

  - intros X Y Z f g. (* extend_law3 *)
    simpl.
    
    (* LHS: F(R g) o F(R f) ≅ F(R g o R f) *)
    rewrite <- fmap_comp.
    apply fmap_proper.

    (* Goal: R g o R f ≅ R (g o F(R f)) *)
    (* Composition R g o R f goes from G(Z) -> G(Y) -> G(X) *)

    transitivity (@right_adj_mor C D F LA (@right_adj_obj C D F LA Z) X
       (@compose C (@fobj D C F (@right_adj_obj C D F LA Z)) (@fobj D C F (@right_adj_obj C D F LA X)) X
          (* Part A: epsilon X *)
          (@epsilon C D F LA X)
          (* Part B: F(R g o R f) *)
          (@fmap D C F (@right_adj_obj C D F LA Z) (@right_adj_obj C D F LA X)
             (@compose D (@right_adj_obj C D F LA Z) (@right_adj_obj C D F LA Y) (@right_adj_obj C D F LA X)
                (* FIX 1: Pass G(Y) as domain for g *)
                (@right_adj_mor C D F LA (@right_adj_obj C D F LA Y) X g)
                (* FIX 2: Pass G(Z) as domain for f *)
                (@right_adj_mor C D F LA (@right_adj_obj C D F LA Z) Y f)
             )))).
    {
       (* lambek_2 applied to (R g o R f) *)
       rewrite <- (@lambek_2 C D F LA (@right_adj_obj C D F LA Z) X) at 1.
       reflexivity.
    }

    (* Peel off the outer R *)
    apply (@right_adj_mor_proper C D F LA).

    (* Simplify internal composition: epsilon o F(R g o R f) *)
    rewrite fmap_comp.
    rewrite comp_assoc.
    
    apply comp_proper.
    + (* epsilon o F(R g) = g *)
      apply (@lambek_1 C D F LA).
    + reflexivity.
Defined.