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
Proof. Admitted.

(* Every Adjunction F -| G (where F:D->C is Left Adjoint) induces a Comonad on C.
   W = F o G
*)
Instance AdjFuncCoMonad (C D : SetoidCategory) (F : Functor D C) (LA : IsLeftAdjoint F):
  CoMonad_Extend_Style (ComposeFunctors (C:=C) (D:=D) (E:=C) F (RightAdjointFunctor F LA)).
Proof. Admitted.