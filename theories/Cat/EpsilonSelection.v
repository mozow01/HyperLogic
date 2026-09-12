(* Syntax-independent semantic epsilon selection in a good fibration. *)

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import HyperLogic.Cat.Fibration.

Section EpsilonSelection.

Context {B : SetoidCategory}.
Context {CB : CartesianCategory B}.
Context {GF : GoodFibration B}.

Definition epsilon_section
  (X A : @obj B) (e : @hom B X A) : @hom B X (@prod B CB X A) :=
  @prod_map B CB X X A (@id B X) e.

Definition EpsilonSelection
  (X A : @obj B)
  (Q : @obj (Fiber (@prod B CB X A)))
  (e : @hom B X A) : Type :=
  @Iso (Fiber X)
    (@left_adj_obj _ _ _ (@pullback_has_left_adjoint B CB GF X A) Q)
    (@fobj _ _ (Pullback (epsilon_section X A e)) Q).

(* This is propositional truncation by an inductive Prop: it cannot be
   eliminated to manufacture a chosen witness in Type. *)
Inductive EpsilonSelectionExists
  (X A : @obj B)
  (Q : @obj (Fiber (@prod B CB X A))) : Prop :=
| epsilon_selection_exists : forall e : @hom B X A,
    EpsilonSelection X A Q e ->
    EpsilonSelectionExists X A Q.

Record ChosenEpsilonSelection
  (X A : @obj B)
  (Q : @obj (Fiber (@prod B CB X A))) : Type := {
  chosen_epsilon_morphism : @hom B X A;
  chosen_epsilon_is_selection :
    EpsilonSelection X A Q chosen_epsilon_morphism
}.

Definition chosen_epsilon_selection_exists
  (X A : @obj B)
  (Q : @obj (Fiber (@prod B CB X A)))
  (S : ChosenEpsilonSelection X A Q) :
  EpsilonSelectionExists X A Q :=
  epsilon_selection_exists X A Q
    (chosen_epsilon_morphism X A Q S)
    (chosen_epsilon_is_selection X A Q S).

(* The hom-set presentation uses the already chosen Sigma adjunction.  It
   contains no naturality or extensionality requirement on epsilon choices. *)
Record EpsilonSelectionAdjunction
  (X A : @obj B)
  (Q : @obj (Fiber (@prod B CB X A)))
  (e : @hom B X A) : Type := {
  epsilon_selection_adjunction_forward :
    forall Theta : @obj (Fiber X),
      @hom (Fiber X)
        (@fobj _ _ (Pullback (epsilon_section X A e)) Q)
        Theta ->
      @hom (Fiber (@prod B CB X A)) Q
        (@fobj _ _ (Pullback (@prod_fst B CB X A)) Theta);

  epsilon_selection_adjunction_backward :
    forall Theta : @obj (Fiber X),
      @hom (Fiber (@prod B CB X A)) Q
        (@fobj _ _ (Pullback (@prod_fst B CB X A)) Theta) ->
      @hom (Fiber X)
        (@fobj _ _ (Pullback (epsilon_section X A e)) Q)
        Theta
}.

Definition epsilon_selection_to_adjunction
  (X A : @obj B)
  (Q : @obj (Fiber (@prod B CB X A)))
  (e : @hom B X A)
  (S : EpsilonSelection X A Q e) :
  EpsilonSelectionAdjunction X A Q e.
Proof.
  constructor.
  - intros Theta h.
    eapply (@compose (Fiber (@prod B CB X A))).
    + eapply (@fmap _ _ (Pullback (@prod_fst B CB X A))).
      eapply (@compose (Fiber X)).
      * exact h.
      * exact (@iso_to _ _ _ S).
    + exact (@unit _ _ _ (@pullback_has_left_adjoint B CB GF X A) Q).
  - intros Theta h.
    eapply (@compose (Fiber X)).
    + exact (@left_adj_mor _ _ _
        (@pullback_has_left_adjoint B CB GF X A) _ _ h).
    + exact (@iso_from _ _ _ S).
Defined.

Definition epsilon_selection_from_adjunction
  (X A : @obj B)
  (Q : @obj (Fiber (@prod B CB X A)))
  (e : @hom B X A)
  (H : EpsilonSelectionAdjunction X A Q e) :
  EpsilonSelection X A Q e.
Proof.
  refine {|
    iso_to := @left_adj_mor _ _ _
      (@pullback_has_left_adjoint B CB GF X A) _ _
      (epsilon_selection_adjunction_forward X A Q e H
        (@fobj _ _ (Pullback (epsilon_section X A e)) Q)
        (@id (Fiber X)
          (@fobj _ _ (Pullback (epsilon_section X A e)) Q)));
    iso_from := epsilon_selection_adjunction_backward X A Q e H
      (@left_adj_obj _ _ _
        (@pullback_has_left_adjoint B CB GF X A) Q)
      (@unit _ _ _ (@pullback_has_left_adjoint B CB GF X A) Q)
  |}.
  - apply (fiber_is_thin X).
  - apply (fiber_is_thin X).
Defined.

Definition epsilon_selection_adjunction_equivalence
  (X A : @obj B)
  (Q : @obj (Fiber (@prod B CB X A)))
  (e : @hom B X A) :
  ((EpsilonSelection X A Q e -> EpsilonSelectionAdjunction X A Q e) *
   (EpsilonSelectionAdjunction X A Q e -> EpsilonSelection X A Q e))%type :=
  (epsilon_selection_to_adjunction X A Q e,
   epsilon_selection_from_adjunction X A Q e).

Inductive EpsilonSelectionAdjunctionExists
  (X A : @obj B)
  (Q : @obj (Fiber (@prod B CB X A))) : Prop :=
| epsilon_selection_adjunction_exists : forall e : @hom B X A,
    EpsilonSelectionAdjunction X A Q e ->
    EpsilonSelectionAdjunctionExists X A Q.

Lemma epsilon_selection_exists_iff_adjunction_exists
  (X A : @obj B)
  (Q : @obj (Fiber (@prod B CB X A))) :
  EpsilonSelectionExists X A Q <->
  EpsilonSelectionAdjunctionExists X A Q.
Proof.
  split.
  - intros H.
    destruct H as [e S].
    constructor 1 with e.
    exact (epsilon_selection_to_adjunction X A Q e S).
  - intros H.
    destruct H as [e AData].
    constructor 1 with e.
    exact (epsilon_selection_from_adjunction X A Q e AData).
Defined.

(* This is the purely propositional reading of the hom-set comparison.  It
   forgets both morphisms and the functions acting on them. *)
Definition EpsilonSelectionAdjunctionInhabited
  (X A : @obj B)
  (Q : @obj (Fiber (@prod B CB X A)))
  (e : @hom B X A) : Prop :=
  forall Theta : @obj (Fiber X),
    (inhabited
      (@hom (Fiber X)
        (@fobj _ _ (Pullback (epsilon_section X A e)) Q)
        Theta)) <->
    (inhabited
      (@hom (Fiber (@prod B CB X A)) Q
        (@fobj _ _ (Pullback (@prod_fst B CB X A)) Theta))).

Lemma epsilon_selection_adjunction_inhabited
  (X A : @obj B)
  (Q : @obj (Fiber (@prod B CB X A)))
  (e : @hom B X A) :
  EpsilonSelectionAdjunction X A Q e ->
  EpsilonSelectionAdjunctionInhabited X A Q e.
Proof.
  intros H Theta.
  split.
  - intros [h].
    constructor.
    exact (epsilon_selection_adjunction_forward X A Q e H Theta h).
  - intros [h].
    constructor.
    exact (epsilon_selection_adjunction_backward X A Q e H Theta h).
Defined.

Inductive EpsilonSelectionAdjunctionInhabitedExists
  (X A : @obj B)
  (Q : @obj (Fiber (@prod B CB X A))) : Prop :=
| epsilon_selection_adjunction_inhabited_exists : forall e : @hom B X A,
    EpsilonSelectionAdjunctionInhabited X A Q e ->
    EpsilonSelectionAdjunctionInhabitedExists X A Q.

(* The reverse implication below remains Prop-valued.  In particular it does
   not unsquash either side into a [ChosenEpsilonSelection]. *)
Lemma epsilon_selection_exists_iff_inhabited_adjunction_exists
  (X A : @obj B)
  (Q : @obj (Fiber (@prod B CB X A))) :
  EpsilonSelectionExists X A Q <->
  EpsilonSelectionAdjunctionInhabitedExists X A Q.
Proof.
  split.
  - intros H.
    destruct H as [e S].
    constructor 1 with e.
    apply epsilon_selection_adjunction_inhabited.
    exact (epsilon_selection_to_adjunction X A Q e S).
  - intros H.
    destruct H as [e Hinh].
    destruct (proj1
      (Hinh (@fobj _ _ (Pullback (epsilon_section X A e)) Q))
      (inhabits (@id (Fiber X)
        (@fobj _ _ (Pullback (epsilon_section X A e)) Q)))) as [h_to].
    destruct (proj2
      (Hinh (@left_adj_obj _ _ _
        (@pullback_has_left_adjoint B CB GF X A) Q))
      (inhabits
        (@unit _ _ _ (@pullback_has_left_adjoint B CB GF X A) Q))) as [h_from].
    constructor 1 with e.
    refine {|
      iso_to := @left_adj_mor _ _ _
        (@pullback_has_left_adjoint B CB GF X A) _ _ h_to;
      iso_from := h_from
    |}.
    + apply (fiber_is_thin X).
    + apply (fiber_is_thin X).
Defined.

End EpsilonSelection.
