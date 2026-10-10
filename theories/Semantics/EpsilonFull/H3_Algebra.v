(** The three-element Heyting algebra and its thin category. *)
Require Import Coq.Classes.Morphisms.
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.

Inductive H3 : Type := HBot | HMid | HTop.

Definition H3_le (x y : H3) : Prop :=
  match x, y with
  | HBot, _ => True
  | _, HTop => True
  | HMid, HMid => True
  | _, _ => False
  end.

Lemma H3_le_refl : forall x, H3_le x x.
Proof. destruct x; exact I. Defined.

Lemma H3_le_trans : forall x y z, H3_le y z -> H3_le x y -> H3_le x z.
Proof. destruct x, y, z; simpl; tauto. Defined.

Definition H3_meet (x y : H3) : H3 :=
  match x, y with
  | HBot, _ | _, HBot => HBot
  | HTop, a | a, HTop => a
  | HMid, HMid => HMid
  end.

Definition H3_join (x y : H3) : H3 :=
  match x, y with
  | HTop, _ | _, HTop => HTop
  | HBot, a | a, HBot => a
  | HMid, HMid => HMid
  end.

Definition H3_impl (x y : H3) : H3 :=
  match x, y with
  | HBot, _ => HTop
  | HMid, HBot => HBot
  | HMid, HMid => HTop
  | HMid, HTop => HTop
  | HTop, a => a
  end.

Ltac h3_crush :=
  repeat intro;
  repeat match goal with
  | |- Proper _ _ => red
  | |- respectful _ _ _ _ => red
  | |- RelationClasses.Equivalence _ => split; red
  end;
  repeat intro;
  simpl in *;
  try exact I;
  try constructor;
  repeat match goal with
  | x : H3 |- _ => destruct x
  end;
  simpl in *;
  auto.

Instance H3_Setoid : SetoidCategory.
Proof.
  refine (mk_SetoidCategory H3 H3_le
    H3_le_refl H3_le_trans (fun _ _ _ _ => True) _ _ _ _ _);
  h3_crush.
Defined.

Instance H3_Cartesian : CartesianCategory H3_Setoid.
Proof.
  refine (mk_CartesianCategory H3_Setoid
    HTop (fun _ => _) _
    H3_meet (fun _ _ _ _ _ => _) (fun _ _ => _) (fun _ _ => _)
    _ _ _ _);
  h3_crush.
  Unshelve. all: h3_crush.
Defined.

Instance H3_Closed : CartesianClosedCategory H3_Setoid.
Proof.
  refine (mk_CartesianClosedCategory H3_Setoid H3_Cartesian
    (fun a b => H3_impl b a) _ _ _ _ _).
  Unshelve. all: h3_crush.
Defined.

Instance H3_BiClosed : BiCartesianClosedCategory H3_Closed.
Proof.
  refine (mk_BiCartesianClosedCategory H3_Setoid H3_Cartesian H3_Closed
    HBot _ _ H3_join _ _ _ _ _ _ _).
  Unshelve. all: h3_crush.
Defined.

Instance H3_IdentityFunctor : Functor H3_Setoid H3_Setoid.
Proof.
  refine (mk_Functor H3_Setoid H3_Setoid (fun x => x) _ _ _ _).
  Unshelve. all: h3_crush.
Defined.

Instance H3_AdjointL : IsLeftAdjoint H3_IdentityFunctor.
Proof.
  refine (mk_IsLeftAdjoint _ _ _ (fun x => x) _ _ _ _ _).
  Unshelve. all: h3_crush.
Defined.

Instance H3_AdjointR : IsRightAdjoint H3_IdentityFunctor.
Proof.
  refine (mk_IsRightAdjoint _ _ _ (fun x => x) _ _ _ _ _).
  Unshelve. all: h3_crush.
Defined.
