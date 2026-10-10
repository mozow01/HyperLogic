Require Import List PeanoNat Coq.Classes.Morphisms.  
Import ListNotations.

(** Syntactic category and completeness for STLC with products. *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.  
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Logic.STLC_PI.STLC_PI.
Require Import HyperLogic.Logic.STLC_PI.STLC_PI_Lemmas.
Require Import HyperLogic.Semantics.STLC_PI.STLC_PI_Soundness.

Open Scope stlc_scope.


(** Weakening along context concatenation. *)
Lemma weakening_append : forall Gamma Delta t A,
  Gamma ⊢ t [:] A -> (Gamma ++ Delta) ⊢ t [:] A.
Proof.
  assert (H_cons_app : forall (T : Type) (l : list T) (a : T), a :: l = [a] ++ l).
  { simpl; auto. }
  intros Gamma Delta t A H.
  induction H;
  try (rewrite H_cons_app; try rewrite <- app_assoc; try rewrite <- H_cons_app); auto.
  - apply T_Unit.
  - apply T_Var0.
  - apply T_VarS; auto.
  - apply T_Lam; auto.
  - eapply T_App; eassumption.
  - apply T_Pair; auto.
  - eapply T_Fst; eassumption.
  - eapply T_Snd; eassumption.
Defined.


Definition obj_stlc_cat := ty.

Definition id_term (A : ty) : tm := tm_lam A (tm_var 0).
Lemma id_typing (A : ty) : ⊢ (id_term A) [:] (A ⊃ A).
Proof. unfold id_term. apply T_Lam. apply T_Var0. Defined.
Definition id_stlc (A : ty) : hom_stlc A A := exist _ (id_term A) (id_typing A).

Definition compose_term {x y z : ty} (f : hom_stlc y z) (g : hom_stlc x y) :=
  tm_lam x (tm_app (proj1_sig f) (tm_app (proj1_sig g) (tm_var 0))).
Lemma compose_typing {x y z : ty} (f : hom_stlc y z) (g : hom_stlc x y) :
  ⊢ (compose_term f g) [:] (x ⊃ z).
Proof.
  unfold compose_term. apply T_Lam.
  apply T_App with (A:=y).
  - apply weakening_append with (Gamma := nil) (Delta := [x]); exact (proj2_sig f).
  - apply T_App with (A:=x).
    -- apply weakening_append with (Gamma := nil) (Delta := [x]); exact (proj2_sig g).
    -- apply T_Var0.
Defined.
Definition compose_stlc {x y z : ty} (f : hom_stlc y z) (g : hom_stlc x y) : hom_stlc x z :=
  exist _ (compose_term f g) (compose_typing f g).

Instance STLC_Category : SetoidCategory.
Proof.
  apply mk_SetoidCategory with (obj := obj_stlc_cat) (hom := hom_stlc) (hom_equiv := @hom_equiv_stlc)
    (id := id_stlc) (compose := @compose_stlc).
  - intros x y; split.
    + intros f; apply hom_equiv_stlc_refl.
    + intros f g; apply hom_equiv_stlc_sym.
    + intros f g h; eapply hom_equiv_stlc_trans.
  - intros; apply generic_axiom_proof.
  - intros; apply generic_axiom_proof.
  - intros; apply generic_axiom_proof.
  - intros; apply generic_axiom_proof.
Defined.

Instance STLC_Thin : Thin STLC_Category.
Proof. intros x y f g. apply generic_axiom_proof. Defined.



Definition terminal_term (A : ty) := (tm_lam A tm_unit).
Lemma terminal_typing (A : ty) : ⊢ (terminal_term A) [:] (A ⊃ Ty_Unit).
Proof. intros; apply T_Lam; apply T_Unit. Defined.
Definition terminal_stlc (x : ty) : hom_stlc x Ty_Unit := exist _ (terminal_term x) (terminal_typing x).

Definition prod_map_term (x y z : ty) (f : hom_stlc x y) (g : hom_stlc x z) :=
  tm_lam x (tm_pair (tm_app (proj1_sig f) (tm_var 0)) (tm_app (proj1_sig g) (tm_var 0))).
Lemma prod_map_typing (x y z : ty) (f : hom_stlc x y) (g : hom_stlc x z) :
  ⊢ prod_map_term x y z f g [:] (x ⊃ (Ty_Prod y z)).
Proof.
  unfold prod_map_term; apply T_Lam; apply T_Pair.
  - apply T_App with (A:=x).
    + apply weakening_append with (Gamma:=nil) (Delta:=[x]); exact (proj2_sig f).
    + apply T_Var0.
  - apply T_App with (A:=x).
    + apply weakening_append with (Gamma:=nil) (Delta:=[x]); exact (proj2_sig g).
    + apply T_Var0.
Defined.
Definition prod_map_stlc {x y z : ty} (f : hom_stlc x y) (g : hom_stlc x z) : hom_stlc x (Ty_Prod y z) :=
  exist _ _ (prod_map_typing x y z f g).

Definition fst_term (x y : ty) := (tm_lam (Ty_Prod x y) (tm_fst (tm_var 0))).
Lemma fst_typing (x y : ty) : ⊢ (fst_term x y) [:] ((Ty_Prod x y) ⊃ x).
Proof. unfold fst_term; apply T_Lam; eapply T_Fst; apply T_Var0. Defined.
Definition fst_stlc {x y : ty} : hom_stlc (Ty_Prod x y) x := exist _ _ (fst_typing x y).

Definition snd_term (x y : ty) := (tm_lam (Ty_Prod x y) (tm_snd (tm_var 0))).
Lemma snd_typing (x y : ty) : ⊢ (snd_term x y) [:] ((Ty_Prod x y) ⊃ y).
Proof. unfold snd_term; apply T_Lam; eapply T_Snd; apply T_Var0. Defined.
Definition snd_stlc {x y : ty} : hom_stlc (Ty_Prod x y) y := exist _ _ (snd_typing x y).

Instance STLC_CC : CartesianCategory STLC_Category.
Proof.
  apply (Build_Thin_CC _ STLC_Thin
    Ty_Unit (fun x => terminal_stlc x)
    Ty_Prod (@prod_map_stlc) (@fst_stlc) (@snd_stlc)).
Defined.


Definition eval_term (y z : ty) :=
  tm_lam (Ty_Prod (Ty_Arrow z y) z) (tm_app (tm_fst (tm_var 0)) (tm_snd (tm_var 0))).
Lemma eval_typing (y z : ty) : ⊢ eval_term y z [:] (Ty_Prod (Ty_Arrow z y) z ⊃ y).
Proof. unfold eval_term; apply T_Lam; eapply T_App; [eapply T_Fst | eapply T_Snd]; apply T_Var0. Defined.
Definition eval_stlc {y z : ty} : hom_stlc (Ty_Prod (Ty_Arrow z y) z) y := exist _ _ (eval_typing y z).

Definition curry_term (x y z : ty) (g : hom_stlc (Ty_Prod x y) z) :=
  (tm_lam x (tm_lam y (tm_app (proj1_sig g) (tm_pair (tm_var 1) (tm_var 0))))).
Lemma curry_typing (x y z : ty) (g : hom_stlc (Ty_Prod x y) z) :
  ⊢ curry_term x y z g [:] (x ⊃ (Ty_Arrow y z)).
Proof.
  unfold curry_term; apply T_Lam; apply T_Lam.
  apply T_App with (A:= (Ty_Prod x y)).
  - apply weakening_append with (Gamma:=nil) (Delta:=[y; x]); exact (proj2_sig g).
  - apply T_Pair; [apply T_VarS; apply T_Var0 | apply T_Var0].
Defined.
Definition curry_stlc {x y z : ty} (g : hom_stlc (Ty_Prod x y) z) : hom_stlc x (Ty_Arrow y z) :=
  exist _ _ (curry_typing x y z g).

Instance STLC_CCC : CartesianClosedCategory STLC_Category.
Proof.
  (* [refine] exposes the product equality needed to recognize [Ty_Prod]. *)
  refine (Build_Thin_CCC _ STLC_Thin
    (fun z y => Ty_Arrow y z)
    (fun y z => @eval_stlc z y)
    (@curry_stlc)
  ).
Defined.


Fixpoint make_ctx_ty (Gamma : context) : ty :=
  match Gamma with
  | nil => Ty_Unit
  | A :: Gamma' => Ty_Prod (make_ctx_ty Gamma') A
  end.

Fixpoint reify_ctx (Gamma : context) : tm :=
  match Gamma with
  | nil => tm_unit
  | A :: Gamma' => tm_pair (lift 1 0 (reify_ctx Gamma')) (tm_var 0)
  end.

Lemma reify_ctx_typing : forall Gamma,
  Gamma ⊢ reify_ctx Gamma [:] (make_ctx_ty Gamma).
Proof.
  induction Gamma; simpl.
  - apply T_Unit.
  - apply T_Pair.
    + apply weakening; assumption.
    + apply T_Var0.
Defined.

Instance STLC_Model : Model STLC_Category := {
  interp_base := Ty_Atomic
}.


Lemma val_identity : forall A, interp_ty STLC_Category STLC_Model A = A.
Proof. induction A; simpl; auto; try (rewrite IHA1; rewrite IHA2); auto. Defined.

Lemma ctx_identity : forall Gamma, interp_ctx STLC_Category STLC_Model Gamma = make_ctx_ty Gamma.
Proof. induction Gamma; simpl; auto. rewrite IHGamma. rewrite val_identity. auto. Defined.

(** Completeness theorems. *)

Theorem Completeness_Equational :
  forall (Gamma : context) (A : ty) (t1 t2 : tm)
         (d1 : derivation Gamma t1 A)
         (d2 : derivation Gamma t2 A),
  (forall (C : SetoidCategory) (Ct : CartesianCategory C) (CC : CartesianClosedCategory C) (M : Model C),
      interp_derivation d1 ≅ interp_derivation d2) ->
  tm_equiv_rel t1 t2.
Proof.
  intros Gamma A t1 t2 d1 d2 H_valid.
  apply (PI_rule Gamma A).
  - apply (forget_derivation d1).
  - apply (forget_derivation d2).
Defined.

Theorem completeness_terms_equiv :
  forall (Gamma : context) (A : ty) (t1 t2 : tm),
  (exists f, interprets_to (C:=STLC_Category) (M:=STLC_Model) Gamma A t1 f) ->
  (exists g, interprets_to (C:=STLC_Category) (M:=STLC_Model) Gamma A t2 g) ->

  (forall (C : SetoidCategory) (Ct : CartesianCategory C) (CC : CartesianClosedCategory C) (M : Model C)
          (f g : hom (interp_ctx C M Gamma) (interp_ty C M A)),
      interprets_to Gamma A t1 f ->
      interprets_to Gamma A t2 g ->
      f ≅ g) ->
  tm_equiv_rel t1 t2.
Proof.
  intros Gamma A t1 t2 [f_can [d1 _]] [g_can [d2 _]] H_sem_eq.
  apply (PI_rule Gamma A).
  - apply (forget_derivation d1).
  - apply (forget_derivation d2).
Defined.

Theorem Completeness : forall Gamma A,
  (forall (C : SetoidCategory) (Ct : CartesianCategory C) (CC : CartesianClosedCategory C) (M : Model C),
     inhabited (hom (interp_ctx C M Gamma) (interp_ty C M A))) ->
  (exists t, (Gamma ⊢ t [:] A)).
Proof.
  intros Gamma A H_valid.
  assert (K : inhabited (hom (interp_ctx STLC_Category STLC_Model Gamma)
                             (interp_ty STLC_Category STLC_Model A))).
  { apply H_valid. }
  destruct K as [[t_closed H_closed]].
  simpl in H_closed.
  rewrite ctx_identity in H_closed.
  rewrite val_identity in H_closed.
  assert (H_weak : Gamma ⊢ (lift (length Gamma) 0 t_closed) [:] (make_ctx_ty Gamma ⊃ A)).
  { apply weakening_from_nil; exact H_closed. }
  exists (tm_app (lift (length Gamma) 0 t_closed) (reify_ctx Gamma)).
  eapply T_App.
  - exact H_weak.
  - apply reify_ctx_typing.
Defined.