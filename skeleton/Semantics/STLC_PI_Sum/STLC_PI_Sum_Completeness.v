Require Import List PeanoNat Coq.Classes.Morphisms.
Import ListNotations.

(* --- HyperLogic Modules --- *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.

Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum.
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum_Lemmas.

Require Import HyperLogic.Semantics.STLC_PI_Sum.STLC_PI_Sum_Soundness.

Open Scope stlc_scope_sum.

(* ================================================================= *)
(* 1. CATEGORY CONSTRUCTION (BiSTLC_Category)                        *)
(* ================================================================= *)

Definition obj_stlc_cat := ty.

Definition id_term (A : ty) : tm := tm_lam A (tm_var 0).
Lemma id_typing (A : ty) : ⊢ (id_term A) [:] (A ⊃ A).
Proof. Admitted.
Definition id_stlc (A : ty) : hom_stlc A A := exist _ (id_term A) (id_typing A).

Definition compose_term {x y z : ty} (f : hom_stlc y z) (g : hom_stlc x y) :=
  tm_lam x (tm_app (proj1_sig f) (tm_app (proj1_sig g) (tm_var 0))).
Lemma compose_typing {x y z : ty} (f : hom_stlc y z) (g : hom_stlc x y) :
  ⊢ (compose_term f g) [:] (x ⊃ z).
Proof. Admitted.
Definition compose_stlc {x y z : ty} (f : hom_stlc y z) (g : hom_stlc x y) : hom_stlc x z :=
  exist _ (compose_term f g) (compose_typing f g).

Instance STLC_Category : SetoidCategory.
Proof. Admitted.

Instance STLC_Thin : Thin STLC_Category.
Proof. Admitted.

(* ================================================================= *)
(* 2. CC & CCC CONSTRUCTION                                          *)
(* ================================================================= *)

Definition terminal_term (A : ty) := (tm_lam A tm_unit).
Lemma terminal_typing (A : ty) : ⊢ (terminal_term A) [:] (A ⊃ Ty_Unit).
Proof. Admitted.
Definition terminal_stlc (x : ty) : hom_stlc x Ty_Unit := exist _ (terminal_term x) (terminal_typing x).

Definition prod_map_term (x y z : ty) (f : hom_stlc x y) (g : hom_stlc x z) :=
  tm_lam x (tm_pair (tm_app (proj1_sig f) (tm_var 0)) (tm_app (proj1_sig g) (tm_var 0))).
Lemma prod_map_typing (x y z : ty) (f : hom_stlc x y) (g : hom_stlc x z) :
  ⊢ prod_map_term x y z f g [:] (x ⊃ (Ty_Prod y z)).
Proof. Admitted.
Definition prod_map_stlc {x y z : ty} (f : hom_stlc x y) (g : hom_stlc x z) : hom_stlc x (Ty_Prod y z) :=
  exist _ _ (prod_map_typing x y z f g).

Definition fst_term (x y : ty) := (tm_lam (Ty_Prod x y) (tm_fst (tm_var 0))).
Lemma fst_typing (x y : ty) : ⊢ (fst_term x y) [:] ((Ty_Prod x y) ⊃ x).
Proof. Admitted.
Definition fst_stlc {x y : ty} : hom_stlc (Ty_Prod x y) x := exist _ _ (fst_typing x y).

Definition snd_term (x y : ty) := (tm_lam (Ty_Prod x y) (tm_snd (tm_var 0))).
Lemma snd_typing (x y : ty) : ⊢ (snd_term x y) [:] ((Ty_Prod x y) ⊃ y).
Proof. Admitted.
Definition snd_stlc {x y : ty} : hom_stlc (Ty_Prod x y) y := exist _ _ (snd_typing x y).

(* ÚJ: STLC_CC Instance *)
Instance STLC_CC : CartesianCategory STLC_Category.
Proof. Admitted.

(* Exponentials *)
Definition eval_term (y z : ty) :=
  tm_lam (Ty_Prod (Ty_Arrow z y) z) (tm_app (tm_fst (tm_var 0)) (tm_snd (tm_var 0))).
Lemma eval_typing (y z : ty) : ⊢ eval_term y z [:] (Ty_Prod (Ty_Arrow z y) z ⊃ y).
Proof. Admitted.
Definition eval_stlc {y z : ty} : hom_stlc (Ty_Prod (Ty_Arrow z y) z) y := exist _ _ (eval_typing y z).

Definition curry_term (x y z : ty) (g : hom_stlc (Ty_Prod x y) z) :=
  (tm_lam x (tm_lam y (tm_app (proj1_sig g) (tm_pair (tm_var 1) (tm_var 0))))).
Lemma curry_typing (x y z : ty) (g : hom_stlc (Ty_Prod x y) z) :
  ⊢ curry_term x y z g [:] (x ⊃ (Ty_Arrow y z)).
Proof. Admitted.
Definition curry_stlc {x y z : ty} (g : hom_stlc (Ty_Prod x y) z) : hom_stlc x (Ty_Arrow y z) :=
  exist _ _ (curry_typing x y z g).

(* ÚJ: STLC_CCC Instance (refine-nal) *)
Instance STLC_CCC : CartesianClosedCategory STLC_Category.
Proof. Admitted.

(* ================================================================= *)
(* 3. BiCCC CONSTRUCTION (Extensions for Sum Types)                  *)
(* ================================================================= *)

Definition initial_term (A : ty) := (tm_lam Ty_Void (tm_absurd A (tm_var 0))).
Lemma initial_typing (A : ty) : ⊢ (initial_term A) [:] (Ty_Void ⊃ A).
Proof. Admitted.
Definition initial_stlc (x : ty) : hom_stlc Ty_Void x := exist _ (initial_term x) (initial_typing x).

Definition inl_term (A B : ty) := tm_lam A (tm_inl B (tm_var 0)).
Lemma inl_typing (A B : ty) : ⊢ (inl_term A B) [:] (A ⊃ (Ty_Sum A B)).
Proof. Admitted.
Definition inl_stlc {A B : ty} : hom_stlc A (Ty_Sum A B) := exist _ _ (inl_typing A B).

Definition inr_term (A B : ty) := tm_lam B (tm_inr A (tm_var 0)).
Lemma inr_typing (A B : ty) : ⊢ (inr_term A B) [:] (B ⊃ (Ty_Sum A B)).
Proof. Admitted.
Definition inr_stlc {A B : ty} : hom_stlc B (Ty_Sum A B) := exist _ _ (inr_typing A B).

Definition coprod_map_term (A B C : ty) (f : hom_stlc A C) (g : hom_stlc B C) :=
  tm_lam (Ty_Sum A B)
    (tm_case (tm_var 0)
      (tm_app (proj1_sig f) (tm_var 0))
      (tm_app (proj1_sig g) (tm_var 0))).
Lemma coprod_map_typing (A B C : ty) (f : hom_stlc A C) (g : hom_stlc B C) :
  ⊢ coprod_map_term A B C f g [:] (Ty_Sum A B ⊃ C).
Proof. Admitted.
Definition coprod_map_stlc {A B C : ty} (f : hom_stlc A C) (g : hom_stlc B C) : hom_stlc (Ty_Sum A B) C :=
  exist _ _ (coprod_map_typing A B C f g).

Instance STLC_BiCCC : BiCartesianClosedCategory STLC_CCC.
Proof. Admitted.

(* ================================================================= *)
(* 4. CANONICAL MODEL INSTANCE                                       *)
(* ================================================================= *)

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
Proof. Admitted.

Instance STLC_Model : Model STLC_Category := {
  interp_base := Ty_Atomic
}.

(* Identity Lemmas *)
(* Itt már nem kell átadni az explicit CC, CCC, BCC-t *)
Lemma val_identity : forall A, interp_ty STLC_Category STLC_Model A = A.
Proof. Admitted.

Lemma ctx_identity : forall Gamma, interp_ctx STLC_Category STLC_Model Gamma = make_ctx_ty Gamma.
Proof. Admitted.

(* ================================================================= *)
(* 5. COMPLETENESS THEOREMS                                          *)
(* ================================================================= *)

Theorem Completeness_Equational :
  forall (Gamma : context) (A : ty) (t1 t2 : tm)
         (d1 : derivation Gamma t1 A)
         (d2 : derivation Gamma t2 A),
  (* Hozzáadva: Ct *)
  (forall (C : SetoidCategory) (Ct : CartesianCategory C) (CC : CartesianClosedCategory C) (BCC : BiCartesianClosedCategory CC) (M : Model C),
      interp_derivation d1 ≅ interp_derivation d2) ->
  tm_equiv_rel t1 t2.
Proof. Admitted.

Theorem Completeness : forall Gamma A,
  (* Hozzáadva: Ct, és implicitek törlése a hívásból *)
  (forall (C : SetoidCategory) (Ct : CartesianCategory C) (CC : CartesianClosedCategory C) (BCC : BiCartesianClosedCategory CC) (M : Model C),
      inhabited (hom (interp_ctx C M Gamma) (interp_ty C M A))) ->
  (exists t, (Gamma ⊢ t [:] A)).
Proof. Admitted.