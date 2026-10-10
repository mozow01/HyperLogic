

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Require Import HyperLogic.Logic.Base.Simple_Ext.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple_Ext.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple_Ext.Hyper_Lemmas.

(** Context reification and structural lifting for the legacy syntax. *)

Fixpoint h_make_ctx_ty {Sign : Type} (G : list (@h_ty Sign)) : @h_ty Sign :=
  match G with
  | nil => Ty_Unit
  | cons A G' => Ty_Prod (@h_make_ctx_ty Sign G') A
  end.

Fixpoint h_lift {Sign : Type} (n : nat) (k : nat) (t : @h_tm Sign) : @h_tm Sign :=
  match t with
  | tm_unit => tm_unit
  | tm_var i => if k <=? i then tm_var (n + i) else tm_var i
  | tm_lam A t' => tm_lam A (h_lift n (S k) t')
  | tm_app t1 t2 => tm_app (h_lift n k t1) (h_lift n k t2)
  | tm_pair t1 t2 => tm_pair (h_lift n k t1) (h_lift n k t2)
  | tm_fst t' => tm_fst (h_lift n k t')
  | tm_snd t' => tm_snd (h_lift n k t')
  | tm_inl B t' => tm_inl B (h_lift n k t')
  | tm_inr A t' => tm_inr A (h_lift n k t')
  | tm_case t t1 t2 => tm_case (h_lift n k t) (h_lift n (S k) t1) (h_lift n (S k) t2)
  | tm_absurd A t' => tm_absurd A (h_lift n k t')
  | tm_all_intro t' => tm_all_intro (h_lift n k t')
  | tm_all_elim t' f => tm_all_elim (h_lift n k t') f
  | tm_ex_intro f t' => tm_ex_intro f (h_lift n k t')
  | tm_ex_elim t1 t2 => tm_ex_elim (h_lift n k t1) (h_lift n (S k) t2)
  end.

Fixpoint h_reify_ctx_offset {Sign : Type} (G : list (@h_ty Sign)) (offset : nat) : @h_tm Sign :=
  match G with
  | nil => tm_unit
  | cons A G' => tm_pair (@h_reify_ctx_offset Sign G' (S offset)) (tm_var offset)
  end.

Definition h_reify_ctx {Sign : Type} (G : list (@h_ty Sign)) : @h_tm Sign :=
  h_reify_ctx_offset G 0.

Fixpoint h_insert_at {Sign : Type} (n : nat) (B : @h_ty Sign) (G : h_context) : h_context :=
  match n, G with
  | 0, _ => B :: G
  | S n', A :: G' => A :: h_insert_at n' B G'
  | S n', nil => nil
  end.


Lemma h_var_typing : forall {Sign : Type} I G1 A G2,
  @wf_ctx Sign I (G1 ++ A :: G2) ->
  @h_derivation Sign I (G1 ++ A :: G2) (tm_var (length G1)) A.
Proof.
  intros Sign I G1. induction G1; intros A G2 wfc; simpl.
  - inversion wfc; subst. apply HD_Var0; auto.
  - inversion wfc; subst. apply HD_VarS; auto.
Qed.

Lemma h_reify_ctx_offset_typing : forall {Sign : Type} I G1 G2,
  @wf_ctx Sign I (G1 ++ G2) ->
  @h_derivation Sign I (G1 ++ G2) (h_reify_ctx_offset G2 (length G1)) (h_make_ctx_ty G2).
Proof.
  intros Sign I G1 G2. revert G1.
  induction G2; intros G1 wfc; simpl.
  - apply HD_Unit. exact wfc.
  - eapply HD_Pair.
    + replace (S (length G1)) with (length (G1 ++ [a])) by (rewrite app_length; simpl; lia).
      replace (G1 ++ a :: G2) with ((G1 ++ [a]) ++ G2) in * by (rewrite <- app_assoc; reflexivity).
      apply IHG2. exact wfc.
    + apply h_var_typing. exact wfc.
Qed.

Theorem h_reify_ctx_typing : forall {Sign : Type} (I : b_ty) (G : h_context) (wfc : @wf_ctx Sign I G),
  @h_derivation Sign I G (h_reify_ctx G) (h_make_ctx_ty G).
Proof.
  intros Sign I G wfc.
  unfold h_reify_ctx.
  replace G with (nil ++ G) at 1 2 by reflexivity.
  apply (h_reify_ctx_offset_typing I nil G).
  simpl. exact wfc.
Qed.


Lemma h_lift_0 : forall {Sign} (t : @h_tm Sign) k, h_lift 0 k t = t.
Proof.
  induction t; intros k; simpl; auto.
  - destruct (k <=? n); auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2, IHt3; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
Qed.

Lemma h_lift_add : forall {Sign} (t : @h_tm Sign) n m k, h_lift n k (h_lift m k t) = h_lift (n + m) k t.
Proof.
  induction t; intros n0 m0 k0; simpl; auto.
  - destruct (k0 <=? n) eqn:Hk.
    + simpl. assert (Hk2 : k0 <=? m0 + n = true) by (apply Nat.leb_le in Hk; apply Nat.leb_le; lia).
      rewrite Hk2. f_equal. lia.
    + simpl. rewrite Hk. auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2, IHt3; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
Qed.


Lemma wf_ctx_insert : forall {Sign : Type} I n B G,
  @wf_ctx Sign I G -> 
  @WellFormed Sign I B -> 
  @wf_ctx Sign I (h_insert_at n B G).
Proof.
  intros Sign I n B G wfc wfB. revert n.
  induction wfc; intros n; destruct n; simpl.
  -
    apply WFC_cons. exact wfB. apply WFC_nil.
  -
    apply WFC_nil.
  -
    apply WFC_cons. exact wfB. apply WFC_cons. exact w. exact wfc.
  -
    apply WFC_cons. exact w. apply IHwfc.
Qed.

Lemma ctx_equiv_insert : forall {Sign : Type} I n B G1 G2,
  @WellFormed Sign I B -> 
  @ctx_equiv Sign I G1 G2 -> 
  @ctx_equiv Sign I (h_insert_at n B G1) (h_insert_at n B G2).
Proof.
  intros Sign I n B G1 G2 wfB ceq. revert n.
  induction ceq; intros n; destruct n; simpl.
  -
    apply CEQ_cons. apply FE_Refl. exact wfB. apply CEQ_nil.
  -
    apply CEQ_nil.
  -
    apply CEQ_cons. apply FE_Refl. exact wfB. apply CEQ_cons. exact f. exact ceq.
  -
    apply CEQ_cons. exact f. apply IHceq.
Qed.

Lemma ctx_pullback_insert : forall {Sign : Type} (f : @b_tm Sign) n B G,
  ctx_pullback f (h_insert_at n B G) = h_insert_at n (form_pullback f B) (ctx_pullback f G).
Proof.
  intros Sign f n B G. revert n.
  induction G; intros n; destruct n; simpl; auto.
  rewrite IHG. reflexivity.
Qed.

Theorem h_weakening_general : forall {Sign : Type} I G p Phi B n,
  @h_derivation Sign I G p Phi ->
  @WellFormed Sign I B ->
  @h_derivation Sign I (h_insert_at n B G) (h_lift 1 n p) Phi.
Proof.
  intros Sign I G p Phi B n Hder wfB.
  revert n B wfB.
  induction Hder; intros n0 B0 wfB0; simpl.
  
  -
    destruct n0; simpl.
    + apply HD_VarS; auto. apply HD_Var0; auto.
    + apply HD_Var0; auto. apply wf_ctx_insert; auto.

  -
    destruct n0; simpl.
    + apply HD_VarS; auto. apply HD_VarS; auto.
    + destruct (n0 <=? i) eqn:Hle.
      * apply HD_VarS; auto.
        replace (tm_var (S i)) with (@h_lift Sign 1 n0 (tm_var i)).
        -- apply IHHder; auto.
        -- simpl. rewrite Hle. reflexivity.
      * apply HD_VarS; auto.
        replace (tm_var i) with (@h_lift Sign 1 n0 (tm_var i)).
        -- apply IHHder; auto.
        -- simpl. rewrite Hle. reflexivity.
  -   eapply HD_Conv; eauto.
  -   apply HD_Unit. apply wf_ctx_insert; auto.
  -   apply HD_Lam. apply (IHHder (S n0) B0 wfB0).
  -   eapply HD_App; eauto.
  -   apply HD_Pair; eauto.
  -   eapply HD_Fst; eauto.
  -   eapply HD_Snd; eauto.
  -   apply HD_Inl; eauto.
  -   apply HD_Inr; eauto.
  -   eapply HD_Case.
    + apply (IHHder1 n0 B0 wfB0).
    + apply (IHHder2 (S n0) B0 wfB0).
    + apply (IHHder3 (S n0) B0 wfB0).
  -   apply HD_Absurd; eauto.
  
  -
    apply HD_All_Intro.
    + apply wf_ctx_insert; auto.
    + rewrite ctx_pullback_insert.
      apply (IHHder n0 (form_pullback b_fst B0)).
      eapply wf_pullback; eauto. apply BT_Fst.
  -
    eapply HD_All_Elim; eauto.
  -
    eapply HD_Ex_Intro; eauto.
  -
    eapply HD_Ctx_Conv.
    + apply (IHHder n0 B0 wfB0).
    + apply ctx_equiv_insert; auto.
    + apply wf_ctx_insert; auto.
  -
    eapply HD_Ex_Elim.
    + exact w.
    + apply (IHHder1 n0 B0 wfB0).
    + rewrite ctx_pullback_insert.
      apply (IHHder2 (S n0) (form_pullback b_fst B0)).
      eapply wf_pullback; eauto. apply BT_Fst.
Qed.

Theorem h_weakening_from_nil : forall {Sign : Type} (I : b_ty) (G : h_context) (p : @h_tm Sign) (Phi : @h_ty Sign),
  @wf_ctx Sign I G ->
  @h_derivation Sign I nil p Phi ->
  @h_derivation Sign I G (h_lift (length G) 0 p) Phi.
Proof.
  intros Sign I G p Phi wfc Hnil.
  induction wfc.
  -
    simpl. rewrite h_lift_0. exact Hnil.
  -
    simpl.
    (* Insert [Phi0], the actual bound formula, at position zero. *)
    apply (@h_weakening_general Sign I G _ Phi Phi0 0) in IHwfc.
    + rewrite h_lift_add in IHwfc.
      replace (1 + length G) with (S (length G)) in IHwfc by lia.
      exact IHwfc.
    + exact w.
Qed.