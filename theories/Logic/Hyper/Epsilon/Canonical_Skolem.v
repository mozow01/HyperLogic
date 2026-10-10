(** Canonical, well-founded epsilon labels for the epsilon-only syntax. *)

Require Import Arith.
Require Import Lia.
Require Import Relations.
Require Import Relation_Operators.
Require Import Arith.Wf_nat.

Require Import HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.

Module CanonicalEpsilon.

Module Base := HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Module Hyper := HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.

Inductive EpsilonLabel (Func Pred : Type) : Type :=
| epsilon_label :
    Base.b_ty ->
    @Hyper.h_ty (EpsilonLabel Func Pred) Func Pred ->
    EpsilonLabel Func Pred.

Arguments epsilon_label {Func Pred} _ _.

Global Instance CanonicalSkolemMapping (Func Pred : Type) :
  Hyper.SkolemMapping (EpsilonLabel Func Pred) Func Pred.
Proof.
  refine {| Hyper.skolem_index := @epsilon_label Func Pred |}.
  intros A B Phi Psi H.
  inversion H.
  split; reflexivity.
Defined.

Section Dependency.

Context {Func Pred : Type}.

Inductive occurs_in_b_tm (s : EpsilonLabel Func Pred) :
  @Base.b_tm (EpsilonLabel Func Pred) Func -> Prop :=
| occurs_b_comp_l : forall u v,
    occurs_in_b_tm s u ->
    occurs_in_b_tm s (Base.b_comp u v)
| occurs_b_comp_r : forall u v,
    occurs_in_b_tm s v ->
    occurs_in_b_tm s (Base.b_comp u v)
| occurs_b_pair_l : forall u v,
    occurs_in_b_tm s u ->
    occurs_in_b_tm s (Base.b_pair u v)
| occurs_b_pair_r : forall u v,
    occurs_in_b_tm s v ->
    occurs_in_b_tm s (Base.b_pair u v)
| occurs_b_const : forall A,
    occurs_in_b_tm s (Base.b_const A s).

Inductive occurs_in_h_ty (s : EpsilonLabel Func Pred) :
  @Hyper.h_ty (EpsilonLabel Func Pred) Func Pred -> Prop :=
| occurs_h_prod_l : forall Phi Psi,
    occurs_in_h_ty s Phi ->
    occurs_in_h_ty s (Hyper.Ty_Prod Phi Psi)
| occurs_h_prod_r : forall Phi Psi,
    occurs_in_h_ty s Psi ->
    occurs_in_h_ty s (Hyper.Ty_Prod Phi Psi)
| occurs_h_sum_l : forall Phi Psi,
    occurs_in_h_ty s Phi ->
    occurs_in_h_ty s (Hyper.Ty_Sum Phi Psi)
| occurs_h_sum_r : forall Phi Psi,
    occurs_in_h_ty s Psi ->
    occurs_in_h_ty s (Hyper.Ty_Sum Phi Psi)
| occurs_h_arrow_l : forall Phi Psi,
    occurs_in_h_ty s Phi ->
    occurs_in_h_ty s (Hyper.Ty_Arrow Phi Psi)
| occurs_h_arrow_r : forall Phi Psi,
    occurs_in_h_ty s Psi ->
    occurs_in_h_ty s (Hyper.Ty_Arrow Phi Psi)
| occurs_h_atom : forall p t,
    occurs_in_b_tm s t ->
    occurs_in_h_ty s (Hyper.Ty_Atom p t)
| occurs_h_all : forall A Phi,
    occurs_in_h_ty s Phi ->
    occurs_in_h_ty s (Hyper.Ty_All A Phi).

Fixpoint epsilon_rank (s : EpsilonLabel Func Pred) : nat :=
  match s with
  | epsilon_label _ Phi =>
      S (
        let fix formula_rank
          (X : @Hyper.h_ty (EpsilonLabel Func Pred) Func Pred) : nat :=
          match X with
          | Hyper.Ty_Unit => 0
          | Hyper.Ty_Void => 0
          | Hyper.Ty_Prod X Y => Nat.max (formula_rank X) (formula_rank Y)
          | Hyper.Ty_Sum X Y => Nat.max (formula_rank X) (formula_rank Y)
          | Hyper.Ty_Arrow X Y => Nat.max (formula_rank X) (formula_rank Y)
          | Hyper.Ty_Atom _ t =>
              let fix term_rank
                (u : @Base.b_tm (EpsilonLabel Func Pred) Func) : nat :=
                match u with
                | Base.b_id => 0
                | Base.b_comp v w => Nat.max (term_rank v) (term_rank w)
                | Base.b_unit => 0
                | Base.b_pair v w => Nat.max (term_rank v) (term_rank w)
                | Base.b_fst => 0
                | Base.b_snd => 0
                | Base.b_const _ r => epsilon_rank r
                | Base.b_func _ => 0
                end
              in term_rank t
          | Hyper.Ty_All _ X => formula_rank X
          end
        in formula_rank Phi)
  end.

Definition b_tm_rank
  (t : @Base.b_tm (EpsilonLabel Func Pred) Func) : nat :=
  let fix go (u : @Base.b_tm (EpsilonLabel Func Pred) Func) : nat :=
    match u with
    | Base.b_id => 0
    | Base.b_comp v w => Nat.max (go v) (go w)
    | Base.b_unit => 0
    | Base.b_pair v w => Nat.max (go v) (go w)
    | Base.b_fst => 0
    | Base.b_snd => 0
    | Base.b_const _ r => epsilon_rank r
    | Base.b_func _ => 0
    end
  in go t.

Definition h_ty_rank
  (Phi : @Hyper.h_ty (EpsilonLabel Func Pred) Func Pred) : nat :=
  Nat.pred (epsilon_rank (epsilon_label Base.b_Unit Phi)).

Lemma epsilon_rank_unfold :
  forall (A : Base.b_ty)
    (Phi : @Hyper.h_ty (EpsilonLabel Func Pred) Func Pred),
    epsilon_rank (epsilon_label A Phi) = S (h_ty_rank Phi).
Proof.
  intros A Phi.
  unfold h_ty_rank.
  cbn [epsilon_rank].
  reflexivity.
Qed.

Lemma occurs_in_b_tm_rank :
  forall s (t : @Base.b_tm (EpsilonLabel Func Pred) Func),
    occurs_in_b_tm s t -> epsilon_rank s <= b_tm_rank t.
Proof.
  intros s t Hocc.
  induction Hocc; cbn [b_tm_rank] in *.
  - eapply Nat.le_trans; [exact IHHocc | apply Nat.le_max_l].
  - eapply Nat.le_trans; [exact IHHocc | apply Nat.le_max_r].
  - eapply Nat.le_trans; [exact IHHocc | apply Nat.le_max_l].
  - eapply Nat.le_trans; [exact IHHocc | apply Nat.le_max_r].
  - apply Nat.le_refl.
Qed.

Lemma occurs_in_h_ty_rank :
  forall s (Phi : @Hyper.h_ty (EpsilonLabel Func Pred) Func Pred),
    occurs_in_h_ty s Phi -> epsilon_rank s <= h_ty_rank Phi.
Proof.
  intros s Phi Hocc.
  induction Hocc; unfold h_ty_rank in *; cbn [epsilon_rank] in *.
  - eapply Nat.le_trans; [exact IHHocc | apply Nat.le_max_l].
  - eapply Nat.le_trans; [exact IHHocc | apply Nat.le_max_r].
  - eapply Nat.le_trans; [exact IHHocc | apply Nat.le_max_l].
  - eapply Nat.le_trans; [exact IHHocc | apply Nat.le_max_r].
  - eapply Nat.le_trans; [exact IHHocc | apply Nat.le_max_l].
  - eapply Nat.le_trans; [exact IHHocc | apply Nat.le_max_r].
  - exact (occurs_in_b_tm_rank s t H).
  - exact IHHocc.
Qed.

Definition immediate_dependency
  (smaller larger : EpsilonLabel Func Pred) : Prop :=
  match larger with
  | epsilon_label _ Phi => occurs_in_h_ty smaller Phi
  end.

Definition dependency : relation (EpsilonLabel Func Pred) :=
  clos_trans (EpsilonLabel Func Pred) immediate_dependency.

Definition occurs_deep_in_h_ty
  (s : EpsilonLabel Func Pred)
  (Phi : @Hyper.h_ty (EpsilonLabel Func Pred) Func Pred) : Prop :=
  occurs_in_h_ty s Phi \/
  exists outer,
    occurs_in_h_ty outer Phi /\ dependency s outer.

Lemma immediate_dependency_rank :
  forall smaller larger,
    immediate_dependency smaller larger ->
    epsilon_rank smaller < epsilon_rank larger.
Proof.
  intros smaller [A Phi] Hdep.
  rewrite epsilon_rank_unfold.
  apply Nat.lt_succ_r.
  exact (occurs_in_h_ty_rank smaller Phi Hdep).
Qed.

Lemma dependency_rank :
  forall smaller larger,
    dependency smaller larger ->
    epsilon_rank smaller < epsilon_rank larger.
Proof.
  intros smaller larger Hdep.
  induction Hdep using clos_trans_ind.
  - apply immediate_dependency_rank. exact H.
  - eapply Nat.lt_trans; eassumption.
Qed.

Lemma rank_decreasing_well_founded :
  forall (R : relation (EpsilonLabel Func Pred)),
    (forall smaller larger, R smaller larger ->
      epsilon_rank smaller < epsilon_rank larger) ->
    well_founded R.
Proof.
  intros R Hrank larger.
  pose proof (well_founded_ltof (EpsilonLabel Func Pred) epsilon_rank larger)
    as Hacc.
  induction Hacc as [larger Hsmaller IH].
  constructor.
  intros smaller Hstep.
  apply IH.
  unfold ltof.
  exact (Hrank smaller larger Hstep).
Qed.

Theorem immediate_dependency_well_founded :
  well_founded immediate_dependency.
Proof.
  apply rank_decreasing_well_founded.
  exact immediate_dependency_rank.
Qed.

Theorem dependency_well_founded : well_founded dependency.
Proof.
  apply rank_decreasing_well_founded.
  exact dependency_rank.
Qed.

Theorem generated_label_has_greater_rank :
  forall (A : Base.b_ty)
    (Phi : @Hyper.h_ty (EpsilonLabel Func Pred) Func Pred) s,
    occurs_in_h_ty s Phi ->
    epsilon_rank s < epsilon_rank (epsilon_label A Phi).
Proof.
  intros A Phi s Hocc.
  apply immediate_dependency_rank.
  exact Hocc.
Qed.

Theorem deeply_generated_label_has_greater_rank :
  forall (A : Base.b_ty)
    (Phi : @Hyper.h_ty (EpsilonLabel Func Pred) Func Pred) s,
    occurs_deep_in_h_ty s Phi ->
    epsilon_rank s < epsilon_rank (epsilon_label A Phi).
Proof.
  intros A Phi s [Hdirect | [outer [Houter Hnested]]].
  - apply generated_label_has_greater_rank. exact Hdirect.
  - eapply Nat.lt_trans.
    + apply dependency_rank. exact Hnested.
    + apply generated_label_has_greater_rank. exact Houter.
Qed.

Corollary no_self_reference :
  forall (A : Base.b_ty)
    (Phi : @Hyper.h_ty (EpsilonLabel Func Pred) Func Pred),
    ~ occurs_in_h_ty (epsilon_label A Phi) Phi.
Proof.
  intros A Phi Hocc.
  pose proof (generated_label_has_greater_rank A Phi (epsilon_label A Phi) Hocc).
  lia.
Qed.

Corollary no_deep_self_reference :
  forall (A : Base.b_ty)
    (Phi : @Hyper.h_ty (EpsilonLabel Func Pred) Func Pred),
    ~ occurs_deep_in_h_ty (epsilon_label A Phi) Phi.
Proof.
  intros A Phi Hocc.
  pose proof
    (deeply_generated_label_has_greater_rank
      A Phi (epsilon_label A Phi) Hocc).
  lia.
Qed.

Corollary no_finite_dependency_cycle :
  forall s : EpsilonLabel Func Pred, ~ dependency s s.
Proof.
  intros s Hcycle.
  pose proof (dependency_rank s s Hcycle).
  lia.
Qed.

End Dependency.

End CanonicalEpsilon.
