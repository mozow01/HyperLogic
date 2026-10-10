
(** Proof-code curvature for the epsilon bi-implication.
    For [f : exists Phi -> Phi(epsilon_Phi)] and its direct return [g],
    curvature is [(g o f, f o g)]. The first component exposes witness
    hiding by replacing an explicit witness with [epsilon_Phi].
    Base terms live in [b_tm], proof codes in [h_tm], and [h_derivation]
    only certifies their typing. This file does not use the term model. *)

Require Import List.
Import ListNotations.

Require Import HyperLogic.Logic.Base.Epsilon_Adjoint.Base_Syntax.
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum.
Require Import HyperLogic.Logic.Hyper.Epsilon_Adjoint.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon_Adjoint.Hyper_Syntax_Lemmas.

Set Implicit Arguments.

Section Internal_Epsilon_Curvature.

Context {Sign : Type} `{SM : SkolemMapping Sign}.

Definition eps_ind (A : b_ty) (Phi : @h_ty Sign) : @b_tm Sign :=
  b_const A (skolem_index A Phi).

Lemma eps_ind_typing : forall (I A : b_ty) (Phi : @h_ty Sign),
  base_typing I (eps_ind A Phi) A.
Proof.
  intros. unfold eps_ind. apply BT_Const.
Defined.

Definition eps_pair (A : b_ty) (Phi : @h_ty Sign) : @b_tm Sign :=
  b_pair b_id (eps_ind A Phi).

Lemma eps_pair_typing : forall (I A : b_ty) (Phi : @h_ty Sign),
  base_typing I (eps_pair A Phi) (b_Prod I A).
Proof.
  intros. unfold eps_pair.
  apply BT_Pair.
  - apply BT_Id.
  - apply eps_ind_typing.
Defined.

Definition ex_ty (A : b_ty) (Phi : @h_ty Sign) : @h_ty Sign :=
  Ty_Ex A Phi.

Definition eps_ty (I A : b_ty) (Phi : @h_ty Sign) : @h_ty Sign :=
  Phi .[ eps_ind A Phi ].

Lemma wf_ex_ty : forall (I A : b_ty) (Phi : @h_ty Sign),
  WellFormed (b_Prod I A) Phi ->
  WellFormed I (ex_ty A Phi).
Proof.
  intros I A Phi wfPhi. unfold ex_ty. apply WF_Ex. exact wfPhi.
Defined.

Lemma wf_eps_ty : forall (I A : b_ty) (Phi : @h_ty Sign),
  WellFormed (b_Prod I A) Phi ->
  WellFormed I (eps_ty I A Phi).
Proof.
  intros I A Phi wfPhi.
  unfold eps_ty.
  eapply wf_subst.
  - apply eps_pair_typing.
  - exact wfPhi.
Defined.

Definition endo_ty (Phi : @h_ty Sign) : @h_ty Sign :=
  Ty_Arrow Phi Phi.

Lemma wf_endo_ty : forall (I : b_ty) (Phi : @h_ty Sign),
  WellFormed I Phi -> WellFormed I (endo_ty Phi).
Proof.
  intros I Phi wfPhi. unfold endo_ty. apply WF_Arrow; exact wfPhi.
Defined.

(** Object-language identity code, not a Coq equality proof. *)
Definition h_id_code (Phi : @h_ty Sign) : @h_tm Sign :=
  tm_lam Phi (tm_var 0).

Lemma h_id_derivation : forall (I : b_ty) (Phi : @h_ty Sign),
  WellFormed I Phi ->
  h_derivation I [] (h_id_code Phi) (endo_ty Phi).
Proof.
  intros I Phi wfPhi.
  unfold h_id_code, endo_ty.
  apply HD_Lam.
  apply HD_Var0.
  apply AWF_Cons.
  - exact wfPhi.
  - apply AWF_Nil.
Defined.

(** Composition of closed object-language proof codes. *)
Definition h_comp_code
  (A B C : @h_ty Sign) (f g : @h_tm Sign) : @h_tm Sign :=
  tm_lam A (tm_app f (tm_app g (tm_var 0))).
  
Lemma awf_singleton :
  forall (I : b_ty) (A : @h_ty Sign),
    WellFormed I A ->
    All_WellFormed I [A].
Proof.
  intros I A wfA.
  constructor.
  - exact wfA.
  - constructor.
Qed.

Lemma h_comp_derivation : forall
  (I : b_ty) (A B C : @h_ty Sign) (f g : @h_tm Sign),
  WellFormed I A ->
  h_derivation I [] f (Ty_Arrow B C) ->
  h_derivation I [] g (Ty_Arrow A B) ->
  h_derivation I [] (h_comp_code A B C f g) (Ty_Arrow A C).
Proof.
  intros I A B C f g wfA df dg.
  unfold h_comp_code.
  apply HD_Lam.

  eapply HD_App with (Phi := B).

  -
    change (h_derivation I ([] ++ [A]) f (Ty_Arrow B C)).
    eapply (@h_derivation_append Sign SM
              I [] [A] f (Ty_Arrow B C)).
    + exact df.
    + constructor.
      * exact wfA.
      * constructor.

  -
    eapply HD_App with (Phi := A).

    +
      change (h_derivation I ([] ++ [A]) g (Ty_Arrow A B)).
      eapply (@h_derivation_append Sign SM
                I [] [A] g (Ty_Arrow A B)).
      * exact dg.
      * constructor.
        -- exact wfA.
        -- constructor.

    +
      apply HD_Var0.
      constructor.
      * exact wfA.
      * constructor.
Qed.
Definition K_left_code
  (A B : @h_ty Sign) (f g : @h_tm Sign) : @h_tm Sign :=
  h_comp_code A B A g f.

Definition K_right_code
  (A B : @h_ty Sign) (f g : @h_tm Sign) : @h_tm Sign :=
  h_comp_code B A B f g.

(** Raw curvature is the pair of return endomorphism codes. *)
Definition K_code
  (A B : @h_ty Sign) (f g : @h_tm Sign) : (@h_tm Sign * @h_tm Sign)%type :=
  (K_left_code A B f g, K_right_code A B f g).

Class BiImplicationTyped
  (I : b_ty) (A B : @h_ty Sign) (f g : @h_tm Sign) : Type := {
  bi_wf_A : WellFormed I A ;
  bi_wf_B : WellFormed I B ;
  bi_f_derivation : h_derivation I [] f (Ty_Arrow A B) ;
  bi_g_derivation : h_derivation I [] g (Ty_Arrow B A)
}.

Definition K_left_derivation
  (I : b_ty) (A B : @h_ty Sign) (f g : @h_tm Sign)
  (bi : BiImplicationTyped I A B f g)
  : h_derivation I [] (K_left_code A B f g) (endo_ty A).
Proof.
  destruct bi as [wfA wfB df dg].
  unfold K_left_code, endo_ty.
  eapply h_comp_derivation.
  - exact wfA.
  - exact dg.
  - exact df.
Defined.

Definition K_right_derivation
  (I : b_ty) (A B : @h_ty Sign) (f g : @h_tm Sign)
  (bi : BiImplicationTyped I A B f g)
  : h_derivation I [] (K_right_code A B f g) (endo_ty B).
Proof.
  destruct bi as [wfA wfB df dg].
  unfold K_right_code, endo_ty.
  eapply h_comp_derivation.
  - exact wfB.
  - exact df.
  - exact dg.
Defined.

Definition eps_choice_statement
  (I A : b_ty) (Phi : @h_ty Sign) : @h_ty Sign :=
  Ty_Arrow (ex_ty A Phi) (eps_ty I A Phi).

Definition eps_return_statement
  (I A : b_ty) (Phi : @h_ty Sign) : @h_ty Sign :=
  Ty_Arrow (eps_ty I A Phi) (ex_ty A Phi).

Lemma wf_eps_choice_statement : forall (I A : b_ty) (Phi : @h_ty Sign),
  WellFormed (b_Prod I A) Phi ->
  WellFormed I (eps_choice_statement I A Phi).
Proof.
  intros I A Phi wfPhi.
  unfold eps_choice_statement.
  apply WF_Arrow.
  - apply wf_ex_ty. exact wfPhi.
  - apply wf_eps_ty. exact wfPhi.
Defined.

Lemma wf_eps_return_statement : forall (I A : b_ty) (Phi : @h_ty Sign),
  WellFormed (b_Prod I A) Phi ->
  WellFormed I (eps_return_statement I A Phi).
Proof.
  intros I A Phi wfPhi.
  unfold eps_return_statement.
  apply WF_Arrow.
  - apply wf_eps_ty. exact wfPhi.
  - apply wf_ex_ty. exact wfPhi.
Defined.

(** The epsilon choice code from an existential to its epsilon instance. *)
Definition eps_choice_code
  (I A : b_ty) (Phi : @h_ty Sign) : @h_tm Sign :=
  tm_lam (ex_ty A Phi)
    (tm_ex_elim (tm_var 0) (tm_eps_intro b_snd (tm_var 0))).

(** The direct return uses [epsilon_Phi] as the existential witness. *)
Definition eps_return_code
  (I A : b_ty) (Phi : @h_ty Sign) : @h_tm Sign :=
  tm_lam (eps_ty I A Phi)
    (tm_ex_intro (eps_ind A Phi) (tm_var 0)).

(** Raw code after the direct round trip; this is not claimed as an
    object-language definitional equality. The outer witness becomes
    [epsilon_Phi], while the original witness remains inside [eps_intro]. *)
Definition eps_hidden_ex_code
  (A : b_ty) (Phi : @h_ty Sign) (t : @b_tm Sign) (p : @h_tm Sign)
  : @h_tm Sign :=
  tm_ex_intro (eps_ind A Phi) (tm_eps_intro t p).

Lemma eps_hidden_ex_derivation : forall
  (I A : b_ty) (G : @h_context Sign) (Phi : @h_ty Sign)
  (t : @b_tm Sign) (p : @h_tm Sign),
  base_typing I t A ->
  h_derivation I G p (Phi .[ t ]) ->
  h_derivation I G (eps_hidden_ex_code A Phi t p) (ex_ty A Phi).
Proof.
  intros I A G Phi t p dt dp.
  unfold eps_hidden_ex_code, ex_ty.
  eapply HD_Ex_Intro.
  - apply eps_ind_typing.
  - eapply HD_Eps_Intro.
    + exact dt.
    + exact dp.
Defined.

Lemma eps_choice_derivation : forall
  (I A : b_ty) (Phi : @h_ty Sign),
  WellFormed (b_Prod I A) Phi ->
  h_derivation I [] (eps_choice_code I A Phi)
    (eps_choice_statement I A Phi).
Proof.
  intros I A Phi wfPhi.
  unfold eps_choice_code, eps_choice_statement, ex_ty, eps_ty.
  apply HD_Lam.
  apply ex_implies_eps.
  exact wfPhi.
Defined.

Lemma eps_return_derivation : forall
  (I A : b_ty) (Phi : @h_ty Sign),
  WellFormed (b_Prod I A) Phi ->
  h_derivation I [] (eps_return_code I A Phi)
    (eps_return_statement I A Phi).
Proof.
  intros I A Phi wfPhi.
  unfold eps_return_code, eps_return_statement, ex_ty, eps_ty.
  apply HD_Lam.
  eapply HD_Ex_Intro.
  - apply eps_ind_typing.
  - apply HD_Var0.
    apply AWF_Cons.
    + apply wf_eps_ty. exact wfPhi.
    + apply AWF_Nil.
Defined.

Global Instance epsilon_biimplication_typed
  (I A : b_ty) (Phi : @h_ty Sign)
  (wfPhi : WellFormed (b_Prod I A) Phi)
  : BiImplicationTyped I
      (ex_ty A Phi)
      (eps_ty I A Phi)
      (eps_choice_code I A Phi)
      (eps_return_code I A Phi).
Proof.
  constructor.
  - apply wf_ex_ty. exact wfPhi.
  - apply wf_eps_ty. exact wfPhi.
  - apply eps_choice_derivation. exact wfPhi.
  - apply eps_return_derivation. exact wfPhi.
Defined.

Definition eps_K_ex_code
  (I A : b_ty) (Phi : @h_ty Sign) : @h_tm Sign :=
  K_left_code (ex_ty A Phi) (eps_ty I A Phi)
    (eps_choice_code I A Phi)
    (eps_return_code I A Phi).

Definition eps_K_eps_code
  (I A : b_ty) (Phi : @h_ty Sign) : @h_tm Sign :=
  K_right_code (ex_ty A Phi) (eps_ty I A Phi)
    (eps_choice_code I A Phi)
    (eps_return_code I A Phi).

Definition eps_K_code
  (I A : b_ty) (Phi : @h_ty Sign) : (@h_tm Sign * @h_tm Sign)%type :=
  K_code (ex_ty A Phi) (eps_ty I A Phi)
    (eps_choice_code I A Phi)
    (eps_return_code I A Phi).

Lemma eps_K_ex_derivation : forall
  (I A : b_ty) (Phi : @h_ty Sign)
  (wfPhi : WellFormed (b_Prod I A) Phi),
  h_derivation I [] (eps_K_ex_code I A Phi)
    (endo_ty (ex_ty A Phi)).
Proof.
  intros I A Phi wfPhi.
  unfold eps_K_ex_code.
  apply K_left_derivation.
  exact (@epsilon_biimplication_typed I A Phi wfPhi).
Defined.

Lemma eps_K_eps_derivation : forall
  (I A : b_ty) (Phi : @h_ty Sign)
  (wfPhi : WellFormed (b_Prod I A) Phi),
  h_derivation I [] (eps_K_eps_code I A Phi)
    (endo_ty (eps_ty I A Phi)).
Proof.
  intros I A Phi wfPhi.
  unfold eps_K_eps_code.
  eapply K_right_derivation.
  eapply epsilon_biimplication_typed.
  exact wfPhi.
Defined.

(** A pluggable non-thin equality on equally typed proof codes. *)
Class ProofCodeEq : Type := {
  pc_eq : forall (I : b_ty) (G : @h_context Sign) (Phi : @h_ty Sign)
                 (p q : @h_tm Sign),
    h_derivation I G p Phi ->
    h_derivation I G q Phi ->
    Prop
}.

Arguments pc_eq {_} {I} {G} {Phi} {p} {q} _ _.

Class ProofCodeEqLaws `{ProofCodeEq} : Type := {
  pc_eq_refl : forall I G Phi p (dp : h_derivation I G p Phi),
    pc_eq dp dp ;

  pc_eq_sym : forall I G Phi p q
                     (dp : h_derivation I G p Phi)
                     (dq : h_derivation I G q Phi),
    pc_eq dp dq ->
    pc_eq dq dp ;

  pc_eq_trans : forall I G Phi p q r
                       (dp : h_derivation I G p Phi)
                       (dq : h_derivation I G q Phi)
                       (dr : h_derivation I G r Phi),
    pc_eq dp dq ->
    pc_eq dq dr ->
    pc_eq dp dr
}.

(** Flatness equates both return codes with the corresponding identities. *)
Definition FlatBiImplication
  `{ProofCodeEq}
  (I : b_ty) (A B : @h_ty Sign) (f g : @h_tm Sign)
  (bi : BiImplicationTyped I A B f g) : Prop :=
  match bi with
  | {| bi_wf_A := wfA ;
       bi_wf_B := wfB ;
       bi_f_derivation := df ;
       bi_g_derivation := dg |} =>
      pc_eq
        (h_comp_derivation
           (I := I) (A := A) (B := B) (C := A)
           (f := g) (g := f)
           wfA dg df)
        (h_id_derivation
           (I := I) (Phi := A)
           wfA)
      /\
      pc_eq
        (h_comp_derivation
           (I := I) (A := B) (B := A) (C := B)
           (f := f) (g := g)
           wfB df dg)
        (h_id_derivation
           (I := I) (Phi := B)
           wfB)
  end.

Definition FlatEpsilonDatum
  `{ProofCodeEq}
  (I Y : b_ty) (Phi : @h_ty Sign)
  (wfPhi : WellFormed (b_Prod I Y) Phi) : Prop :=
  FlatBiImplication
    (I := I)
    (A := ex_ty Y Phi)
    (B := eps_ty I Y Phi)
    (f := eps_choice_code I Y Phi)
    (g := eps_return_code I Y Phi)
    (epsilon_biimplication_typed
       (I := I) (A := Y) (Phi := Phi)
       wfPhi).

(** Witness-side flatness prevents the direct round trip from hiding an
    explicit existential witness. *)
Definition FlatEpsilonWitnessSide
  `{ProofCodeEq}
  (I Y : b_ty) (Phi : @h_ty Sign)
  (wfPhi : WellFormed (b_Prod I Y) Phi) : Prop :=
  pc_eq
    (eps_K_ex_derivation
       (I := I) (A := Y) (Phi := Phi)
       wfPhi)
    (h_id_derivation
       (I := I) (Phi := ex_ty Y Phi)
       (wf_ex_ty
          (I := I) (A := Y) (Phi := Phi)
          wfPhi)).
(** The epsilon-instance side is the second component of the same curvature. *)
Definition FlatEpsilonEpsSide
  `{ProofCodeEq}
  (I Y : b_ty) (Phi : @h_ty Sign)
  (wfPhi : WellFormed (b_Prod I Y) Phi) : Prop :=
  pc_eq
    (eps_K_eps_derivation
       (I := I) (A := Y) (Phi := Phi)
       wfPhi)
    (h_id_derivation
       (I := I) (Phi := eps_ty I Y Phi)
       (wf_eps_ty
          (I := I) (A := Y) (Phi := Phi)
          wfPhi)).

Definition SystemFlat `{ProofCodeEq} : Prop :=
  forall (I Y : b_ty) (Phi : @h_ty Sign)
         (wfPhi : WellFormed (b_Prod I Y) Phi),
    FlatEpsilonDatum
      (I := I)
      (Y := Y)
      (Phi := Phi)
      wfPhi.
    
End Internal_Epsilon_Curvature.

(** A binary relation example using a product-valued base term. *)

Section Romeo_Juliet_Binary_Atom.

Context {Sign : Type} `{SM : SkolemMapping Sign}.

Variable I Person : b_ty.
Variable loves : nat.

Definition RJ_PairTy : b_ty :=
  b_Prod Person Person.

Definition RJ_pair_var : @b_tm Sign :=
  b_snd.

(* Reads as [Loves z] for a bound pair [z : Person × Person]. *)
Definition RJ_Loves_body : @h_ty Sign :=
  Ty_Atom loves RJ_pair_var.

Lemma RJ_Loves_body_wf :
  WellFormed (b_Prod I RJ_PairTy) RJ_Loves_body.
Proof.
  unfold RJ_Loves_body, RJ_pair_var, RJ_PairTy.
  eapply WF_Atom.
  apply BT_Snd.
Defined.

Definition RJ_Exists_Love : @h_ty Sign :=
  Ty_Ex RJ_PairTy RJ_Loves_body.

Lemma RJ_Exists_Love_wf :
  WellFormed I RJ_Exists_Love.
Proof.
  unfold RJ_Exists_Love.
  apply WF_Ex.
  exact RJ_Loves_body_wf.
Defined.

(* The epsilon-selected pair is read as Romeo and Juliet. *)
Definition RJ_eps_pair : @b_tm Sign :=
  b_const RJ_PairTy (skolem_index RJ_PairTy RJ_Loves_body).

Lemma RJ_eps_pair_typing :
  base_typing I RJ_eps_pair RJ_PairTy.
Proof.
  unfold RJ_eps_pair.
  apply BT_Const.
Defined.

Definition RJ_Romeo : @b_tm Sign :=
  b_comp b_fst RJ_eps_pair.

Definition RJ_Juliet : @b_tm Sign :=
  b_comp b_snd RJ_eps_pair.

Lemma RJ_Romeo_typing :
  base_typing I RJ_Romeo Person.
Proof.
  unfold RJ_Romeo, RJ_eps_pair, RJ_PairTy.
  eapply BT_Comp.
  - eapply BT_Fst.
  - apply BT_Const.
Defined.

Lemma RJ_Juliet_typing :
  base_typing I RJ_Juliet Person.
Proof.
  unfold RJ_Juliet, RJ_eps_pair, RJ_PairTy.
  eapply BT_Comp.
  - eapply BT_Snd.
  - apply BT_Const.
Defined.

Definition RJ_pair_from_components : @b_tm Sign :=
  b_pair RJ_Romeo RJ_Juliet.

Lemma RJ_pair_from_components_typing :
  base_typing I RJ_pair_from_components RJ_PairTy.
Proof.
  unfold RJ_pair_from_components, RJ_PairTy.
  apply BT_Pair.
  - apply RJ_Romeo_typing.
  - apply RJ_Juliet_typing.
Defined.

Definition RJ_eps_subst : @b_tm Sign :=
  b_pair b_id RJ_eps_pair.

Lemma RJ_eps_subst_typing :
  base_typing I RJ_eps_subst (b_Prod I RJ_PairTy).
Proof.
  unfold RJ_eps_subst.
  apply BT_Pair.
  - apply BT_Id.
  - apply RJ_eps_pair_typing.
Defined.

(* Reads as [Loves (Romeo, Juliet)]. *)
Definition RJ_Loves_epsilon_pair : @h_ty Sign :=
  RJ_Loves_body .[ RJ_eps_pair ].

Lemma RJ_Loves_epsilon_pair_wf :
  WellFormed I RJ_Loves_epsilon_pair.
Proof.
  unfold RJ_Loves_epsilon_pair.
  eapply wf_subst.
  - apply RJ_eps_subst_typing.
  - apply RJ_Loves_body_wf.
Defined.

(* The explicit pair has the same intended reading; its base eta
   equivalence is outside this file. *)
Definition RJ_Loves_Romeo_Juliet_explicit : @h_ty Sign :=
  Ty_Atom loves RJ_pair_from_components.

Lemma RJ_Loves_Romeo_Juliet_explicit_wf :
  WellFormed I RJ_Loves_Romeo_Juliet_explicit.
Proof.
  unfold RJ_Loves_Romeo_Juliet_explicit.
  eapply WF_Atom.
  apply RJ_pair_from_components_typing.
Defined.

Lemma RJ_exists_love_equiv_epsilon_pair :
  form_equiv I RJ_Exists_Love RJ_Loves_epsilon_pair.
Proof.
  unfold RJ_Exists_Love, RJ_Loves_epsilon_pair.
  apply FE_Eps_Adjoint_Iso.
  exact RJ_Loves_body_wf.
Defined.

Definition RJ_if_love_then_Romeo_loves_Juliet : @h_ty Sign :=
  Ty_Arrow RJ_Exists_Love RJ_Loves_epsilon_pair.

Lemma RJ_if_love_then_Romeo_loves_Juliet_wf :
  WellFormed I RJ_if_love_then_Romeo_loves_Juliet.
Proof.
  unfold RJ_if_love_then_Romeo_loves_Juliet.
  apply WF_Arrow.
  - apply RJ_Exists_Love_wf.
  - apply RJ_Loves_epsilon_pair_wf.
Defined.

Definition RJ_if_love_then_Romeo_loves_Juliet_code : @h_tm Sign :=
  eps_choice_code I RJ_PairTy RJ_Loves_body.

Lemma RJ_if_love_then_Romeo_loves_Juliet_derivation :
  h_derivation I []
    RJ_if_love_then_Romeo_loves_Juliet_code
    RJ_if_love_then_Romeo_loves_Juliet.
Proof.
  unfold RJ_if_love_then_Romeo_loves_Juliet_code.
  unfold RJ_if_love_then_Romeo_loves_Juliet.
  unfold RJ_Exists_Love.
  unfold RJ_Loves_epsilon_pair.
  apply eps_choice_derivation.
  exact RJ_Loves_body_wf.
Defined.

(** The binary dual drinker formula:
    [exists z, (exists w, Loves w) -> Loves z]. *)
Definition RJ_DualDrinker_body : @h_ty Sign :=
  Ty_Arrow
    (form_subst b_fst RJ_Exists_Love)
    RJ_Loves_body.

Definition RJ_DualDrinker_Love : @h_ty Sign :=
  Ty_Ex RJ_PairTy RJ_DualDrinker_body.

Lemma RJ_DualDrinker_body_wf :
  WellFormed (b_Prod I RJ_PairTy) RJ_DualDrinker_body.
Proof.
  unfold RJ_DualDrinker_body.
  apply WF_Arrow.
  - eapply wf_subst.
    + apply BT_Fst.
    + apply RJ_Exists_Love_wf.
  - apply RJ_Loves_body_wf.
Defined.

Lemma RJ_DualDrinker_Love_wf :
  WellFormed I RJ_DualDrinker_Love.
Proof.
  unfold RJ_DualDrinker_Love.
  apply WF_Ex.
  apply RJ_DualDrinker_body_wf.
Defined.

(* The dual-drinker witness is the same epsilon-selected pair. *)
Definition RJ_DualDrinker_witness : @b_tm Sign :=
  RJ_eps_pair.

Definition RJ_DualDrinker_witness_code : @h_tm Sign :=
  tm_ex_intro
    RJ_DualDrinker_witness
    RJ_if_love_then_Romeo_loves_Juliet_code.

End Romeo_Juliet_Binary_Atom.
