(* theories/Logic/Hyper/Epsilon_Adjoint/Curvature.v *)

 (*  Proof-code level curvature for the epsilon syntax.

   IMPORTANT SEPARATION OF LEVELS
   ------------------------------
   - b_tm          : individual/base terms, e.g. epsilon_Phi.
   - h_tm          : object-language proof codes, e.g. f, g, K(f,g), id.
   - h_derivation  : Coq-level evidence that an h_tm proof code has a type.

   Curvature is defined on h_tm proof codes.
   h_derivation is used only to certify that those codes are well typed.

   This file deliberately does NOT import the completeness/term-model file.
*)

Require Import List.
Import ListNotations.

Require Import HyperLogic.Logic.Base.Epsilon_Adjoint.Base_Syntax.
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum.
Require Import HyperLogic.Logic.Hyper.Epsilon_Adjoint.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon_Adjoint.Hyper_Syntax_Lemmas.

Set Implicit Arguments.

Section Internal_Epsilon_Curvature.

Context {Sign : Type} `{SM : SkolemMapping Sign}.

(* ================================================================= *)
(* 1. Epsilon is an individual term                                  *)
(* ================================================================= *)

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

(* The existential formula and the epsilon instance. *)
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

(* ================================================================= *)
(* 2. Identity and composition as object-language proof codes         *)
(* ================================================================= *)

(* Object-language identity proof code:
      id_Phi := lambda x:Phi. x  : Phi -> Phi
   This is an h_tm, not a Coq equality proof. *)
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

(* Object-language composition of closed proof codes:
      comp(f,g) := lambda x. f (g x)
   If f : B -> C and g : A -> B, then comp(f,g) : A -> C. *)
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

  - (* f : B -> C, weakened from [] to [A] *)
    change (h_derivation I ([] ++ [A]) f (Ty_Arrow B C)).
    eapply (@h_derivation_append Sign SM
              I [] [A] f (Ty_Arrow B C)).
    + exact df.
    + constructor.
      * exact wfA.
      * constructor.

  - (* g x : B *)
    eapply HD_App with (Phi := A).

    + (* g : A -> B, weakened from [] to [A] *)
      change (h_derivation I ([] ++ [A]) g (Ty_Arrow A B)).
      eapply (@h_derivation_append Sign SM
                I [] [A] g (Ty_Arrow A B)).
      * exact dg.
      * constructor.
        -- exact wfA.
        -- constructor.

    + (* x : A *)
      apply HD_Var0.
      constructor.
      * exact wfA.
      * constructor.
Qed.
(* ================================================================= *)
(* 3. Curvature K(f,g) for proof codes f : A -> B and g : B -> A    *)
(* ================================================================= *)

(* Left holonomy / curvature component:
      K_left(f,g) = g o f : A -> A. *)
Definition K_left_code
  (A B : @h_ty Sign) (f g : @h_tm Sign) : @h_tm Sign :=
  h_comp_code A B A g f.

(* Right holonomy / curvature component:
      K_right(f,g) = f o g : B -> B. *)
Definition K_right_code
  (A B : @h_ty Sign) (f g : @h_tm Sign) : @h_tm Sign :=
  h_comp_code B A B f g.

(* The raw curvature is the pair of object-language endomorphism codes. *)
Definition K_code
  (A B : @h_ty Sign) (f g : @h_tm Sign) : (@h_tm Sign * @h_tm Sign)%type :=
  (K_left_code A B f g, K_right_code A B f g).

(* A typed bi-implication datum at the proof-code level. *)
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

(* ================================================================= *)
(* 4. The canonical epsilon bi-implication proof codes               *)
(* ================================================================= *)

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

(* f_Phi : exists y. Phi(y) -> Phi(epsilon_Phi)

   The body is supplied by ex_implies_eps from Hyper_Syntax_Lemmas. *)
Definition eps_choice_code
  (I A : b_ty) (Phi : @h_ty Sign) : @h_tm Sign :=
  tm_lam (ex_ty A Phi)
    (tm_ex_elim (tm_var 0) (tm_eps_intro b_snd (tm_var 0))).

(* g_Phi : Phi(epsilon_Phi) -> exists y. Phi(y)

   This is ordinary existential introduction with the individual term
   epsilon_Phi. *)
Definition eps_return_code
  (I A : b_ty) (Phi : @h_ty Sign) : @h_tm Sign :=
  tm_lam (eps_ty I A Phi)
    (tm_ex_intro (eps_ind A Phi) (tm_var 0)).

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

(* The two epsilon curvature proof codes. *)
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

(* ================================================================= *)
(* 5. Flatness                                                       *)
(* ================================================================= *)

(* Later you can instantiate this with the intended non-thin equality of
   proof codes: raw syntactic equality, beta-eta equality, normalization
   equality, proof-net equality, etc.

   The relation is typed: it compares p and q only after both have been
   certified as derivations of the same formula Phi in the same context. *)
Class ProofCodeEq : Type := {
  pc_eq : forall (I : b_ty) (G : @h_context Sign) (Phi : @h_ty Sign)
                 (p q : @h_tm Sign),
    h_derivation I G p Phi ->
    h_derivation I G q Phi ->
    Prop
}.

Class ProofCodeEqLaws `{ProofCodeEq} : Type := {
  pc_eq_refl : forall I G Phi p (dp : h_derivation I G p Phi),
    pc_eq
      (I := I) (G := G) (Phi := Phi)
      (p := p) (q := p)
      dp dp ;

  pc_eq_sym : forall I G Phi p q
                     (dp : h_derivation I G p Phi)
                     (dq : h_derivation I G q Phi),
    pc_eq
      (I := I) (G := G) (Phi := Phi)
      (p := p) (q := q)
      dp dq ->
    pc_eq
      (I := I) (G := G) (Phi := Phi)
      (p := q) (q := p)
      dq dp ;

  pc_eq_trans : forall I G Phi p q r
                       (dp : h_derivation I G p Phi)
                       (dq : h_derivation I G q Phi)
                       (dr : h_derivation I G r Phi),
    pc_eq
      (I := I) (G := G) (Phi := Phi)
      (p := p) (q := q)
      dp dq ->
    pc_eq
      (I := I) (G := G) (Phi := Phi)
      (p := q) (q := r)
      dq dr ->
    pc_eq
      (I := I) (G := G) (Phi := Phi)
      (p := p) (q := r)
      dp dr
}.

(* A typed bi-implication datum is flat iff its two holonomies are equal
   to the corresponding object-language identity proof codes. *)


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

Definition SystemFlat `{ProofCodeEq} : Prop :=
  forall (I Y : b_ty) (Phi : @h_ty Sign)
         (wfPhi : WellFormed (b_Prod I Y) Phi),
    FlatEpsilonDatum
      (I := I)
      (Y := Y)
      (Phi := Phi)
      wfPhi.
    
End Internal_Epsilon_Curvature.