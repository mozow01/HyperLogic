(* theories/Semantics/Metatheory/Pasquali_Epsilon.v *)

Require Import List.
Import ListNotations.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Fibration.

Require Import HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.
Require Import HyperLogic.Semantics.Epsilon.Epsilon_Fibration.
Require Import HyperLogic.Semantics.Epsilon.Epsilon_Soundness.

(* Reading guide for Pasquali 2016 and 2019:

   - Definition 2.1 introduces the typed epsilon calculus by the rules
     epsilon-form and epsilon-I.  In this development epsilon terms are stored
     as Skolem constants in the base syntax; the formula-level epsilon instance
     is [eps_instance].

   - Section 4 interprets substitution by pullback and quantifiers by
     adjoints to pullback.  The wrapper lemmas below name the corresponding
     facts already proved in [Epsilon_Soundness].

   - Definition 6.1 defines an epsilon-category by the condition
     Sigma_pi psi <= <id, epsilon_psi>^* psi.  In the indexed/fibrational
     presentation here this is represented by [eps_unit], and substitution
     along a witness gives [eps_intro].

   - Pasquali 2019, Definition 2.1 calls this "having enough epsilon terms":
     for every predicate psi over Gamma x A there is an epsilon map such that
     P(<id, epsilon_psi>)(psi) <= theta iff psi <= P(pi_Gamma)(theta).
     The lemma [pasquali_has_enough_epsilon_terms_semantic] proves this
     adjunction-style property from [EpsilonGoodFibration].

   - Proposition 6.2 is the soundness theorem for pointed interpretations of
     epsilon calculi.  The corresponding formal theorem is [soundness].

   - Definitions 3.4 and 3.5 isolate AC and wLEM; Propositions 6.3 and 6.4
     use regular epis, subobjects, AC and wLEM.  Those structures are not
     currently present in [Cat.Fibration], so they are good future targets
     rather than wrappers here.

   - Proposition 5.3 says projections between pointed objects have sections.
     The syntactic representative below is [pasquali_projection_section_term].

   - Section 7 says that product/unit/arrow/sum type constructors behave well
     for pointed objects, while an empty base type degenerates the semantics.
     Our base type language has unit, products and a distinguished sort, but
     no empty base type; [Ty_Void] is a logical formula, not a base type.

   - Section 8 compares epsilon-categories with Bell's Hilbertian toposes.
     That needs topos-specific structure not currently represented here.
*)

(* Pasquali 2016, Remark 2.2: every type becomes inhabited by an epsilon term
   obtained from the always-true formula.  Syntactically this is represented
   by the Skolem constant attached to [Ty_Unit]. *)
Definition pasquali_default_epsilon_term
  {Sign Func Pred : Type} `{SkolemMapping Sign Func Pred}
  (A : b_ty) : @b_tm Sign Func :=
  b_const A (skolem_index A (@Ty_Unit Sign Func Pred)).

Lemma pasquali_default_epsilon_term_typing :
  forall {Sign Func Pred : Type} {HFunc : FunctionSignature Func}
    {SM : SkolemMapping Sign Func Pred} (I A : b_ty),
  @base_typing Sign Func HFunc I
    (@pasquali_default_epsilon_term Sign Func Pred SM A) A.
Proof.
  intros Sign Func Pred HFunc SM I A.
  unfold pasquali_default_epsilon_term.
  apply BT_Const.
Defined.

(* Pasquali 2016, Proposition 5.3: in pointed objects, a projection has a
   section.  Syntactically, for the first projection I x A -> I, the section is
   <id_I, epsilon_A_top>. *)
Definition pasquali_projection_section_term
  {Sign Func Pred : Type} `{SkolemMapping Sign Func Pred}
  (I A : b_ty) : @b_tm Sign Func :=
  b_pair b_id (pasquali_default_epsilon_term A).

Lemma pasquali_projection_section_typing :
  forall {Sign Func Pred : Type} {HFunc : FunctionSignature Func}
    {SM : SkolemMapping Sign Func Pred} (I A : b_ty),
  @base_typing Sign Func HFunc I
    (@pasquali_projection_section_term Sign Func Pred SM I A)
    (b_Prod I A).
Proof.
  intros Sign Func Pred HFunc SM I A.
  unfold pasquali_projection_section_term.
  apply BT_Pair.
  - apply BT_Id.
  - apply pasquali_default_epsilon_term_typing.
Defined.

(* Pasquali 2016, Section 4, "Substitution": formula substitution is
   interpreted as pullback along the interpretation of the substituting term. *)
Lemma pasquali_formula_substitution_semantic :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred}
    {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
    {BEM : BaseEpsilonModel} {GF : GoodFibration C}
    {EHM : EpsilonHyperModel}
    (I A : b_ty) (f : @b_tm Sign Func) (df : base_typing I f A)
    (Phi : @h_ty Sign Func Pred),
  interp_h_ty I (form_subst f Phi) ≅O
  @fobj _ _ (Pullback (interp_tm df)) (interp_h_ty A Phi).
Proof.
  intros Sign Func Pred HFunc HPred C CC TSC BEM GF EHM I A f df Phi.
  apply form_subst_iso.
Defined.

(* Pasquali 2016, Section 4, "Quantifications": the displayed instance is the
   projection-substitution part used for quantification over a fresh variable. *)
Lemma pasquali_context_projection_substitution_semantic :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred}
    {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
    {BEM : BaseEpsilonModel} {GF : GoodFibration C}
    {EHM : EpsilonHyperModel}
    (I A : b_ty) (G : @h_context Sign Func Pred),
  interp_h_ctx (b_Prod I A) (ctx_subst b_fst G) ≅O
  @fobj _ _ (Pullback (interp_tm (BT_Fst (Sign:=Sign) (Func:=Func) (A:=I) (B:=A))))
    (interp_h_ctx I G).
Proof.
  intros Sign Func Pred HFunc HPred C CC TSC BEM GF EHM I A G.
  apply ctx_subst_iso.
Defined.

(* Pasquali 2016, Definition 2.1 and Definition 6.1: this is the formula
   obtained by substituting the epsilon term into the body.  It plays the role
   of "psi[epsilon x psi / x]" in the pure epsilon fragment. *)
Definition pasquali_eps_exists
  {Sign Func Pred : Type} `{SkolemMapping Sign Func Pred}
  (A : b_ty) (Phi : @h_ty Sign Func Pred) : @h_ty Sign Func Pred :=
  eps_instance A Phi.

(* Pasquali 2016, Definition 6.1: the epsilon-category condition
   Sigma_pi psi <= <id, epsilon_psi>^* psi, written in the fiber over
   Gamma x A.  By adjunction this is the semantic core of the transfinite
   axiom. *)
Lemma pasquali_epsilon_category_condition_semantic :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
    {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
    {BEM : BaseEpsilonModel} {GF : GoodFibration C}
    {EHM : EpsilonHyperModel} {EGF : EpsilonGoodFibration}
    (I A : b_ty) (Phi : @h_ty Sign Func Pred),
  WellFormed (b_Prod I A) Phi ->
  hom (interp_h_ty (b_Prod I A) Phi)
      (interp_h_ty (b_Prod I A) (form_subst b_fst (pasquali_eps_exists A Phi))).
Proof.
  intros Sign Func Pred HFunc HPred SM C CC TSC BEM GF EHM EGF I A Phi Hwf.
  apply eps_unit. exact Hwf.
Defined.

(* Pasquali 2019, Definition 2.1: "has enough epsilon terms".
   In order notation this says:

      P(<id, epsilon_phi>)(phi) <= theta
        iff
      phi <= P(pi_Gamma)(theta).

   Our fibers use morphisms for entailment.  The left side is the epsilon
   instance [pasquali_eps_exists A Phi]; the right side is the projection
   substitution [form_subst b_fst Theta]. *)
Class PasqualiEnoughEpsilonTerms
  {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} `{SkolemMapping Sign Func Pred}
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
  {BEM : BaseEpsilonModel} {GF : GoodFibration C}
  {EHM : EpsilonHyperModel} := {

  pasquali_enough_epsilon_terms :
    forall (I A : b_ty) (Phi Theta : @h_ty Sign Func Pred),
    WellFormed (b_Prod I A) Phi ->
    WellFormed I Theta ->
    ((hom (interp_h_ty I (pasquali_eps_exists A Phi))
          (interp_h_ty I Theta) ->
      hom (interp_h_ty (b_Prod I A) Phi)
          (interp_h_ty (b_Prod I A) (form_subst b_fst Theta))) *
     (hom (interp_h_ty (b_Prod I A) Phi)
          (interp_h_ty (b_Prod I A) (form_subst b_fst Theta)) ->
      hom (interp_h_ty I (pasquali_eps_exists A Phi))
          (interp_h_ty I Theta)))%type
}.

Instance PasqualiEnoughEpsilonTerms_from_EpsilonGoodFibration :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
    {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
    {BEM : BaseEpsilonModel} {GF : GoodFibration C}
    {EHM : EpsilonHyperModel} {EGF : EpsilonGoodFibration},
  PasqualiEnoughEpsilonTerms.
Proof.
  intros Sign Func Pred HFunc HPred SM C CC TSC BEM GF EHM EGF.
  constructor.
  intros I A Phi Theta HwfPhi HwfTheta.
  split.
  - intros H_eps_theta.
    eapply compose.
    + apply (@iso_from _ _ _
        (form_subst_iso (b_Prod I A) I b_fst
          (BT_Fst (Sign:=Sign) (Func:=Func) (A:=I) (B:=A)) Theta)).
    + eapply compose.
      * eapply (@fmap _ _ (Pullback (interp_tm
          (BT_Fst (Sign:=Sign) (Func:=Func) (A:=I) (B:=A)))) _ _).
        exact H_eps_theta.
      * eapply compose.
        -- apply (@iso_to _ _ _
             (form_subst_iso (b_Prod I A) I b_fst
               (BT_Fst (Sign:=Sign) (Func:=Func) (A:=I) (B:=A))
               (pasquali_eps_exists A Phi))).
        -- apply eps_unit. exact HwfPhi.
  - intros H_phi_theta.
    eapply compose.
    + apply (eps_elim_frobenius I A [] Phi Theta).
      * apply AWF_Nil.
      * exact HwfPhi.
      * exact HwfTheta.
      * eapply compose.
        -- exact H_phi_theta.
        -- apply prod_snd.
    + apply prod_map.
      * apply terminal_map.
      * apply id.
Defined.

Lemma pasquali_has_enough_epsilon_terms_semantic :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
    {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
    {BEM : BaseEpsilonModel} {GF : GoodFibration C}
    {EHM : EpsilonHyperModel} {PEET : PasqualiEnoughEpsilonTerms}
    (I A : b_ty) (Phi Theta : @h_ty Sign Func Pred),
  WellFormed (b_Prod I A) Phi ->
  WellFormed I Theta ->
  ((hom (interp_h_ty I (pasquali_eps_exists A Phi))
        (interp_h_ty I Theta) ->
    hom (interp_h_ty (b_Prod I A) Phi)
        (interp_h_ty (b_Prod I A) (form_subst b_fst Theta))) *
   (hom (interp_h_ty (b_Prod I A) Phi)
        (interp_h_ty (b_Prod I A) (form_subst b_fst Theta)) ->
    hom (interp_h_ty I (pasquali_eps_exists A Phi))
        (interp_h_ty I Theta)))%type.
Proof.
  intros Sign Func Pred HFunc HPred SM C CC TSC BEM GF EHM PEET
    I A Phi Theta HwfPhi HwfTheta.
  apply pasquali_enough_epsilon_terms; assumption.
Defined.

(* Pasquali 2016, Definition 2.1, epsilon-I, and Pasquali 2019, Lemma 2.4:
   after substituting an actual witness [f] into the body, epsilon-introduction
   transports the proof to the epsilon instance.  Since this fragment has no
   primitive existential formula, this is the witness-specialized form of the
   transfinite axiom. *)
Lemma pasquali_eps_intro_semantic :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
    {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
    {BEM : BaseEpsilonModel} {GF : GoodFibration C}
    {EHM : EpsilonHyperModel} {EGF : EpsilonGoodFibration}
    (I A : b_ty) (Phi : @h_ty Sign Func Pred) (f : @b_tm Sign Func),
  WellFormed (b_Prod I A) Phi ->
  base_typing I f A ->
  hom (interp_h_ty I (form_subst (b_pair b_id f) Phi))
      (interp_h_ty I (pasquali_eps_exists A Phi)).
Proof.
  intros Sign Func Pred HFunc HPred SM C CC TSC BEM GF EHM EGF
    I A Phi f Hwf df.
  apply eps_intro; assumption.
Defined.

(* Pasquali 2016, Definition 2.1, epsilon-E, and Pasquali 2019, Proposition
   2.5: epsilon substitution serves as existential quantification.  In this
   formalization the existential object is represented by [pasquali_eps_exists],
   and this is its elimination/Frobenius rule. *)
Lemma pasquali_eps_elim_semantic :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
    {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
    {BEM : BaseEpsilonModel} {GF : GoodFibration C}
    {EHM : EpsilonHyperModel} {EGF : EpsilonGoodFibration}
    (I A : b_ty) (G : @h_context Sign Func Pred) (Phi Chi : @h_ty Sign Func Pred),
  All_WellFormed I G ->
  WellFormed (b_Prod I A) Phi ->
  WellFormed I Chi ->
  hom (prod (interp_h_ctx (b_Prod I A) (ctx_subst b_fst G))
            (interp_h_ty (b_Prod I A) Phi))
      (interp_h_ty (b_Prod I A) (form_subst b_fst Chi)) ->
  hom (prod (interp_h_ctx I G) (interp_h_ty I (pasquali_eps_exists A Phi)))
      (interp_h_ty I Chi).
Proof.
  intros Sign Func Pred HFunc HPred SM C CC TSC BEM GF EHM EGF
    I A G Phi Chi HwfG HwfPhi HwfChi H.
  apply eps_elim_frobenius; assumption.
Defined.

(* Pasquali 2016, Definition 6.1: epsilon terms are attached to subobjects.
   This wrapper records that equivalent predicates give equivalent epsilon
   instances in the fiber. *)
Lemma pasquali_eps_functorial_semantic :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
    {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
    {BEM : BaseEpsilonModel} {GF : GoodFibration C}
    {EHM : EpsilonHyperModel} {EGF : EpsilonGoodFibration}
    (I A : b_ty) (Phi Psi : @h_ty Sign Func Pred),
  WellFormed (b_Prod I A) Phi ->
  WellFormed (b_Prod I A) Psi ->
  interp_h_ty (b_Prod I A) Phi ≅O interp_h_ty (b_Prod I A) Psi ->
  interp_h_ty I (pasquali_eps_exists A Phi) ≅O
  interp_h_ty I (pasquali_eps_exists A Psi).
Proof.
  intros Sign Func Pred HFunc HPred SM C CC TSC BEM GF EHM EGF I A Phi Psi WFPhi WFPsi Hiso.
  apply eps_functorial_iso; assumption.
Defined.

(* Pasquali 2016, Section 4 plus Definition 6.1: epsilon instances must be
   stable under change of context/substitution.  This is the indexed
   Beck-Chevalley form needed by the syntax rule [FE_Eps_BC]. *)
Lemma pasquali_eps_beck_chevalley :
  forall {Sign Func Pred : Type}
    `{FunctionSignature Func} `{PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
    {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
    {BEM : BaseEpsilonModel} {GF : GoodFibration C}
    {EHM : EpsilonHyperModel} {EGF : EpsilonGoodFibration}
    (I J A : b_ty) (g : @b_tm Sign Func) (dg : base_typing I g J)
    (Phi : @h_ty Sign Func Pred),
  WellFormed (b_Prod J A) Phi ->
  interp_h_ty I (pasquali_eps_exists A (form_subst (b_subst_ext g) Phi)) ≅O
  interp_h_ty I (form_subst g (pasquali_eps_exists A Phi)).
Proof.
  intros Sign Func Pred HFunc HPred SM C CC TSC BEM GF EHM EGF
    I J A g dg Phi Hwf.
  symmetry.
  exact (eps_beck_chevalley_iso I J A g dg Phi Hwf).
Defined.
