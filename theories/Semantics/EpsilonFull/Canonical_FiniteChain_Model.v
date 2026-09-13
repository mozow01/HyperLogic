(* Canonical epsilon-exists models over finite Heyting chains. *)

Require Import Coq.Lists.List.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.Morphisms.
Import ListNotations.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Fibration.
Require Import HyperLogic.Cat.EpsilonSelection.

Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Canonical_Skolem.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_Fibration.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_Soundness.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_ModelCategory.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_AllPredicates.
Require Import HyperLogic.Semantics.EpsilonFull.FiniteHeytingPredicates.

Module CFLabels :=
  HyperLogic.Logic.Hyper.EpsilonFull.Canonical_Skolem.CanonicalEpsilonFull.

Definition FHModelBase (A : b_ty) : b_ty :=
  @interp_ty FHBaseCategory FHBaseCartesian FHBaseTwoSort A.

Inductive FHRawValue : Type :=
| FHRUnit : FHRawValue
| FHRBool : bool -> FHRawValue
| FHRPair : FHRawValue -> FHRawValue -> FHRawValue.

Fixpoint FHEncode (A : b_ty) : fh_base_denote A -> FHRawValue :=
  match A return fh_base_denote A -> FHRawValue with
  | b_Unit => fun _ => FHRUnit
  | b_S => fun b => FHRBool b
  | b_Prod B C => fun xy => FHRPair (FHEncode B (fst xy)) (FHEncode C (snd xy))
  end.

Fixpoint FHDecode (A : b_ty) (v : FHRawValue) : option (fh_base_denote A) :=
  match A return option (fh_base_denote A) with
  | b_Unit =>
      match v with
      | FHRUnit => Some tt
      | _ => None
      end
  | b_S =>
      match v with
      | FHRBool b => Some b
      | _ => None
      end
  | b_Prod B C =>
      match v with
      | FHRPair x y =>
          match FHDecode B x, FHDecode C y with
          | Some b, Some c => Some (b, c)
          | _, _ => None
          end
      | _ => None
      end
  end.

Lemma FHDecode_encode : forall (A : b_ty) (x : fh_base_denote A),
  FHDecode A (FHEncode A x) = Some x.
Proof.
  induction A; intros x; cbn.
  - destruct x. reflexivity.
  - reflexivity.
  - destruct x as [x y]. rewrite IHA1, IHA2. reflexivity.
Defined.

Lemma FHEncode_injective : forall (A : b_ty) (x y : fh_base_denote A),
  FHEncode A x = FHEncode A y -> x = y.
Proof.
  intros A x y H.
  pose proof (f_equal (FHDecode A) H) as Hd.
  rewrite !FHDecode_encode in Hd. inversion Hd. reflexivity.
Defined.

Section CanonicalFiniteChainEvaluation.

Context `{FH : FiniteHeytingAlgebra}.
Context (Hchain : FiniteHeytingChain).
Context {Func Pred : Type}.
Context `{HFunc : FunctionSignature Func}.
Context `{HPred : PredicateSignature Pred}.

Variable function_value : forall f : Func,
  fh_base_denote (FHModelBase (func_dom f)) ->
  fh_base_denote (FHModelBase (func_cod f)).
Variable predicate_value : forall p : Pred,
  fh_base_denote (FHModelBase (pred_dom p)) -> fh_carrier.

Definition CFLabel := CFLabels.EpsilonLabel Func Pred.

(** These two evaluators expose every occurrence of a nested epsilon label.
    The callback may therefore be invoked only with a proof that the label
    occurs in the term or formula currently being traversed. *)
Fixpoint FHRawTermEvalBelow
  (t : @b_tm CFLabel Func)
  (choose : forall r : CFLabel,
    CFLabels.occurs_in_b_tm r t ->
    forall A : b_ty, FHRawValue -> fh_base_denote A)
  (env : FHRawValue) : option FHRawValue :=
  match t as t0 return
    (forall r : CFLabel, CFLabels.occurs_in_b_tm r t0 ->
      forall A : b_ty, FHRawValue -> fh_base_denote A) ->
    option FHRawValue
  with
  | b_id => fun _ => Some env
  | b_comp g f => fun ch =>
      match FHRawTermEvalBelow f
        (fun r Hr => ch r (CFLabels.occurs_b_comp_r r g f Hr)) env with
      | Some y => FHRawTermEvalBelow g
          (fun r Hr => ch r (CFLabels.occurs_b_comp_l r g f Hr)) y
      | None => None
      end
  | b_unit => fun _ => Some FHRUnit
  | b_pair f g => fun ch =>
      match
        FHRawTermEvalBelow f
          (fun r Hr => ch r (CFLabels.occurs_b_pair_l r f g Hr)) env,
        FHRawTermEvalBelow g
          (fun r Hr => ch r (CFLabels.occurs_b_pair_r r f g Hr)) env
      with
      | Some y, Some z => Some (FHRPair y z)
      | _, _ => None
      end
  | b_fst => fun _ =>
      match env with FHRPair y _ => Some y | _ => None end
  | b_snd => fun _ =>
      match env with FHRPair _ z => Some z | _ => None end
  | b_const A r => fun ch =>
      Some (FHEncode (FHModelBase A)
        (ch r (CFLabels.occurs_b_const r A) (FHModelBase A) env))
  | b_func f => fun _ =>
      match FHDecode (FHModelBase (func_dom f)) env with
      | Some x => Some (FHEncode (FHModelBase (func_cod f)) (function_value f x))
      | None => None
      end
  end choose.

Fixpoint FHFormulaEvalBelow
  (Phi : @h_ty CFLabel Func Pred)
  (choose : forall r : CFLabel,
    CFLabels.occurs_in_h_ty r Phi ->
    forall A : b_ty, FHRawValue -> fh_base_denote A)
  (env : FHRawValue) : fh_carrier :=
  match Phi as Phi0 return
    (forall r : CFLabel, CFLabels.occurs_in_h_ty r Phi0 ->
      forall A : b_ty, FHRawValue -> fh_base_denote A) -> fh_carrier
  with
  | Ty_Unit => fun _ => fh_top
  | Ty_Void => fun _ => fh_bot
  | Ty_Prod P Q => fun ch =>
      fh_meet
        (FHFormulaEvalBelow P
          (fun r Hr => ch r (CFLabels.occurs_h_prod_l r P Q Hr)) env)
        (FHFormulaEvalBelow Q
          (fun r Hr => ch r (CFLabels.occurs_h_prod_r r P Q Hr)) env)
  | Ty_Sum P Q => fun ch =>
      fh_join
        (FHFormulaEvalBelow P
          (fun r Hr => ch r (CFLabels.occurs_h_sum_l r P Q Hr)) env)
        (FHFormulaEvalBelow Q
          (fun r Hr => ch r (CFLabels.occurs_h_sum_r r P Q Hr)) env)
  | Ty_Arrow P Q => fun ch =>
      fh_impl
        (FHFormulaEvalBelow P
          (fun r Hr => ch r (CFLabels.occurs_h_arrow_l r P Q Hr)) env)
        (FHFormulaEvalBelow Q
          (fun r Hr => ch r (CFLabels.occurs_h_arrow_r r P Q Hr)) env)
  | Ty_Atom p t => fun ch =>
      match FHRawTermEvalBelow t
        (fun r Hr => ch r (CFLabels.occurs_h_atom r p t Hr)) env with
      | Some y =>
          match FHDecode (FHModelBase (pred_dom p)) y with
          | Some z => predicate_value p z
          | None => fh_top
          end
      | None => fh_top
      end
  | Ty_All A P => fun ch =>
      FHFiniteMeet (FHModelBase A) (fun a =>
        FHFormulaEvalBelow P
          (fun r Hr => ch r (CFLabels.occurs_h_all r A P Hr))
          (FHRPair env (FHEncode (FHModelBase A) a)))
  | Ty_Ex A P => fun ch =>
      FHFiniteJoin (FHModelBase A) (fun a =>
        FHFormulaEvalBelow P
          (fun r Hr => ch r (CFLabels.occurs_h_ex r A P Hr))
          (FHRPair env (FHEncode (FHModelBase A) a)))
  end choose.

Lemma FHFiniteJoin_ext : forall (A : b_ty)
  (P Q : fh_base_denote A -> fh_carrier),
  (forall a, P a = Q a) -> FHFiniteJoin A P = FHFiniteJoin A Q.
Proof.
  induction A; intros P Q Heq; cbn.
  - apply Heq.
  - rewrite (Heq true), (Heq false). reflexivity.
  - apply IHA1. intro a. apply IHA2. intro b. apply Heq.
Defined.

Lemma FHFiniteMeet_ext : forall (A : b_ty)
  (P Q : fh_base_denote A -> fh_carrier),
  (forall a, P a = Q a) -> FHFiniteMeet A P = FHFiniteMeet A Q.
Proof.
  induction A; intros P Q Heq; cbn.
  - apply Heq.
  - rewrite (Heq true), (Heq false). reflexivity.
  - apply IHA1. intro a. apply IHA2. intro b. apply Heq.
Defined.

Lemma FHArgmax_ext : forall (A : b_ty)
  (P Q : fh_base_denote A -> fh_carrier),
  (forall a, P a = Q a) -> FHArgmax A P = FHArgmax A Q.
Proof.
  induction A; intros P Q Heq; cbn.
  - reflexivity.
  - rewrite (Heq true), (Heq false). reflexivity.
  - assert (Houter :
      FHArgmax A1 (fun a => FHFiniteJoin A2 (fun b => P (a, b))) =
      FHArgmax A1 (fun a => FHFiniteJoin A2 (fun b => Q (a, b)))).
    {
      apply IHA1. intro a. apply FHFiniteJoin_ext. intro b. apply Heq.
    }
    destruct Houter.
    f_equal. apply IHA2. intro b. apply Heq.
Defined.

Lemma FHRawTermEvalBelow_ext : forall (t : @b_tm CFLabel Func)
  (c1 c2 : forall r : CFLabel,
    CFLabels.occurs_in_b_tm r t ->
    forall A : b_ty, FHRawValue -> fh_base_denote A),
  (forall r Hr A env, c1 r Hr A env = c2 r Hr A env) ->
  forall env, FHRawTermEvalBelow t c1 env = FHRawTermEvalBelow t c2 env.
Proof.
  induction t; intros c1 c2 Hc env; cbn.
  - reflexivity.
  - rewrite (IHt2
      (fun r Hr => c1 r (CFLabels.occurs_b_comp_r r t1 t2 Hr))
      (fun r Hr => c2 r (CFLabels.occurs_b_comp_r r t1 t2 Hr))).
    + destruct (FHRawTermEvalBelow t2
        (fun r Hr => c2 r (CFLabels.occurs_b_comp_r r t1 t2 Hr)) env);
        [apply IHt1 | reflexivity].
      intros. apply Hc.
    + intros. apply Hc.
  - reflexivity.
  - rewrite (IHt1
      (fun r Hr => c1 r (CFLabels.occurs_b_pair_l r t1 t2 Hr))
      (fun r Hr => c2 r (CFLabels.occurs_b_pair_l r t1 t2 Hr))).
    + rewrite (IHt2
        (fun r Hr => c1 r (CFLabels.occurs_b_pair_r r t1 t2 Hr))
        (fun r Hr => c2 r (CFLabels.occurs_b_pair_r r t1 t2 Hr))).
      * reflexivity.
      * intros. apply Hc.
    + intros. apply Hc.
  - reflexivity.
  - reflexivity.
  - f_equal. f_equal. apply Hc.
  - reflexivity.
Defined.

Lemma FHFormulaEvalBelow_ext : forall (Phi : @h_ty CFLabel Func Pred)
  (c1 c2 : forall r : CFLabel,
    CFLabels.occurs_in_h_ty r Phi ->
    forall A : b_ty, FHRawValue -> fh_base_denote A),
  (forall r Hr A env, c1 r Hr A env = c2 r Hr A env) ->
  forall env, FHFormulaEvalBelow Phi c1 env = FHFormulaEvalBelow Phi c2 env.
Proof.
  induction Phi; intros c1 c2 Hc env; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite (IHPhi1
      (fun r Hr => c1 r (CFLabels.occurs_h_prod_l r Phi1 Phi2 Hr))
      (fun r Hr => c2 r (CFLabels.occurs_h_prod_l r Phi1 Phi2 Hr))).
    + rewrite (IHPhi2
        (fun r Hr => c1 r (CFLabels.occurs_h_prod_r r Phi1 Phi2 Hr))
        (fun r Hr => c2 r (CFLabels.occurs_h_prod_r r Phi1 Phi2 Hr))).
      * reflexivity.
      * intros. apply Hc.
    + intros. apply Hc.
  - rewrite (IHPhi1
      (fun r Hr => c1 r (CFLabels.occurs_h_sum_l r Phi1 Phi2 Hr))
      (fun r Hr => c2 r (CFLabels.occurs_h_sum_l r Phi1 Phi2 Hr))).
    + rewrite (IHPhi2
        (fun r Hr => c1 r (CFLabels.occurs_h_sum_r r Phi1 Phi2 Hr))
        (fun r Hr => c2 r (CFLabels.occurs_h_sum_r r Phi1 Phi2 Hr))).
      * reflexivity.
      * intros. apply Hc.
    + intros. apply Hc.
  - rewrite (IHPhi1
      (fun r Hr => c1 r (CFLabels.occurs_h_arrow_l r Phi1 Phi2 Hr))
      (fun r Hr => c2 r (CFLabels.occurs_h_arrow_l r Phi1 Phi2 Hr))).
    + rewrite (IHPhi2
        (fun r Hr => c1 r (CFLabels.occurs_h_arrow_r r Phi1 Phi2 Hr))
        (fun r Hr => c2 r (CFLabels.occurs_h_arrow_r r Phi1 Phi2 Hr))).
      * reflexivity.
      * intros. apply Hc.
    + intros. apply Hc.
  - rewrite (FHRawTermEvalBelow_ext b
      (fun r Hr => c1 r (CFLabels.occurs_h_atom r p b Hr))
      (fun r Hr => c2 r (CFLabels.occurs_h_atom r p b Hr))).
    + reflexivity.
    + intros. apply Hc.
  - apply FHFiniteMeet_ext. intro a.
    apply IHPhi. intros. apply Hc.
  - apply FHFiniteJoin_ext. intro a.
    apply IHPhi. intros. apply Hc.
Defined.

Record FHChoiceState : Type := mk_FHChoiceState {
  fh_choice_label : CFLabel;
  fh_choice_type : b_ty;
  fh_choice_environment : FHRawValue
}.

Definition FHChoiceMeasure (st : FHChoiceState) : nat :=
  CFLabels.epsilon_rank (fh_choice_label st).

Definition FHChoiceRel : FHChoiceState -> FHChoiceState -> Prop :=
  fun smaller larger =>
    CFLabels.immediate_dependency
      (fh_choice_label smaller) (fh_choice_label larger).

Definition FHChoiceRel_wf : well_founded FHChoiceRel :=
  @wf_inverse_image FHChoiceState CFLabel CFLabels.immediate_dependency
    fh_choice_label CFLabels.immediate_dependency_well_founded.

Definition FHChoiceResult (st : FHChoiceState) : Type :=
  fh_base_denote (fh_choice_type st).

Definition FHCanonicalChoiceBody
  (st : FHChoiceState)
  (rec : forall smaller : FHChoiceState,
    FHChoiceRel smaller st -> FHChoiceResult smaller) : FHChoiceResult st.
Proof.
  destruct st as [s A env].
  destruct s as [D Phi]. cbn [FHChoiceResult].
  refine (FHArgmax A (fun a =>
    FHFormulaEvalBelow Phi _ (FHRPair env (FHEncode A a)))).
  intros r Hr B nested_env.
  exact (rec (mk_FHChoiceState r B nested_env) Hr).
Defined.

Definition FHCanonicalChoiceState (st : FHChoiceState) : FHChoiceResult st :=
  Fix FHChoiceRel_wf FHChoiceResult FHCanonicalChoiceBody st.

Definition FHCanonicalChoice (s : CFLabel) (A : b_ty)
  (env : FHRawValue) : fh_base_denote A :=
  FHCanonicalChoiceState (mk_FHChoiceState s A env).

Lemma FHCanonicalChoiceBody_ext :
  forall (st : FHChoiceState)
    (f g : forall smaller : FHChoiceState,
      FHChoiceRel smaller st -> FHChoiceResult smaller),
  (forall smaller p, f smaller p = g smaller p) ->
  FHCanonicalChoiceBody st f = FHCanonicalChoiceBody st g.
Proof.
  intros [s A env] f g Hfg. destruct s as [D Phi]. cbn.
  apply FHArgmax_ext. intro a.
  apply FHFormulaEvalBelow_ext. intros r Hr B nested_env.
  pose proof (Hfg (mk_FHChoiceState r B nested_env) Hr) as Heq.
  exact Heq.
Defined.

Lemma FHCanonicalChoiceState_unfold : forall st,
  FHCanonicalChoiceState st =
  FHCanonicalChoiceBody st
    (fun smaller _ => FHCanonicalChoiceState smaller).
Proof.
  intro st. unfold FHCanonicalChoiceState.
  apply Fix_eq. exact FHCanonicalChoiceBody_ext.
Defined.

Fixpoint FHCanonicalRawTermEval
  (t : @b_tm CFLabel Func) (env : FHRawValue) : option FHRawValue :=
  match t with
  | b_id => Some env
  | b_comp g f =>
      match FHCanonicalRawTermEval f env with
      | Some y => FHCanonicalRawTermEval g y
      | None => None
      end
  | b_unit => Some FHRUnit
  | b_pair f g =>
      match FHCanonicalRawTermEval f env, FHCanonicalRawTermEval g env with
      | Some y, Some z => Some (FHRPair y z)
      | _, _ => None
      end
  | b_fst => match env with FHRPair y _ => Some y | _ => None end
  | b_snd => match env with FHRPair _ z => Some z | _ => None end
  | b_const A r =>
      Some (FHEncode (FHModelBase A)
        (FHCanonicalChoice r (FHModelBase A) env))
  | b_func f =>
      match FHDecode (FHModelBase (func_dom f)) env with
      | Some x => Some (FHEncode (FHModelBase (func_cod f)) (function_value f x))
      | None => None
      end
  end.

Fixpoint FHCanonicalFormulaEval
  (Phi : @h_ty CFLabel Func Pred) (env : FHRawValue) : fh_carrier :=
  match Phi with
  | Ty_Unit => fh_top
  | Ty_Void => fh_bot
  | Ty_Prod P Q =>
      fh_meet (FHCanonicalFormulaEval P env) (FHCanonicalFormulaEval Q env)
  | Ty_Sum P Q =>
      fh_join (FHCanonicalFormulaEval P env) (FHCanonicalFormulaEval Q env)
  | Ty_Arrow P Q =>
      fh_impl (FHCanonicalFormulaEval P env) (FHCanonicalFormulaEval Q env)
  | Ty_Atom p t =>
      match FHCanonicalRawTermEval t env with
      | Some y =>
          match FHDecode (FHModelBase (pred_dom p)) y with
          | Some z => predicate_value p z
          | None => fh_top
          end
      | None => fh_top
      end
  | Ty_All A P =>
      FHFiniteMeet (FHModelBase A) (fun a =>
        FHCanonicalFormulaEval P
          (FHRPair env (FHEncode (FHModelBase A) a)))
  | Ty_Ex A P =>
      FHFiniteJoin (FHModelBase A) (fun a =>
        FHCanonicalFormulaEval P
          (FHRPair env (FHEncode (FHModelBase A) a)))
  end.

Lemma FHRawTermEvalBelow_canonical :
  forall (t : @b_tm CFLabel Func) env,
  FHRawTermEvalBelow t
    (fun r _ A nested_env => FHCanonicalChoice r A nested_env) env =
  FHCanonicalRawTermEval t env.
Proof.
  induction t; intro env; cbn.
  - reflexivity.
  - rewrite IHt2.
    destruct (FHCanonicalRawTermEval t2 env); [apply IHt1 | reflexivity].
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

Lemma FHFormulaEvalBelow_canonical :
  forall (Phi : @h_ty CFLabel Func Pred) env,
  FHFormulaEvalBelow Phi
    (fun r _ A nested_env => FHCanonicalChoice r A nested_env) env =
  FHCanonicalFormulaEval Phi env.
Proof.
  induction Phi; intro env; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite IHPhi1, IHPhi2. reflexivity.
  - rewrite IHPhi1, IHPhi2. reflexivity.
  - rewrite IHPhi1, IHPhi2. reflexivity.
  - rewrite FHRawTermEvalBelow_canonical. reflexivity.
  - apply FHFiniteMeet_ext. intro a. apply IHPhi.
  - apply FHFiniteJoin_ext. intro a. apply IHPhi.
Defined.

Lemma FHCanonicalChoice_unfold :
  forall (D A : b_ty) (Phi : @h_ty CFLabel Func Pred) env,
  FHCanonicalChoice (CFLabels.epsilon_label D Phi) A env =
  FHArgmax A (fun a =>
    FHCanonicalFormulaEval Phi (FHRPair env (FHEncode A a))).
Proof.
  intros D A Phi env.
  unfold FHCanonicalChoice.
  rewrite FHCanonicalChoiceState_unfold.
  cbn [FHCanonicalChoiceBody].
  apply FHArgmax_ext. intro a.
  apply FHFormulaEvalBelow_canonical.
Defined.

Theorem FHCanonicalChoice_uses_lower_rank :
  forall (D : b_ty) (Phi : @h_ty CFLabel Func Pred) r,
  CFLabels.occurs_in_h_ty r Phi ->
  CFLabels.epsilon_rank r <
    CFLabels.epsilon_rank (CFLabels.epsilon_label D Phi).
Proof.
  exact CFLabels.generated_label_has_greater_rank.
Defined.

End CanonicalFiniteChainEvaluation.

Section CanonicalFiniteChainModel.

Context `{FH : FiniteHeytingAlgebra}.
Context (Hchain : FiniteHeytingChain).
Context {Func Pred : Type}.
Context `{HFunc : FunctionSignature Func}.
Context `{HPred : PredicateSignature Pred}.

Variable function_value : forall f : Func,
  fh_base_denote (FHModelBase (func_dom f)) ->
  fh_base_denote (FHModelBase (func_cod f)).
Variable predicate_value : forall p : Pred,
  fh_base_denote (FHModelBase (pred_dom p)) -> fh_carrier.

Local Notation Label := (CFLabel (Func:=Func) (Pred:=Pred)).

Definition FHCanonicalBaseEpsilonFullModel :
  @BaseEpsilonFullModel Label Func HFunc
    FHBaseCategory FHBaseCartesian FHBaseTwoSort.
Proof.
  refine {|
    i_const := fun I A s x =>
      FHCanonicalChoice function_value predicate_value s (FHModelBase A)
        (FHEncode (FHModelBase I) x);
    i_func := function_value
  |}.
Defined.

Lemma FHCanonicalRawTerm_typed :
  forall {I A : b_ty} {t : @b_tm Label Func}
    (d : @base_typing Label Func HFunc I t A)
    (env : fh_base_denote (FHModelBase I)),
  FHCanonicalRawTermEval function_value predicate_value t
    (FHEncode (FHModelBase I) env) =
  Some (FHEncode (FHModelBase A)
    (@interp_tm Label Func HFunc
      FHBaseCategory FHBaseCartesian FHBaseTwoSort
      FHCanonicalBaseEpsilonFullModel I A t d env)).
Proof.
  intros I A t d. induction d; intro env; cbn
    [FHCanonicalRawTermEval FHRawTermEvalBelow
     FHCanonicalBaseEpsilonFullModel].
  - reflexivity.
  - rewrite (IHd2 env), (IHd1
      (@interp_tm Label Func HFunc
        FHBaseCategory FHBaseCartesian FHBaseTwoSort
        FHCanonicalBaseEpsilonFullModel _ _ _ d2 env)).
    reflexivity.
  - reflexivity.
  - rewrite (IHd1 env), (IHd2 env). reflexivity.
  - destruct env. reflexivity.
  - destruct env. reflexivity.
  - reflexivity.
  - rewrite FHDecode_encode. reflexivity.
Defined.

Lemma FHCanonicalRawTerm_equiv :
  forall {I A : b_ty} {t1 t2 : @b_tm Label Func}
    {d1 : @base_typing Label Func HFunc I t1 A}
    {d2 : @base_typing Label Func HFunc I t2 A},
  @base_equiv Label Func HFunc I A t1 t2 d1 d2 ->
  forall env : fh_base_denote (FHModelBase I),
    FHCanonicalRawTermEval function_value predicate_value t1
      (FHEncode (FHModelBase I) env) =
    FHCanonicalRawTermEval function_value predicate_value t2
      (FHEncode (FHModelBase I) env).
Proof.
  intros I A t1 t2 d1 d2 Heq.
  induction Heq; intro env; cbn [FHCanonicalRawTermEval FHRawTermEvalBelow].
  - reflexivity.
  - symmetry. apply IHHeq.
  - etransitivity; [apply IHHeq1 | apply IHHeq2].
  - rewrite (IHHeq1 env).
    rewrite (FHCanonicalRawTerm_typed df' env).
    apply IHHeq2.
  - rewrite (IHHeq1 env), (IHHeq2 env). reflexivity.
  - destruct (FHCanonicalRawTermEval function_value predicate_value f
      (FHEncode (FHModelBase A) env));
      [destruct (FHCanonicalRawTermEval function_value predicate_value g f0)
      |]; reflexivity.
  - rewrite (FHCanonicalRawTerm_typed df env). reflexivity.
  - reflexivity.
  - rewrite (FHCanonicalRawTerm_typed df env).
    rewrite (FHCanonicalRawTerm_typed dg env). reflexivity.
  - rewrite (FHCanonicalRawTerm_typed df env).
    rewrite (FHCanonicalRawTerm_typed dg env). reflexivity.
  - rewrite (FHCanonicalRawTerm_typed dh env).
    destruct (@interp_tm Label Func HFunc
      FHBaseCategory FHBaseCartesian FHBaseTwoSort
      FHCanonicalBaseEpsilonFullModel
      A (b_Prod B C) h dh env). reflexivity.
  - rewrite (FHCanonicalRawTerm_typed df env). reflexivity.
  - destruct (FHCanonicalRawTermEval function_value predicate_value h
      (FHEncode (FHModelBase A) env)); reflexivity.
Defined.

Lemma FHCanonicalConst_interp :
  forall (I A : b_ty) (s : Label)
    (env : fh_base_denote (FHModelBase I)),
  @interp_tm Label Func HFunc
    FHBaseCategory FHBaseCartesian FHBaseTwoSort
    FHCanonicalBaseEpsilonFullModel I A (b_const A s) BT_Const env =
  FHCanonicalChoice function_value predicate_value s (FHModelBase A)
    (FHEncode (FHModelBase I) env).
Proof.
  intros I A s env.
  pose proof (FHCanonicalRawTerm_typed
    (@BT_Const Label Func HFunc I A s) env) as Hraw.
  cbn [FHCanonicalRawTermEval] in Hraw.
  pose proof (f_equal
    (fun o => match o with Some x => x | None => FHRUnit end) Hraw) as Henc.
  cbn in Henc.
  symmetry. apply FHEncode_injective. exact Henc.
Defined.

Global Instance FHCanonicalCoherentBaseModel :
  @CoherentBaseModel Label Func HFunc
    FHBaseCategory FHBaseCartesian FHBaseTwoSort
    FHCanonicalBaseEpsilonFullModel.
Proof.
  constructor. intros I A t d1 d2.
  cbn [FHBaseCategory FHBaseHomEquiv].
  intro env.
  pose proof (FHCanonicalRawTerm_typed d1 env) as H1.
  pose proof (FHCanonicalRawTerm_typed d2 env) as H2.
  rewrite H1 in H2.
  inversion H2. apply FHEncode_injective. assumption.
Defined.

Definition FHCanonicalAtom (p : Pred) (t : @b_tm Label Func) (I : b_ty) :
  FHPredicate (FHModelBase I) := fun env =>
  match FHCanonicalRawTermEval function_value predicate_value t
    (FHEncode (FHModelBase I) env) with
  | Some raw =>
      match FHDecode (FHModelBase (pred_dom p)) raw with
      | Some value => predicate_value p value
      | None => fh_top
      end
  | None => fh_top
  end.

(** This statement quantifies over raw [t], including ill-typed atom codes.
    Both failure branches are interpreted by top. *)
Lemma FHCanonicalAtom_pullback_all_raw :
  forall (p : Pred) (t : @b_tm Label Func)
    (I A : b_ty) (f : @b_tm Label Func)
    (df : @base_typing Label Func HFunc I f A) env,
  FHCanonicalAtom p t A
    (@interp_tm Label Func HFunc
      FHBaseCategory FHBaseCartesian FHBaseTwoSort
      FHCanonicalBaseEpsilonFullModel I A f df env) =
  FHCanonicalAtom p (b_comp t f) I env.
Proof.
  intros p t I A f df env.
  unfold FHCanonicalAtom. cbn [FHCanonicalRawTermEval FHRawTermEvalBelow].
  rewrite (FHCanonicalRawTerm_typed df env). reflexivity.
Defined.

Lemma FHCanonicalAtom_equiv :
  forall (p : Pred) (I A : b_ty) (t1 t2 : @b_tm Label Func)
    (d1 : @base_typing Label Func HFunc I t1 A)
    (d2 : @base_typing Label Func HFunc I t2 A),
  @base_equiv Label Func HFunc I A t1 t2 d1 d2 ->
  forall env, FHCanonicalAtom p t1 I env = FHCanonicalAtom p t2 I env.
Proof.
  intros p I A t1 t2 d1 d2 Heq env.
  unfold FHCanonicalAtom.
  rewrite (FHCanonicalRawTerm_equiv Heq env). reflexivity.
Defined.

Global Instance FHCanonicalEpsilonHyperModel :
  @EpsilonHyperModel Label Func Pred HFunc HPred
    FHBaseCategory FHBaseCartesian FHBaseTwoSort
    FHCanonicalBaseEpsilonFullModel FHGoodFibration.
Proof.
  unshelve econstructor.
  - exact FHCanonicalAtom.
  - intros p t I A f df.
    apply FHPredicateIsoOfPointwiseEq. intro env.
    apply FHCanonicalAtom_pullback_all_raw.
  - intros p I A t1 t2 d1 d2 Heq.
    apply FHPredicateIsoOfPointwiseEq. intro env.
    apply FHCanonicalAtom_equiv with (d1 := d1) (d2 := d2). exact Heq.
Defined.

Lemma FHCanonicalFormula_interp :
  forall (I : b_ty) (Phi : @h_ty Label Func Pred)
    (env : fh_base_denote (FHModelBase I)),
  FHPredicateValue
    (@interp_h_ty Label Func Pred HFunc HPred
      FHBaseCategory FHBaseCartesian FHBaseTwoSort
      FHCanonicalBaseEpsilonFullModel FHGoodFibration
      FHCanonicalEpsilonHyperModel I Phi) env =
  FHCanonicalFormulaEval function_value predicate_value Phi
    (FHEncode (FHModelBase I) env).
Proof.
  intros I Phi. revert I.
  induction Phi; intros I env; cbn
    [interp_h_ty FHCanonicalFormulaEval FHFormulaEvalBelow FHCanonicalAtom
     FHPredicateValue FHPredicateCategory FHPredicateCartesian
     FHPredicateClosed FHPredicateBiClosed Build_Thin_CC Build_Thin_CCC
     Build_Thin_BiCCC FHGoodFibration GF_Fiber_CC GF_Fiber_CCC
     GF_Fiber_BCCC
     FHProjectionPullbackRightAdjoint FHProjectionPullbackLeftAdjoint
     FHSigma FHPi].
  - reflexivity.
  - reflexivity.
  - change (FHPredicateValue
      (@prod (FHPredicateCategory (FHModelBase I))
        (FHPredicateCartesian (FHModelBase I))
        (@interp_h_ty Label Func Pred HFunc HPred
        FHBaseCategory FHBaseCartesian FHBaseTwoSort
        FHCanonicalBaseEpsilonFullModel FHGoodFibration
        FHCanonicalEpsilonHyperModel I Phi1)
        (@interp_h_ty Label Func Pred HFunc HPred
        FHBaseCategory FHBaseCartesian FHBaseTwoSort
        FHCanonicalBaseEpsilonFullModel FHGoodFibration
        FHCanonicalEpsilonHyperModel I Phi2)) env =
      fh_meet
        (FHCanonicalFormulaEval function_value predicate_value Phi1
          (FHEncode (FHModelBase I) env))
        (FHCanonicalFormulaEval function_value predicate_value Phi2
          (FHEncode (FHModelBase I) env))).
    rewrite FHPredicateProduct_value.
    f_equal.
    + exact (IHPhi1 I env).
    + exact (IHPhi2 I env).
  - change (FHPredicateValue
      (@coprod (FHPredicateCategory (FHModelBase I))
        (FHPredicateCartesian (FHModelBase I))
        (FHPredicateClosed (FHModelBase I))
        (FHPredicateBiClosed (FHModelBase I))
        (@interp_h_ty Label Func Pred HFunc HPred
        FHBaseCategory FHBaseCartesian FHBaseTwoSort
        FHCanonicalBaseEpsilonFullModel FHGoodFibration
        FHCanonicalEpsilonHyperModel I Phi1)
        (@interp_h_ty Label Func Pred HFunc HPred
        FHBaseCategory FHBaseCartesian FHBaseTwoSort
        FHCanonicalBaseEpsilonFullModel FHGoodFibration
        FHCanonicalEpsilonHyperModel I Phi2)) env =
      fh_join
        (FHCanonicalFormulaEval function_value predicate_value Phi1
          (FHEncode (FHModelBase I) env))
        (FHCanonicalFormulaEval function_value predicate_value Phi2
          (FHEncode (FHModelBase I) env))).
    rewrite FHPredicateCoproduct_value.
    f_equal.
    + exact (IHPhi1 I env).
    + exact (IHPhi2 I env).
  - change (FHPredicateValue
      (@exp (FHPredicateCategory (FHModelBase I))
        (FHPredicateCartesian (FHModelBase I))
        (FHPredicateClosed (FHModelBase I))
        (@interp_h_ty Label Func Pred HFunc HPred
        FHBaseCategory FHBaseCartesian FHBaseTwoSort
        FHCanonicalBaseEpsilonFullModel FHGoodFibration
        FHCanonicalEpsilonHyperModel I Phi2)
        (@interp_h_ty Label Func Pred HFunc HPred
        FHBaseCategory FHBaseCartesian FHBaseTwoSort
        FHCanonicalBaseEpsilonFullModel FHGoodFibration
        FHCanonicalEpsilonHyperModel I Phi1)) env =
      fh_impl
        (FHCanonicalFormulaEval function_value predicate_value Phi1
          (FHEncode (FHModelBase I) env))
        (FHCanonicalFormulaEval function_value predicate_value Phi2
          (FHEncode (FHModelBase I) env))).
    rewrite FHPredicateExponential_value.
    f_equal.
    + exact (IHPhi1 I env).
    + exact (IHPhi2 I env).
  - reflexivity.
  - apply FHFiniteMeet_ext. intro a.
    exact (IHPhi (b_Prod I b) (env, a)).
  - apply FHFiniteJoin_ext. intro a.
    exact (IHPhi (b_Prod I b) (env, a)).
Defined.

Lemma FHCanonicalEpsilon_pointwise_maximum :
  forall (I A : b_ty) (Phi : @h_ty Label Func Pred),
  FHPointwiseMaximum (FHModelBase I) (FHModelBase A)
    (@interp_h_ty Label Func Pred HFunc HPred
      FHBaseCategory FHBaseCartesian FHBaseTwoSort
      FHCanonicalBaseEpsilonFullModel FHGoodFibration
      FHCanonicalEpsilonHyperModel (b_Prod I A) Phi)
    (@interp_tm Label Func HFunc
      FHBaseCategory FHBaseCartesian FHBaseTwoSort
      FHCanonicalBaseEpsilonFullModel I A
      (b_const A (CFLabels.epsilon_label A Phi)) BT_Const).
Proof.
  intros I A Phi env. cbn [FHCanonicalBaseEpsilonFullModel].
  transitivity
    (FHPredicateValue
      (@interp_h_ty Label Func Pred HFunc HPred
        FHBaseCategory FHBaseCartesian FHBaseTwoSort
        FHCanonicalBaseEpsilonFullModel FHGoodFibration
        FHCanonicalEpsilonHyperModel (b_Prod I A) Phi)
      (env, FHCanonicalChoice function_value predicate_value
        (CFLabels.epsilon_label A Phi) (FHModelBase A)
        (FHEncode (FHModelBase I) env))).
  - apply f_equal. f_equal.
  - transitivity
      (FHCanonicalFormulaEval function_value predicate_value Phi
        (FHRPair (FHEncode (FHModelBase I) env)
          (FHEncode (FHModelBase A)
            (FHCanonicalChoice function_value predicate_value
              (CFLabels.epsilon_label A Phi) (FHModelBase A)
              (FHEncode (FHModelBase I) env))))).
    + exact (FHCanonicalFormula_interp (b_Prod I A) Phi
        (env, FHCanonicalChoice function_value predicate_value
          (CFLabels.epsilon_label A Phi) (FHModelBase A)
          (FHEncode (FHModelBase I) env))).
    + rewrite (FHCanonicalChoice_unfold function_value predicate_value A
        (FHModelBase A) Phi (FHEncode (FHModelBase I) env)).
      transitivity (FHFiniteJoin (FHModelBase A)
        (fun a => FHCanonicalFormulaEval function_value predicate_value Phi
          (FHRPair (FHEncode (FHModelBase I) env)
            (FHEncode (FHModelBase A) a)))).
      * exact (FHArgmax_spec Hchain (FHModelBase A)
          (fun a => FHCanonicalFormulaEval function_value predicate_value Phi
            (FHRPair (FHEncode (FHModelBase I) env)
              (FHEncode (FHModelBase A) a)))).
      * apply FHFiniteJoin_ext. intro a. symmetry.
        exact (FHCanonicalFormula_interp (b_Prod I A) Phi (env, a)).
Defined.

Global Instance FHCanonicalAdjointEpsilonFullFibration :
  @AdjointEpsilonFullFibration Label Func Pred HFunc HPred
    (CFLabels.CanonicalSkolemMapping Func Pred)
    FHBaseCategory FHBaseCartesian FHBaseTwoSort
    FHCanonicalBaseEpsilonFullModel FHGoodFibration
    FHCanonicalEpsilonHyperModel.
Proof.
  refine {|
    eps_is_left_adj_obj := _;
    eps_functorial := _
  |}.
  - intros I A Phi Hwf.
    eapply iso_trans.
    + apply FHPointwiseMaximum_to_EpsilonSelection.
      apply FHCanonicalEpsilon_pointwise_maximum.
    + apply iso_sym.
      exact (@form_subst_iso Label Func Pred HFunc HPred
        (CFLabels.CanonicalSkolemMapping Func Pred)
        FHBaseCategory FHBaseCartesian FHBaseTwoSort
        FHCanonicalBaseEpsilonFullModel FHGoodFibration
        FHCanonicalEpsilonHyperModel
        I (b_Prod I A)
        (b_pair b_id (b_const A (CFLabels.epsilon_label A Phi)))
        (BT_Pair BT_Id BT_Const) Phi).
  - eapply eps_functorial_from_eps_is_left_adj_obj.
    intros I A Phi Hwf.
    eapply iso_trans.
    + apply FHPointwiseMaximum_to_EpsilonSelection.
      apply FHCanonicalEpsilon_pointwise_maximum.
    + apply iso_sym.
      exact (@form_subst_iso Label Func Pred HFunc HPred
        (CFLabels.CanonicalSkolemMapping Func Pred)
        FHBaseCategory FHBaseCartesian FHBaseTwoSort
        FHCanonicalBaseEpsilonFullModel FHGoodFibration
        FHCanonicalEpsilonHyperModel
        I (b_Prod I A)
        (b_pair b_id (b_const A (CFLabels.epsilon_label A Phi)))
        (BT_Pair BT_Id BT_Const) Phi).
Defined.

Global Instance FHCanonicalAllPredicateEpsilonFullFibration :
  @AllPredicateEpsilonFullFibration
    FHBaseCategory FHBaseCartesian FHBaseTwoSort FHGoodFibration.
Proof.
  constructor. intros I A Q.
  exact (FHMaximumToChosenEpsilon (FHChainMaximumSelectionData Hchain)
    (FHModelBase I) (FHModelBase A) Q).
Defined.

Global Instance FHCanonicalAllPredicateEpsilonFullModel :
  @AllPredicateEpsilonFullModel Label Func Pred HFunc HPred
    (CFLabels.CanonicalSkolemMapping Func Pred)
    FHBaseCategory FHBaseCartesian FHBaseTwoSort
    FHCanonicalBaseEpsilonFullModel FHGoodFibration
    FHCanonicalEpsilonHyperModel FHCanonicalAdjointEpsilonFullFibration.
Proof.
  constructor. exact FHCanonicalAllPredicateEpsilonFullFibration.
Defined.

Definition FHCanonicalEpsilonFullModel :
  @EpsilonFullModel Label Func Pred HFunc HPred
    (CFLabels.CanonicalSkolemMapping Func Pred).
Proof.
  refine {|
    efm_cat := FHBaseCategory;
    efm_cartesian := FHBaseCartesian;
    efm_twosort := FHBaseTwoSort;
    efm_base_model := FHCanonicalBaseEpsilonFullModel;
    efm_base_coherent := FHCanonicalCoherentBaseModel;
    efm_good_fibration := FHGoodFibration;
    efm_hyper_model := FHCanonicalEpsilonHyperModel;
    efm_adjoint_epsilon := FHCanonicalAdjointEpsilonFullFibration
  |}.
Defined.

End CanonicalFiniteChainModel.
