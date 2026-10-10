
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Equality.
Require Import List.
Import ListNotations.

Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.
Require Import HyperLogic.Semantics.EpsilonFull.LargeSetoidCategory.

Set Universe Polymorphism.

Section EpsilonFullRawCarrierCategory.

Context {Sign Func Pred : Type}.
Context `{HFunc : FunctionSignature Func}.
Context `{HPred : PredicateSignature Pred}.
Context {SM : SkolemMapping Sign Func Pred}.

Class EpsilonFullRawCarrier := mk_EpsilonFullRawCarrier {
  raw_base :
    forall (I : b_ty) (t : @b_tm Sign Func) (A : b_ty), Type;
  raw_hyper :
    forall (I : b_ty) (G : @h_context Sign Func Pred)
      (p : @h_tm Sign Func Pred) (Phi : @h_ty Sign Func Pred), Type
}.

Class EpsilonFullRawCarrierHom
  (X Y : EpsilonFullRawCarrier) := mk_EpsilonFullRawCarrierHom {
  raw_base_map :
    forall (I : b_ty) (t : @b_tm Sign Func) (A : b_ty),
      @raw_base X I t A -> @raw_base Y I t A;
  raw_hyper_map :
    forall (I : b_ty) (G : @h_context Sign Func Pred)
      (p : @h_tm Sign Func Pred) (Phi : @h_ty Sign Func Pred),
      @raw_hyper X I G p Phi -> @raw_hyper Y I G p Phi
}.

Definition EpsilonFullRawCarrierHom_equiv
  {X Y : EpsilonFullRawCarrier}
  (F G : EpsilonFullRawCarrierHom X Y) : Prop :=
  (forall I t A (d : @raw_base X I t A),
      @raw_base_map X Y F I t A d = @raw_base_map X Y G I t A d) /\
  (forall I Gamma p Phi (d : @raw_hyper X I Gamma p Phi),
      @raw_hyper_map X Y F I Gamma p Phi d =
      @raw_hyper_map X Y G I Gamma p Phi d).

Global Instance EpsilonFullRawCarrierHom_equiv_equivalence
  {X Y : EpsilonFullRawCarrier}
  : Equivalence (@EpsilonFullRawCarrierHom_equiv X Y).
Proof.
  constructor.
  - intro F. split; intros; reflexivity.
  - intros F G [Hb Hh]. split; intros.
    + symmetry. apply Hb.
    + symmetry. apply Hh.
  - intros F G H [HbFG HhFG] [HbGH HhGH]. split; intros.
    + transitivity (@raw_base_map X Y G I t A d).
      * apply HbFG.
      * apply HbGH.
    + transitivity (@raw_hyper_map X Y G I Gamma p Phi d).
      * apply HhFG.
      * apply HhGH.
Defined.

Instance EpsilonFullRawCarrier_id
  (X : EpsilonFullRawCarrier) : EpsilonFullRawCarrierHom X X.
Proof.
  constructor.
  - intros I t A d. exact d.
  - intros I Gamma p Phi d. exact d.
Defined.

Instance EpsilonFullRawCarrier_comp
  {X Y Z : EpsilonFullRawCarrier}
  (G : EpsilonFullRawCarrierHom Y Z)
  (F : EpsilonFullRawCarrierHom X Y)
  : EpsilonFullRawCarrierHom X Z.
Proof.
  constructor.
  - intros I t A d.
    exact (raw_base_map (X:=Y) (Y:=Z) I t A
      (raw_base_map (X:=X) (Y:=Y) I t A d)).
  - intros I Gamma p Phi d.
    exact (raw_hyper_map (X:=Y) (Y:=Z) I Gamma p Phi
      (raw_hyper_map (X:=X) (Y:=Y) I Gamma p Phi d)).
Defined.

Instance EpsilonFullRawCarrier_LargeSetoidCategory : LargeSetoidCategory.
Proof.
  refine {|
    lobj := EpsilonFullRawCarrier;
    lhom := EpsilonFullRawCarrierHom;
    lid := EpsilonFullRawCarrier_id;
    lcompose := fun X Y Z G F => EpsilonFullRawCarrier_comp G F;
    lhom_equiv := @EpsilonFullRawCarrierHom_equiv;
    lhom_equiv_equivalence := fun X Y =>
      @EpsilonFullRawCarrierHom_equiv_equivalence X Y
  |}.
  - intros X Y Z W F G H. split; intros; reflexivity.
  - intros X Y F. split; intros; reflexivity.
  - intros X Y F. split; intros; reflexivity.
  - intros X Y Z G G' F F' [HbG HhG] [HbF HhF].
    split; intros; cbn.
    + rewrite (HbF I t A d). apply HbG.
    + rewrite (HhF I Gamma p Phi d). apply HhG.
Defined.

Inductive RawBaseOneStep (X : EpsilonFullRawCarrier)
  : forall (I : b_ty) (t : @b_tm Sign Func) (A : b_ty), Type :=
  | RBOS_Id : forall A,
      RawBaseOneStep X A b_id A
  | RBOS_Comp : forall A B C (g f : @b_tm Sign Func),
      @raw_base X B g C ->
      @raw_base X A f B ->
      RawBaseOneStep X A (b_comp g f) C
  | RBOS_Unit : forall A,
      RawBaseOneStep X A b_unit b_Unit
  | RBOS_Pair : forall A B C (f g : @b_tm Sign Func),
      @raw_base X A f B ->
      @raw_base X A g C ->
      RawBaseOneStep X A (b_pair f g) (b_Prod B C)
  | RBOS_Fst : forall A B,
      RawBaseOneStep X (b_Prod A B) b_fst A
  | RBOS_Snd : forall A B,
      RawBaseOneStep X (b_Prod A B) b_snd B
  | RBOS_Const : forall I A (s : Sign),
      RawBaseOneStep X I (b_const A s) A
  | RBOS_Func : forall f,
      RawBaseOneStep X (func_dom f) (b_func f) (func_cod f).

Arguments RBOS_Id {X} A.
Arguments RBOS_Comp {X} A B C g f _ _.
Arguments RBOS_Unit {X} A.
Arguments RBOS_Pair {X} A B C f g _ _.
Arguments RBOS_Fst {X} A B.
Arguments RBOS_Snd {X} A B.
Arguments RBOS_Const {X} I A s.
Arguments RBOS_Func {X} f.

Inductive RawHyperOneStep (X : EpsilonFullRawCarrier) :
  forall (I : b_ty) (G : @h_context Sign Func Pred)
    (p : @h_tm Sign Func Pred) (Phi : @h_ty Sign Func Pred), Type :=
  | RHOS_Var0 : forall I Phi G,
      All_WellFormed I (Phi :: G) ->
      RawHyperOneStep X I (Phi :: G) (tm_var 0) Phi
  | RHOS_VarS : forall I Phi Psi G n,
      WellFormed I Psi ->
      @raw_hyper X I G (tm_var n) Phi ->
      RawHyperOneStep X I (Psi :: G) (tm_var (Datatypes.S n)) Phi
  | RHOS_Unit : forall I G,
      All_WellFormed I G ->
      RawHyperOneStep X I G tm_unit Ty_Unit
  | RHOS_Conv : forall I G p Phi Psi,
      @raw_hyper X I G p Phi ->
      form_equiv I Phi Psi ->
      RawHyperOneStep X I G p Psi
  | RHOS_Ctx_Conv : forall I G1 G2 p Phi,
      ctx_equiv I G1 G2 ->
      @raw_hyper X I G1 p Phi ->
      RawHyperOneStep X I G2 p Phi
  | RHOS_Lam : forall I G p Phi Psi,
      @raw_hyper X I (Phi :: G) p Psi ->
      RawHyperOneStep X I G (tm_lam Phi p) (Ty_Arrow Phi Psi)
  | RHOS_App : forall I G p1 p2 Phi Psi,
      @raw_hyper X I G p1 (Ty_Arrow Phi Psi) ->
      @raw_hyper X I G p2 Phi ->
      RawHyperOneStep X I G (tm_app p1 p2) Psi
  | RHOS_Pair : forall I G p1 p2 Phi Psi,
      @raw_hyper X I G p1 Phi ->
      @raw_hyper X I G p2 Psi ->
      RawHyperOneStep X I G (tm_pair p1 p2) (Ty_Prod Phi Psi)
  | RHOS_Fst : forall I G p Phi Psi,
      @raw_hyper X I G p (Ty_Prod Phi Psi) ->
      RawHyperOneStep X I G (tm_fst p) Phi
  | RHOS_Snd : forall I G p Phi Psi,
      @raw_hyper X I G p (Ty_Prod Phi Psi) ->
      RawHyperOneStep X I G (tm_snd p) Psi
  | RHOS_Inl : forall I G p Phi Psi,
      WellFormed I Psi ->
      @raw_hyper X I G p Phi ->
      RawHyperOneStep X I G (tm_inl Psi p) (Ty_Sum Phi Psi)
  | RHOS_Inr : forall I G p Phi Psi,
      WellFormed I Phi ->
      @raw_hyper X I G p Psi ->
      RawHyperOneStep X I G (tm_inr Phi p) (Ty_Sum Phi Psi)
  | RHOS_Case : forall I G p p1 p2 Phi Psi Chi,
      @raw_hyper X I G p (Ty_Sum Phi Psi) ->
      @raw_hyper X I (Phi :: G) p1 Chi ->
      @raw_hyper X I (Psi :: G) p2 Chi ->
      RawHyperOneStep X I G (tm_case p p1 p2) Chi
  | RHOS_Absurd : forall I G p Phi,
      WellFormed I Phi ->
      @raw_hyper X I G p Ty_Void ->
      RawHyperOneStep X I G (tm_absurd Phi p) Phi
  | RHOS_All_Intro : forall I A G p Phi,
      @raw_hyper X (b_Prod I A) (ctx_subst b_fst G) p Phi ->
      RawHyperOneStep X I G (tm_all_intro p) (Ty_All A Phi)
  | RHOS_All_Elim : forall I A G p Phi f,
      @raw_hyper X I G p (Ty_All A Phi) ->
      @raw_base X I f A ->
      RawHyperOneStep X I G (tm_all_elim p f)
        (form_subst (b_pair b_id f) Phi)
  | RHOS_Ex_Intro : forall I A G p Phi f,
      @raw_base X I f A ->
      @raw_hyper X I G p (form_subst (b_pair b_id f) Phi) ->
      RawHyperOneStep X I G (tm_ex_intro f p) (Ty_Ex A Phi)
  | RHOS_Ex_Elim : forall I A G p p2 Phi Chi,
      @raw_hyper X I G p (Ty_Ex A Phi) ->
      @raw_hyper X (b_Prod I A) (Phi :: ctx_subst b_fst G) p2
        (form_subst b_fst Chi) ->
      RawHyperOneStep X I G (tm_ex_elim p p2) Chi
  | RHOS_Eps_Intro : forall I A G p Phi f,
      @raw_base X I f A ->
      @raw_hyper X I G p (form_subst (b_pair b_id f) Phi) ->
      RawHyperOneStep X I G (tm_eps_intro f p)
        (form_subst (b_pair b_id (b_const A (skolem_index A Phi))) Phi)
  | RHOS_Eps_Elim : forall I A G p p2 Phi Chi,
      @raw_hyper X I G p
        (form_subst (b_pair b_id (b_const A (skolem_index A Phi))) Phi) ->
      @raw_hyper X (b_Prod I A) (Phi :: ctx_subst b_fst G) p2
        (form_subst b_fst Chi) ->
      RawHyperOneStep X I G (tm_eps_elim p p2) Chi.

Arguments RHOS_Var0 {X} I Phi G _.
Arguments RHOS_VarS {X} I Phi Psi G n _ _.
Arguments RHOS_Unit {X} I G _.
Arguments RHOS_Conv {X} I G p Phi Psi _ _.
Arguments RHOS_Ctx_Conv {X} I G1 G2 p Phi _ _.
Arguments RHOS_Lam {X} I G p Phi Psi _.
Arguments RHOS_App {X} I G p1 p2 Phi Psi _ _.
Arguments RHOS_Pair {X} I G p1 p2 Phi Psi _ _.
Arguments RHOS_Fst {X} I G p Phi Psi _.
Arguments RHOS_Snd {X} I G p Phi Psi _.
Arguments RHOS_Inl {X} I G p Phi Psi _ _.
Arguments RHOS_Inr {X} I G p Phi Psi _ _.
Arguments RHOS_Case {X} I G p p1 p2 Phi Psi Chi _ _ _.
Arguments RHOS_Absurd {X} I G p Phi _ _.
Arguments RHOS_All_Intro {X} I A G p Phi _.
Arguments RHOS_All_Elim {X} I A G p Phi f _ _.
Arguments RHOS_Ex_Intro {X} I A G p Phi f _ _.
Arguments RHOS_Ex_Elim {X} I A G p p2 Phi Chi _ _.
Arguments RHOS_Eps_Intro {X} I A G p Phi f _ _.
Arguments RHOS_Eps_Elim {X} I A G p p2 Phi Chi _ _.

Definition raw_base_onestep_map
  {X Y : EpsilonFullRawCarrier}
  (F : EpsilonFullRawCarrierHom X Y)
  {I : b_ty} {t : @b_tm Sign Func} {A : b_ty}
  (s : RawBaseOneStep X I t A) : RawBaseOneStep Y I t A :=
  match s in RawBaseOneStep _ I0 t0 A0
        return RawBaseOneStep Y I0 t0 A0 with
  | RBOS_Id A =>
      @RBOS_Id Y A
  | RBOS_Comp A B C g f dg df =>
      @RBOS_Comp Y A B C g f
        (raw_base_map (X:=X) (Y:=Y) B g C dg)
        (raw_base_map (X:=X) (Y:=Y) A f B df)
  | RBOS_Unit A =>
      @RBOS_Unit Y A
  | RBOS_Pair A B C f g df dg =>
      @RBOS_Pair Y A B C f g
        (raw_base_map (X:=X) (Y:=Y) A f B df)
        (raw_base_map (X:=X) (Y:=Y) A g C dg)
  | RBOS_Fst A B =>
      @RBOS_Fst Y A B
  | RBOS_Snd A B =>
      @RBOS_Snd Y A B
  | RBOS_Const i A s =>
      @RBOS_Const Y i A s
  | RBOS_Func f =>
      @RBOS_Func Y f
  end.

Definition raw_hyper_onestep_map
  {X Y : EpsilonFullRawCarrier}
  (F : EpsilonFullRawCarrierHom X Y)
  {I : b_ty} {G : @h_context Sign Func Pred}
  {p : @h_tm Sign Func Pred} {Phi : @h_ty Sign Func Pred}
  (s : RawHyperOneStep X I G p Phi) : RawHyperOneStep Y I G p Phi :=
  match s in RawHyperOneStep _ I0 G0 p0 Phi0
        return RawHyperOneStep Y I0 G0 p0 Phi0 with
  | RHOS_Var0 i Phi G wf =>
      @RHOS_Var0 Y i Phi G wf
  | RHOS_VarS i Phi Psi G n wf d =>
      @RHOS_VarS Y i Phi Psi G n wf
        (raw_hyper_map (X:=X) (Y:=Y) i G (tm_var n) Phi d)
  | RHOS_Unit i G wf =>
      @RHOS_Unit Y i G wf
  | RHOS_Conv i G p Phi Psi d e =>
      @RHOS_Conv Y i G p Phi Psi
        (raw_hyper_map (X:=X) (Y:=Y) i G p Phi d) e
  | RHOS_Ctx_Conv i G1 G2 p Phi e d =>
      @RHOS_Ctx_Conv Y i G1 G2 p Phi e
        (raw_hyper_map (X:=X) (Y:=Y) i G1 p Phi d)
  | RHOS_Lam i G p Phi Psi d =>
      @RHOS_Lam Y i G p Phi Psi
        (raw_hyper_map (X:=X) (Y:=Y) i (Phi :: G) p Psi d)
  | RHOS_App i G p1 p2 Phi Psi d1 d2 =>
      @RHOS_App Y i G p1 p2 Phi Psi
        (raw_hyper_map (X:=X) (Y:=Y) i G p1 (Ty_Arrow Phi Psi) d1)
        (raw_hyper_map (X:=X) (Y:=Y) i G p2 Phi d2)
  | RHOS_Pair i G p1 p2 Phi Psi d1 d2 =>
      @RHOS_Pair Y i G p1 p2 Phi Psi
        (raw_hyper_map (X:=X) (Y:=Y) i G p1 Phi d1)
        (raw_hyper_map (X:=X) (Y:=Y) i G p2 Psi d2)
  | RHOS_Fst i G p Phi Psi d =>
      @RHOS_Fst Y i G p Phi Psi
        (raw_hyper_map (X:=X) (Y:=Y) i G p (Ty_Prod Phi Psi) d)
  | RHOS_Snd i G p Phi Psi d =>
      @RHOS_Snd Y i G p Phi Psi
        (raw_hyper_map (X:=X) (Y:=Y) i G p (Ty_Prod Phi Psi) d)
  | RHOS_Inl i G p Phi Psi wf d =>
      @RHOS_Inl Y i G p Phi Psi wf
        (raw_hyper_map (X:=X) (Y:=Y) i G p Phi d)
  | RHOS_Inr i G p Phi Psi wf d =>
      @RHOS_Inr Y i G p Phi Psi wf
        (raw_hyper_map (X:=X) (Y:=Y) i G p Psi d)
  | RHOS_Case i G p p1 p2 Phi Psi Chi d d1 d2 =>
      @RHOS_Case Y i G p p1 p2 Phi Psi Chi
        (raw_hyper_map (X:=X) (Y:=Y) i G p (Ty_Sum Phi Psi) d)
        (raw_hyper_map (X:=X) (Y:=Y) i (Phi :: G) p1 Chi d1)
        (raw_hyper_map (X:=X) (Y:=Y) i (Psi :: G) p2 Chi d2)
  | RHOS_Absurd i G p Phi wf d =>
      @RHOS_Absurd Y i G p Phi wf
        (raw_hyper_map (X:=X) (Y:=Y) i G p Ty_Void d)
  | RHOS_All_Intro i A G p Phi d =>
      @RHOS_All_Intro Y i A G p Phi
        (raw_hyper_map (X:=X) (Y:=Y)
          (b_Prod i A) (ctx_subst b_fst G) p Phi d)
  | RHOS_All_Elim i A G p Phi f d df =>
      @RHOS_All_Elim Y i A G p Phi f
        (raw_hyper_map (X:=X) (Y:=Y) i G p (Ty_All A Phi) d)
        (raw_base_map (X:=X) (Y:=Y) i f A df)
  | RHOS_Ex_Intro i A G p Phi f df d =>
      @RHOS_Ex_Intro Y i A G p Phi f
        (raw_base_map (X:=X) (Y:=Y) i f A df)
        (raw_hyper_map (X:=X) (Y:=Y)
          i G p (form_subst (b_pair b_id f) Phi) d)
  | RHOS_Ex_Elim i A G p p2 Phi Chi d d2 =>
      @RHOS_Ex_Elim Y i A G p p2 Phi Chi
        (raw_hyper_map (X:=X) (Y:=Y) i G p (Ty_Ex A Phi) d)
        (raw_hyper_map (X:=X) (Y:=Y)
          (b_Prod i A) (Phi :: ctx_subst b_fst G) p2
          (form_subst b_fst Chi) d2)
  | RHOS_Eps_Intro i A G p Phi f df d =>
      @RHOS_Eps_Intro Y i A G p Phi f
        (raw_base_map (X:=X) (Y:=Y) i f A df)
        (raw_hyper_map (X:=X) (Y:=Y)
          i G p (form_subst (b_pair b_id f) Phi) d)
  | RHOS_Eps_Elim i A G p p2 Phi Chi d d2 =>
      @RHOS_Eps_Elim Y i A G p p2 Phi Chi
        (raw_hyper_map (X:=X) (Y:=Y) i G p
          (form_subst (b_pair b_id (b_const A (skolem_index A Phi))) Phi) d)
        (raw_hyper_map (X:=X) (Y:=Y)
          (b_Prod i A) (Phi :: ctx_subst b_fst G) p2
          (form_subst b_fst Chi) d2)
  end.

Definition RawOneStepCarrier
  (X : EpsilonFullRawCarrier) : EpsilonFullRawCarrier.
Proof.
  constructor.
  - exact (RawBaseOneStep X).
  - exact (RawHyperOneStep X).
Defined.

Definition RawOneStepCarrierHom
  {X Y : EpsilonFullRawCarrier}
  (F : EpsilonFullRawCarrierHom X Y)
  : EpsilonFullRawCarrierHom (RawOneStepCarrier X) (RawOneStepCarrier Y).
Proof.
  constructor.
  - intros I t A s. exact (raw_base_onestep_map F s).
  - intros I G p Phi s. exact (raw_hyper_onestep_map F s).
Defined.

Ltac rewrite_raw_carrier_maps :=
  repeat match goal with
  | Hb : forall I t A (d : @raw_base ?X I t A),
      @raw_base_map ?X ?Y ?F I t A d =
      @raw_base_map ?X ?Z ?G I t A d
    |- context[@raw_base_map ?X ?Y ?F ?I ?t ?A ?d0] =>
      rewrite (Hb I t A d0)
  | Hh : forall I Gm p Phi (d : @raw_hyper ?X I Gm p Phi),
      @raw_hyper_map ?X ?Y ?F I Gm p Phi d =
      @raw_hyper_map ?X ?Z ?G I Gm p Phi d
    |- context[@raw_hyper_map ?X ?Y ?F ?I ?Gm ?p ?Phi ?d0] =>
      rewrite (Hh I Gm p Phi d0)
  end.

Lemma RawOneStepCarrierHom_proper
  {X Y : EpsilonFullRawCarrier}
  (F G : EpsilonFullRawCarrierHom X Y)
  : EpsilonFullRawCarrierHom_equiv F G ->
    EpsilonFullRawCarrierHom_equiv
      (RawOneStepCarrierHom F) (RawOneStepCarrierHom G).
Proof.
  intros [Hb Hh]. split.
  - intros I t A s.
    destruct s; cbn; try reflexivity; rewrite_raw_carrier_maps; reflexivity.
  - intros I Gm p Phi s.
    destruct s; cbn; try reflexivity; rewrite_raw_carrier_maps; reflexivity.
Defined.

Instance EpsilonFullRawOneStep_Endofunctor
  : LargeEndofunctor EpsilonFullRawCarrier_LargeSetoidCategory.
Proof.
  refine {|
    large_fobj := RawOneStepCarrier;
    large_fmap := fun X Y F => RawOneStepCarrierHom F
  |}.
  - intros X Y F G HFG.
    apply RawOneStepCarrierHom_proper.
    exact HFG.
  - intro X. split; intros.
    + destruct d; cbn; reflexivity.
    + destruct d; cbn; reflexivity.
  - intros X Y Z G F. split; intros.
    + destruct d; cbn; reflexivity.
    + destruct d; cbn; reflexivity.
Defined.

Definition TermModelRawCarrier : EpsilonFullRawCarrier.
Proof.
  constructor.
  - exact (@base_typing Sign Func HFunc).
  - exact (@h_derivation Sign Func Pred HFunc HPred SM).
Defined.

Definition term_raw_base_roll
  {I : b_ty} {t : @b_tm Sign Func} {A : b_ty}
  (s : RawBaseOneStep TermModelRawCarrier I t A)
  : @base_typing Sign Func HFunc I t A.
Proof.
  destruct s as
    [ A
    | A B C g f dg df
    | A
    | A B C f g df dg
    | A B
    | A B
    | i A s
    | f ].
  - exact (@BT_Id Sign Func HFunc A).
  - exact (@BT_Comp Sign Func HFunc A B C g f dg df).
  - exact (@BT_Unit Sign Func HFunc A).
  - exact (@BT_Pair Sign Func HFunc A B C f g df dg).
  - exact (@BT_Fst Sign Func HFunc A B).
  - exact (@BT_Snd Sign Func HFunc A B).
  - exact (@BT_Const Sign Func HFunc i A s).
  - exact (@BT_Func Sign Func HFunc f).
Defined.

Definition term_raw_base_unroll
  {I : b_ty} {t : @b_tm Sign Func} {A : b_ty}
  (d : @base_typing Sign Func HFunc I t A)
  : RawBaseOneStep TermModelRawCarrier I t A.
Proof.
  dependent destruction d.
  - apply RBOS_Id.
  - eapply RBOS_Comp; eassumption.
  - apply RBOS_Unit.
  - eapply RBOS_Pair; eassumption.
  - apply RBOS_Fst.
  - apply RBOS_Snd.
  - apply RBOS_Const.
  - apply RBOS_Func.
Defined.

Definition term_raw_hyper_roll
  {I : b_ty} {G : @h_context Sign Func Pred}
  {p : @h_tm Sign Func Pred} {Phi : @h_ty Sign Func Pred}
  (s : RawHyperOneStep TermModelRawCarrier I G p Phi)
  : @h_derivation Sign Func Pred HFunc HPred SM I G p Phi :=
  match s with
  | RHOS_Var0 i Phi G wf =>
      HD_Var0 i Phi G wf
  | RHOS_VarS i Phi Psi G n wf d =>
      HD_VarS i Phi Psi G n wf d
  | RHOS_Unit i G wf =>
      HD_Unit i G wf
  | RHOS_Conv i G p Phi Psi d e =>
      HD_Conv i G p Phi Psi d e
  | RHOS_Ctx_Conv i G1 G2 p Phi e d =>
      HD_Ctx_Conv i G1 G2 p Phi e d
  | RHOS_Lam i G p Phi Psi d =>
      HD_Lam i G p Phi Psi d
  | RHOS_App i G p1 p2 Phi Psi d1 d2 =>
      HD_App i G p1 p2 Phi Psi d1 d2
  | RHOS_Pair i G p1 p2 Phi Psi d1 d2 =>
      HD_Pair i G p1 p2 Phi Psi d1 d2
  | RHOS_Fst i G p Phi Psi d =>
      HD_Fst i G p Phi Psi d
  | RHOS_Snd i G p Phi Psi d =>
      HD_Snd i G p Phi Psi d
  | RHOS_Inl i G p Phi Psi wf d =>
      HD_Inl wf d
  | RHOS_Inr i G p Phi Psi wf d =>
      HD_Inr wf d
  | RHOS_Case i G p p1 p2 Phi Psi Chi d d1 d2 =>
      HD_Case i G p p1 p2 Phi Psi Chi d d1 d2
  | RHOS_Absurd i G p Phi wf d =>
      HD_Absurd wf d
  | RHOS_All_Intro i A G p Phi d =>
      HD_All_Intro i A G p Phi d
  | RHOS_All_Elim i A G p Phi f d df =>
      HD_All_Elim i A G p Phi f d df
  | RHOS_Ex_Intro i A G p Phi f df d =>
      HD_Ex_Intro i A G p Phi f df d
  | RHOS_Ex_Elim i A G p p2 Phi Chi d d2 =>
      HD_Ex_Elim i A G p p2 Phi Chi d d2
  | RHOS_Eps_Intro i A G p Phi f df d =>
      HD_Eps_Intro i A G p Phi f df d
  | RHOS_Eps_Elim i A G p p2 Phi Chi d d2 =>
      HD_Eps_Elim i A G p p2 Phi Chi d d2
  end.

Definition term_raw_hyper_unroll
  {I : b_ty} {G : @h_context Sign Func Pred}
  {p : @h_tm Sign Func Pred} {Phi : @h_ty Sign Func Pred}
  (d : @h_derivation Sign Func Pred HFunc HPred SM I G p Phi)
  : RawHyperOneStep TermModelRawCarrier I G p Phi.
Proof.
  dependent destruction d.
  - exact (@RHOS_Var0 TermModelRawCarrier I Phi G a).
  - exact (@RHOS_VarS TermModelRawCarrier I Phi Psi G n w d).
  - exact (@RHOS_Unit TermModelRawCarrier I G a).
  - exact (@RHOS_Conv TermModelRawCarrier I G p Phi Psi d f).
  - exact (@RHOS_Ctx_Conv TermModelRawCarrier I G1 G2 p Phi c d).
  - exact (@RHOS_Lam TermModelRawCarrier I G p Phi Psi d).
  - exact (@RHOS_App TermModelRawCarrier I G p1 p2 Phi Psi d1 d2).
  - exact (@RHOS_Pair TermModelRawCarrier I G p1 p2 Phi Psi d1 d2).
  - exact (@RHOS_Fst TermModelRawCarrier I G p Phi Psi d).
  - exact (@RHOS_Snd TermModelRawCarrier I G p Phi Psi d).
  - exact (@RHOS_Inl TermModelRawCarrier I G p Phi Psi w d).
  - exact (@RHOS_Inr TermModelRawCarrier I G p Phi Psi w d).
  - exact (@RHOS_Case TermModelRawCarrier I G p p1 p2 Phi Psi Chi d1 d2 d3).
  - exact (@RHOS_Absurd TermModelRawCarrier I G p Phi w d).
  - exact (@RHOS_All_Intro TermModelRawCarrier I A G p Phi d).
  - exact (@RHOS_All_Elim TermModelRawCarrier I A G p Phi f d b).
  - exact (@RHOS_Ex_Intro TermModelRawCarrier I A G p Phi f b d).
  - exact (@RHOS_Ex_Elim TermModelRawCarrier I A G p p2 Phi Chi d1 d2).
  - exact (@RHOS_Eps_Intro TermModelRawCarrier I A G p Phi f b d).
  - exact (@RHOS_Eps_Elim TermModelRawCarrier I A G p p2 Phi Chi d1 d2).
Defined.

Definition TermModelRawCarrier_roll
  : EpsilonFullRawCarrierHom
      (RawOneStepCarrier TermModelRawCarrier) TermModelRawCarrier.
Proof.
  constructor.
  - intros I t A s. exact (term_raw_base_roll s).
  - intros I G p Phi s. exact (term_raw_hyper_roll s).
Defined.

Definition TermModelRawCarrier_unroll
  : EpsilonFullRawCarrierHom
      TermModelRawCarrier (RawOneStepCarrier TermModelRawCarrier).
Proof.
  constructor.
  - intros I t A d. exact (term_raw_base_unroll d).
  - intros I G p Phi d. exact (term_raw_hyper_unroll d).
Defined.

Lemma TermModelRawCarrier_roll_unroll :
  EpsilonFullRawCarrierHom_equiv
    (EpsilonFullRawCarrier_comp
      TermModelRawCarrier_roll TermModelRawCarrier_unroll)
    (EpsilonFullRawCarrier_id TermModelRawCarrier).
Proof.
  split.
  - intros I t A d.
    cbn in d.
    dependent destruction d; reflexivity.
  - intros I G p Phi d.
    cbn in d.
    dependent destruction d; reflexivity.
Defined.

Lemma TermModelRawCarrier_unroll_roll :
  EpsilonFullRawCarrierHom_equiv
    (EpsilonFullRawCarrier_comp
      TermModelRawCarrier_unroll TermModelRawCarrier_roll)
    (EpsilonFullRawCarrier_id (RawOneStepCarrier TermModelRawCarrier)).
Proof.
  split.
  - intros I t A s.
    cbn. unfold term_raw_base_roll, term_raw_base_unroll.
    destruct s; reflexivity.
  - intros I G p Phi s.
    cbn. unfold term_raw_hyper_roll, term_raw_hyper_unroll.
    destruct s; reflexivity.
Defined.

Instance TermModelRawCarrier_OneStepIsomorphism
  : @LargeIsomorphism EpsilonFullRawCarrier_LargeSetoidCategory
      (RawOneStepCarrier TermModelRawCarrier) TermModelRawCarrier.
Proof.
  refine {|
    large_iso_to := TermModelRawCarrier_roll;
    large_iso_from := TermModelRawCarrier_unroll
  |}.
  - exact TermModelRawCarrier_unroll_roll.
  - exact TermModelRawCarrier_roll_unroll.
Defined.

End EpsilonFullRawCarrierCategory.
