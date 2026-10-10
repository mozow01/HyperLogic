
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import List.
Import ListNotations.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Fibration.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.

Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax_Lemmas.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax_Lemmas.

Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_Fibration.
Require Import HyperLogic.Semantics.EpsilonFull.Base_EpsilonFull_Soundness.
Require Import HyperLogic.Semantics.EpsilonFull.Base_EpsilonFull_Completeness.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_Soundness.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_Completeness.

Section EpsilonFullModelCategory.

Context {Sign Func Pred : Type}.
Context `{HFunc : FunctionSignature Func}.
Context `{HPred : PredicateSignature Pred}.
Context {SM : SkolemMapping Sign Func Pred}.

Class EpsilonFullModel := mk_EpsilonFullModel {
  efm_cat : SetoidCategory;
  efm_cartesian : CartesianCategory efm_cat;
  efm_twosort : @TwoSortCategory efm_cat efm_cartesian;

  efm_base_model :
    @BaseEpsilonFullModel Sign Func HFunc efm_cat efm_cartesian efm_twosort;
  efm_base_coherent :
    @CoherentBaseModel Sign Func HFunc
      efm_cat efm_cartesian efm_twosort efm_base_model;

  efm_good_fibration :
    @GoodFibration efm_cat efm_cartesian;

  efm_hyper_model :
    @EpsilonHyperModel Sign Func Pred HFunc HPred
      efm_cat efm_cartesian efm_twosort efm_base_model
      efm_good_fibration;
  efm_adjoint_epsilon :
    @AdjointEpsilonFullFibration Sign Func Pred HFunc HPred SM
      efm_cat efm_cartesian efm_twosort efm_base_model
      efm_good_fibration efm_hyper_model
}.

Definition efm_interp_ty (M : EpsilonFullModel) (I : b_ty) : @obj (@efm_cat M) :=
  @interp_ty (@efm_cat M) (@efm_cartesian M) (@efm_twosort M) I.

Definition efm_fiber (M : EpsilonFullModel) (I : b_ty) : SetoidCategory :=
  @Fiber (@efm_cat M) (@efm_cartesian M) (@efm_good_fibration M)
    (efm_interp_ty M I).

Definition efm_interp_h_ty
  (M : EpsilonFullModel) (I : b_ty) (Phi : @h_ty Sign Func Pred)
  : @obj (efm_fiber M I) :=
  @interp_h_ty Sign Func Pred HFunc HPred
    (@efm_cat M) (@efm_cartesian M) (@efm_twosort M)
    (@efm_base_model M) (@efm_good_fibration M)
    (@efm_hyper_model M) I Phi.

Definition efm_interp_h_ctx
  (M : EpsilonFullModel) (I : b_ty) (G : @h_context Sign Func Pred)
  : @obj (efm_fiber M I) :=
  @interp_h_ctx Sign Func Pred HFunc HPred
    (@efm_cat M) (@efm_cartesian M) (@efm_twosort M)
    (@efm_base_model M) (@efm_good_fibration M)
    (@efm_hyper_model M) I G.

Definition efm_interp_tm
  (M : EpsilonFullModel) {I A : b_ty} {t : @b_tm Sign Func}
  (dt : @base_typing Sign Func HFunc I t A)
  : @hom (@efm_cat M) (efm_interp_ty M I) (efm_interp_ty M A) :=
  @interp_tm Sign Func HFunc
    (@efm_cat M) (@efm_cartesian M) (@efm_twosort M)
    (@efm_base_model M) I A t dt.

Definition efm_soundness
  (M : EpsilonFullModel) {I : b_ty} {G : @h_context Sign Func Pred}
  {p : @h_tm Sign Func Pred} {Phi : @h_ty Sign Func Pred}
  (d : @h_derivation Sign Func Pred HFunc HPred SM I G p Phi)
  : @hom (efm_fiber M I) (efm_interp_h_ctx M I G) (efm_interp_h_ty M I Phi) :=
  @soundness Sign Func Pred HFunc HPred SM
    (@efm_cat M) (@efm_cartesian M) (@efm_twosort M)
    (@efm_base_model M) (@efm_good_fibration M)
    (@efm_hyper_model M)
    (@efm_adjoint_epsilon M) I G p Phi d.

Class EpsilonFullModelHom (M N : EpsilonFullModel) := mk_EpsilonFullModelHom {
  efh_base_map :
    forall (I A : b_ty),
      @hom (@efm_cat M) (efm_interp_ty M I) (efm_interp_ty M A) ->
      @hom (@efm_cat N) (efm_interp_ty N I) (efm_interp_ty N A);

  efh_base_map_proper :
    forall (I A : b_ty),
      Proper
        (@hom_equiv (@efm_cat M) (efm_interp_ty M I) (efm_interp_ty M A) ==>
         @hom_equiv (@efm_cat N) (efm_interp_ty N I) (efm_interp_ty N A))
        (efh_base_map I A);

  efh_base_soundness :
    forall (I A : b_ty) (t : @b_tm Sign Func)
      (dt : @base_typing Sign Func HFunc I t A),
      efh_base_map I A (efm_interp_tm M dt)
      ≅ efm_interp_tm N dt;

  efh_fiber_map :
    forall (I : b_ty) (Phi Psi : @h_ty Sign Func Pred),
      WellFormed I Phi ->
      WellFormed I Psi ->
      @hom (efm_fiber M I) (efm_interp_h_ty M I Phi) (efm_interp_h_ty M I Psi) ->
      @hom (efm_fiber N I) (efm_interp_h_ty N I Phi) (efm_interp_h_ty N I Psi);

  efh_fiber_map_proper :
    forall (I : b_ty) (Phi Psi : @h_ty Sign Func Pred)
      (wf_Phi : WellFormed I Phi) (wf_Psi : WellFormed I Psi),
      Proper
        (@hom_equiv (efm_fiber M I) (efm_interp_h_ty M I Phi) (efm_interp_h_ty M I Psi) ==>
         @hom_equiv (efm_fiber N I) (efm_interp_h_ty N I Phi) (efm_interp_h_ty N I Psi))
        (efh_fiber_map I Phi Psi wf_Phi wf_Psi);

  efh_fiber_id :
    forall (I : b_ty) (Phi : @h_ty Sign Func Pred) (wf_Phi : WellFormed I Phi),
      efh_fiber_map I Phi Phi wf_Phi wf_Phi
        (@id (efm_fiber M I) (efm_interp_h_ty M I Phi))
      ≅ @id (efm_fiber N I) (efm_interp_h_ty N I Phi);

  efh_fiber_comp :
    forall (I : b_ty) (Phi Psi Chi : @h_ty Sign Func Pred)
      (wf_Phi : WellFormed I Phi)
      (wf_Psi : WellFormed I Psi)
      (wf_Chi : WellFormed I Chi)
      (g : @hom (efm_fiber M I) (efm_interp_h_ty M I Psi) (efm_interp_h_ty M I Chi))
      (f : @hom (efm_fiber M I) (efm_interp_h_ty M I Phi) (efm_interp_h_ty M I Psi)),
      efh_fiber_map I Phi Chi wf_Phi wf_Chi (@compose (efm_fiber M I)
        (efm_interp_h_ty M I Phi) (efm_interp_h_ty M I Psi)
        (efm_interp_h_ty M I Chi) g f)
      ≅
      @compose (efm_fiber N I)
        (efm_interp_h_ty N I Phi) (efm_interp_h_ty N I Psi)
        (efm_interp_h_ty N I Chi)
        (efh_fiber_map I Psi Chi wf_Psi wf_Chi g)
        (efh_fiber_map I Phi Psi wf_Phi wf_Psi f);

  efh_sequent_map :
    forall (I : b_ty) (G : @h_context Sign Func Pred) (Phi : @h_ty Sign Func Pred),
      All_WellFormed I G ->
      WellFormed I Phi ->
      @hom (efm_fiber M I) (efm_interp_h_ctx M I G) (efm_interp_h_ty M I Phi) ->
      @hom (efm_fiber N I) (efm_interp_h_ctx N I G) (efm_interp_h_ty N I Phi);

  efh_sequent_map_proper :
    forall (I : b_ty) (G : @h_context Sign Func Pred) (Phi : @h_ty Sign Func Pred)
      (wf_G : All_WellFormed I G) (wf_Phi : WellFormed I Phi),
      Proper
        (@hom_equiv (efm_fiber M I) (efm_interp_h_ctx M I G) (efm_interp_h_ty M I Phi) ==>
         @hom_equiv (efm_fiber N I) (efm_interp_h_ctx N I G) (efm_interp_h_ty N I Phi))
        (efh_sequent_map I G Phi wf_G wf_Phi);

  efh_hyper_soundness :
    forall (I : b_ty) (G : @h_context Sign Func Pred)
      (p : @h_tm Sign Func Pred) (Phi : @h_ty Sign Func Pred)
      (d : @h_derivation Sign Func Pred HFunc HPred SM I G p Phi),
      efh_sequent_map I G Phi (meta_ctx_wf d) (meta_type_wf d)
        (efm_soundness M d)
      ≅ efm_soundness N d
}.

Existing Instance efh_base_map_proper.
Existing Instance efh_fiber_map_proper.
Existing Instance efh_sequent_map_proper.

Definition efh_base_preserves_id
  {M N : EpsilonFullModel} (F : EpsilonFullModelHom M N) (I : b_ty)
  : @efh_base_map M N F I I (@id (@efm_cat M) (efm_interp_ty M I))
    ≅ @id (@efm_cat N) (efm_interp_ty N I).
Proof.
  change (@efh_base_map M N F I I
    (efm_interp_tm M (@BT_Id Sign Func HFunc I))
    ≅ efm_interp_tm N (@BT_Id Sign Func HFunc I)).
  apply efh_base_soundness.
Defined.

Definition efh_base_preserves_comp
  {M N : EpsilonFullModel} (F : EpsilonFullModelHom M N)
  {I A B : b_ty} {g f : @b_tm Sign Func}
  (dg : @base_typing Sign Func HFunc A g B)
  (df : @base_typing Sign Func HFunc I f A)
  : @efh_base_map M N F I B
      (@compose (@efm_cat M)
        (efm_interp_ty M I) (efm_interp_ty M A) (efm_interp_ty M B)
        (efm_interp_tm M dg) (efm_interp_tm M df))
    ≅
    @compose (@efm_cat N)
      (efm_interp_ty N I) (efm_interp_ty N A) (efm_interp_ty N B)
      (efm_interp_tm N dg) (efm_interp_tm N df).
Proof.
  change (@efh_base_map M N F I B
    (efm_interp_tm M (@BT_Comp Sign Func HFunc I A B g f dg df))
    ≅ efm_interp_tm N (@BT_Comp Sign Func HFunc I A B g f dg df)).
  apply efh_base_soundness.
Defined.

Definition efh_base_preserves_unit
  {M N : EpsilonFullModel} (F : EpsilonFullModelHom M N) (I : b_ty)
  : @efh_base_map M N F I b_Unit
      (@terminal_map (@efm_cat M) (@efm_cartesian M) (efm_interp_ty M I))
    ≅
    @terminal_map (@efm_cat N) (@efm_cartesian N) (efm_interp_ty N I).
Proof.
  change (@efh_base_map M N F I b_Unit
    (efm_interp_tm M (@BT_Unit Sign Func HFunc I))
    ≅ efm_interp_tm N (@BT_Unit Sign Func HFunc I)).
  apply efh_base_soundness.
Defined.

Definition efh_base_preserves_pair
  {M N : EpsilonFullModel} (F : EpsilonFullModelHom M N)
  {I A B : b_ty} {f g : @b_tm Sign Func}
  (df : @base_typing Sign Func HFunc I f A)
  (dg : @base_typing Sign Func HFunc I g B)
  : @efh_base_map M N F I (b_Prod A B)
      (@prod_map (@efm_cat M) (@efm_cartesian M)
        (efm_interp_ty M I) (efm_interp_ty M A) (efm_interp_ty M B)
        (efm_interp_tm M df) (efm_interp_tm M dg))
    ≅
    @prod_map (@efm_cat N) (@efm_cartesian N)
      (efm_interp_ty N I) (efm_interp_ty N A) (efm_interp_ty N B)
      (efm_interp_tm N df) (efm_interp_tm N dg).
Proof.
  change (@efh_base_map M N F I (b_Prod A B)
    (efm_interp_tm M (@BT_Pair Sign Func HFunc I A B f g df dg))
    ≅ efm_interp_tm N (@BT_Pair Sign Func HFunc I A B f g df dg)).
  apply efh_base_soundness.
Defined.

Definition efh_base_preserves_fst
  {M N : EpsilonFullModel} (F : EpsilonFullModelHom M N) (A B : b_ty)
  : @efh_base_map M N F (b_Prod A B) A
      (@prod_fst (@efm_cat M) (@efm_cartesian M)
        (efm_interp_ty M A) (efm_interp_ty M B))
    ≅
    @prod_fst (@efm_cat N) (@efm_cartesian N)
      (efm_interp_ty N A) (efm_interp_ty N B).
Proof.
  change (@efh_base_map M N F (b_Prod A B) A
    (efm_interp_tm M (@BT_Fst Sign Func HFunc A B))
    ≅ efm_interp_tm N (@BT_Fst Sign Func HFunc A B)).
  apply efh_base_soundness.
Defined.

Definition efh_base_preserves_snd
  {M N : EpsilonFullModel} (F : EpsilonFullModelHom M N) (A B : b_ty)
  : @efh_base_map M N F (b_Prod A B) B
      (@prod_snd (@efm_cat M) (@efm_cartesian M)
        (efm_interp_ty M A) (efm_interp_ty M B))
    ≅
    @prod_snd (@efm_cat N) (@efm_cartesian N)
      (efm_interp_ty N A) (efm_interp_ty N B).
Proof.
  change (@efh_base_map M N F (b_Prod A B) B
    (efm_interp_tm M (@BT_Snd Sign Func HFunc A B))
    ≅ efm_interp_tm N (@BT_Snd Sign Func HFunc A B)).
  apply efh_base_soundness.
Defined.

Definition efh_base_preserves_const
  {M N : EpsilonFullModel} (F : EpsilonFullModelHom M N)
  (I A : b_ty) (s : Sign)
  : @efh_base_map M N F I A
      (@i_const Sign Func HFunc
        (@efm_cat M) (@efm_cartesian M) (@efm_twosort M)
        (@efm_base_model M) I A s)
    ≅
    @i_const Sign Func HFunc
      (@efm_cat N) (@efm_cartesian N) (@efm_twosort N)
      (@efm_base_model N) I A s.
Proof.
  change (@efh_base_map M N F I A
    (efm_interp_tm M (@BT_Const Sign Func HFunc I A s))
    ≅ efm_interp_tm N (@BT_Const Sign Func HFunc I A s)).
  apply efh_base_soundness.
Defined.

Definition efh_base_preserves_func
  {M N : EpsilonFullModel} (F : EpsilonFullModelHom M N) (f : Func)
  : @efh_base_map M N F (func_dom f) (func_cod f)
      (@i_func Sign Func HFunc
        (@efm_cat M) (@efm_cartesian M) (@efm_twosort M)
        (@efm_base_model M) f)
    ≅
    @i_func Sign Func HFunc
      (@efm_cat N) (@efm_cartesian N) (@efm_twosort N)
      (@efm_base_model N) f.
Proof.
  change (@efh_base_map M N F (func_dom f) (func_cod f)
    (efm_interp_tm M (@BT_Func Sign Func HFunc f))
    ≅ efm_interp_tm N (@BT_Func Sign Func HFunc f)).
  apply efh_base_soundness.
Defined.

Definition EpsilonFullModelHom_equiv
  {M N : EpsilonFullModel} (F G : EpsilonFullModelHom M N) : Prop :=
  (forall (I A : b_ty)
     (f : @hom (@efm_cat M) (efm_interp_ty M I) (efm_interp_ty M A)),
      @efh_base_map M N F I A f ≅ @efh_base_map M N G I A f) /\
  (forall (I : b_ty) (Phi Psi : @h_ty Sign Func Pred)
      (wf_Phi : WellFormed I Phi) (wf_Psi : WellFormed I Psi)
      (f : @hom (efm_fiber M I)
        (efm_interp_h_ty M I Phi) (efm_interp_h_ty M I Psi)),
       @efh_fiber_map M N F I Phi Psi wf_Phi wf_Psi f
       ≅
       @efh_fiber_map M N G I Phi Psi wf_Phi wf_Psi f) /\
  (forall (I : b_ty) (Gamma : @h_context Sign Func Pred)
      (Phi : @h_ty Sign Func Pred)
      (wf_Gamma : All_WellFormed I Gamma) (wf_Phi : WellFormed I Phi)
      (f : @hom (efm_fiber M I)
        (efm_interp_h_ctx M I Gamma) (efm_interp_h_ty M I Phi)),
       @efh_sequent_map M N F I Gamma Phi wf_Gamma wf_Phi f
       ≅
       @efh_sequent_map M N G I Gamma Phi wf_Gamma wf_Phi f).

Global Instance EpsilonFullModelHom_equiv_equivalence
  {M N : EpsilonFullModel}
  : Equivalence (@EpsilonFullModelHom_equiv M N).
Proof.
  constructor.
  - intro F.
    split; [intros; reflexivity | split; intros; reflexivity].
  - intros F G [Hbase [Hfiber Hsequent]].
    split; [intros; symmetry; auto | split; intros; symmetry; auto].
  - intros F G H [Hbase_FG [Hfiber_FG Hsequent_FG]]
      [Hbase_GH [Hfiber_GH Hsequent_GH]].
    split.
    + intros I A f.
      transitivity (@efh_base_map M N G I A f).
      * apply Hbase_FG.
      * apply Hbase_GH.
    + split.
      * intros I Phi Psi wf_Phi wf_Psi f.
        transitivity (@efh_fiber_map M N G I Phi Psi wf_Phi wf_Psi f).
        -- apply Hfiber_FG.
        -- apply Hfiber_GH.
      * intros I Gamma Phi wf_Gamma wf_Phi f.
        transitivity (@efh_sequent_map M N G I Gamma Phi wf_Gamma wf_Phi f).
        -- apply Hsequent_FG.
        -- apply Hsequent_GH.
Defined.

Definition EpsilonFullModel_id (M : EpsilonFullModel) : EpsilonFullModelHom M M.
Proof.
  refine (mk_EpsilonFullModelHom M M
    (fun I A f => f)
    _
    _
    (fun I Phi Psi _ _ f => f)
    _
    _
    _
    (fun I Gamma Phi _ _ f => f)
    _
    _).
  - intros I A f g Hfg. exact Hfg.
  - intros I A t dt. reflexivity.
  - intros I Phi Psi wf_Phi wf_Psi f g Hfg. exact Hfg.
  - intros I Phi wf_Phi. reflexivity.
  - intros I Phi Psi Chi wf_Phi wf_Psi wf_Chi g f. reflexivity.
  - intros I Gamma Phi wf_Gamma wf_Phi f g Hfg. exact Hfg.
  - intros I Gamma p Phi d. reflexivity.
Defined.

Definition EpsilonFullModel_comp
  {M N P : EpsilonFullModel}
  (G : EpsilonFullModelHom N P) (F : EpsilonFullModelHom M N)
  : EpsilonFullModelHom M P.
Proof.
  refine (mk_EpsilonFullModelHom M P
    (fun I A f => @efh_base_map N P G I A (@efh_base_map M N F I A f))
    _
    _
    (fun I Phi Psi wf_Phi wf_Psi f =>
       @efh_fiber_map N P G I Phi Psi wf_Phi wf_Psi
         (@efh_fiber_map M N F I Phi Psi wf_Phi wf_Psi f))
    _
    _
    _
    (fun I Gamma Phi wf_Gamma wf_Phi f =>
       @efh_sequent_map N P G I Gamma Phi wf_Gamma wf_Phi
         (@efh_sequent_map M N F I Gamma Phi wf_Gamma wf_Phi f))
    _
    _).
  - intros I A f g Hfg.
    apply efh_base_map_proper.
    apply efh_base_map_proper.
    exact Hfg.
  - intros I A t dt.
    transitivity (@efh_base_map N P G I A (efm_interp_tm N dt)).
    + apply efh_base_map_proper.
      apply efh_base_soundness.
    + apply efh_base_soundness.
  - intros I Phi Psi wf_Phi wf_Psi f g Hfg.
    apply efh_fiber_map_proper.
    apply efh_fiber_map_proper.
    exact Hfg.
  - intros I Phi wf_Phi.
    apply (fiber_is_thin (efm_interp_ty P I)).
  - intros I Phi Psi Chi wf_Phi wf_Psi wf_Chi g f.
    apply (fiber_is_thin (efm_interp_ty P I)).
  - intros I Gamma Phi wf_Gamma wf_Phi f g0 Hfg.
    apply efh_sequent_map_proper.
    apply efh_sequent_map_proper.
    exact Hfg.
  - intros I Gamma p Phi d.
    transitivity
      (@efh_sequent_map N P G I Gamma Phi
        (@meta_ctx_wf Sign Func Pred HFunc HPred SM I Gamma p Phi d)
        (@meta_type_wf Sign Func Pred HFunc HPred SM I Gamma p Phi d)
        (efm_soundness N d)).
    + apply efh_sequent_map_proper.
      apply efh_hyper_soundness.
    + apply efh_hyper_soundness.
Defined.

Definition EpsilonFullModel_comp_assoc
  {M N P Q : EpsilonFullModel}
  (H : EpsilonFullModelHom P Q)
  (G : EpsilonFullModelHom N P)
  (F : EpsilonFullModelHom M N)
  : EpsilonFullModelHom_equiv
      (EpsilonFullModel_comp H (EpsilonFullModel_comp G F))
      (EpsilonFullModel_comp (EpsilonFullModel_comp H G) F).
Proof.
  split; [intros; reflexivity | split; intros; reflexivity].
Defined.

Definition EpsilonFullModel_id_left
  {M N : EpsilonFullModel} (F : EpsilonFullModelHom M N)
  : EpsilonFullModelHom_equiv (EpsilonFullModel_comp (EpsilonFullModel_id N) F) F.
Proof.
  split; [intros; reflexivity | split; intros; reflexivity].
Defined.

Definition EpsilonFullModel_id_right
  {M N : EpsilonFullModel} (F : EpsilonFullModelHom M N)
  : EpsilonFullModelHom_equiv (EpsilonFullModel_comp F (EpsilonFullModel_id M)) F.
Proof.
  split; [intros; reflexivity | split; intros; reflexivity].
Defined.

Definition EpsilonFullModel_comp_proper
  {M N P : EpsilonFullModel}
  {G G' : EpsilonFullModelHom N P}
  {F F' : EpsilonFullModelHom M N}
  : EpsilonFullModelHom_equiv G G' ->
    EpsilonFullModelHom_equiv F F' ->
    EpsilonFullModelHom_equiv
      (EpsilonFullModel_comp G F)
      (EpsilonFullModel_comp G' F').
Proof.
  intros [Hbase_GG' [Hfiber_GG' Hsequent_GG']]
    [Hbase_FF' [Hfiber_FF' Hsequent_FF']].
  split.
  - intros I A f.
    transitivity (@efh_base_map N P G I A (@efh_base_map M N F' I A f)).
    + eapply (@efh_base_map_proper N P G I A).
      apply Hbase_FF'.
    + apply Hbase_GG'.
  - split.
    + intros I Phi Psi wf_Phi wf_Psi f.
      transitivity
        (@efh_fiber_map N P G I Phi Psi wf_Phi wf_Psi
          (@efh_fiber_map M N F' I Phi Psi wf_Phi wf_Psi f)).
      * eapply (@efh_fiber_map_proper N P G I Phi Psi wf_Phi wf_Psi).
        apply Hfiber_FF'.
      * apply Hfiber_GG'.
    + intros I Gamma Phi wf_Gamma wf_Phi f.
      transitivity
        (@efh_sequent_map N P G I Gamma Phi wf_Gamma wf_Phi
          (@efh_sequent_map M N F' I Gamma Phi wf_Gamma wf_Phi f)).
      * eapply (@efh_sequent_map_proper N P G I Gamma Phi wf_Gamma wf_Phi).
        apply Hsequent_FF'.
      * apply Hsequent_GG'.
Defined.

Instance TermModel_EpsilonFullModel : EpsilonFullModel.
Proof.
  refine (mk_EpsilonFullModel
    (Base_SetoidCategory Sign Func)
    (Base_CartesianCategory Sign Func)
    (Base_TwoSortCategory Sign Func)
    (Base_SyntacticEpsilonFullModel Sign Func)
    (Base_SyntacticCoherentModel Sign Func)
    TermModel_GoodFibration
    TermModel_EpsilonHyperModel
    TermModel_AdjointEpsilonFullFibration).
Defined.

Definition closed_arrow_soundness_to_hom
  (M : EpsilonFullModel) (I : b_ty)
  (Phi Psi : @h_ty Sign Func Pred) (p : @h_tm Sign Func Pred)
  (d : @h_derivation Sign Func Pred HFunc HPred SM
        I [] p (Ty_Arrow Phi Psi))
  : @hom (efm_fiber M I) (efm_interp_h_ty M I Phi) (efm_interp_h_ty M I Psi).
Proof.
  eapply compose.
  - exact (@eval (efm_fiber M I) _ _
      (efm_interp_h_ty M I Phi) (efm_interp_h_ty M I Psi)).
  - apply prod_map.
    + eapply compose.
      * exact (efm_soundness M d).
      * apply terminal_map.
    + apply id.
Defined.

Fixpoint interp_h_ctx_to_make_ctx_ty
  (M : EpsilonFullModel) (I : b_ty) (G : @h_context Sign Func Pred)
  : @hom (efm_fiber M I)
      (efm_interp_h_ctx M I G)
      (efm_interp_h_ty M I (h_make_ctx_ty G)) :=
  match G with
  | [] => terminal_map
  | Phi :: G' =>
      prod_map
        (@compose (efm_fiber M I)
          (efm_interp_h_ctx M I (Phi :: G'))
          (efm_interp_h_ctx M I G')
          (efm_interp_h_ty M I (h_make_ctx_ty G'))
          (interp_h_ctx_to_make_ctx_ty M I G')
          prod_fst)
        prod_snd
  end.

Definition closed_ctx_arrow_soundness_to_hom
  (M : EpsilonFullModel) (I : b_ty)
  (G : @h_context Sign Func Pred) (Phi : @h_ty Sign Func Pred)
  (p : @h_tm Sign Func Pred)
  (d : @h_derivation Sign Func Pred HFunc HPred SM
        I [] p (Ty_Arrow (h_make_ctx_ty G) Phi))
  : @hom (efm_fiber M I) (efm_interp_h_ctx M I G) (efm_interp_h_ty M I Phi).
Proof.
  eapply compose.
  - exact (closed_arrow_soundness_to_hom M I (h_make_ctx_ty G) Phi p d).
  - exact (interp_h_ctx_to_make_ctx_ty M I G).
Defined.

Definition term_model_base_hom
  {I A : b_ty}
  (f : @hom (@efm_cat TermModel_EpsilonFullModel)
      (efm_interp_ty TermModel_EpsilonFullModel I)
      (efm_interp_ty TermModel_EpsilonFullModel A))
  : @hom_base Sign Func HFunc I A.
Proof.
  unfold efm_interp_ty in f.
  cbn in f.
  rewrite (interp_ty_id Sign Func I) in f.
  rewrite (interp_ty_id Sign Func A) in f.
  exact f.
Defined.

Lemma tm_of_eq_rect_src_tgt :
  forall (I A I_sem A_sem : b_ty)
    (eqI : I_sem = I) (eqA : A_sem = A)
    (f : @hom_base Sign Func HFunc I_sem A_sem),
    tm_of
      (eq_rect A_sem (fun o : b_ty => @hom_base Sign Func HFunc I o)
        (eq_rect I_sem (fun o : b_ty => @hom_base Sign Func HFunc o A_sem)
          f I eqI) A eqA)
    = tm_of f.
Proof.
  intros I A I_sem A_sem eqI eqA f.
  destruct eqI.
  destruct eqA.
  reflexivity.
Defined.

Lemma term_model_base_hom_interp_tm_tm_of
  {I A : b_ty} {t : @b_tm Sign Func}
  (dt : @base_typing Sign Func HFunc I t A)
  : tm_of (term_model_base_hom (efm_interp_tm TermModel_EpsilonFullModel dt)) = t.
Proof.
  unfold term_model_base_hom, efm_interp_tm, efm_interp_ty.
  cbn.
  rewrite tm_of_eq_rect_src_tgt.
  apply interp_tm_term.
Defined.

Lemma term_model_base_hom_tm_of
  {I A : b_ty}
  (f : @hom (@efm_cat TermModel_EpsilonFullModel)
    (efm_interp_ty TermModel_EpsilonFullModel I)
    (efm_interp_ty TermModel_EpsilonFullModel A))
  : tm_of (term_model_base_hom f) = tm_of f.
Proof.
  unfold term_model_base_hom, efm_interp_ty.
  cbn.
  rewrite tm_of_eq_rect_src_tgt.
  reflexivity.
Defined.

Definition TermModel_to_base_map
  (M : EpsilonFullModel) {I A : b_ty}
  (f : @hom (@efm_cat TermModel_EpsilonFullModel)
      (efm_interp_ty TermModel_EpsilonFullModel I)
      (efm_interp_ty TermModel_EpsilonFullModel A))
  : @hom (@efm_cat M) (efm_interp_ty M I) (efm_interp_ty M A) :=
  efm_interp_tm M (deriv_of (term_model_base_hom f)).

Definition TermModel_to_fiber_map
  (M : EpsilonFullModel) (I : b_ty)
  (Phi Psi : @h_ty Sign Func Pred)
  (wf_Phi : WellFormed I Phi) (wf_Psi : WellFormed I Psi)
  (f : @hom (efm_fiber TermModel_EpsilonFullModel I)
      (efm_interp_h_ty TermModel_EpsilonFullModel I Phi)
      (efm_interp_h_ty TermModel_EpsilonFullModel I Psi))
  : @hom (efm_fiber M I) (efm_interp_h_ty M I Phi) (efm_interp_h_ty M I Psi).
Proof.
  unfold efm_fiber, efm_interp_h_ty, efm_interp_ty in f.
  cbn in f.
  destruct f as [p d].
  pose proof (term_model_interp_id I Phi wf_Phi) as H_phi.
  pose proof (term_model_interp_id I Psi wf_Psi) as H_psi.
  cbn in H_phi, H_psi.
  rewrite H_phi in d.
  rewrite H_psi in d.
  rewrite (interp_ty_id Sign Func I) in d.
  exact (closed_arrow_soundness_to_hom M I Phi Psi p d).
Defined.

Definition TermModel_to_sequent_map
  (M : EpsilonFullModel) (I : b_ty)
  (G : @h_context Sign Func Pred) (Phi : @h_ty Sign Func Pred)
  (wf_G : All_WellFormed I G) (wf_Phi : WellFormed I Phi)
  (f : @hom (efm_fiber TermModel_EpsilonFullModel I)
      (efm_interp_h_ctx TermModel_EpsilonFullModel I G)
      (efm_interp_h_ty TermModel_EpsilonFullModel I Phi))
  : @hom (efm_fiber M I) (efm_interp_h_ctx M I G) (efm_interp_h_ty M I Phi).
Proof.
  unfold efm_fiber, efm_interp_h_ctx, efm_interp_h_ty, efm_interp_ty in f.
  cbn in f.
  destruct f as [p d].
  pose proof (term_model_interp_ctx_id I G wf_G) as H_ctx.
  pose proof (term_model_interp_id I Phi wf_Phi) as H_phi.
  cbn in H_ctx, H_phi.
  rewrite H_ctx in d.
  rewrite H_phi in d.
  rewrite (interp_ty_id Sign Func I) in d.
  exact (closed_ctx_arrow_soundness_to_hom M I G Phi p d).
Defined.

Definition TermModel_to (M : EpsilonFullModel)
  : EpsilonFullModelHom TermModel_EpsilonFullModel M.
Proof.
  refine (@mk_EpsilonFullModelHom TermModel_EpsilonFullModel M
    (fun I A f => TermModel_to_base_map M f)
    _
    _
    (fun I Phi Psi wf_Phi wf_Psi f =>
       TermModel_to_fiber_map M I Phi Psi wf_Phi wf_Psi f)
    _
    _
    _
    (fun I G Phi wf_G wf_Phi f =>
       TermModel_to_sequent_map M I G Phi wf_G wf_Phi f)
    _
    _).
  - intros I A f g Hfg.
    unfold TermModel_to_base_map.
    eapply (@base_soundness_equational
      Sign Func HFunc
      (@efm_cat M) (@efm_cartesian M) (@efm_twosort M)
      (@efm_base_model M) (@efm_base_coherent M)).
    exists (deriv_of (term_model_base_hom f)).
    exists (deriv_of (term_model_base_hom g)).
    unfold term_model_base_hom.
    cbn in *.
    destruct (interp_ty_id Sign Func I).
    destruct (interp_ty_id Sign Func A).
    exact Hfg.
  - intros I A t dt.
    unfold TermModel_to_base_map.
    eapply (@base_soundness_equational
      Sign Func HFunc
      (@efm_cat M) (@efm_cartesian M) (@efm_twosort M)
      (@efm_base_model M) (@efm_base_coherent M)).
    pose (h := term_model_base_hom (efm_interp_tm TermModel_EpsilonFullModel dt)).
    exists (deriv_of h).
    exists dt.
    eapply (@base_equiv_cast Sign Func HFunc
      I A I A (tm_of h) t t t
      eq_refl eq_refl
      (eq_sym (term_model_base_hom_interp_tm_tm_of dt)) eq_refl
      dt dt (deriv_of h) dt).
    apply BE_Refl.
  - intros I Phi Psi wf_Phi wf_Psi f g Hfg.
    apply (fiber_is_thin (efm_interp_ty M I)).
  - intros I Phi wf_Phi.
    apply (fiber_is_thin (efm_interp_ty M I)).
  - intros I Phi Psi Chi wf_Phi wf_Psi wf_Chi g f.
    apply (fiber_is_thin (efm_interp_ty M I)).
  - intros I G Phi wf_G wf_Phi f g Hfg.
    apply (fiber_is_thin (efm_interp_ty M I)).
  - intros I G p Phi d.
    apply (fiber_is_thin (efm_interp_ty M I)).
Defined.

Class TermModelBasePreserving
  (M : EpsilonFullModel)
  (F : EpsilonFullModelHom TermModel_EpsilonFullModel M) := mk_TermModelBasePreserving {
  term_model_base_preserving :
    forall (I A : b_ty)
      (f : @hom (@efm_cat TermModel_EpsilonFullModel)
        (efm_interp_ty TermModel_EpsilonFullModel I)
        (efm_interp_ty TermModel_EpsilonFullModel A)),
      @efh_base_map TermModel_EpsilonFullModel M F I A f
      ≅
      TermModel_to_base_map M f
}.

Lemma term_model_base_hom_reinterp_equiv
  {I A : b_ty}
  (f : @hom (@efm_cat TermModel_EpsilonFullModel)
    (efm_interp_ty TermModel_EpsilonFullModel I)
    (efm_interp_ty TermModel_EpsilonFullModel A))
  : f ≅ efm_interp_tm TermModel_EpsilonFullModel
      (deriv_of (term_model_base_hom f)).
Proof.
  pose (h := term_model_base_hom f).
  eapply (@base_equiv_cast Sign Func HFunc
    (efm_interp_ty TermModel_EpsilonFullModel I)
    (efm_interp_ty TermModel_EpsilonFullModel A)
    (efm_interp_ty TermModel_EpsilonFullModel I)
    (efm_interp_ty TermModel_EpsilonFullModel A)
    (tm_of f)
    (tm_of (efm_interp_tm TermModel_EpsilonFullModel (deriv_of h)))
    (tm_of f) (tm_of f)
    eq_refl eq_refl eq_refl
    (eq_sym
      (eq_trans
        (@interp_tm_term Sign Func HFunc I A (tm_of h) (deriv_of h))
        (term_model_base_hom_tm_of f)))
    (deriv_of f) (deriv_of f)
    (deriv_of f)
    (deriv_of (efm_interp_tm TermModel_EpsilonFullModel (deriv_of h)))).
  apply BE_Refl.
Defined.

Instance TermModel_hom_base_preserving
  (M : EpsilonFullModel)
  (F : EpsilonFullModelHom TermModel_EpsilonFullModel M)
  : TermModelBasePreserving M F.
Proof.
  constructor.
  intros I A f.
  unfold TermModel_to_base_map.
  transitivity
    (@efh_base_map TermModel_EpsilonFullModel M F I A
      (efm_interp_tm TermModel_EpsilonFullModel
        (deriv_of (term_model_base_hom f)))).
  - apply efh_base_map_proper.
    apply term_model_base_hom_reinterp_equiv.
  - apply efh_base_soundness.
Defined.

Definition TermModel_weak_initial :
  forall M : EpsilonFullModel,
    inhabited (EpsilonFullModelHom TermModel_EpsilonFullModel M).
Proof.
  intro M.
  constructor.
  exact (TermModel_to M).
Defined.

Definition TermModel_fiber_initial_unique :
  forall (M : EpsilonFullModel)
    (F G : EpsilonFullModelHom TermModel_EpsilonFullModel M),
    forall (I : b_ty) (Phi Psi : @h_ty Sign Func Pred)
      (wf_Phi : WellFormed I Phi) (wf_Psi : WellFormed I Psi)
      (f : @hom (efm_fiber TermModel_EpsilonFullModel I)
        (efm_interp_h_ty TermModel_EpsilonFullModel I Phi)
        (efm_interp_h_ty TermModel_EpsilonFullModel I Psi)),
      @efh_fiber_map TermModel_EpsilonFullModel M F I Phi Psi wf_Phi wf_Psi f
      ≅
      @efh_fiber_map TermModel_EpsilonFullModel M G I Phi Psi wf_Phi wf_Psi f.
Proof.
  intros M F G I Phi Psi wf_Phi wf_Psi f.
  apply (fiber_is_thin (efm_interp_ty M I)).
Defined.

Lemma TermModel_initial_unique_from_base_preserving :
  forall (M : EpsilonFullModel)
    (F G : EpsilonFullModelHom TermModel_EpsilonFullModel M),
    TermModelBasePreserving M F ->
    TermModelBasePreserving M G ->
    EpsilonFullModelHom_equiv F G.
Proof.
  intros M F G HF HG.
  split.
  - intros I A f.
    transitivity (TermModel_to_base_map M f).
    + exact (@term_model_base_preserving M F HF I A f).
    + symmetry.
      exact (@term_model_base_preserving M G HG I A f).
  - split.
    + intros I Phi Psi wf_Phi wf_Psi f.
      apply (TermModel_fiber_initial_unique M F G I Phi Psi wf_Phi wf_Psi f).
    + intros I Gamma Phi wf_Gamma wf_Phi f.
      apply (fiber_is_thin (efm_interp_ty M I)).
Defined.

Definition TermModel_initial_unique :
  forall (M : EpsilonFullModel)
    (F G : EpsilonFullModelHom TermModel_EpsilonFullModel M),
    EpsilonFullModelHom_equiv F G.
Proof.
  intros M F G.
  apply TermModel_initial_unique_from_base_preserving.
  - apply TermModel_hom_base_preserving.
  - apply TermModel_hom_base_preserving.
Defined.

(* Compatibility name: uniqueness is in the hom setoid, not record equality. *)
Definition TermModel_strict_initial_unique :
  forall (M : EpsilonFullModel)
    (F G : EpsilonFullModelHom TermModel_EpsilonFullModel M),
    EpsilonFullModelHom_equiv F G :=
  TermModel_initial_unique.

Definition TermModel_interpretation_natural
  (M N : EpsilonFullModel) (F : EpsilonFullModelHom M N) :
  EpsilonFullModelHom_equiv
    (EpsilonFullModel_comp F (TermModel_to M)) (TermModel_to N) :=
  TermModel_initial_unique N _ _.

Definition TermModel_interpretation_identity :
  EpsilonFullModelHom_equiv
    (TermModel_to TermModel_EpsilonFullModel)
    (EpsilonFullModel_id TermModel_EpsilonFullModel) :=
  TermModel_initial_unique TermModel_EpsilonFullModel _ _.

End EpsilonFullModelCategory.
