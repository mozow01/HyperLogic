
Require Import Coq.Classes.Morphisms.
Require Import List Arith PeanoNat Lia.
Import ListNotations.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC. 
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import HyperLogic.Cat.Fibration.

Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Semantics.Simple.Base_Simple_Soundness.
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum.
(*Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.*)
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Lemmas.

(** Well-formedness extractors for derivations. *)
Definition ext_prod_L {I A B} (wf : WellFormed I (Ty_Prod A B)) : WellFormed I A :=
  match wf in (WellFormed I' P) return (match P with Ty_Prod A' _ => WellFormed I' A' | _ => Datatypes.unit end) with
  | WF_Prod _ _ _ wfA _ => wfA | _ => Datatypes.tt end.

Definition ext_prod_R {I A B} (wf : WellFormed I (Ty_Prod A B)) : WellFormed I B :=
  match wf in (WellFormed I' P) return (match P with Ty_Prod _ B' => WellFormed I' B' | _ => Datatypes.unit end) with
  | WF_Prod _ _ _ _ wfB => wfB | _ => Datatypes.tt end.

Definition ext_sum_L {I A B} (wf : WellFormed I (Ty_Sum A B)) : WellFormed I A :=
  match wf in (WellFormed I' P) return (match P with Ty_Sum A' _ => WellFormed I' A' | _ => Datatypes.unit end) with
  | WF_Sum _ _ _ wfA _ => wfA | _ => Datatypes.tt end.

Definition ext_sum_R {I A B} (wf : WellFormed I (Ty_Sum A B)) : WellFormed I B :=
  match wf in (WellFormed I' P) return (match P with Ty_Sum _ B' => WellFormed I' B' | _ => Datatypes.unit end) with
  | WF_Sum _ _ _ _ wfB => wfB | _ => Datatypes.tt end.

Definition ext_arr_L {I A B} (wf : WellFormed I (Ty_Arrow A B)) : WellFormed I A :=
  match wf in (WellFormed I' P) return (match P with Ty_Arrow A' _ => WellFormed I' A' | _ => Datatypes.unit end) with
  | WF_Arrow _ _ _ wfA _ => wfA | _ => Datatypes.tt end.

Definition ext_arr_R {I A B} (wf : WellFormed I (Ty_Arrow A B)) : WellFormed I B :=
  match wf in (WellFormed I' P) return (match P with Ty_Arrow _ B' => WellFormed I' B' | _ => Datatypes.unit end) with
  | WF_Arrow _ _ _ _ wfB => wfB | _ => Datatypes.tt end.

Definition ext_all {I A Body} (wf : WellFormed I (Ty_All A Body)) : WellFormed (b_Prod I A) Body :=
  match wf in (WellFormed I' P) return (match P with Ty_All A' B' => WellFormed (b_Prod I' A') B' | _ => Datatypes.unit end) with
  | WF_All _ _ _ wfBody => wfBody | _ => Datatypes.tt end.

Definition ext_ex {I A Body} (wf : WellFormed I (Ty_Ex A Body)) : WellFormed (b_Prod I A) Body :=
  match wf in (WellFormed I' P) return (match P with Ty_Ex A' B' => WellFormed (b_Prod I' A') B' | _ => Datatypes.unit end) with
  | WF_Ex _ _ _ wfBody => wfBody | _ => Datatypes.tt end.

(* Atom well-formedness exposes its codomain and base typing derivation. *)
Definition ext_atom {I p t} (wf : WellFormed I (Ty_Atom p t)) : { A : b_ty & base_typing I t A } :=
  match wf in (WellFormed I' P) return (match P with Ty_Atom p' t' => { A : b_ty & base_typing I' t' A } | _ => Datatypes.unit end) with
  | WF_Atom _ _ _ A dt => existT _ A dt | _ => Datatypes.tt end.



Class HyperModel {C : SetoidCategory} {CC : CartesianCategory C} 
                 {TSC : TwoSortCategory C} {GF : GoodFibration C} 
                 (SGF : StrictGoodFibration C GF) := {
  
  i_atom : forall (p : nat) (t : b_tm) (I A : b_ty) (dt : base_typing I t A), @obj (Fiber (interp_ty I)) ;
  
  i_atom_pb : forall (p : nat) (t : b_tm) (I J A : b_ty) (f : b_tm) 
                     (df : base_typing I f J) (dt : base_typing J t A),
      @fobj _ _ (Pullback (interp_tm df)) (i_atom p t J A dt) ≅O i_atom p (b_comp t f) I A (BT_Comp dt df) ;
      
  base_model_sound : forall (I J : b_ty) (f g : b_tm) (df : base_typing I f J) (dg : base_typing I g J),
      base_equiv I J f g ->
      interp_tm df ≅ interp_tm dg ;
      
  i_atom_cong : forall (p : nat) (t1 t2 : b_tm) (I A : b_ty)
                       (d1 : base_typing I t1 A) (d2 : base_typing I t2 A),
      base_equiv I A t1 t2 ->
      i_atom p t1 I A d1 ≅O i_atom p t2 I A d2}.

Fixpoint interp_h_ty {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
                     {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF}
                     (I : b_ty) (Phi : h_ty) {struct Phi} : WellFormed I Phi -> @obj (Fiber (interp_ty I)) :=
  match Phi return (WellFormed I Phi -> @obj (Fiber (interp_ty I))) with
  | Ty_Unit => fun _ => terminal
  | Ty_Void => fun _ => initial
  | Ty_Prod A B => fun wf => prod (interp_h_ty I A (ext_prod_L wf)) (interp_h_ty I B (ext_prod_R wf))
  | Ty_Sum A B => fun wf => coprod (interp_h_ty I A (ext_sum_L wf)) (interp_h_ty I B (ext_sum_R wf))
  | Ty_Arrow A B => fun wf => exp (interp_h_ty I B (ext_arr_R wf)) (interp_h_ty I A (ext_arr_L wf))
  | Ty_Atom p t => fun wf => 
      i_atom p t I (projT1 (ext_atom wf)) (projT2 (ext_atom wf))
  | Ty_All A Body => fun wf => @right_adj_obj _ _ _ pullback_has_right_adjoint (interp_h_ty (b_Prod I A) Body (ext_all wf))
  | Ty_Ex A Body => fun wf => @left_adj_obj _ _ _ pullback_has_left_adjoint (interp_h_ty (b_Prod I A) Body (ext_ex wf))
  end.
  
Definition ext_ctx_hd {I Phi G} (wfc : wf_ctx I (Phi :: G)) : WellFormed I Phi :=
  match wfc in (wf_ctx _ G') return (match G' with | nil => Datatypes.unit | Phi' :: _ => WellFormed I Phi' end) with
  | WFC_cons _ _ _ wf_Phi _ => wf_Phi 
  | _ => Datatypes.tt 
  end.

Definition ext_ctx_tl {I Phi G} (wfc : wf_ctx I (Phi :: G)) : wf_ctx I G :=
  match wfc in (wf_ctx _ G') return (match G' with | nil => Datatypes.unit | _ :: G'' => wf_ctx I G'' end) with
  | WFC_cons _ _ _ _ wfc_G => wfc_G 
  | _ => Datatypes.tt 
  end.

Fixpoint interp_h_ctx {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
                      {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF}
                      (I : b_ty) (G : h_context) {struct G} : wf_ctx I G -> @obj (Fiber (interp_ty I)) :=
  match G return (wf_ctx I G -> @obj (Fiber (interp_ty I))) with
  | nil => fun _ => terminal
  | Phi :: G' => fun wfc => prod (interp_h_ctx I G' (ext_ctx_tl wfc)) (interp_h_ty I Phi (ext_ctx_hd wfc))
  end.


Lemma typing_pullback_ext :
  forall {I J b : b_ty} {g : b_tm} (dg : base_typing I g J),
  base_typing (b_Prod I b) (b_pullback_ext g) (b_Prod J b).
Proof.
  intros I J b g dg.
  unfold b_pullback_ext.
  apply BT_Pair.
  - eapply BT_Comp; [exact dg | apply BT_Fst].
  - apply BT_Snd.
Defined.

Lemma form_pullback_general_iso :
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF}
         {I J : b_ty} {Phi : h_ty} (wf : WellFormed J Phi) (g : b_tm) (dg : base_typing I g J),
  interp_h_ty I (form_pullback g Phi) (wf_pullback I J g Phi dg wf) ≅O
  @fobj _ _ (Pullback (interp_tm dg)) (interp_h_ty J Phi wf).
Proof.
  intros C CC TSC GF SGF HM I J Phi wf.
  
  revert I. 
  (* [I_src] avoids shadowing contexts introduced by formula constructors. *)
  induction wf; intros I_src g dg; cbn.
  
  -
    symmetry. apply pb_term_iso.
    
  -
    symmetry. apply pb_init_iso.
    
  -
    eapply iso_trans.
    + apply (prod_iso_cong (IHwf1 I_src g dg) (IHwf2 I_src g dg)).
    + symmetry. apply pb_prod_iso.
    
  -
    eapply iso_trans.
    + apply (coprod_iso_cong (IHwf1 I_src g dg) (IHwf2 I_src g dg)).
    + symmetry. apply pb_coprod_iso.
    
  -
    eapply iso_trans.
    + apply (exp_iso_cong (IHwf2 I_src g dg) (IHwf1 I_src g dg)).
    + symmetry. apply pb_exp_iso.
    
  -
    symmetry. apply i_atom_pb.
    
  -
    eapply iso_trans.
    + apply pi_iso_cong. 
      exact (IHwf (b_Prod I_src A) (b_pullback_ext g) (typing_pullback_ext dg)).
    + symmetry. apply beck_chevalley_pi.
    
  -
    eapply iso_trans.
    + apply sigma_iso_cong. 
      exact (IHwf (b_Prod I_src A) (b_pullback_ext g) (typing_pullback_ext dg)).
    + symmetry. apply beck_chevalley_sigma.
Defined.

Lemma ctx_pullback_iso : 
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF} 
         {I A : b_ty} {G : h_context} (wfc : wf_ctx I G),
  interp_h_ctx (b_Prod I A) (ctx_pullback b_fst G) (wf_ctx_pullback _ _ b_fst G BT_Fst wfc) ≅O 
  @fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ctx I G wfc).
Proof.
  intros C CC TSC GF SGF HM I A G wfc.
  induction wfc; cbn.
  
  -
    symmetry. apply pb_term_iso.
    
  -
    eapply iso_trans.
    + (* Explicit proof arguments keep [prod_iso_cong] from leaving unification variables. *)
      apply (prod_iso_cong IHwfc (form_pullback_general_iso w b_fst BT_Fst)).
    + symmetry. apply pb_prod_iso.
Defined.



Lemma semantic_pi_ty : 
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF} 
         {I : b_ty} {Phi : h_ty} (wf1 wf2 : WellFormed I Phi),
  interp_h_ty I Phi wf1 ≅O interp_h_ty I Phi wf2.
Proof.
  intros C CC TSC GF SGF HM I Phi.
  (* Generalize [I] so induction applies under quantifiers. *)
  revert I.
  induction Phi; intros I wf1 wf2; cbn.
  
  - apply iso_refl.
  - apply iso_refl.
  - apply prod_iso_cong; [apply IHPhi1 | apply IHPhi2].
  - apply coprod_iso_cong; [apply IHPhi1 | apply IHPhi2].
  - apply exp_iso_cong; [apply IHPhi2 | apply IHPhi1].
  
  -
    destruct (ext_atom wf1) as [A1 dt1].
    destruct (ext_atom wf2) as [A2 dt2].
    assert (Heq : A1 = A2) by (eapply base_typing_unique; [exact dt1 | exact dt2]).
    subst A2.
    apply i_atom_cong.
    eapply BE_Refl. exact dt1.

  -
    apply pi_iso_cong. apply (IHPhi (b_Prod I b)).
  -
    apply sigma_iso_cong. apply (IHPhi (b_Prod I b)).
Defined.

Lemma form_pullback_iso :
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF}
         {I A : b_ty} {f : b_tm} (df : base_typing I f A) {Phi : h_ty}
         (wf : WellFormed (b_Prod I A) Phi),
  interp_h_ty I (form_pullback (b_pair b_id f) Phi) 
              (wf_pullback I (b_Prod I A) (b_pair b_id f) Phi (BT_Pair BT_Id df) wf) ≅O
  @fobj _ _ (Pullback (interp_tm (BT_Pair BT_Id df))) (interp_h_ty (b_Prod I A) Phi wf).
Proof.
  intros. apply (form_pullback_general_iso wf (b_pair b_id f) (BT_Pair BT_Id df)).
Defined.

Lemma form_pullback_fst_iso : 
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF} 
         {I A : b_ty} {Phi : h_ty} (wf : WellFormed I Phi),
  interp_h_ty (b_Prod I A) (form_pullback b_fst Phi) 
              (wf_pullback (b_Prod I A) I b_fst Phi BT_Fst wf) ≅O 
  @fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I Phi wf).
Proof.
  intros. apply (form_pullback_general_iso wf b_fst BT_Fst).
Defined.

Lemma pb_eval_iso : 
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF} 
         {I A : b_ty} {f : b_tm} (df : base_typing I f A) {Phi : h_ty}
         (wf : WellFormed (b_Prod I A) Phi),
  hom (interp_h_ty I (Ty_All A Phi) (WF_All I A Phi wf)) 
      (@fobj _ _ (Pullback (interp_tm (BT_Pair BT_Id df))) 
       (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) 
         (interp_h_ty I (Ty_All A Phi) (WF_All I A Phi wf)))).
Proof.
  intros. eapply compose.
  - eapply compose.
    + apply (@iso_to _ _ _ (pullback_comp_iso prod_fst (prod_map (id (interp_ty I)) (interp_tm df)) _)).
    + assert (H_eq : id (interp_ty I) ≅ compose prod_fst (prod_map (id (interp_ty I)) (interp_tm df))).
      { symmetry. apply prod_map_fst. }
      apply (@iso_to _ _ _ (pb_iso _ _ H_eq _)).
  - apply (@iso_from _ _ _ (pullback_id_iso _)).
Defined.

Lemma pb_unit_iso : 
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF} 
         {I A : b_ty} {f : b_tm} (df : base_typing I f A) {Phi : h_ty}
         (wf : WellFormed (b_Prod I A) Phi),
  hom (@fobj _ _ (Pullback (interp_tm (BT_Pair BT_Id df))) 
        (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I (Ty_Ex A Phi) (WF_Ex I A Phi wf)))) 
      (interp_h_ty I (Ty_Ex A Phi) (WF_Ex I A Phi wf)).
Proof.
  intros. eapply compose.
  - apply (@iso_to _ _ _ (pullback_id_iso _)).
  - eapply compose.
    + assert (H_eq : compose prod_fst (prod_map (id (interp_ty I)) (interp_tm df)) ≅ id (interp_ty I)).
      { apply prod_map_fst. }
      apply (@iso_to _ _ _ (pb_iso _ _ H_eq _)).
    + apply (@iso_from _ _ _ (pullback_comp_iso prod_fst (prod_map (id (interp_ty I)) (interp_tm df)) _)).
Defined.

Lemma ex_elim_frobenius : 
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF} 
         {I A : b_ty} {G : h_context} {Phi Chi : h_ty} 
         (wfc : wf_ctx I G) (wf_Phi : WellFormed (b_Prod I A) Phi) (wf_Chi : WellFormed I Chi),
  hom (prod (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ctx I G wfc)) 
            (interp_h_ty (b_Prod I A) Phi wf_Phi)) 
      (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I Chi wf_Chi)) -> 
  hom (prod (interp_h_ctx I G wfc) (interp_h_ty I (Ty_Ex A Phi) (WF_Ex I A Phi wf_Phi))) (interp_h_ty I Chi wf_Chi).
Proof.
  intros C CC TSC GF SGF HM I A G Phi Chi wfc wf_Phi wf_Chi H_premissza.
  assert (H_curry : hom (interp_h_ty (b_Prod I A) Phi wf_Phi) 
                        (exp (@fobj _ _ (Pullback (interp_tm BT_Fst)) (interp_h_ty I Chi wf_Chi)) 
                             (@fobj _ _ (Pullback (interp_tm BT_Fst)) (interp_h_ctx I G wfc)))).
  { apply exp_map. eapply compose; [exact H_premissza | apply prod_map; [apply prod_snd | apply prod_fst]]. }
  assert (H_pb : hom (interp_h_ty (b_Prod I A) Phi wf_Phi) 
                     (@fobj _ _ (Pullback (interp_tm BT_Fst)) 
                            (exp (interp_h_ty I Chi wf_Chi) (interp_h_ctx I G wfc)))).
  { eapply compose; [apply (@iso_from _ _ _ (pb_exp_iso (interp_tm BT_Fst) _ _)) | exact H_curry]. }
  assert (H_sigma : hom (interp_h_ty I (Ty_Ex A Phi) (WF_Ex _ _ _ wf_Phi)) 
                        (exp (interp_h_ty I Chi wf_Chi) (interp_h_ctx I G wfc))).
  { apply left_adj_mor. exact H_pb. }
  eapply compose.
  - eapply eval.
  - apply prod_map.
    + eapply compose; [exact H_sigma | apply prod_snd].
    + apply prod_fst.
Defined.

Lemma pullback_fmap_iso : 
  forall {C : SetoidCategory} {CC : CartesianCategory C} {GF : GoodFibration C} {X Y : obj} (f : hom X Y)
         (A B : @obj (Fiber Y)),
  A ≅O B -> @fobj _ _ (Pullback f) A ≅O @fobj _ _ (Pullback f) B.
Proof.
  intros C CC GF X Y f A B H.
  refine {|
    iso_to   := @fmap _ _ (Pullback f) A B (@iso_to _ _ _ H) ;
    iso_from := @fmap _ _ (Pullback f) B A (@iso_from _ _ _ H)
  |}.
  - apply (fiber_is_thin X).
  - apply (fiber_is_thin X).
Defined.

Lemma interp_form_equiv : 
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF} 
         {I : b_ty} {Phi Psi : h_ty} (H : form_equiv I Phi Psi)
         (wf1 : WellFormed I Phi) (wf2 : WellFormed I Psi),
  interp_h_ty I Phi wf1 ≅O interp_h_ty I Psi wf2.
Proof.
  intros C CC TSC GF SGF HM I Phi Psi H.
  induction H; intros wf1 wf2; cbn.
  
  -
    destruct (ext_atom wf1) as [A1 dt1].
    destruct (ext_atom wf2) as [A2 dt2].
    assert (Heq1 : A1 = A) by (eapply base_typing_unique; [exact dt1 | exact d1]).
    assert (Heq2 : A2 = A) by (eapply base_typing_unique; [exact dt2 | exact d2]).
    subst A1 A2.
    apply i_atom_cong. exact b.

  -   apply semantic_pi_ty.
  -   symmetry. apply IHform_equiv.
  
  -
    assert (wf_Psi : WellFormed I Psi) by exact (snd (form_equiv_wf I Phi Psi H)).
    eapply iso_trans. 
    + apply (IHform_equiv1 wf1 wf_Psi).
    + apply (IHform_equiv2 wf_Psi wf2).
    
  -   apply prod_iso_cong; [apply IHform_equiv1 | apply IHform_equiv2].
  -   apply coprod_iso_cong; [apply IHform_equiv1 | apply IHform_equiv2].
  -   apply exp_iso_cong; [apply IHform_equiv2 | apply IHform_equiv1].
  -   apply pi_iso_cong; apply IHform_equiv.
  -   apply sigma_iso_cong; apply IHform_equiv.

  -
    eapply iso_trans. { apply semantic_pi_ty. } 
    eapply iso_trans.
    { apply (form_pullback_general_iso w b_id BT_Id). }
    eapply iso_trans.
    { assert (H_id : interp_tm BT_Id ≅ id (interp_ty I)) by reflexivity.
      eapply iso_trans.
      { apply (@pb_iso _ _ _ _ _ _ _ H_id). }
      { apply pullback_id_iso. } }
    { apply semantic_pi_ty. } 

  -
    eapply iso_trans. { apply semantic_pi_ty. } 
    eapply iso_trans.
    { eapply (form_pullback_general_iso (wf_pullback _ _ _ _ _ w) g dg). }
    eapply iso_trans.
    { apply pullback_fmap_iso. apply (form_pullback_general_iso w f df). }
    eapply iso_trans.
    { symmetry. apply pullback_comp_iso. }
    eapply iso_trans.
    { assert (H_comp : compose (interp_tm df) (interp_tm dg) ≅ interp_tm (BT_Comp df dg)) by reflexivity.
      apply (@pb_iso _ _ _ _ _ _ _ H_comp). }
    eapply iso_trans.
    { symmetry. apply (form_pullback_general_iso w (b_comp f g) (BT_Comp df dg)). }
    { apply semantic_pi_ty. } 

  -
    eapply iso_trans. { apply semantic_pi_ty. } 
    eapply iso_trans.
    { apply (form_pullback_general_iso w f df). }
    eapply iso_trans.
    { assert (H_cong : interp_tm df ≅ interp_tm dg).
      { apply (base_model_sound I J f g df dg b). }
      apply (@pb_iso _ _ _ _ _ _ _ H_cong). }
    eapply iso_trans.
    { symmetry. apply (form_pullback_general_iso w g dg). }
    { apply semantic_pi_ty. } 
Defined.

Lemma semantic_pi_ctx : 
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF} 
         {I : b_ty} {G : h_context} (wfc1 wfc2 : wf_ctx I G),
  interp_h_ctx I G wfc1 ≅O interp_h_ctx I G wfc2.
Proof.
  intros C CC TSC GF SGF HM I G.
  induction G; intros wfc1 wfc2; cbn.
  - apply iso_refl.
  - apply prod_iso_cong; [apply IHG | apply semantic_pi_ty].
Defined.

Lemma interp_ctx_equiv : 
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF} 
         {I : b_ty} {G1 G2 : h_context} (H : ctx_equiv I G1 G2)
         (wfc1 : wf_ctx I G1) (wfc2 : wf_ctx I G2),
  interp_h_ctx I G1 wfc1 ≅O interp_h_ctx I G2 wfc2.
Proof.
  intros C CC TSC GF SGF HM I G1 G2 H.
  induction H; intros wfc1 wfc2; cbn.
  
  -
    apply iso_refl.
    
  -
    apply prod_iso_cong.
    + apply IHctx_equiv.
    + apply interp_form_equiv. exact f.
Defined.


Theorem hyper_soundness_inhabited 
  {C : SetoidCategory} {CC : CartesianCategory C}
  {TSC : TwoSortCategory C} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF}
  {I : b_ty} {G : h_context} {p : h_tm} {Phi : h_ty}
  (D : h_derivation I G p Phi) :
  forall (wfc : wf_ctx I G) (wf_Phi : WellFormed I Phi),
  hom (interp_h_ctx I G wfc) (interp_h_ty I Phi wf_Phi).
Proof.
  induction D; intros wfc wf_Phi.
  
  -
    cbn. eapply compose. 
    { apply (@iso_to _ _ _ (semantic_pi_ty (ext_ctx_hd wfc) wf_Phi)). }
    { apply prod_snd. }

  -
    cbn. eapply compose. 
    { apply (IHD (ext_ctx_tl wfc) wf_Phi). }
    { apply prod_fst. }

  -
    apply terminal_map.

  -
    cbn. apply exp_map. 
    apply (IHD (WFC_cons _ _ _ (ext_arr_L wf_Phi) wfc) (ext_arr_R wf_Phi)).

 -
    pose proof (well_formed_target _ _ _ _ D2) as wf_A.
    eapply compose. { eapply eval. }
    apply prod_map.
    +
      exact (IHD1 wfc (WF_Arrow _ _ _ wf_A wf_Phi)).
    + exact (IHD2 wfc wf_A).

  -
    cbn. apply prod_map.
    + exact (IHD1 wfc (ext_prod_L wf_Phi)).
    + exact (IHD2 wfc (ext_prod_R wf_Phi)).

  -
    pose proof (well_formed_target _ _ _ _ D) as wf_prod.
    eapply compose. 
    { apply (@iso_to _ _ _ (semantic_pi_ty (ext_prod_L wf_prod) wf_Phi)). }
    eapply compose. 
    { eapply prod_fst. }
    { exact (IHD wfc wf_prod). }

  -
    pose proof (well_formed_target _ _ _ _ D) as wf_prod.
    eapply compose. 
    { apply (@iso_to _ _ _ (semantic_pi_ty (ext_prod_R wf_prod) wf_Phi)). }
    eapply compose. 
    { eapply prod_snd. }
    { exact (IHD wfc wf_prod). }

  -
    cbn. eapply compose. 
    { apply coprod_inl. }
    { exact (IHD wfc (ext_sum_L wf_Phi)). }

  -
    cbn. eapply compose. 
    { apply coprod_inr. }
    { exact (IHD wfc (ext_sum_R wf_Phi)). }

  -
    pose proof (well_formed_target _ _ _ _ D1) as wf_sum.
    eapply compose.
    { eapply compose.
      { apply (coprod_map (IHD2 (WFC_cons _ _ _ (ext_sum_L wf_sum) wfc) wf_Phi) 
                          (IHD3 (WFC_cons _ _ _ (ext_sum_R wf_sum) wfc) wf_Phi)). }
      { eapply compose. { eapply eval. }
        eapply compose. { apply prod_map.
          { eapply compose.
            { apply (coprod_map (exp_map (compose coprod_inl (prod_map prod_snd prod_fst))) 
                                (exp_map (compose coprod_inr (prod_map prod_snd prod_fst)))). }
            { eapply prod_fst. } }
          { apply prod_snd. } }
        { eapply (prod_map prod_snd prod_fst). } } }
    { apply (prod_map (id _) (IHD1 wfc wf_sum)). }

  -
    eapply compose. 
    { apply initial_map. }
    { exact (IHD wfc (WF_Void I)). }

  -
    cbn. apply right_adj_mor. eapply compose.
    {
      exact (IHD (wf_ctx_pullback _ _ _ _ BT_Fst wfc) (ext_all wf_Phi)). }
    { apply (@iso_from _ _ _ (ctx_pullback_iso wfc)). }

  -
    pose proof (well_formed_target _ _ _ _ D) as wf_all.
    eapply compose. 
    { eapply (@iso_to _ _ _ (semantic_pi_ty _ wf_Phi)). }
    eapply compose. 
    {
      eapply (@iso_from _ _ _ (form_pullback_iso b (ext_all wf_all))). }
    eapply compose. 
    { eapply (@fmap _ _ (Pullback (interp_tm (BT_Pair BT_Id b))) _ _).
      apply (@epsilon _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) pullback_has_right_adjoint). }
    eapply compose. 
    {
      apply (pb_eval_iso b (ext_all wf_all)). }
    { exact (IHD wfc wf_all). }

  -
    pose proof (well_formed_target _ _ _ _ D) as wf_pb.
    eapply compose. 
    { eapply (@iso_to _ _ _ (semantic_pi_ty _ wf_Phi)). }
    eapply compose. 
    { eapply pb_unit_iso. }
    eapply compose. 
    { eapply (@fmap _ _ (Pullback (interp_tm (BT_Pair BT_Id b))) _ _).
      apply (@unit _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) pullback_has_left_adjoint). }
    eapply compose. 
    { apply (@iso_to _ _ _ (form_pullback_iso b (ext_ex wf_Phi))). }
    
    eapply compose. 
    { apply (@iso_to _ _ _ (semantic_pi_ty wf_pb _)). } 
    { exact (IHD wfc wf_pb). }

  -
    pose proof (well_formed_target _ _ _ _ D1) as wf_ex.
    pose proof (well_formed_target _ _ _ _ D2) as wf_chi_pb.
    eapply compose. 
    { apply (ex_elim_frobenius wfc (ext_ex wf_ex) wf_Phi).
      eapply compose. { apply (@iso_to _ _ _ (form_pullback_fst_iso wf_Phi)). }
      
      eapply compose. { apply (@iso_to _ _ _ (semantic_pi_ty wf_chi_pb _)). }
      
      eapply compose. { exact (IHD2 (WFC_cons _ _ _ (ext_ex wf_ex) (wf_ctx_pullback _ _ _ _ BT_Fst wfc)) wf_chi_pb). }
      { apply (prod_map (compose (@iso_from _ _ _ (ctx_pullback_iso wfc)) prod_fst) prod_snd). } }
    { apply prod_map; [apply (id _) | exact (IHD1 wfc wf_ex)]. }
  -
      pose proof (well_formed_ctx _ _ _ _ D) as wfc1.
      pose proof (fst (form_equiv_wf _ _ _ f)) as wf1.
      eapply compose. 
      { apply (@iso_to _ _ _ (interp_form_equiv f wf1 wf_Phi)). }
      eapply compose. 
      { exact (IHD wfc1 wf1). }
      { apply (@iso_from _ _ _ (interp_ctx_equiv c wfc1 wfc)). }
Defined.