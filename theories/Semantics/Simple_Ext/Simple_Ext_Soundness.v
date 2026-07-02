(* HyperLogic/theories/Semantics/Simple_Ext/Simple_Ext_Soundness.v *)

Require Import Coq.Classes.Morphisms.
Require Import List Arith PeanoNat Lia.
Require Import Stdlib.Program.Equality.
Import ListNotations.

(* Kategóriaelméleti alapok *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC. 
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import HyperLogic.Cat.Fibration.

(* Szintaxis és Bázis Szemantika *)
Require Import HyperLogic.Logic.Base.Simple_Ext.Base_Syntax.
Require Import HyperLogic.Semantics.Simple_Ext.Base_Epsilon_Soundness.
Require Import HyperLogic.Semantics.Simple_Ext.Simple_Ext_Fibration.
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum.
Require Import HyperLogic.Logic.Hyper.Simple_Ext.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple_Ext.Hyper_Lemmas.




(* ================================================================= *)
(* AXIOM-FREE EXTRACTORS (Sign paraméterrel)                         *)
(* ================================================================= *)

Definition ext_prod_L {Sign : Type} {I A B} (wf : @WellFormed Sign I (Ty_Prod A B)) : @WellFormed Sign I A :=
  match wf in (@WellFormed _ I' P) return (match P with Ty_Prod A' _ => @WellFormed Sign I' A' | _ => Datatypes.unit end) with
  | WF_Prod _ _ _ wfA _ => wfA | _ => Datatypes.tt end.

Definition ext_prod_R {Sign : Type} {I A B} (wf : @WellFormed Sign I (Ty_Prod A B)) : @WellFormed Sign I B :=
  match wf in (@WellFormed _ I' P) return (match P with Ty_Prod _ B' => @WellFormed Sign I' B' | _ => Datatypes.unit end) with
  | WF_Prod _ _ _ _ wfB => wfB | _ => Datatypes.tt end.

Definition ext_sum_L {Sign : Type} {I A B} (wf : @WellFormed Sign I (Ty_Sum A B)) : @WellFormed Sign I A :=
  match wf in (@WellFormed _ I' P) return (match P with Ty_Sum A' _ => @WellFormed Sign I' A' | _ => Datatypes.unit end) with
  | WF_Sum _ _ _ wfA _ => wfA | _ => Datatypes.tt end.

Definition ext_sum_R {Sign : Type} {I A B} (wf : @WellFormed Sign I (Ty_Sum A B)) : @WellFormed Sign I B :=
  match wf in (@WellFormed _ I' P) return (match P with Ty_Sum _ B' => @WellFormed Sign I' B' | _ => Datatypes.unit end) with
  | WF_Sum _ _ _ _ wfB => wfB | _ => Datatypes.tt end.

Definition ext_arr_L {Sign : Type} {I A B} (wf : @WellFormed Sign I (Ty_Arrow A B)) : @WellFormed Sign I A :=
  match wf in (@WellFormed _ I' P) return (match P with Ty_Arrow A' _ => @WellFormed Sign I' A' | _ => Datatypes.unit end) with
  | WF_Arrow _ _ _ wfA _ => wfA | _ => Datatypes.tt end.

Definition ext_arr_R {Sign : Type} {I A B} (wf : @WellFormed Sign I (Ty_Arrow A B)) : @WellFormed Sign I B :=
  match wf in (@WellFormed _ I' P) return (match P with Ty_Arrow _ B' => @WellFormed Sign I' B' | _ => Datatypes.unit end) with
  | WF_Arrow _ _ _ _ wfB => wfB | _ => Datatypes.tt end.

Definition ext_all {Sign : Type} {I A Body} (wf : @WellFormed Sign I (Ty_All A Body)) : @WellFormed Sign (b_Prod I A) Body :=
  match wf in (@WellFormed _ I' P) return (match P with Ty_All A' B' => @WellFormed Sign (b_Prod I' A') B' | _ => Datatypes.unit end) with
  | WF_All _ _ _ wfBody => wfBody | _ => Datatypes.tt end.

Definition ext_ex {Sign : Type} {I A Body} (wf : @WellFormed Sign I (Ty_Ex A Body)) : @WellFormed Sign (b_Prod I A) Body :=
  match wf in (@WellFormed _ I' P) return (match P with Ty_Ex A' B' => @WellFormed Sign (b_Prod I' A') B' | _ => Datatypes.unit end) with
  | WF_Ex _ _ _ wfBody => wfBody | _ => Datatypes.tt end.

Definition ext_atom {Sign : Type} {I p t} (wf : @WellFormed Sign I (Ty_Atom p t)) : { A : b_ty & @base_typing Sign I t A } :=
  match wf in (@WellFormed _ I' P) return (match P with Ty_Atom p' t' => { A : b_ty & @base_typing Sign I' t' A } | _ => Datatypes.unit end) with
  | WF_Atom _ _ _ A dt => existT _ A dt | _ => Datatypes.tt end.

(* Axiom-Free Extractors a kontextusokhoz is: *)
Definition ext_ctx_hd {Sign : Type} {I Phi G} (wfc : @wf_ctx Sign I (Phi :: G)) : @WellFormed Sign I Phi :=
  match wfc in (@wf_ctx _ _ G') return (match G' with | nil => Datatypes.unit | Phi' :: _ => @WellFormed Sign I Phi' end) with
  | WFC_cons _ _ _ wf_Phi _ => wf_Phi 
  | _ => Datatypes.tt 
  end.

Definition ext_ctx_tl {Sign : Type} {I Phi G} (wfc : @wf_ctx Sign I (Phi :: G)) : @wf_ctx Sign I G :=
  match wfc in (@wf_ctx _ _ G') return (match G' with | nil => Datatypes.unit | _ :: G'' => @wf_ctx Sign I G'' end) with
  | WFC_cons _ _ _ _ wfc_G => wfc_G 
  | _ => Datatypes.tt 
  end.

(* ================================================================= *)
(* 1. HYPER MODEL DEFINÍCIÓ                                          *)
(* ================================================================= *)

Class HyperModel {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} 
                 {TSC : TwoSortCategory C} {GF : GoodFibration C} 
                 {SGF : StrictGoodFibration C GF} 
                 (BEM : @BaseSignatureModel Sign C CC TSC) 
                 (CBM : @CoherentBaseModel Sign C CC TSC BEM) := {
  
  i_atom : forall (p : nat) (t : @b_tm Sign) (I A : b_ty) (dt : base_typing I t A), @obj (Fiber (interp_ty I)) ;
  
  i_atom_pb : forall (p : nat) (t : @b_tm Sign) (I J A : b_ty) (f : @b_tm Sign) 
                     (df : base_typing I f J) (dt : base_typing J t A),
      @fobj _ _ (Pullback (interp_tm df)) (i_atom p t J A dt) ≅O i_atom p (b_comp t f) I A (BT_Comp dt df) ;
      
  (* Itt a javítás: A @base_equiv megvédi a változókat az implicit csúszástól! *)
  i_atom_cong : forall (p : nat) (t1 t2 : @b_tm Sign) (I A : b_ty)
                       (d1 : base_typing I t1 A) (d2 : base_typing I t2 A),
      @base_equiv Sign I A t1 t2 d1 d2 -> 
      i_atom p t1 I A d1 ≅O i_atom p t2 I A d2
}.

(* ================================================================= *)
(* 2. HYPER SZINTŰ TÍPUSOK ÉS KONTEXTUSOK INTERPRETÁCIÓJA            *)
(* ================================================================= *)

Fixpoint interp_h_ty {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
                     {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {BEM : @BaseSignatureModel Sign C CC TSC}
                     {CBM : @CoherentBaseModel Sign C CC TSC BEM} 
                     {HM : @HyperModel Sign C CC TSC GF SGF BEM CBM} (* <-- ITT A GOLYÓÁLLÓ JAVÍTÁS *)
                     (I : b_ty) (Phi : @h_ty Sign) {struct Phi} : @WellFormed Sign I Phi -> @obj (Fiber (interp_ty I)) :=
  match Phi return (@WellFormed Sign I Phi -> @obj (Fiber (interp_ty I))) with
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

Fixpoint interp_h_ctx {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
                      {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {BEM : @BaseSignatureModel Sign C CC TSC}
                      {CBM : @CoherentBaseModel Sign C CC TSC BEM} 
                      {HM : @HyperModel Sign C CC TSC GF SGF BEM CBM} (* <-- ITT IS *)
                      (I : b_ty) (G : @h_context Sign) {struct G} : @wf_ctx Sign I G -> @obj (Fiber (interp_ty I)) :=
  match G return (@wf_ctx Sign I G -> @obj (Fiber (interp_ty I))) with
  | nil => fun _ => terminal
  | Phi :: G' => fun wfc => prod (interp_h_ctx I G' (ext_ctx_tl wfc)) (interp_h_ty I Phi (ext_ctx_hd wfc))
  end.


(* ================================================================= *)
(* 2. STRUKTURÁLIS KOMPATIBILITÁSI LEMMÁK (DEPENDENTLY TYPED)        *)
(* ================================================================= *)

Lemma typing_pullback_ext :
  forall {Sign : Type} {I J b : b_ty} {g : @b_tm Sign} (dg : base_typing I g J),
  base_typing (b_Prod I b) (b_pullback_ext g) (b_Prod J b).
Proof.
  intros Sign I J b g dg.
  unfold b_pullback_ext.
  apply BT_Pair.
  - eapply BT_Comp; [exact dg | apply BT_Fst].
  - apply BT_Snd.
Defined.

Lemma base_typing_unique : forall {Sign : Type} I f B1 (d1 : @base_typing Sign I f B1) B2 (d2 : @base_typing Sign I f B2),
  B1 = B2.
Proof.
  intros Sign I f B1 d1.
  induction d1; intros B2 d2; dependent destruction d2.
  - reflexivity.
  - assert (H_B : B = B0). { eapply IHd1_2. exact d2_2. }
    subst B0. eapply IHd1_1. exact d2_1.
  - reflexivity.
  - assert (H_B : B = B0). { eapply IHd1_1. exact d2_1. }
    assert (H_C : C = C0). { eapply IHd1_2. exact d2_2. }
    subst. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

(* ÚJ LEMMA: Proof Irrelevance a levezetésekre! Bármely két levezetés ugyanarra a termre ekvivalens! *)
Lemma base_typing_pi : forall {Sign : Type} I A f (d1 d2 : @base_typing Sign I f A), 
  @base_equiv Sign I A f f d1 d2.
Proof.
  intros Sign I A f d1.
  induction d1; intros d2; dependent destruction d2.
  - apply BE_Refl.
  - assert (H_B : B = B0). { eapply base_typing_unique. exact d1_2. exact d2_2. }
    subst B0.
    apply BE_CongComp.
    + apply IHd1_2.
    + apply IHd1_1.
  - apply BE_Refl.
  - apply BE_CongPair.
    + apply IHd1_1.
    + apply IHd1_2.
  - apply BE_Refl.
  - apply BE_Refl.
  - apply BE_Refl.
Defined.


Lemma semantic_pi_ty : 
  forall {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {BEM : @BaseSignatureModel Sign C CC TSC}
         {CBM : @CoherentBaseModel Sign C CC TSC BEM} {HM : @HyperModel Sign C CC TSC GF SGF BEM CBM}
         {I : b_ty} {Phi : @h_ty Sign} (wf1 wf2 : @WellFormed Sign I Phi),
  interp_h_ty I Phi wf1 ≅O interp_h_ty I Phi wf2.
Proof.
  intros Sign C CC TSC GF SGF BEM CBM HM I Phi.
  (* We MUST revert the context I so the IH can handle the extended contexts created by the quantifiers! *)
  revert I.
  induction Phi; intros I wf1 wf2; cbn.
  
  - apply iso_refl.
  - apply iso_refl.
  - apply prod_iso_cong; [apply IHPhi1 | apply IHPhi2].
  - apply coprod_iso_cong; [apply IHPhi1 | apply IHPhi2].
  - apply exp_iso_cong; [apply IHPhi2 | apply IHPhi1].
  
  - (* Ty_Atom *)
    destruct (ext_atom wf1) as [A1 dt1].
    destruct (ext_atom wf2) as [A2 dt2].
    assert (Heq : A1 = A2) by (eapply base_typing_unique; [exact dt1 | exact dt2]).
    subst A2.
    apply i_atom_cong.
    (* Itt már nem kell exists, csak bevetjük a proof irrelevance lemmát! *)
    apply base_typing_pi.
  - (* Ty_All *) 
    apply pi_iso_cong. apply (IHPhi (b_Prod I b)).
  - (* Ty_Ex *)  
    apply sigma_iso_cong. apply (IHPhi (b_Prod I b)).
Defined.

Lemma form_pullback_general_iso :
  forall {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {BEM : @BaseSignatureModel Sign C CC TSC}
         {CBM : @CoherentBaseModel Sign C CC TSC BEM} {HM : @HyperModel Sign C CC TSC GF SGF BEM CBM}
         {I J : b_ty} {Phi : @h_ty Sign} (wf : @WellFormed Sign J Phi) (g : @b_tm Sign) (dg : base_typing I g J),
  interp_h_ty I (form_pullback g Phi) (wf_pullback I J g Phi dg wf) ≅O
  @fobj _ _ (Pullback (interp_tm dg)) (interp_h_ty J Phi wf).
Proof.
  intros Sign C CC TSC GF SGF BEM CBM HM I J Phi wf.
  revert I. 
  induction wf; intros I_src g dg; cbn.
  
  - (* Ty_Unit *) 
    symmetry. apply pb_term_iso.
    
  - (* Ty_Void *) 
    symmetry. apply pb_init_iso.
    
  - (* Ty_Prod *) 
    eapply iso_trans.
    + eapply prod_iso_cong; apply semantic_pi_ty.
    + eapply iso_trans.
      * apply (prod_iso_cong (IHwf1 I_src g dg) (IHwf2 I_src g dg)).
      * symmetry. apply pb_prod_iso.
      
  - (* Ty_Sum *) 
    eapply iso_trans.
    + eapply coprod_iso_cong; apply semantic_pi_ty.
    + eapply iso_trans.
      * apply (coprod_iso_cong (IHwf1 I_src g dg) (IHwf2 I_src g dg)).
      * symmetry. apply pb_coprod_iso.
      
  - (* Ty_Arrow *) 
    eapply iso_trans.
    + eapply exp_iso_cong; apply semantic_pi_ty.
    + eapply iso_trans.
      * apply (exp_iso_cong (IHwf2 I_src g dg) (IHwf1 I_src g dg)).
      * symmetry. apply pb_exp_iso.
      
 - (* Ty_Atom *) 
    cbn. 
    destruct (ext_atom (wf_pullback I_src I g (Ty_Atom p t) dg (WF_Atom I p t A b))) as [A_ext dt_ext].
    assert (H_A : A_ext = A).
    { eapply base_typing_unique. 
      - exact dt_ext. 
      - exact (BT_Comp b dg). }
    subst A_ext.
    cbn.
    eapply iso_trans.
    + apply (i_atom_cong p (b_comp t g) (b_comp t g) I_src A dt_ext (BT_Comp b dg)).
      (* A beragadt célra csak ráküldjük a lemmát, ami feloldja a levezetések közti különbséget! *)
      apply base_typing_pi.
    + symmetry. apply i_atom_pb.
    
  - (* Ty_All *) 
    eapply iso_trans.
    + apply pi_iso_cong. apply (semantic_pi_ty (I := b_Prod I_src A)).
    + eapply iso_trans.
      * apply pi_iso_cong. apply (IHwf (b_Prod I_src A) (b_pullback_ext g) (typing_pullback_ext dg)).
      * symmetry. apply beck_chevalley_pi.
      
  - (* Ty_Ex *) 
    eapply iso_trans.
    + apply sigma_iso_cong. apply (semantic_pi_ty (I := b_Prod I_src A)).
    + eapply iso_trans.
      * apply sigma_iso_cong. apply (IHwf (b_Prod I_src A) (b_pullback_ext g) (typing_pullback_ext dg)).
      * symmetry. apply beck_chevalley_sigma.
Defined.

Lemma form_pullback_iso :
  forall {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {BEM : @BaseSignatureModel Sign C CC TSC}
         {CBM : @CoherentBaseModel Sign C CC TSC BEM} {HM : @HyperModel Sign C CC TSC GF SGF BEM CBM}
         {I A : b_ty} {f : @b_tm Sign} (df : base_typing I f A) {Phi : @h_ty Sign}
         (wf : @WellFormed Sign (b_Prod I A) Phi),
  interp_h_ty I (form_pullback (b_pair b_id f) Phi) 
              (wf_pullback I (b_Prod I A) (b_pair b_id f) Phi (BT_Pair BT_Id df) wf) ≅O
  @fobj _ _ (Pullback (interp_tm (BT_Pair BT_Id df))) (interp_h_ty (b_Prod I A) Phi wf).
Proof.
  intros. apply (form_pullback_general_iso wf (b_pair b_id f) (BT_Pair BT_Id df)).
Defined.

Lemma form_pullback_fst_iso : 
  forall {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {BEM : @BaseSignatureModel Sign C CC TSC}
         {CBM : @CoherentBaseModel Sign C CC TSC BEM} {HM : @HyperModel Sign C CC TSC GF SGF BEM CBM}
         {I A : b_ty} {Phi : @h_ty Sign} (wf : @WellFormed Sign I Phi),
  interp_h_ty (b_Prod I A) (form_pullback b_fst Phi) 
              (wf_pullback (b_Prod I A) I b_fst Phi BT_Fst wf) ≅O 
  @fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I Phi wf).
Proof.
  intros. apply (form_pullback_general_iso wf b_fst BT_Fst).
Defined.

Lemma pb_eval_iso : 
  forall {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {BEM : @BaseSignatureModel Sign C CC TSC}
         {CBM : @CoherentBaseModel Sign C CC TSC BEM} {HM : @HyperModel Sign C CC TSC GF SGF BEM CBM}
         {I A : b_ty} {f : @b_tm Sign} (df : base_typing I f A) {Phi : @h_ty Sign}
         (wf : @WellFormed Sign (b_Prod I A) Phi),
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
  forall {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {BEM : @BaseSignatureModel Sign C CC TSC}
         {CBM : @CoherentBaseModel Sign C CC TSC BEM} {HM : @HyperModel Sign C CC TSC GF SGF BEM CBM}
         {I A : b_ty} {f : @b_tm Sign} (df : base_typing I f A) {Phi : @h_ty Sign}
         (wf : @WellFormed Sign (b_Prod I A) Phi),
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
  forall {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {BEM : @BaseSignatureModel Sign C CC TSC}
         {CBM : @CoherentBaseModel Sign C CC TSC BEM} {HM : @HyperModel Sign C CC TSC GF SGF BEM CBM}
         {I A : b_ty} {G : @h_context Sign} {Phi Chi : @h_ty Sign} 
         (wfc : @wf_ctx Sign I G) (wf_Phi : @WellFormed Sign (b_Prod I A) Phi) (wf_Chi : @WellFormed Sign I Chi),
  hom (prod (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ctx I G wfc)) 
            (interp_h_ty (b_Prod I A) Phi wf_Phi)) 
      (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I Chi wf_Chi)) -> 
  hom (prod (interp_h_ctx I G wfc) (interp_h_ty I (Ty_Ex A Phi) (WF_Ex I A Phi wf_Phi))) (interp_h_ty I Chi wf_Chi).
Proof.
  intros Sign C CC TSC GF SGF BEM CBM HM I A G Phi Chi wfc wf_Phi wf_Chi H_premissza.
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

(* ================================================================= *)
(* FORM EQUIV WELL-FORMEDNESS KIVONATOLÓ                             *)
(* ================================================================= *)

Lemma form_equiv_wf : forall {Sign : Type} (I : b_ty) (Phi Psi : @h_ty Sign),
  @form_equiv Sign I Phi Psi -> @WellFormed Sign I Phi * @WellFormed Sign I Psi.
Proof.
  intros Sign I Phi Psi H.
  induction H.
  - (* FE_Atom *) split; econstructor; eassumption.
  - (* FE_Refl *) split; assumption.
  - (* FE_Sym *) destruct IHform_equiv; split; assumption.
  - (* FE_Trans *) destruct IHform_equiv1, IHform_equiv2; split; assumption.
  - (* FE_Prod *) destruct IHform_equiv1, IHform_equiv2; split; constructor; assumption.
  - (* FE_Sum *) destruct IHform_equiv1, IHform_equiv2; split; constructor; assumption.
  - (* FE_Arrow *) destruct IHform_equiv1, IHform_equiv2; split; constructor; assumption.
  - (* FE_All *) destruct IHform_equiv; split; constructor; assumption.
  - (* FE_Ex *) destruct IHform_equiv; split; constructor; assumption.
  - (* FE_Pullback_Id *) 
    split. 
    + eapply wf_pullback. apply BT_Id. eassumption.
    + assumption.
  - (* FE_Pullback_Comp *)
    split.
    + (* 1. Cél: Egymásba ágyazott visszahúzás (először g, majd f mentén) *)
      eapply wf_pullback. exact dg. 
      eapply wf_pullback. exact df. 
      exact w.
    + (* 2. Cél: Visszahúzás a kompozíció mentén *)
      eapply wf_pullback. eapply BT_Comp; [exact df | exact dg]. 
      exact w.
  - (* FE_Pullback_Cong *)
    split; eapply wf_pullback; eassumption.
Defined.

(* Átnevezve az új szintaxisnak megfelelően (FE_ prefixek FEQ_ helyett) *)
Lemma interp_form_equiv : 
  forall {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {BEM : @BaseSignatureModel Sign C CC TSC}
         {CBM : @CoherentBaseModel Sign C CC TSC BEM} {HM : @HyperModel Sign C CC TSC GF SGF BEM CBM}
         {I : b_ty} {Phi Psi : @h_ty Sign} (H : @form_equiv Sign I Phi Psi)
         (wf1 : @WellFormed Sign I Phi) (wf2 : @WellFormed Sign I Psi),
  interp_h_ty I Phi wf1 ≅O interp_h_ty I Psi wf2.
Proof.
  intros Sign C CC TSC GF SGF BEM CBM HM I Phi Psi H.
  induction H; intros wf1 wf2; cbn.
  
 - (* FE_Atom *)
    destruct (ext_atom wf1) as [A1 dt1].
    destruct (ext_atom wf2) as [A2 dt2].
    assert (Heq1 : A1 = A) by (eapply base_typing_unique; [exact dt1 | exact d1]).
    assert (Heq2 : A2 = A) by (eapply base_typing_unique; [exact dt2 | exact d2]).
    subst A1 A2.
    apply i_atom_cong.
    
    (* A BE_Trans és a base_typing_pi segítségével átkonvertáljuk a levezetéseket! *)
    eapply BE_Trans. { apply base_typing_pi. } (* dt1 átalakul d1-re *)
    eapply BE_Trans. { exact b. }              (* d1 átalakul d2-re (ez a b bizonyítékod) *)
    { apply base_typing_pi. }                  (* d2 átalakul dt2-re *)

  - (* FE_Refl *) apply semantic_pi_ty.
  - (* FE_Sym *) symmetry. apply IHform_equiv.
  
  - (* FE_Trans *)
    assert (wf_Psi : WellFormed I Psi) by exact (snd (form_equiv_wf I Phi Psi H)).
    eapply iso_trans. 
    + apply (IHform_equiv1 wf1 wf_Psi).
    + apply (IHform_equiv2 wf_Psi wf2).
    
  - (* FE_Prod *) apply prod_iso_cong; [apply IHform_equiv1 | apply IHform_equiv2].
  - (* FE_Sum *) apply coprod_iso_cong; [apply IHform_equiv1 | apply IHform_equiv2].
  - (* FE_Arrow *) apply exp_iso_cong; [apply IHform_equiv2 | apply IHform_equiv1].
  - (* FE_All *) apply pi_iso_cong; apply IHform_equiv.
  - (* FE_Ex *) apply sigma_iso_cong; apply IHform_equiv.

  - (* FE_Pullback_Id *)
    eapply iso_trans. { apply semantic_pi_ty. } 
    eapply iso_trans.
    { apply (form_pullback_general_iso w b_id BT_Id). }
    eapply iso_trans.
    { assert (H_id : interp_tm BT_Id ≅ id (interp_ty I)) by reflexivity.
      eapply iso_trans.
      { apply (@pb_iso _ _ _ _ _ _ _ H_id). }
      { apply pullback_id_iso. } }
    { apply semantic_pi_ty. } 

  - (* FE_Pullback_Comp *)
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

 - (* FE_Pullback_Cong *)
    eapply iso_trans. { apply semantic_pi_ty. } 
    eapply iso_trans.
    { apply (form_pullback_general_iso w f df). }
    eapply iso_trans.
    { assert (H_cong : interp_tm df ≅ interp_tm dg).
      { (* 1. Megadjuk a levezetéseket a tételnek *)
        apply (base_soundness_equational df dg).
        (* 2. Becsomagoljuk a 'b' bizonyítékot a várt típusba *)
        exists df, dg. exact b. 
        (* (Ha a fenti 'exists' esetleg szintaktikai hibát adna a definíciód miatt, 
           használd helyette ezt a sort: econstructor. exact b. ) *)
      }
      apply (@pb_iso _ _ _ _ _ _ _ H_cong). }
    eapply iso_trans.
    { symmetry. apply (form_pullback_general_iso w g dg). }
    { apply semantic_pi_ty. }
Defined.

Lemma semantic_pi_ctx : 
  forall {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {BEM : @BaseSignatureModel Sign C CC TSC}
         {CBM : @CoherentBaseModel Sign C CC TSC BEM} {HM : @HyperModel Sign C CC TSC GF SGF BEM CBM}
         {I : b_ty} {G : @h_context Sign} (wfc1 wfc2 : @wf_ctx Sign I G),
  interp_h_ctx I G wfc1 ≅O interp_h_ctx I G wfc2.
Proof.
  intros Sign C CC TSC GF SGF BEM CBM HM I G.
  induction G; intros wfc1 wfc2; cbn.
  - apply iso_refl.
  - apply prod_iso_cong; [apply IHG | apply semantic_pi_ty].
Defined.

Lemma interp_ctx_equiv : 
  forall {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {BEM : @BaseSignatureModel Sign C CC TSC}
         {CBM : @CoherentBaseModel Sign C CC TSC BEM} {HM : @HyperModel Sign C CC TSC GF SGF BEM CBM}
         {I : b_ty} {G1 G2 : @h_context Sign} (H : @ctx_equiv Sign I G1 G2)
         (wfc1 : @wf_ctx Sign I G1) (wfc2 : @wf_ctx Sign I G2),
  interp_h_ctx I G1 wfc1 ≅O interp_h_ctx I G2 wfc2.
Proof.
  intros Sign C CC TSC GF SGF BEM CBM HM I G1 G2 H.
  induction H; intros wfc1 wfc2; cbn.
  - apply iso_refl.
  - apply prod_iso_cong; [apply IHctx_equiv | apply interp_form_equiv; assumption].
Defined.


Lemma ctx_pullback_iso : 
  forall {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {BEM : @BaseSignatureModel Sign C CC TSC}
         {CBM : @CoherentBaseModel Sign C CC TSC BEM} {HM : @HyperModel Sign C CC TSC GF SGF BEM CBM}
         {I A : b_ty} {G : @h_context Sign} (wfc : @wf_ctx Sign I G),
  interp_h_ctx (b_Prod I A) (ctx_pullback b_fst G) (wf_ctx_pullback _ _ b_fst G BT_Fst wfc) ≅O 
  @fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ctx I G wfc).
Proof.
  intros Sign C CC TSC GF SGF BEM CBM HM I A G wfc.
  induction wfc; cbn.
  
  - (* WFC_nil *)
    symmetry. apply pb_term_iso.
    
  - (* WFC_cons *)
    eapply iso_trans.
    + (* We pass the proofs directly into prod_iso_cong so Coq's unifier doesn't have to guess! *)
      apply (prod_iso_cong IHwfc (form_pullback_general_iso w b_fst BT_Fst)).
    + symmetry. apply pb_prod_iso.
Defined.

(* ================================================================= *)
(* LEVEZETÉS-JÓLFORMÁLTSÁG KIVONATOLÓK (AXIÓMÁK NÉLKÜL)              *)
(* ================================================================= *)

Lemma well_formed_ctx : forall {Sign : Type} (I : b_ty) (G : @h_context Sign) (p : @h_tm Sign) (Phi : @h_ty Sign),
  @h_derivation Sign I G p Phi -> @wf_ctx Sign I G.
Proof.
  intros Sign I G p Phi D.
  induction D.
  
  (* 1. Közvetlen hipotézisek: *)
  all: try assumption.
  
  (* 2. Ahol csak le kell vágni a kontextus fejét (pl. Lam): *)
  all: try match goal with
  | [ IH : @wf_ctx _ _ (_ :: ?Ctx) |- @wf_ctx _ _ ?Ctx ] => exact (ext_ctx_tl IH)
  end.
  
  (* 3. Intro szabályok (VarS, ahol hozzáadunk a kontextushoz): *)
  all: try (econstructor; assumption).
Defined.

Lemma well_formed_target : forall {Sign : Type} (I : b_ty) (G : @h_context Sign) (p : @h_tm Sign) (Phi : @h_ty Sign),
  @h_derivation Sign I G p Phi -> @WellFormed Sign I Phi.
Proof.
  intros Sign I G p Phi D.
  induction D.
  
  (* 1. Közvetlen hipotézisek (Var0, Conv, Inl, Inr_kiemelt, Ex_Elim, stb.) *)
  all: try assumption.
  
  (* 2. HD_All_Elim speciális esete (ahol a cél Phi .[ f ]) 
     Itt az exact paranccsal direktben, hiba nélkül felépítjük a visszahúzást! *)
  all: try match goal with
  | [ H : @WellFormed _ ?I (Ty_All ?A ?Phi), b_der : @base_typing _ ?I ?f ?A |- _ ] => 
      exact (wf_pullback I (b_Prod I A) (b_pair b_id f) Phi (BT_Pair BT_Id b_der) (ext_all H))
  end.
  
  (* 3. Eliminációs szabályok (Fst, Snd, App) *)
  all: try match goal with
  | [ H : @WellFormed _ _ (Ty_Arrow _ _) |- _ ] => exact (ext_arr_R H)
  | [ H : @WellFormed _ _ (Ty_Prod _ _) |- _ ] => first [ exact (ext_prod_L H) | exact (ext_prod_R H) ]
  end.
  
  (* 4. HD_Lam (Arrow Intro) speciális esete *)
  all: try match goal with
  | [ d_prem : @h_derivation _ _ (?P :: _) _ _ |- @WellFormed _ _ (Ty_Arrow ?P _) ] =>
      apply WF_Arrow; [ exact (ext_ctx_hd (well_formed_ctx _ _ _ _ d_prem)) | assumption ]
  end.
  
  (* 5. Intro szabályok (Unit, Pair, All_Intro, Ex_Intro, Absurd) *)
  all: try (econstructor; assumption).
Defined.

(* ================================================================= *)
(* 3. A HELYESSÉG TÉTEL (SOUNDNESS)                                  *)
(* ================================================================= *)

Theorem hyper_soundness_inhabited 
  {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C}
  {TSC : TwoSortCategory C} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
  {BEM : @BaseSignatureModel Sign C CC TSC} {CBM : @CoherentBaseModel Sign C CC TSC BEM} 
  {HM : @HyperModel Sign C CC TSC GF SGF BEM CBM}
  {I : b_ty} {G : @h_context Sign} {p : @h_tm Sign} {Phi : @h_ty Sign}
  (D : @h_derivation Sign I G p Phi) :
  forall (wfc : @wf_ctx Sign I G) (wf_Phi : @WellFormed Sign I Phi),
  hom (interp_h_ctx I G wfc) (interp_h_ty I Phi wf_Phi).
Proof.
  induction D; intros wfc wf_Phi.
  
  - (* 1. HD_Var0 *)
    cbn. eapply compose. 
    { apply (@iso_to _ _ _ (semantic_pi_ty (ext_ctx_hd wfc) wf_Phi)). }
    { apply prod_snd. }

  - (* 2. HD_VarS *)
    cbn. eapply compose. 
    { apply (IHD (ext_ctx_tl wfc) wf_Phi). }
    { apply prod_fst. }

  - (* 3. ág (Valójában ez most a HD_Conv!) *)
    (* Kinyerjük az eredeti Phi formula jólformáltságát a Type-szintű párból *)
    pose proof (fst (form_equiv_wf I Phi Psi f)) as wf_Phi_orig.
    eapply compose.
    { apply (@iso_to _ _ _ (interp_form_equiv f wf_Phi_orig wf_Phi)). }
    { exact (IHD wfc wf_Phi_orig). }

  - (* Valahanyadik ág (HD_Unit) *)
      apply terminal_map.

  - (* 4. HD_Lam *)
    cbn. apply exp_map. 
    apply (IHD (WFC_cons _ _ _ (ext_arr_L wf_Phi) wfc) (ext_arr_R wf_Phi)).

  - (* 5. HD_App *)
    pose proof (well_formed_target _ _ _ _ D2) as wf_A.
    eapply compose. { eapply eval. }
    apply prod_map.
    + exact (IHD1 wfc (WF_Arrow _ _ _ wf_A wf_Phi)).
    + exact (IHD2 wfc wf_A).

  - (* 6. HD_Pair *)
    cbn. apply prod_map.
    + exact (IHD1 wfc (ext_prod_L wf_Phi)).
    + exact (IHD2 wfc (ext_prod_R wf_Phi)).

  - (* 7. HD_Fst *)
    pose proof (well_formed_target _ _ _ _ D) as wf_prod.
    eapply compose. 
    { apply (@iso_to _ _ _ (semantic_pi_ty (ext_prod_L wf_prod) wf_Phi)). }
    eapply compose. 
    { eapply prod_fst. }
    { exact (IHD wfc wf_prod). }

  - (* 8. HD_Snd *)
    pose proof (well_formed_target _ _ _ _ D) as wf_prod.
    eapply compose. 
    { apply (@iso_to _ _ _ (semantic_pi_ty (ext_prod_R wf_prod) wf_Phi)). }
    eapply compose. 
    { eapply prod_snd. }
    { exact (IHD wfc wf_prod). }

  - (* 9. HD_Inl *)
    cbn. eapply compose. 
    { apply coprod_inl. }
    { exact (IHD wfc (ext_sum_L wf_Phi)). }

  - (* 10. HD_Inr *)
    cbn. eapply compose. 
    { apply coprod_inr. }
    { exact (IHD wfc (ext_sum_R wf_Phi)). }

  - (* 11. HD_Case *)
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

  - (* 12. HD_Absurd *)
    eapply compose. 
    { apply initial_map. }
    { exact (IHD wfc (WF_Void I)). }

  - (* 13. HD_All_Intro *)
    cbn. apply right_adj_mor. eapply compose.
    { exact (IHD (wf_ctx_pullback _ _ _ _ BT_Fst wfc) (ext_all wf_Phi)). }
    { apply (@iso_from _ _ _ (ctx_pullback_iso wfc)). }

  - (* 14. HD_All_Elim *)
    pose proof (well_formed_target _ _ _ _ D) as wf_all.
    eapply compose. 
    { eapply (@iso_to _ _ _ (semantic_pi_ty _ wf_Phi)). }
    eapply compose. 
    { eapply (@iso_from _ _ _ (form_pullback_iso b (ext_all wf_all))). }
    eapply compose. 
    { eapply (@fmap _ _ (Pullback (interp_tm (BT_Pair BT_Id b))) _ _).
      apply (@epsilon _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) pullback_has_right_adjoint). }
    eapply compose. 
    { apply (pb_eval_iso b (ext_all wf_all)). }
    { exact (IHD wfc wf_all). }

  - (* 15. HD_Ex_Intro *)
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
    
  - (* 18. HD_Ctx_Conv *)
    (* Kinyerjük a régi kontextus (G1) jólformáltságát az eredeti levezetésből *)
    pose proof (well_formed_ctx _ _ _ _ D) as wf_G1.
    
    (* A kategóriaelméleti kompozíció: G2 -> G1 -> Phi *)
    eapply compose.
    { (* 2. LÉPÉS (Külső függvény): G1 -> Phi a levezetésből (Indukciós Hipotézis) *)
      exact (IHD wf_G1 wf_Phi). }
    { (* 1. LÉPÉS (Belső függvény): G2 -> G1 izomorfizmus a kontextus-ekvivalenciából (c) *)
      apply (@iso_from _ _ _ (interp_ctx_equiv c wf_G1 wfc)). }

  - (* 16. HD_Ex_Elim *)
    pose proof (well_formed_target _ _ _ _ D1) as wf_ex.
    pose proof (well_formed_target _ _ _ _ D2) as wf_chi_pb.
    eapply compose. 
    { apply (ex_elim_frobenius wfc (ext_ex wf_ex) wf_Phi).
      eapply compose. { apply (@iso_to _ _ _ (form_pullback_fst_iso wf_Phi)). }
      eapply compose. { apply (@iso_to _ _ _ (semantic_pi_ty wf_chi_pb _)). }
      eapply compose. { exact (IHD2 (WFC_cons _ _ _ (ext_ex wf_ex) (wf_ctx_pullback _ _ _ _ BT_Fst wfc)) wf_chi_pb). }
      { apply (prod_map (compose (@iso_from _ _ _ (ctx_pullback_iso wfc)) prod_fst) prod_snd). } }
    { apply prod_map; [apply (id _) | exact (IHD1 wfc wf_ex)]. }
Defined.

(* ================================================================= *)
(* 4. EQUATIONAL SOUNDNESS (PROOF IRRELEVANCE)                       *)
(* ================================================================= *)

Theorem hyper_soundness_equational :
  forall {Sign : Type} {C : SetoidCategory} {CC : CartesianCategory C}
         {TSC : TwoSortCategory C} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF}
         {BEM : @BaseSignatureModel Sign C CC TSC} {CBM : @CoherentBaseModel Sign C CC TSC BEM}
         {HM : @HyperModel Sign C CC TSC GF SGF BEM CBM}
         {I : b_ty} {G : @h_context Sign} {p q : @h_tm Sign} {Phi : @h_ty Sign}
         (Dp : @h_derivation Sign I G p Phi)
         (Dq : @h_derivation Sign I G q Phi)
         (wfc : @wf_ctx Sign I G) (wf_Phi : @WellFormed Sign I Phi),
  @h_equiv_rel Sign I p q ->
  hyper_soundness_inhabited Dp wfc wf_Phi ≅ hyper_soundness_inhabited Dq wfc wf_Phi.
Proof.
  intros Sign C CC TSC GF SGF BEM CBM HM I G p q Phi Dp Dq wfc wf_Phi Hequiv.
  
  (* A base_soundness_equational-hez hasonlóan a szintaxis megköveteli 
     az ekvivalenciát (Hequiv).
     A szemantikában a Hyper szintű interpretáció a szálakban (Fibers) 
     történik. A szálak (a Proof Irrelevance elve miatt) Thin kategóriák.
     Így a tétel független a levezetések mély struktúrájától: 
     bármely két párhuzamos morfizmus definíció szerint egyenlő! *)
  
  apply (fiber_is_thin (interp_ty I)).
Qed.