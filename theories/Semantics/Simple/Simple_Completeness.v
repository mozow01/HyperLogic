
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
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum.

Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Lemmas.




Require Import HyperLogic.Semantics.Simple.Base_Simple_Soundness.
Require Import HyperLogic.Semantics.Simple.Simple_Soundness.



(** Legacy syntactic completeness model. *)


(** A fiber arrow is a derivation from the singleton source formula. *)
    
Record hom_hyper (I : b_ty) (Phi Psi : h_ty) : Type := mk_hom_hyper {
  h_tm_of : h_tm;
  h_deriv_of : h_derivation I (Phi :: nil) h_tm_of Psi
}.

(** Fiber objects package formulas with well-formedness data. *)
Record obj_hyper (I : b_ty) : Type := mk_obj_hyper {
  ty_val : h_ty;
  ty_wf  : WellFormed I ty_val
}.

(* The coercion exposes the underlying formula where [h_ty] is expected. *)
Coercion ty_val : obj_hyper >-> h_ty.


Arguments h_tm_of {I Phi Psi} _.
Arguments h_deriv_of {I Phi Psi} _.



Lemma ctx_pullback_app : forall f (G Delta : h_context),
  ctx_pullback f (G ++ Delta) = ctx_pullback f G ++ ctx_pullback f Delta.
Proof.
  intros. unfold ctx_pullback. apply map_app.
Qed.


Fixpoint derivation_to_typing {I G p A} 
  (d : h_derivation I G p A) : h_typing I G p A.
Proof.
  induction d.
  - apply HT_Var0; assumption.
  - apply HT_VarS; assumption.
  - apply HT_Unit; assumption.
  - apply HT_Lam; assumption.
  - eapply HT_App; eassumption.
  - apply HT_Pair; assumption.
  - eapply HT_Fst; eassumption.
  - eapply HT_Snd; eassumption.
  - apply HT_Inl; assumption.
  - apply HT_Inr; assumption.
  - eapply HT_Case; eassumption.
  - apply HT_Absurd; assumption.
  - apply HT_All_Intro; assumption.
  - eapply HT_All_Elim; eassumption.
  - eapply HT_Ex_Intro; eassumption.
  - eapply HT_Ex_Elim; eassumption.
  - eapply HT_Conv; eassumption.
Defined.


Lemma hyper_pi : forall I G p q A 
  (dp : h_derivation I G p A) (dq : h_derivation I G q A), 
  h_equiv_rel I p q.
Proof.
  intros. eapply PI_rule.
  - apply derivation_to_typing; exact dp.
  - apply derivation_to_typing; exact dq.
Qed.


Definition hyper_id_term (Phi : h_ty) : h_tm :=
  tm_var 0.

Definition hyper_id_deriv (I : b_ty) (Phi : obj_hyper I) 
  : h_derivation I ((Phi : h_ty) :: nil) (hyper_id_term Phi) Phi :=
  HD_Var0 I nil Phi (WFC_nil I) (ty_wf I Phi).

Definition hyper_id (I : b_ty) (Phi : obj_hyper I) : hom_hyper I Phi Phi :=
  mk_hom_hyper I Phi Phi (hyper_id_term Phi) (hyper_id_deriv I Phi).

Definition hyper_comp_term (Psi : h_ty) (tf tg : h_tm) : h_tm :=
  tm_app (tm_lam Psi tg) tf.

(* The object record supplies context well-formedness without axioms. *)
Lemma obj_ctx_wf : forall (I : b_ty) (Phi : obj_hyper I), wf_ctx I ((Phi : h_ty) :: nil).
Proof.
  intros I Phi. apply WFC_cons. exact (ty_wf I Phi). apply WFC_nil.
Qed.

(* Derivation-level append weakening constructs fiber morphisms. *)
Lemma hd_weakening_append : forall I G Delta p Phi,
  wf_ctx I Delta ->
  h_derivation I G p Phi -> h_derivation I (G ++ Delta) p Phi.
Proof.
  assert (H_cons_app : forall (T : Type) (l : list T) (a : T), a :: l = [a] ++ l) by (simpl; auto).
  intros I G Delta p Phi Hwf d.
  revert Delta Hwf.
  induction d; intros Delta Hwf;
  try (rewrite H_cons_app; try rewrite <- app_assoc; try rewrite <- H_cons_app).
  - apply HD_Var0; [apply wf_ctx_app; assumption | assumption].
  - apply HD_VarS; [assumption | apply IHd; assumption].
  - apply HD_Unit; apply wf_ctx_app; [assumption | assumption].
  - apply HD_Lam. apply IHd; assumption.
  - eapply HD_App; [apply IHd1; assumption | apply IHd2; assumption].
  - apply HD_Pair; [apply IHd1; assumption | apply IHd2; assumption].
  - eapply HD_Fst; apply IHd; assumption.
  - eapply HD_Snd; apply IHd; assumption.
  - apply HD_Inl; [assumption | apply IHd; assumption].
  - apply HD_Inr; [assumption | apply IHd; assumption].
  - eapply HD_Case; [apply IHd1; assumption | apply IHd2; assumption | apply IHd3; assumption].
  - apply HD_Absurd; [assumption | apply IHd; assumption].
  - apply HD_All_Intro; [apply wf_ctx_app; assumption | idtac].
    unfold ctx_pullback. rewrite map_app. apply IHd. 
    eapply wf_ctx_pullback; [apply BT_Fst | assumption].
  - eapply HD_All_Elim; [apply IHd; assumption | assumption].
  - eapply HD_Ex_Intro; [assumption | assumption | apply IHd; assumption].
  - eapply HD_Ex_Elim; [assumption | apply IHd1; assumption | idtac].
    unfold ctx_pullback. rewrite map_app. apply IHd2. 
    eapply wf_ctx_pullback; [apply BT_Fst | assumption].
  - eapply HD_Conv.
    + apply ctx_equiv_app; [eassumption | assumption].
    + eassumption.
    + apply IHd; assumption.
Defined.

Definition hyper_comp_deriv (I : b_ty) (Phi Psi Chi : obj_hyper I)
  (tf tg : h_tm)
  (df : h_derivation I ((Phi : h_ty) :: nil) tf Psi)
  (dg : h_derivation I ((Psi : h_ty) :: nil) tg Chi) :
  h_derivation I ((Phi : h_ty) :: nil) (hyper_comp_term Psi tf tg) Chi.
Proof.
  unfold hyper_comp_term.
  eapply HD_App.
  - apply (hd_weakening_append I nil ((Phi : h_ty) :: nil)).
    + apply obj_ctx_wf.
    + apply HD_Lam. exact dg.
  - exact df.
Defined.

Definition hyper_comp (I : b_ty) (Phi Psi Chi : obj_hyper I)
  (g : hom_hyper I Psi Chi) (f : hom_hyper I Phi Psi) : hom_hyper I Phi Chi :=
  mk_hom_hyper I Phi Chi 
    (hyper_comp_term Psi (h_tm_of f) (h_tm_of g)) 
    (hyper_comp_deriv I Phi Psi Chi (h_tm_of f) (h_tm_of g) (h_deriv_of f) (h_deriv_of g)).

Definition hyper_hom_equiv (I : b_ty) (Phi Psi : obj_hyper I)
  (f g : hom_hyper I Phi Psi) : Prop :=
  h_equiv_rel I (h_tm_of f) (h_tm_of g).

Lemma hyper_hom_equiv_pi : forall 
  (I : b_ty) (Phi Psi : obj_hyper I) (f g : hom_hyper I Phi Psi),
  hyper_hom_equiv I Phi Psi f g.
Proof.
  intros I Phi Psi f g.
  unfold hyper_hom_equiv.
  eapply hyper_pi.
  - exact (h_deriv_of f).
  - exact (h_deriv_of g).
Qed.


Instance Syntactic_Fiber (I : b_ty) : SetoidCategory.
Proof.
  refine (mk_SetoidCategory 
    (obj_hyper I)
    (hom_hyper I)
    (hyper_id I)
    (hyper_comp I)
    (hyper_hom_equiv I)
    _ _ _ _ _).
  -
    intros A B. split.
    + intros f. apply hyper_hom_equiv_pi.
    + intros f g H. apply hyper_hom_equiv_pi.
    + intros f g h H1 H2. apply hyper_hom_equiv_pi.
  -   intros A B C D f g h. apply hyper_hom_equiv_pi.
  -   intros A B f. apply hyper_hom_equiv_pi.
  -   intros A B f. apply hyper_hom_equiv_pi.
  -   unfold Proper, respectful. intros A B C f f' Hf g g' Hg. apply hyper_hom_equiv_pi.
Defined.


Definition syn_terminal_obj (I : b_ty) : obj_hyper I :=
  mk_obj_hyper I Ty_Unit (WF_Unit I).

Definition syn_prod_obj (I : b_ty) (Phi Psi : obj_hyper I) : obj_hyper I :=
  mk_obj_hyper I (Ty_Prod Phi Psi) (WF_Prod I Phi Psi (ty_wf I Phi) (ty_wf I Psi)).

Definition syn_exp_obj (I : b_ty) (S T : obj_hyper I) : obj_hyper I :=
  mk_obj_hyper I (Ty_Arrow S T) (WF_Arrow I S T (ty_wf I S) (ty_wf I T)).

Definition syn_initial_obj (I : b_ty) : obj_hyper I :=
  mk_obj_hyper I Ty_Void (WF_Void I).

Definition syn_coprod_obj (I : b_ty) (Phi Psi : obj_hyper I) : obj_hyper I :=
  mk_obj_hyper I (Ty_Sum Phi Psi) (WF_Sum I Phi Psi (ty_wf I Phi) (ty_wf I Psi)).

Lemma double_ctx_wf : forall I (A C : obj_hyper I), wf_ctx I ((A:h_ty) :: (C:h_ty) :: nil).
Proof.
  intros I A C. apply WFC_cons. exact (ty_wf I A). apply WFC_cons. exact (ty_wf I C). apply WFC_nil.
Qed.


Instance Syntactic_Cartesian (I : b_ty) : CartesianCategory (Syntactic_Fiber I).
Proof.
  refine (mk_CartesianCategory (Syntactic_Fiber I)
    
    (syn_terminal_obj I)
    
    (fun (Phi : obj_hyper I) => @mk_hom_hyper I Phi (syn_terminal_obj I) tm_unit 
       (HD_Unit I ((Phi : h_ty) :: nil) (obj_ctx_wf I Phi)))
    
    _
    
    (syn_prod_obj I)
    
    (fun (Phi Psi Chi : obj_hyper I) f g => @mk_hom_hyper I Phi (syn_prod_obj I Psi Chi) (tm_pair (h_tm_of f) (h_tm_of g)) 
       ltac:(apply HD_Pair; [ exact (h_deriv_of f) | exact (h_deriv_of g) ]))
       
    (fun (Phi Psi : obj_hyper I) => @mk_hom_hyper I (syn_prod_obj I Phi Psi) Phi (tm_fst (tm_var 0)) 
       ltac:(eapply HD_Fst; exact (hyper_id_deriv I (syn_prod_obj I Phi Psi))))
       
    (fun (Phi Psi : obj_hyper I) => @mk_hom_hyper I (syn_prod_obj I Phi Psi) Psi (tm_snd (tm_var 0)) 
       ltac:(eapply HD_Snd; exact (hyper_id_deriv I (syn_prod_obj I Phi Psi))))
    
    _ _ _ _
  ).
  - intros x f. apply hyper_hom_equiv_pi.
  - intros A B C f g. apply hyper_hom_equiv_pi.
  - intros A B C f g. apply hyper_hom_equiv_pi.
  - intros A B C h. apply hyper_hom_equiv_pi.
  - unfold Proper, respectful. intros A B C f f' Hf g g' Hg. apply hyper_hom_equiv_pi.
Defined.


Instance Syntactic_Closed(I : b_ty) : CartesianClosedCategory (Syntactic_Fiber I).
Proof.
  refine (mk_CartesianClosedCategory (Syntactic_Fiber I) (Syntactic_Cartesian I)
    
    (* Exponentials receive target then source, following [B^A]. *)
    (fun Tgt Src => syn_exp_obj I Src Tgt)

    (fun (C A B : obj_hyper I) f => @mk_hom_hyper I C (syn_exp_obj I A B) 
       (tm_lam A (tm_app (tm_lam (Ty_Prod C A) (h_tm_of f)) (tm_pair (tm_var 1) (tm_var 0)))) 
       
       ltac:(apply HD_Lam; eapply HD_App; 
             [ apply HD_Lam; apply (hd_weakening_append I ((Ty_Prod C A : h_ty) :: nil) ((A : h_ty) :: (C : h_ty) :: nil)); [ apply double_ctx_wf | exact (h_deriv_of f) ]
             | apply HD_Pair; 
               [ exact (HD_VarS I ((C:h_ty)::nil) C A _ (ty_wf I A) (hyper_id_deriv I C)) 
               | exact (HD_Var0 I ((C:h_ty)::nil) A (obj_ctx_wf I C) (ty_wf I A)) ] ]))

    (fun (A B : obj_hyper I) => @mk_hom_hyper I (syn_prod_obj I (syn_exp_obj I A B) A) B 
       (tm_app (tm_fst (tm_var 0)) (tm_snd (tm_var 0))) 
       
       ltac:(eapply HD_App;
             [ eapply HD_Fst; exact (hyper_id_deriv I (syn_prod_obj I (syn_exp_obj I A B) A)) 
             | eapply HD_Snd; exact (hyper_id_deriv I (syn_prod_obj I (syn_exp_obj I A B) A)) ]))
           
    _ _ _
  ).
  - intros A B C f. apply hyper_hom_equiv_pi.
  - intros A B C h. apply hyper_hom_equiv_pi.
  - unfold Proper, respectful. intros A B C f f' Hf. apply hyper_hom_equiv_pi.
Defined.

Instance Syntactic_BiClosed (I : b_ty) : BiCartesianClosedCategory (Syntactic_Closed I).
Proof.
  refine (mk_BiCartesianClosedCategory (Syntactic_Fiber I) (Syntactic_Cartesian I) (Syntactic_Closed I)
    
    (syn_initial_obj I)
    
    (fun (Phi : obj_hyper I) => @mk_hom_hyper I (syn_initial_obj I) Phi (tm_absurd Phi (tm_var 0)) 
       ltac:(apply HD_Absurd; [exact (ty_wf I Phi) | exact (hyper_id_deriv I (syn_initial_obj I))]))
       
    _
    
    (syn_coprod_obj I)
   
    (fun (Phi Psi : obj_hyper I) => @mk_hom_hyper I Phi (syn_coprod_obj I Phi Psi) (tm_inl Psi (tm_var 0)) 
       ltac:(apply HD_Inl; [exact (ty_wf I Psi) | exact (hyper_id_deriv I Phi)]))
       
    (fun (Phi Psi : obj_hyper I) => @mk_hom_hyper I Psi (syn_coprod_obj I Phi Psi) (tm_inr Phi (tm_var 0)) 
       ltac:(apply HD_Inr; [exact (ty_wf I Phi) | exact (hyper_id_deriv I Psi)]))
       
    (fun (Phi Psi Chi : obj_hyper I) f g => @mk_hom_hyper I (syn_coprod_obj I Phi Psi) Chi 
       (tm_case (tm_var 0) (h_tm_of f) (h_tm_of g)) 
       ltac:(eapply HD_Case; 
             [ exact (hyper_id_deriv I (syn_coprod_obj I Phi Psi)) 
             | apply (hd_weakening_append I ((Phi:h_ty) :: nil) ((Ty_Sum Phi Psi : h_ty) :: nil)); [ apply (obj_ctx_wf I (syn_coprod_obj I Phi Psi)) | exact (h_deriv_of f) ]
             | apply (hd_weakening_append I ((Psi:h_ty) :: nil) ((Ty_Sum Phi Psi : h_ty) :: nil)); [ apply (obj_ctx_wf I (syn_coprod_obj I Phi Psi)) | exact (h_deriv_of g) ] ]))
             
    _ _ _ _
  ).
  - intros x f. apply hyper_hom_equiv_pi.
  - intros A B C f g. apply hyper_hom_equiv_pi.
  - intros A B C f g. apply hyper_hom_equiv_pi.
  - intros A B C h. apply hyper_hom_equiv_pi.
  - unfold Proper, respectful. intros A B C f f' Hf g g' Hg. apply hyper_hom_equiv_pi.
Defined.



Fixpoint h_tm_pullback (f : b_tm) (p : h_tm) : h_tm :=
  match p with
  | tm_unit => tm_unit
  | tm_var i => tm_var i
  | tm_lam Phi p' => tm_lam (form_pullback f Phi) (h_tm_pullback f p')
  | tm_app p1 p2 => tm_app (h_tm_pullback f p1) (h_tm_pullback f p2)
  | tm_pair p1 p2 => tm_pair (h_tm_pullback f p1) (h_tm_pullback f p2)
  | tm_fst p' => tm_fst (h_tm_pullback f p')
  | tm_snd p' => tm_snd (h_tm_pullback f p')
  | tm_inl B p' => tm_inl (form_pullback f B) (h_tm_pullback f p')
  | tm_inr A p' => tm_inr (form_pullback f A) (h_tm_pullback f p')
  | tm_case p1 p2 p3 => tm_case (h_tm_pullback f p1) (h_tm_pullback f p2) (h_tm_pullback f p3)
  | tm_absurd A p' => tm_absurd (form_pullback f A) (h_tm_pullback f p')
  
  | tm_all_intro p' => tm_all_intro (h_tm_pullback (b_pullback_ext f) p')
  | tm_all_elim p' t => tm_all_elim (h_tm_pullback f p') (b_comp t f)
  | tm_ex_intro t p' => tm_ex_intro (b_comp t f) (h_tm_pullback f p')
  | tm_ex_elim p1 p2 => tm_ex_elim (h_tm_pullback f p1) (h_tm_pullback (b_pullback_ext f) p2)
  end.

Definition syn_pullback_obj (I J : b_ty) (f : b_tm) (df : base_typing I f J) (Phi : obj_hyper J) : obj_hyper I :=
  mk_obj_hyper I (form_pullback f Phi) (wf_pullback I J f Phi df (ty_wf J Phi)).


Lemma form_equiv_pullback_comp : forall I J K (f g : b_tm) (df : base_typing J f K) (dg : base_typing I g J) (Phi : obj_hyper K),
  form_equiv I (form_pullback g (form_pullback f Phi)) (form_pullback (b_comp f g) Phi).
Proof.
  intros. eapply FEQ_Pullback_Comp.
  - exact df.
  - exact dg.
  - exact (ty_wf K Phi).
Qed.


Lemma form_equiv_pullback_ext_comm : forall I J A (g : b_tm) (dg : base_typing I g J) (Phi : obj_hyper J),
  form_equiv (b_Prod I A) 
             (form_pullback b_fst (form_pullback g Phi)) 
             (form_pullback (b_pullback_ext g) (form_pullback b_fst Phi)).
Proof.
  intros I J A g dg Phi.
  eapply FEQ_Trans.
  - eapply FEQ_Pullback_Comp; [exact dg | apply BT_Fst | exact (ty_wf J Phi)].
  - eapply FEQ_Trans.
    + eapply FEQ_Pullback_Cong.
      * eapply BT_Comp; [exact dg | apply BT_Fst].
      * eapply BT_Comp; [eapply BT_Fst | eapply BT_Pair; [eapply BT_Comp; [exact dg | apply BT_Fst] | apply BT_Snd]].
      *
        apply BE_Sym.
        eapply BE_BetaFst.
        { eapply BT_Comp; [exact dg | apply BT_Fst]. }
        { apply BT_Snd. }
      * exact (ty_wf J Phi).
    + eapply FEQ_Sym. eapply FEQ_Pullback_Comp.
      * eapply BT_Fst.
      * eapply BT_Pair; [eapply BT_Comp; [exact dg | apply BT_Fst] | apply BT_Snd].
      * exact (ty_wf J Phi).
Defined.

Lemma ctx_equiv_pullback_ext_comm : forall I J A (g : b_tm) (dg : base_typing I g J) (G : h_context),
  wf_ctx J G ->
  ctx_equiv (b_Prod I A)
            (ctx_pullback b_fst (ctx_pullback g G)) 
            (ctx_pullback (b_pullback_ext g) (ctx_pullback b_fst G)).
Proof.
  intros I J A g dg G Hwf.
  induction Hwf; simpl.
  - apply CEQ_nil.
  - apply CEQ_cons.
    + apply (form_equiv_pullback_ext_comm _ _ A g dg (mk_obj_hyper J Phi w)).
    + exact IHHwf.
Qed.

Lemma form_pullback_equiv : forall I J (f : b_tm) (df : base_typing I f J) Phi Psi,
  form_equiv J Phi Psi -> form_equiv I (form_pullback f Phi) (form_pullback f Psi).
Proof.
  intros I J f df Phi Psi f_eq.
  revert I f df.
  induction f_eq; intros; simpl; eauto.
  
  - eapply FEQ_Atom.
    + eapply BT_Comp; [exact d1 | exact df].
    + eapply BT_Comp; [exact d2 | exact df].
    + eapply BE_CongComp.
      * exact b.
      * eapply BE_Refl. exact df.
      
  - apply FEQ_Refl. eapply wf_pullback; eauto.
  - apply FEQ_Sym; eauto.
  - eapply FEQ_Trans; eauto.
  - apply FEQ_Prod; eauto.
  - apply FEQ_Sum; eauto.
  - apply FEQ_Arrow; eauto.
  - apply FEQ_All. apply IHf_eq. eapply BT_Pair; [eapply BT_Comp; [exact df | apply BT_Fst] | apply BT_Snd].
  - apply FEQ_Ex. apply IHf_eq. eapply BT_Pair; [eapply BT_Comp; [exact df | apply BT_Fst] | apply BT_Snd].
  
  - eapply FEQ_Trans.
    + eapply FEQ_Pullback_Comp; [apply BT_Id | exact df | exact w].
    + eapply FEQ_Pullback_Cong.
      * eapply BT_Comp; [apply BT_Id | exact df].
      * exact df.
      * apply BE_IdL. exact df.
      * exact w.
      
  - eapply FEQ_Trans.
    + eapply FEQ_Pullback_Comp; [exact dg | exact df0 | eapply wf_pullback; [exact df | exact w]].
    + eapply FEQ_Trans.
      * eapply FEQ_Pullback_Comp; [exact df | eapply BT_Comp; [exact dg | exact df0] | exact w].
      * eapply FEQ_Trans.
        { eapply FEQ_Pullback_Cong.
          - eapply BT_Comp; [exact df | eapply BT_Comp; [exact dg | exact df0]].
          - eapply BT_Comp; [eapply BT_Comp; [exact df | exact dg] | exact df0].
          - eapply BE_Assoc.
            * exact df0.
            * exact dg.
            * exact df.
          - exact w. }
        { eapply FEQ_Sym. eapply FEQ_Pullback_Comp; [eapply BT_Comp; [exact df | exact dg] | exact df0 | exact w]. }
        
  - eapply FEQ_Trans.
    + eapply FEQ_Pullback_Comp; [exact df | exact df0 | exact w].
    + eapply FEQ_Trans.
      * eapply FEQ_Pullback_Cong.
        { eapply BT_Comp; [exact df | exact df0]. }
        { eapply BT_Comp; [exact dg | exact df0]. }
        { eapply BE_CongComp.
          - exact b.
          - eapply BE_Refl. exact df0.
        }
        { exact w. }
      * eapply FEQ_Sym. eapply FEQ_Pullback_Comp; [exact dg | exact df0 | exact w].
Qed.

Lemma ctx_pullback_equiv_lemma : forall I J (f : b_tm) (df : base_typing I f J) G1 G2,
  ctx_equiv J G1 G2 -> ctx_equiv I (ctx_pullback f G1) (ctx_pullback f G2).
Proof.
  intros I J f df G1 G2 c_eq.
  induction c_eq; simpl.
  - apply CEQ_nil.
  - apply CEQ_cons.
    + eapply form_pullback_equiv; eauto.
    + exact IHc_eq.
Qed.

Lemma derivation_pullback : forall {I J : b_ty} (f : b_tm) (df : base_typing I f J) 
  {G : h_context} {p : h_tm} {Phi : h_ty},
  h_derivation J G p Phi -> 
  h_derivation I (ctx_pullback f G) (h_tm_pullback f p) (form_pullback f Phi).
Proof.
  intros I J f df G p Phi d.
  revert I f df.
  induction d; intros I_src g dg; simpl.
  - apply HD_Var0; [eapply wf_ctx_pullback; [exact dg | exact w] | eapply wf_pullback; [exact dg | exact w0]].
  - apply HD_VarS; [eapply wf_pullback; [exact dg | exact w] | apply IHd; exact dg].
  - eapply HD_Unit; eapply wf_ctx_pullback; [exact dg | exact w].
  - apply HD_Lam. apply IHd; exact dg.
  - eapply HD_App; [apply IHd1; exact dg | apply IHd2; exact dg].
  - apply HD_Pair; [apply IHd1; exact dg | apply IHd2; exact dg].
  - eapply HD_Fst; apply IHd; exact dg.
  - eapply HD_Snd; apply IHd; exact dg.
  - apply HD_Inl; [eapply wf_pullback; [exact dg | exact w] | apply IHd; exact dg].
  - apply HD_Inr; [eapply wf_pullback; [exact dg | exact w] | apply IHd; exact dg].
  - eapply HD_Case; [apply IHd1; exact dg | apply IHd2; exact dg | apply IHd3; exact dg].
  - apply HD_Absurd; [eapply wf_pullback; [exact dg | exact w] | apply IHd; exact dg].
  - apply HD_All_Intro.
    + eapply wf_ctx_pullback; [exact dg | exact w].
    + eapply HD_Conv.
      * apply ctx_equiv_sym. eapply ctx_equiv_pullback_ext_comm; [exact dg | exact w].
      * apply FEQ_Refl. eapply wf_pullback.
        { eapply BT_Pair; [eapply BT_Comp; [exact dg | apply BT_Fst] | apply BT_Snd]. }
        { pose proof (well_formed_target _ _ _ _ d) as Hwf; exact Hwf. }
      * apply IHd. eapply BT_Pair; [eapply BT_Comp; [exact dg | apply BT_Fst] | apply BT_Snd].
 -
    eapply HD_Conv.
    + apply ctx_equiv_refl. eapply wf_ctx_pullback; [exact dg | pose proof (well_formed_ctx _ _ _ _ d) as Hctx; exact Hctx].
    + eapply FEQ_Trans.
      * eapply FEQ_Pullback_Comp.
        { eapply BT_Pair; [eapply BT_Comp; [exact dg | eapply BT_Fst] | apply BT_Snd]. }
        { eapply BT_Pair; [apply BT_Id | eapply BT_Comp; [exact b | exact dg]]. }
        { pose proof (well_formed_all_body _ _ _ _ _ d) as Hwf; exact Hwf. }
      * eapply FEQ_Trans.
        { eapply FEQ_Pullback_Cong.
          - eapply BT_Comp.
            + eapply BT_Pair; [eapply BT_Comp; [exact dg | eapply BT_Fst] | apply BT_Snd].
            + eapply BT_Pair; [apply BT_Id | eapply BT_Comp; [exact b | exact dg]].
          - eapply BT_Comp.
            + eapply BT_Pair; [apply BT_Id | exact b].
            + exact dg.
          -
            eapply BE_Trans.
            { eapply BE_Sym. eapply BE_EtaPair; eauto 10 using base_typing. }
            eapply BE_Trans.
            2: { eapply BE_EtaPair; eauto 10 using base_typing. }
            eapply BE_CongPair.
            +
              eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
              eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_BetaFst; eauto 10 using base_typing | eapply BE_Refl; eauto 10 using base_typing ]. }
              eapply BE_Trans. { eapply BE_Sym. eapply BE_Assoc; eauto 10 using base_typing. }
              eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_Refl; eauto 10 using base_typing | eapply BE_BetaFst; eauto 10 using base_typing ]. }
              eapply BE_Trans. { eapply BE_IdR; eauto 10 using base_typing. }
              eapply BE_Sym. 
              eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
              eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_BetaFst; eauto 10 using base_typing | eapply BE_Refl; eauto 10 using base_typing ]. }
              eapply BE_IdL; eauto 10 using base_typing.
            +
              eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
              eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_BetaSnd; eauto 10 using base_typing | eapply BE_Refl; eauto 10 using base_typing ]. }
              eapply BE_Trans. { eapply BE_BetaSnd; eauto 10 using base_typing. }
              eapply BE_Sym. 
              eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
              eapply BE_CongComp; [ eapply BE_BetaSnd; eauto 10 using base_typing | eapply BE_Refl; eauto 10 using base_typing ].
          - pose proof (well_formed_all_body _ _ _ _ _ d) as Hwf; exact Hwf. }
        { eapply FEQ_Sym. eapply FEQ_Pullback_Comp.
          - eapply BT_Pair; [apply BT_Id | exact b].
          - exact dg.
          - pose proof (well_formed_all_body _ _ _ _ _ d) as Hwf; exact Hwf. }
    + eapply HD_All_Elim; [apply IHd; exact dg | eapply BT_Comp; [exact b | exact dg]].
 -
    eapply HD_Ex_Intro.
    + eapply wf_pullback; [eapply BT_Pair; [eapply BT_Comp; [exact dg | apply BT_Fst] | apply BT_Snd] | exact w].
    + eapply BT_Comp; [exact b | exact dg].
    + eapply HD_Conv.
      * apply ctx_equiv_refl. eapply wf_ctx_pullback; [exact dg | pose proof (well_formed_ctx _ _ _ _ d) as Hctx; exact Hctx].
      * eapply FEQ_Trans.
        { eapply FEQ_Pullback_Comp.
          - eapply BT_Pair; [apply BT_Id | exact b].
          - exact dg.
          - exact w. }
        { eapply FEQ_Trans.
          - eapply FEQ_Pullback_Cong.
            + eapply BT_Comp.
              * eapply BT_Pair; [apply BT_Id | exact b].
              * exact dg.
            + eapply BT_Comp.
              * eapply BT_Pair; [eapply BT_Comp; [exact dg | eapply BT_Fst] | apply BT_Snd].
              * eapply BT_Pair; [apply BT_Id | eapply BT_Comp; [exact b | exact dg]].
            +
              eapply BE_Sym.
              eapply BE_Trans. { eapply BE_Sym. eapply BE_EtaPair; eauto 10 using base_typing. }
              eapply BE_Trans. 2: { eapply BE_EtaPair; eauto 10 using base_typing. }
              eapply BE_CongPair.
              *
                eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
                eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_BetaFst; eauto 10 using base_typing | eapply BE_Refl; eauto 10 using base_typing ]. }
                eapply BE_Trans. { eapply BE_Sym. eapply BE_Assoc; eauto 10 using base_typing. }
                eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_Refl; eauto 10 using base_typing | eapply BE_BetaFst; eauto 10 using base_typing ]. }
                eapply BE_Trans. { eapply BE_IdR; eauto 10 using base_typing. }
                eapply BE_Sym.
                eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
                eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_BetaFst; eauto 10 using base_typing | eapply BE_Refl; eauto 10 using base_typing ]. }
                eapply BE_IdL; eauto 10 using base_typing.
              *
                eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
                eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_BetaSnd; eauto 10 using base_typing | eapply BE_Refl; eauto 10 using base_typing ]. }
                eapply BE_Trans. { eapply BE_BetaSnd; eauto 10 using base_typing. }
                eapply BE_Sym.
                eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
                eapply BE_CongComp; [ eapply BE_BetaSnd; eauto 10 using base_typing | eapply BE_Refl; eauto 10 using base_typing ].
            + exact w.
          - eapply FEQ_Sym. eapply FEQ_Pullback_Comp.
            + eapply BT_Pair; [eapply BT_Comp; [exact dg | eapply BT_Fst] | apply BT_Snd].
            + eapply BT_Pair; [apply BT_Id | eapply BT_Comp; [exact b | exact dg]].
            + exact w. }
      * apply IHd; exact dg.
  -
    eapply HD_Ex_Elim.
    + eapply wf_pullback; [exact dg | exact w].
    + apply IHd1; exact dg.
    + eapply HD_Conv.
      * apply CEQ_cons.
        { apply FEQ_Refl. eapply wf_pullback.
          - eapply BT_Pair; [eapply BT_Comp; [exact dg | apply BT_Fst] | apply BT_Snd].
          - pose proof (well_formed_ex_body _ _ _ _ _ d1) as Hwf; exact Hwf. }
        { apply ctx_equiv_sym. eapply ctx_equiv_pullback_ext_comm; [exact dg | pose proof (well_formed_ctx _ _ _ _ d1) as Hctx; exact Hctx]. }
      * apply FEQ_Sym. exact (form_equiv_pullback_ext_comm I_src I A g dg (mk_obj_hyper I Chi w)).
      * apply IHd2. eapply BT_Pair; [eapply BT_Comp; [exact dg | apply BT_Fst] | apply BT_Snd].

  -
    eapply HD_Conv.
    + eapply ctx_pullback_equiv_lemma; [exact dg | exact c].
    + eapply form_pullback_equiv; [exact dg | exact f].
    + apply IHd; exact dg.
Defined.

Lemma hyper_pullback_map (I J : b_ty) (f : b_tm) (df : base_typing I f J) 
  (Phi Psi : obj_hyper J) 
  (g : hom_hyper J Phi Psi) : 
  hom_hyper I (syn_pullback_obj I J f df Phi) (syn_pullback_obj I J f df Psi).
Proof.
  destruct g as [p dp].
  refine (mk_hom_hyper I 
            (syn_pullback_obj I J f df Phi) 
            (syn_pullback_obj I J f df Psi) 
            (h_tm_pullback f p)
            _).
  change ((syn_pullback_obj I J f df Phi : h_ty) :: nil) with (ctx_pullback f ((Phi : h_ty) :: nil)).
  exact (derivation_pullback f df dp).
Defined.


Lemma syn_iso_from_eq : forall (I : b_ty) (Phi Psi : obj_hyper I),
  (Phi : h_ty) = (Psi : h_ty) -> (Phi : @obj (Syntactic_Fiber I)) ≅O (Psi : @obj (Syntactic_Fiber I)).
Proof.
  intros I Phi Psi Heq.
  
  (* [unshelve] exposes morphism obligations before isomorphism laws. *)
  unshelve econstructor. 
  
  -
    refine (mk_hom_hyper I Phi Psi (tm_var 0) _).
    rewrite <- Heq. exact (hyper_id_deriv I Phi).
    
  -
    refine (mk_hom_hyper I Psi Phi (tm_var 0) _).
    rewrite Heq. exact (hyper_id_deriv I Psi).
    
  -   apply hyper_hom_equiv_pi.
  -   apply hyper_hom_equiv_pi.
Defined.

(** [HD_Conv] turns formula equivalence into a fiber isomorphism. *)
Lemma syn_iso_from_equiv : forall (I : b_ty) (Phi Psi : obj_hyper I),
  form_equiv I Phi Psi -> (Phi : @obj (Syntactic_Fiber I)) ≅O (Psi : @obj (Syntactic_Fiber I)).
Proof.
  intros I Phi Psi Heq.
  
  (* [unshelve] exposes morphism obligations before isomorphism laws. *)
  unshelve econstructor.
  
  -
    refine (mk_hom_hyper I Phi Psi (tm_var 0) _).
    eapply HD_Conv.
    + apply ctx_equiv_refl. apply obj_ctx_wf.
    + exact Heq.
    + exact (hyper_id_deriv I Phi).
    
  -
    refine (mk_hom_hyper I Psi Phi (tm_var 0) _).
    eapply HD_Conv.
    + apply ctx_equiv_refl. apply obj_ctx_wf.
    + apply FEQ_Sym. exact Heq.
    + exact (hyper_id_deriv I Psi).
    
  -   apply hyper_hom_equiv_pi.
  -   apply hyper_hom_equiv_pi.
Defined.

Instance Syntactic_Pullback {I J : b_ty} (f : b_tm) (df : base_typing I f J)
  : Functor (Syntactic_Fiber J) (Syntactic_Fiber I).
Proof.
  refine (mk_Functor (Syntactic_Fiber J) (Syntactic_Fiber I)
    (fun (Phi : obj_hyper J) => syn_pullback_obj I J f df Phi)
    (fun (Phi Psi : obj_hyper J) (g : hom_hyper J Phi Psi) => hyper_pullback_map I J f df Phi Psi g)
    _ _ _ ).
  - unfold Proper, respectful. intros A B g1 g2 Hg. apply hyper_hom_equiv_pi.
  - intros A. apply hyper_hom_equiv_pi.
  - intros A B C g1 g2. apply hyper_hom_equiv_pi.
Defined.



Definition syn_all_obj (I A : b_ty) (Phi : obj_hyper (b_Prod I A)) : obj_hyper I := 
  mk_obj_hyper I (Ty_All A Phi) (WF_All I A Phi (ty_wf (b_Prod I A) Phi)).

Definition syn_all_counit (I A : b_ty) (dfst : base_typing (b_Prod I A) b_fst I) (Psi : obj_hyper (b_Prod I A)) : 
  hom_hyper (b_Prod I A) (syn_pullback_obj (b_Prod I A) I b_fst dfst (syn_all_obj I A Psi)) Psi.
Proof.
  refine (mk_hom_hyper (b_Prod I A) (syn_pullback_obj (b_Prod I A) I b_fst dfst (syn_all_obj I A Psi)) Psi (tm_all_elim (tm_var 0) b_snd) _).
  assert (H_der : h_derivation (b_Prod I A) ((form_pullback b_fst (Ty_All A Psi)) :: nil) (tm_all_elim (tm_var 0) b_snd) 
                               (form_pullback (b_pair b_id b_snd) (form_pullback (b_pullback_ext b_fst) Psi))).
  { eapply HD_All_Elim.
    - exact (HD_Var0 (b_Prod I A) nil (form_pullback b_fst (Ty_All A Psi)) (WFC_nil _) (wf_pullback _ _ _ _ dfst (WF_All I A Psi (ty_wf _ Psi)))).
    - exact BT_Snd. }
  eapply HD_Conv. 3: exact H_der. 1: apply ctx_equiv_refl; apply obj_ctx_wf. 
  
  eapply FEQ_Trans.
  { eapply FEQ_Pullback_Comp. 
    - eapply typing_pullback_ext; exact dfst.
    - eapply BT_Pair; [apply BT_Id | apply BT_Snd].
    - exact (ty_wf _ Psi). }
  eapply FEQ_Trans.
  { eapply FEQ_Pullback_Cong.
    - eapply BT_Comp; [ eapply typing_pullback_ext; exact dfst | eapply BT_Pair; [apply BT_Id | apply BT_Snd] ].
    - apply BT_Id.
    -
      eapply BE_Trans. { eapply BE_Sym. eapply BE_EtaPair; eauto 10 using base_typing. }
      eapply BE_Trans. 2: { eapply BE_EtaPair; eauto 10 using base_typing. }
      eapply BE_CongPair.
      +
        eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
        eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_BetaFst; eauto 10 using base_typing | eapply BE_Refl; eauto 10 using base_typing ]. }
        eapply BE_Trans. { eapply BE_Sym. eapply BE_Assoc; eauto 10 using base_typing. }
        eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_Refl; eauto 10 using base_typing | eapply BE_BetaFst; eauto 10 using base_typing ]. }
        eapply BE_Trans. { eapply BE_IdR; eauto 10 using base_typing. }
        eapply BE_Sym. eapply BE_IdR; eauto 10 using base_typing.
      +
        eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
        eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_BetaSnd; eauto 10 using base_typing | eapply BE_Refl; eauto 10 using base_typing ]. }
        eapply BE_Trans. { eapply BE_BetaSnd; eauto 10 using base_typing. }
        eapply BE_Sym. eapply BE_IdR; eauto 10 using base_typing.
    - exact (ty_wf _ Psi). }
  eapply FEQ_Pullback_Id; exact (ty_wf _ Psi).
Defined.

Definition syn_all_mor (I A : b_ty) (dfst : base_typing (b_Prod I A) b_fst I) (Y : obj_hyper I) (X : obj_hyper (b_Prod I A)) 
  (f : hom_hyper (b_Prod I A) (syn_pullback_obj (b_Prod I A) I b_fst dfst Y) X) : 
  hom_hyper I Y (syn_all_obj I A X).
Proof.
  refine (mk_hom_hyper I Y (syn_all_obj I A X) (tm_all_intro (h_tm_of f)) _).
  apply HD_All_Intro.
  - apply obj_ctx_wf. 
  - exact (h_deriv_of f).
Defined.

Instance Syntactic_All_Adjunction (I A : b_ty) (dfst : base_typing (b_Prod I A) b_fst I) :
  IsLeftAdjoint (Syntactic_Pullback b_fst dfst).
Proof.
  refine (@mk_IsLeftAdjoint (Syntactic_Fiber (b_Prod I A)) (Syntactic_Fiber I) (Syntactic_Pullback b_fst dfst) 
    (syn_all_obj I A) (syn_all_counit I A dfst) (syn_all_mor I A dfst) _ _ _).
  - unfold Proper, respectful. intros Y X f g Hfg. apply hyper_hom_equiv_pi.
  - intros. apply hyper_hom_equiv_pi.
  - intros. apply hyper_hom_equiv_pi.
Defined.


Definition syn_ex_obj (I A : b_ty) (Phi : obj_hyper (b_Prod I A)) : obj_hyper I := 
  mk_obj_hyper I (Ty_Ex A Phi) (WF_Ex I A Phi (ty_wf (b_Prod I A) Phi)).

Definition syn_ex_unit (I A : b_ty) (dfst : base_typing (b_Prod I A) b_fst I) (Y : obj_hyper (b_Prod I A)) : 
  hom_hyper (b_Prod I A) Y (syn_pullback_obj (b_Prod I A) I b_fst dfst (syn_ex_obj I A Y)).
Proof.
  refine (mk_hom_hyper (b_Prod I A) Y (syn_pullback_obj (b_Prod I A) I b_fst dfst (syn_ex_obj I A Y)) (tm_ex_intro b_snd (tm_var 0)) _).
  assert (H_inner : h_derivation (b_Prod I A) ((Y:h_ty) :: nil) (tm_var 0) (form_pullback (b_pair b_id b_snd) (form_pullback (b_pullback_ext b_fst) Y))).
  { eapply HD_Conv. 3: exact (HD_Var0 (b_Prod I A) nil Y (WFC_nil _) (ty_wf _ Y)). 1: apply ctx_equiv_refl; apply obj_ctx_wf. 
    
    eapply FEQ_Sym.
    eapply FEQ_Trans.
    { eapply FEQ_Pullback_Comp. 
      - eapply typing_pullback_ext; exact dfst.
      - eapply BT_Pair; [apply BT_Id | apply BT_Snd].
      - exact (ty_wf _ Y). }
    eapply FEQ_Trans.
    { eapply FEQ_Pullback_Cong.
      - eapply BT_Comp; [ eapply typing_pullback_ext; exact dfst | eapply BT_Pair; [apply BT_Id | apply BT_Snd] ].
      - apply BT_Id.
      -
        eapply BE_Trans. { eapply BE_Sym. eapply BE_EtaPair; eauto 10 using base_typing. }
        eapply BE_Trans. 2: { eapply BE_EtaPair; eauto 10 using base_typing. }
        eapply BE_CongPair.
        +
          eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
          eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_BetaFst; eauto 10 using base_typing | eapply BE_Refl; eauto 10 using base_typing ]. }
          eapply BE_Trans. { eapply BE_Sym. eapply BE_Assoc; eauto 10 using base_typing. }
          eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_Refl; eauto 10 using base_typing | eapply BE_BetaFst; eauto 10 using base_typing ]. }
          eapply BE_Trans. { eapply BE_IdR; eauto 10 using base_typing. }
          eapply BE_Sym. eapply BE_IdR; eauto 10 using base_typing.
        +
          eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
          eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_BetaSnd; eauto 10 using base_typing | eapply BE_Refl; eauto 10 using base_typing ]. }
          eapply BE_Trans. { eapply BE_BetaSnd; eauto 10 using base_typing. }
          eapply BE_Sym. eapply BE_IdR; eauto 10 using base_typing.
      - exact (ty_wf _ Y). }
    eapply FEQ_Pullback_Id; exact (ty_wf _ Y).
  }
  
  assert (H_outer : h_derivation (b_Prod I A) ((Y:h_ty) :: nil) (tm_ex_intro b_snd (tm_var 0)) (Ty_Ex A (form_pullback (b_pullback_ext b_fst) Y))).
  { eapply HD_Ex_Intro.
    - eapply wf_pullback; [eapply BT_Pair; [eapply BT_Comp; [exact dfst | apply BT_Fst] | apply BT_Snd] | exact (ty_wf _ Y)].
    - exact BT_Snd.
    - exact H_inner. }
    
  eapply HD_Conv. 3: exact H_outer. 1: apply ctx_equiv_refl; apply obj_ctx_wf. 
  
  apply FEQ_Refl. eapply wf_pullback; [exact dfst | apply WF_Ex; exact (ty_wf _ Y)].
Defined.

Definition syn_ex_mor (I A : b_ty) (dfst : base_typing (b_Prod I A) b_fst I) (Y : obj_hyper (b_Prod I A)) (X : obj_hyper I) 
  (g : hom_hyper (b_Prod I A) Y (syn_pullback_obj (b_Prod I A) I b_fst dfst X)) : 
  hom_hyper I (syn_ex_obj I A Y) X.
Proof.
  refine (mk_hom_hyper I (syn_ex_obj I A Y) X (tm_ex_elim (tm_var 0) (h_tm_of g)) _).
  assert (H_inner : h_derivation (b_Prod I A) ((Y:h_ty) :: (form_pullback b_fst (Ty_Ex A Y)) :: nil) (h_tm_of g) (form_pullback b_fst X)).
  { apply (hd_weakening_append (b_Prod I A) ((Y:h_ty) :: nil) ((form_pullback b_fst (Ty_Ex A Y)) :: nil)).
    - apply WFC_cons. 
      + eapply wf_pullback. exact dfst. exact (WF_Ex _ _ _ (ty_wf _ Y)).
      + apply WFC_nil.
    - exact (h_deriv_of g). }
  eapply HD_Ex_Elim.
  - exact (ty_wf I X).
  - exact (HD_Var0 I nil (Ty_Ex A Y) (WFC_nil _) (WF_Ex _ _ _ (ty_wf _ Y))).
  - exact H_inner.
Defined.

Instance Syntactic_Ex_Adjunction (I A : b_ty) (dfst : base_typing (b_Prod I A) b_fst I) :
  IsRightAdjoint (Syntactic_Pullback b_fst dfst).
Proof.
  refine (@mk_IsRightAdjoint (Syntactic_Fiber I) (Syntactic_Fiber (b_Prod I A)) (Syntactic_Pullback b_fst dfst) 
    (syn_ex_obj I A) (syn_ex_unit I A dfst) (syn_ex_mor I A dfst) _ _ _).
  - unfold Proper, respectful. intros Y X f g Hfg. apply hyper_hom_equiv_pi.
  - intros. apply hyper_hom_equiv_pi.
  - intros. apply hyper_hom_equiv_pi.
Defined.


Record hom_base {Sign : Type} (I J : b_ty) : Type := mk_hom_base {
  b_tm_of : b_tm;
  b_deriv_of : base_typing I b_tm_of J
}.

Definition base_hom_equiv {Sign : Type} (I J : b_ty) (f g : hom_base I J) : Prop :=
  @base_equiv I J 
    (@b_tm_of Sign I J f) (@b_tm_of Sign I J g).

Instance Base_SetoidCategory {Sign : Type} : SetoidCategory.
Proof.
  refine (mk_SetoidCategory 
    b_ty 
    (@hom_base Sign) 
    (fun I => mk_hom_base Sign I I b_id BT_Id)
    (fun I J K g f => mk_hom_base Sign I K (b_comp (b_tm_of J K g) (b_tm_of I J f)) 
                        (BT_Comp (b_deriv_of J K g) (b_deriv_of I J f)))
    (@base_hom_equiv Sign)
    _ _ _ _ _
  ).
  -
    intros A B. split.
    + intros [tf df]. eapply BE_Refl. exact df.
    + intros [tf df] [tg dg] H. apply BE_Sym. exact H.
    + intros [tf df] [tg dg] [th dh] H1 H2. eapply BE_Trans; eassumption.
  -
    intros A B C D [tf df] [tg dg] [th dh]. 
    simpl. eapply BE_Assoc; eassumption.
  -
    intros A B [tf df]. 
    simpl. eapply BE_IdR; eassumption.
  -
    intros A B [tf df]. 
    simpl. eapply BE_IdL; eassumption.
  -
    unfold Proper, respectful. 
    intros A B C [tf df] [tf' df'] [tg dg] [tg' dg'] Hf Hg. 
    simpl. eapply BE_CongComp; eassumption.
Defined.


Instance Base_CartesianCategory {Sign : Type} : CartesianCategory (@Base_SetoidCategory Sign).
Proof.
  refine (mk_CartesianCategory (@Base_SetoidCategory Sign)
    b_Unit
    (fun I => mk_hom_base Sign I b_Unit b_unit BT_Unit)
    _
    b_Prod
    (fun I J K f g => mk_hom_base Sign I (b_Prod J K) (b_pair (b_tm_of I J f) (b_tm_of I K g)) 
                        (BT_Pair (b_deriv_of I J f) (b_deriv_of I K g)))
    (fun I J => mk_hom_base Sign (b_Prod I J) I b_fst BT_Fst)
    (fun I J => mk_hom_base Sign (b_Prod I J) J b_snd BT_Snd)
    _ _ _ _ 
  ).
  - intros x [tf df]. simpl. eapply BE_Terminal; [exact df | apply BT_Unit].
  - intros A B C [tf df] [tg dg]. simpl. eapply BE_BetaFst; eassumption.
  - intros A B C [tf df] [tg dg]. simpl. eapply BE_BetaSnd; eassumption.
  - intros A B C [th dh]. simpl. eapply BE_EtaPair; eassumption.
  - unfold Proper, respectful. 
    intros A B C [tf df] [tf' df'] Hf [tg dg] [tg' dg'] Hg. 
    simpl. eapply BE_CongPair; eassumption.
Defined.


Instance Base_TwoSortCategory {Sign : Type} : TwoSortCategory (@Base_SetoidCategory Sign).
Proof.
  econstructor.
  assert (H : b_S <> b_Unit) by (intro Heq; discriminate).
  exact H.
Defined.


Definition syn_obj {Sign : Type} (I : @obj (@Base_SetoidCategory Sign)) : b_ty := I.
Definition syn_hom {Sign : Type} {I J : @obj (@Base_SetoidCategory Sign)} (f : hom I J) : 
  @hom_base Sign (syn_obj I) (syn_obj J) := f.

Instance Syntactic_GoodFibration {Sign : Type} : GoodFibration (@Base_SetoidCategory Sign).
Proof.
  refine {|
    Fiber := fun I => Syntactic_Fiber (syn_obj I);
    fiber_is_thin := fun I => hyper_hom_equiv_pi (syn_obj I);
    Fiber_is_Cartesian := fun I => Syntactic_Cartesian (syn_obj I);
    Fiber_is_Closed := fun I => Syntactic_Closed (syn_obj I);
    Fiber_is_BiClosed := fun I => Syntactic_BiClosed (syn_obj I);
    Pullback := fun I J f => 
      Syntactic_Pullback (@b_tm_of Sign (syn_obj I) (syn_obj J) (syn_hom f)) 
                         (@b_deriv_of Sign (syn_obj I) (syn_obj J) (syn_hom f)) ;
    pullback_has_left_adjoint  := fun I A => 
      Syntactic_Ex_Adjunction (syn_obj I) (syn_obj A) BT_Fst ;
    pullback_has_right_adjoint := fun I A => 
      Syntactic_All_Adjunction (syn_obj I) (syn_obj A) BT_Fst
  |}.
  - intros I A. apply syn_iso_from_equiv. apply FEQ_Pullback_Id. exact (ty_wf _ A).
  - intros I J K g f A. apply syn_iso_from_equiv. eapply FEQ_Sym. eapply FEQ_Pullback_Comp.
    + exact (@b_deriv_of Sign _ _ (syn_hom g)). 
    + exact (@b_deriv_of Sign _ _ (syn_hom f)).
    + exact (ty_wf _ A).
  - intros I J f. apply syn_iso_from_eq. reflexivity.
  - intros I J f A B. apply syn_iso_from_eq. reflexivity.
  - intros I J f. apply syn_iso_from_eq. reflexivity.
  - intros I J f A B. apply syn_iso_from_eq. reflexivity.
  - intros I J f A B. apply syn_iso_from_eq. reflexivity.
  - intros I J K f A. apply syn_iso_from_equiv. apply FEQ_Refl. apply WF_Ex. eapply wf_pullback.
    + eapply BT_Pair; [eapply BT_Comp; [exact (@b_deriv_of Sign _ _ (syn_hom f)) | apply BT_Fst] | apply BT_Snd].
    + exact (ty_wf _ A).
  - intros I J K f A. apply syn_iso_from_equiv. apply FEQ_Refl. apply WF_All. eapply wf_pullback.
    + eapply BT_Pair; [eapply BT_Comp; [exact (@b_deriv_of Sign _ _ (syn_hom f)) | apply BT_Fst] | apply BT_Snd].
    + exact (ty_wf _ A).
  - intros I J f g Hfg A. apply syn_iso_from_equiv. eapply FEQ_Pullback_Cong.
    + exact (@b_deriv_of Sign _ _ (syn_hom f)).
    + exact (@b_deriv_of Sign _ _ (syn_hom g)).
    + exact Hfg.
    + exact (ty_wf _ A).
Defined.


Instance Syntactic_StrictGoodFibration {Sign : Type} : 
  StrictGoodFibration (@Base_SetoidCategory Sign) (@Syntactic_GoodFibration Sign).
Proof.
  econstructor.
  intros X Y M1 M2 Hbase.
  assert (Hrev : h_base M2 ≅ h_base M1) by (symmetry; exact Hbase).
  exists Hrev.
  apply hyper_hom_equiv_pi.
Defined.

Lemma interp_ty_id : forall {Sign : Type} (I : b_ty), 
  @interp_ty (@Base_SetoidCategory Sign) _ _ I = I.
Proof.
  intros Sign I. induction I; simpl; reflexivity || (rewrite IHI1, IHI2; reflexivity).
Defined.

Lemma interp_tm_erasure : forall {Sign : Type} {I J : b_ty} {f : b_tm} (df : base_typing I f J),
  @b_tm_of Sign (syn_obj (interp_ty I)) (syn_obj (interp_ty J)) (syn_hom (interp_tm df)) = f.
Proof.
  intros Sign I J f df.
  induction df; simpl; try reflexivity; try (f_equal; eauto).
Qed.


Instance Syntactic_HyperModel {Sign : Type} : 
  HyperModel (@Syntactic_StrictGoodFibration Sign).
Proof.
  econstructor.
  Unshelve.
  
  4: {
    intros p t I A dt.
    assert (Heq : I = @interp_ty (@Base_SetoidCategory Sign) _ _ I) by (symmetry; apply interp_ty_id).
    exact (mk_obj_hyper (@interp_ty (@Base_SetoidCategory Sign) _ _ I) (Ty_Atom p t) 
             (eq_rect I (fun X => WellFormed X (Ty_Atom p t)) (WF_Atom I p t A dt) _ Heq)).
  }
  
  -
    intros p t I J A f df dt.
    apply syn_iso_from_eq.
    simpl. f_equal. f_equal. 
    apply interp_tm_erasure.
    
  -
    intros I J f g df dg Heq.
    apply base_soundness_equational. exact Heq.
    
  -
    intros p t1 t2 I A d1 d2 Heq.
    apply syn_iso_from_equiv. simpl.
    rewrite interp_ty_id.
    eapply FEQ_Atom; [exact d1 | exact d2 | ].
    exact Heq.
Defined.


Lemma interp_h_ty_id : forall {Sign : Type} I Phi (wf : WellFormed I Phi),
  (@interp_h_ty (@Base_SetoidCategory Sign) _ _ _ _ (@Syntactic_HyperModel Sign) I Phi wf : h_ty) = Phi.
Proof.
  intros Sign I Phi. 
  
  (* Generalize [I] so induction applies in the contexts extended by quantifiers. *)
  revert I. 
  
  induction Phi; intros I wf; simpl; try reflexivity.
  - f_equal; [apply IHPhi1 | apply IHPhi2].
  - f_equal; [apply IHPhi1 | apply IHPhi2].
  - f_equal; [apply IHPhi1 | apply IHPhi2].
  
  -
    f_equal.
    +
      apply interp_ty_id.
    +
      exact (IHPhi (b_Prod I b) (ext_all wf)).
      
  -
    f_equal.
    +
      apply interp_ty_id.
    +
      exact (IHPhi (b_Prod I b) (ext_ex wf)).
Qed.

Theorem hyper_completeness_equational : 
  forall {I : b_ty} {G : h_context} {Phi : h_ty} {p q : h_tm}
  (dp : h_derivation I G p Phi) (dq : h_derivation I G q Phi),
  (forall (C : SetoidCategory) (CC : CartesianCategory C) 
          (TSC : TwoSortCategory C)
          (GF : GoodFibration C) (SGF : StrictGoodFibration C GF) (HM : HyperModel SGF)
          (wfc : wf_ctx I G) (wf_Phi : WellFormed I Phi),
     hyper_soundness_inhabited dp wfc wf_Phi ≅
     hyper_soundness_inhabited dq wfc wf_Phi) ->
  h_equiv_rel I p q.
Proof.
  intros I G Phi p q dp dq H_univ.
  pose proof (well_formed_ctx _ _ _ _ dp) as wfc_syn.
  pose proof (well_formed_target _ _ _ _ dp) as wf_Phi_syn.
  
  pose proof (@H_univ 
               (@Base_SetoidCategory nat) 
               (@Base_CartesianCategory nat)
               (@Base_TwoSortCategory nat)
               (@Syntactic_GoodFibration nat)
               (@Syntactic_StrictGoodFibration nat)
               (@Syntactic_HyperModel nat)
               wfc_syn wf_Phi_syn) as H_syn.
               
  unfold hyper_hom_equiv in H_syn.
  eapply hyper_pi; [exact dp | exact dq].
Qed.

Theorem hyper_completeness_inhabitational : 
  forall {I : b_ty} {Phi : h_ty} (wf_Phi : WellFormed I Phi),
  (forall (C : SetoidCategory) (CC : CartesianCategory C)
          (TSC : TwoSortCategory C)
          (GF : GoodFibration C) (SGF : StrictGoodFibration C GF) (HM : HyperModel SGF)
          (wfc : wf_ctx I nil) (wf_Phi' : WellFormed I Phi),
     inhabited (hom (interp_h_ctx I nil wfc) (interp_h_ty I Phi wf_Phi'))) ->
  exists (p : h_tm), inhabited (h_derivation I nil p Phi).
Proof.
  intros I Phi wf_Phi H_univ.
  
  pose proof (@H_univ 
               (@Base_SetoidCategory nat) 
               (@Base_CartesianCategory nat)
               (@Base_TwoSortCategory nat)
               (@Syntactic_GoodFibration nat)
               (@Syntactic_StrictGoodFibration nat)
               (@Syntactic_HyperModel nat)
               (WFC_nil I) wf_Phi) as [[p_syn dp_syn]].
               
  assert (Heq_Phi : (@interp_h_ty (@Base_SetoidCategory nat) _ _ _ _ (@Syntactic_HyperModel nat) I Phi wf_Phi : h_ty) = Phi)
    by apply interp_h_ty_id.
  rewrite Heq_Phi in dp_syn.
    
  change (@interp_h_ctx (@Base_SetoidCategory nat) _ _ _ _ (@Syntactic_HyperModel nat) I nil (WFC_nil I) : h_ty) 
    with Ty_Unit in dp_syn.
  
  (* Fix [I] only after eliminating the dependent wrappers. *)
  assert (Heq_I : (@interp_ty (@Base_SetoidCategory nat) _ _ I) = I) by apply interp_ty_id.
  unfold syn_obj in dp_syn.
  rewrite Heq_I in dp_syn.
  
  exists (tm_app (tm_lam Ty_Unit p_syn) tm_unit).
  constructor.
  eapply HD_App.
  - apply HD_Lam. exact dp_syn.
  - apply HD_Unit. apply WFC_nil.
Qed.



Fixpoint h_make_ctx_ty (G : h_context) : h_ty :=
  match G with
  | nil => Ty_Unit
  | A :: G' => Ty_Prod (h_make_ctx_ty G') A
  end.



Fixpoint h_reify_ctx (G : h_context) : h_tm :=
  match G with
  | nil => tm_unit
  | A :: G' => tm_pair (h_lift 1 0 (h_reify_ctx G')) (tm_var 0)
  end.


Theorem hd_weakening_general : forall I G p Phi Psi n,
  WellFormed I Psi ->
  h_derivation I G p Phi ->
  h_derivation I (h_insert_at n Psi G) (h_lift 1 n p) Phi.
Proof.
  intros I G p Phi Psi n Hwf d.
  revert n Psi Hwf.
  induction d; intros n0 Psi0 Hwf0; simpl.
  -
    destruct n0; simpl.
    + apply HD_VarS; [assumption | apply HD_Var0; assumption].
    + apply HD_Var0; [apply wf_ctx_insert; assumption | assumption].
  -
    destruct n0; simpl.
    + apply HD_VarS; [assumption | apply HD_VarS; assumption].
    + destruct (n0 <=? i) eqn:Heq.
      * apply HD_VarS; [assumption | idtac].
        replace (tm_var (Datatypes.S i)) with (h_lift 1 n0 (tm_var i)) by (simpl; rewrite Heq; reflexivity).
        exact (IHd n0 Psi0 Hwf0).
      * apply HD_VarS; [assumption | idtac].
        replace (tm_var i) with (h_lift 1 n0 (tm_var i)) by (simpl; rewrite Heq; reflexivity).
        exact (IHd n0 Psi0 Hwf0).
  -
    apply HD_Unit. apply wf_ctx_insert; assumption.
  -
    apply HD_Lam. apply (IHd (Datatypes.S n0) Psi0 Hwf0).
  -
    eapply HD_App. apply (IHd1 n0 Psi0 Hwf0). apply (IHd2 n0 Psi0 Hwf0).
  -
    apply HD_Pair. apply (IHd1 n0 Psi0 Hwf0). apply (IHd2 n0 Psi0 Hwf0).
  -
    eapply HD_Fst. apply (IHd n0 Psi0 Hwf0).
  -
    eapply HD_Snd. apply (IHd n0 Psi0 Hwf0).
  -
    apply HD_Inl; [assumption | apply (IHd n0 Psi0 Hwf0)].
  -
    apply HD_Inr; [assumption | apply (IHd n0 Psi0 Hwf0)].
  -
    eapply HD_Case.
    + apply (IHd1 n0 Psi0 Hwf0).
    + apply (IHd2 (Datatypes.S n0) Psi0 Hwf0).
    + apply (IHd3 (Datatypes.S n0) Psi0 Hwf0).
  -
    apply HD_Absurd; [assumption | apply (IHd n0 Psi0 Hwf0)].
  -
    apply HD_All_Intro; [apply wf_ctx_insert; assumption | idtac].
    rewrite ctx_pullback_insert. apply (IHd n0 (form_pullback b_fst Psi0)).
    eapply wf_pullback; [apply BT_Fst | assumption].
  -
    eapply HD_All_Elim; [apply (IHd n0 Psi0 Hwf0) | assumption].
  -
    eapply HD_Ex_Intro; [assumption | assumption | apply (IHd n0 Psi0 Hwf0)].
  -
    eapply HD_Ex_Elim; [assumption | apply (IHd1 n0 Psi0 Hwf0) | idtac].
    rewrite ctx_pullback_insert. apply (IHd2 (Datatypes.S n0) (form_pullback b_fst Psi0)).
    eapply wf_pullback; [apply BT_Fst | assumption].
  -
    eapply HD_Conv.
    + apply ctx_equiv_insert; [assumption | eassumption].
    + eassumption.
    + apply (IHd n0 Psi0 Hwf0).
Defined.




Lemma hd_weakening : forall I G A p Phi,
  wf_ctx I (A :: G) ->
  h_derivation I G p Phi ->
  h_derivation I (A :: G) (h_lift 1 0 p) Phi.
Proof.
  intros I G A p Phi wfc d.
  assert (Hwf : WellFormed I A) by (inversion wfc; subst; assumption).
  exact (hd_weakening_general I G p Phi A 0 Hwf d).
Qed.

Lemma h_lift_0 : forall p n, h_lift 0 n p = p.
Proof.
  induction p; intros n0; simpl; f_equal; eauto.
  -
    destruct (n0 <=? n).
    +
      f_equal.
    + reflexivity.
Qed.

Lemma h_lift_S_gen : forall p shift cutoff, 
  h_lift (Datatypes.S shift) cutoff p = h_lift 1 cutoff (h_lift shift cutoff p).
Proof.
  induction p; intros shift cutoff; simpl; f_equal; eauto.
-
    destruct (cutoff <=? n) eqn:Heq1.
    +
      simpl. 
      
      assert (Heq2 : (cutoff <=? shift + n) = true).
      { apply Nat.leb_le. apply Nat.leb_le in Heq1. lia. }
      
      rewrite Heq2. f_equal.
      
    +
      simpl. rewrite Heq1. reflexivity.
Qed.

Lemma h_lift_S : forall p shift, h_lift (Datatypes.S shift) 0 p = h_lift 1 0 (h_lift shift 0 p).
Proof.
  intros p shift. apply h_lift_S_gen.
Qed.

Lemma h_weakening_from_nil : forall I G p Phi,
  wf_ctx I G ->
  h_derivation I nil p Phi ->
  h_derivation I G (h_lift (length G) 0 p) Phi.
Proof.
  intros I G. induction G; intros p Phi wfc d; simpl.
  -
    rewrite h_lift_0. 
    exact d.
    
  -
    rewrite h_lift_S. 
    
    apply hd_weakening.
    + exact wfc.
    + apply IHG. 
      * inversion wfc; subst; assumption.
      * exact d.
Qed.

Lemma h_reify_ctx_typing : forall I G (wfc : wf_ctx I G),
  h_derivation I G (h_reify_ctx G) (h_make_ctx_ty G).
Proof.
  intros I G. induction G; intros wfc; simpl.
  - apply HD_Unit. exact wfc.
  - apply HD_Pair.
    +
      eapply hd_weakening. 
      * exact wfc.
      * apply IHG. inversion wfc; subst; assumption.
    +
      apply HD_Var0.
      *
        inversion wfc; subst; assumption.
      *
        inversion wfc; subst; assumption.
Qed.


(** Context interpretation computes to the packed product formula. *)
Lemma h_ctx_identity : forall {Sign : Type} I G (wfc : wf_ctx I G),
  (@interp_h_ctx (@Base_SetoidCategory Sign) _ _ _ _ (@Syntactic_HyperModel Sign) I G wfc : h_ty) = h_make_ctx_ty G.
Proof.
  intros Sign I G. 
  
  revert I. 
  
  induction G; intros I wfc; simpl.
  -
    reflexivity.
    
  -
    f_equal.
    +
      apply IHG.
      
    +
      apply interp_h_ty_id.
Qed.




Theorem hyper_completeness_inhabitational_gen : 
  forall {I : b_ty} {G : h_context} {Phi : h_ty} 
         (wfc : wf_ctx I G) (wf_Phi : WellFormed I Phi),
  (forall (C : SetoidCategory) (CC : CartesianCategory C)
          (TSC : TwoSortCategory C)
          (GF : GoodFibration C) (SGF : StrictGoodFibration C GF) (HM : HyperModel SGF)
          (wfc' : wf_ctx I G) (wf_Phi' : WellFormed I Phi),
     inhabited (hom (interp_h_ctx I G wfc') (interp_h_ty I Phi wf_Phi'))) ->
  exists (p : h_tm), inhabited (h_derivation I G p Phi).
Proof.
  intros I G Phi wfc wf_Phi H_univ.
  
  pose proof (@H_univ 
               (@Base_SetoidCategory nat) 
               (@Base_CartesianCategory nat)
               (@Base_TwoSortCategory nat)
               (@Syntactic_GoodFibration nat)
               (@Syntactic_StrictGoodFibration nat)
               (@Syntactic_HyperModel nat)
               wfc wf_Phi) as [[p_syn dp_syn]].
               
  assert (Heq_Phi : (@interp_h_ty (@Base_SetoidCategory nat) _ _ _ _ (@Syntactic_HyperModel nat) I Phi wf_Phi : h_ty) = Phi)
    by apply interp_h_ty_id.
  rewrite Heq_Phi in dp_syn.
    
  assert (Heq_Ctx : (@interp_h_ctx (@Base_SetoidCategory nat) _ _ _ _ (@Syntactic_HyperModel nat) I G wfc : h_ty) = h_make_ctx_ty G)
    by apply h_ctx_identity.
  rewrite Heq_Ctx in dp_syn.
  
  assert (Heq_I : (@interp_ty (@Base_SetoidCategory nat) _ _ I) = I) by apply interp_ty_id.
  unfold syn_obj in dp_syn.
  rewrite Heq_I in dp_syn.
  
  
  (* Close the fiber arrow as an implication before weakening it into [G]. *)
  assert (H_weak : h_derivation I G (h_lift (length G) 0 (tm_lam (h_make_ctx_ty G) p_syn)) (Ty_Arrow (h_make_ctx_ty G) Phi)).
  { apply h_weakening_from_nil. 
    - exact wfc. 
    - apply HD_Lam. exact dp_syn. }

  exists (tm_app (h_lift (length G) 0 (tm_lam (h_make_ctx_ty G) p_syn)) (h_reify_ctx G)).
  constructor.
  eapply HD_App.
  - exact H_weak.
  - apply h_reify_ctx_typing. exact wfc.
Qed.













