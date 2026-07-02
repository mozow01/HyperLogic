(* HyperLogic/theories/Semantics/Simple_Ext/Simple_Ext_Completeness.v *)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Equality.
Require Import List Arith PeanoNat Lia.

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
Require Import HyperLogic.Semantics.Simple_Ext.Base_Epsilon_Completeness.
Require Import HyperLogic.Semantics.Simple_Ext.Base_Epsilon_Soundness.
Require Import HyperLogic.Semantics.Simple_Ext.Simple_Ext_Soundness.
Require Import HyperLogic.Semantics.Simple_Ext.Simple_Ext_Fibration.
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum.
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum_Lemmas.
Require Import HyperLogic.Logic.Hyper.Simple_Ext.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple_Ext.Hyper_Lemmas.
Require Import HyperLogic.Logic.Hyper.Simple_Ext.Hyper_Lifting.

(* ================================================================= *)
(* 1. MORPHISMS OF THE SYNTACTIC FIBER                               *)
(* ================================================================= *)
(* In the fiber over base context 'I', a morphism from Phi to Psi 
    is a valid derivation from the singleton context [Phi] to Psi. *)
Record hom_hyper {Sign : Type} (I : b_ty) (Phi Psi : @h_ty Sign) : Type := mk_hom_hyper {
  h_tm_of : @h_tm Sign;
  h_deriv_of : @h_derivation Sign I (Phi :: nil) h_tm_of Psi
}.

(* The new rigorous objects of the Syntactic Fiber *)
Record obj_hyper {Sign : Type} (I : b_ty) : Type := mk_obj_hyper {
  ty_val : @h_ty Sign;
  ty_wf  : @WellFormed Sign I ty_val
}.

(* Coercion allows you to seamlessly use obj_hyper where h_ty is expected *)
Coercion ty_val : obj_hyper >-> h_ty.

Arguments h_tm_of {Sign I Phi Psi} _.
Arguments h_deriv_of {Sign I Phi Psi} _.

(* ================================================================= *)
(* 1.5 SYNTACTIC FIBER INFRASTRUCTURE                                *)
(* ================================================================= *)

Lemma ctx_pullback_app : forall {Sign : Type} f (G Delta : @h_context Sign),
  ctx_pullback f (G ++ Delta) = ctx_pullback f G ++ ctx_pullback f Delta.
Proof.
  intros. unfold ctx_pullback. apply map_app.
Qed.


Fixpoint derivation_to_typing {Sign : Type} {I G p A} 
  (d : @h_derivation Sign I G p A) : @h_typing Sign I G p A.
Proof.
  induction d.
  - apply HT_Var0.
  - apply HT_VarS; assumption.
  - eapply HT_Conv; eassumption.
  - apply HT_Unit.
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
  - eapply HT_Ctx_Conv; eassumption.
  - eapply HT_Ex_Elim; eassumption.
Defined.

Lemma hyper_pi : forall {Sign : Type} I G p q A 
  (dp : @h_derivation Sign I G p A) (dq : @h_derivation Sign I G q A), 
  @h_equiv_rel Sign I p q.
Proof.
  intros. eapply PI_rule.
  - apply derivation_to_typing; exact dp.
  - apply derivation_to_typing; exact dq.
Qed.

(* ================================================================= *)
(* 2. IDENTITY AND COMPOSITION OF THE SYNTACTIC FIBER                *)
(* ================================================================= *)

Definition hyper_id_term {Sign : Type} (Phi : @h_ty Sign) : @h_tm Sign :=
  tm_var 0.

(* A '@' operátorral kikerüljük az implicit kitalálósdit: *)
Definition hyper_id_deriv {Sign : Type} (I : b_ty) (Phi : obj_hyper I) 
  : @h_derivation Sign I ((Phi : h_ty) :: nil) (hyper_id_term Phi) Phi :=
  @HD_Var0 Sign I nil Phi (@WFC_nil Sign I) (@ty_wf Sign I Phi).

Definition hyper_id {Sign : Type} (I : b_ty) (Phi : obj_hyper I) : hom_hyper I Phi Phi :=
  @mk_hom_hyper Sign I Phi Phi (hyper_id_term Phi) (hyper_id_deriv I Phi).

Definition hyper_comp_term {Sign : Type} (Psi : @h_ty Sign) (tf tg : @h_tm Sign) : @h_tm Sign :=
  tm_app (tm_lam Psi tg) tf.

Lemma ctx_equiv_refl : forall {Sign : Type} I G, @wf_ctx Sign I G -> @ctx_equiv Sign I G G.
Proof.
  intros Sign I G Hwf. induction Hwf; simpl.
  - apply CEQ_nil.
  - apply CEQ_cons; [apply FE_Refl; assumption | assumption].
Defined.

Lemma ctx_equiv_sym : forall {Sign : Type} I G1 G2, 
  @ctx_equiv Sign I G1 G2 -> @ctx_equiv Sign I G2 G1.
Proof.
  intros Sign I G1 G2 H. induction H.
  - apply CEQ_nil.
  - apply CEQ_cons; [apply FE_Sym; assumption | assumption].
Defined.

Lemma ctx_equiv_app : forall {Sign : Type} I G1 G2 D1 D2,
  @ctx_equiv Sign I G1 G2 -> @ctx_equiv Sign I D1 D2 -> @ctx_equiv Sign I (G1 ++ D1) (G2 ++ D2).
Proof.
  intros Sign I G1 G2 D1 D2 H1 H2.
  induction H1; simpl.
  - exact H2.
  - apply CEQ_cons; [assumption | exact IHctx_equiv].
Defined.

Lemma obj_ctx_wf : forall {Sign : Type} (I : b_ty) (Phi : obj_hyper I), @wf_ctx Sign I ((Phi : h_ty) :: nil).
Proof.
  intros Sign I Phi. eapply WFC_cons. exact (@ty_wf Sign I Phi). apply WFC_nil.
Qed.

(* Két jólformált kontextus összefűzése is jólformált *)
Lemma wf_ctx_app : forall {Sign : Type} I (G Delta : @h_context Sign),
  @wf_ctx Sign I G ->
  @wf_ctx Sign I Delta ->
  @wf_ctx Sign I (G ++ Delta).
Proof.
  intros Sign I G Delta wG wDelta.
  induction wG; simpl.
  - (* Ha G üres, a Delta jólformáltsága az eredmény *)
    exact wDelta.
  - (* Ha G = Phi :: G', akkor hozzáadjuk a fejet az összefűzött farokhoz *)
    apply WFC_cons; [assumption | exact IHwG].
Defined.

Lemma hd_weakening_append : forall {Sign : Type} I (G Delta : @h_context Sign) p Phi,
  @wf_ctx Sign I Delta ->
  @h_derivation Sign I G p Phi -> @h_derivation Sign I (G ++ Delta) p Phi.
Proof.
  assert (H_cons_app : forall (T : Type) (l : list T) (a : T), a :: l = [a] ++ l) by (simpl; auto).
  intros Sign I G Delta p Phi Hwf d.
  revert Delta Hwf.
  induction d; intros Delta Hwf;
  try (rewrite H_cons_app; try rewrite <- app_assoc; try rewrite <- H_cons_app).
  - (* 1. HD_Var0 *) apply HD_Var0; [apply wf_ctx_app; assumption | assumption].
  - (* 2. HD_VarS *) apply HD_VarS; [apply IHd; assumption | assumption].
  - (* 3. HD_Conv *) eapply HD_Conv; [apply IHd; assumption | eassumption | assumption].
  - (* 4. HD_Unit *) apply HD_Unit; apply wf_ctx_app; assumption.
  - (* 5. HD_Lam  *) apply HD_Lam; apply IHd; assumption.
  - (* 6. HD_App  *) eapply HD_App; [apply IHd1; assumption | apply IHd2; assumption].
  - (* 7. HD_Pair *) apply HD_Pair; [apply IHd1; assumption | apply IHd2; assumption].
  - (* 8. HD_Fst  *) eapply HD_Fst; apply IHd; assumption.
  - (* 9. HD_Snd  *) eapply HD_Snd; apply IHd; assumption.
  - (* 10. HD_Inl *) apply HD_Inl; [apply IHd; assumption | assumption].
  - (* 11. HD_Inr *) apply HD_Inr; [apply IHd; assumption | assumption].
  - (* 12. HD_Case *) eapply HD_Case; [apply IHd1; assumption | apply IHd2; assumption | apply IHd3; assumption].
  - (* 13. HD_Absurd *) apply HD_Absurd; [apply IHd; assumption | assumption].
  - (* 14. HD_All_Intro *) 
    apply HD_All_Intro. 
    + apply wf_ctx_app; assumption.
    + rewrite ctx_pullback_app. apply IHd. eapply wf_ctx_pullback; [apply (@BT_Fst Sign I A) | assumption].
  - (* 15. HD_All_Elim *) eapply HD_All_Elim; [apply IHd; assumption | assumption].
  - (* 16. HD_Ex_Intro *) eapply HD_Ex_Intro; [assumption | assumption | apply IHd; assumption].
  - (* HD_Ctx_Conv ág (Kontextus Konverzió) *)
    eapply HD_Ctx_Conv.
    + apply IHd. apply Hwf.
    + apply ctx_equiv_app; [eassumption | apply ctx_equiv_refl; assumption].
    + apply wf_ctx_app; [eassumption | assumption].
    
  - (* HD_Ex_Elim ág (Egzisztenciális Kvantor Kivezetés) *)
    eapply HD_Ex_Elim. 
    + assumption. 
    + apply IHd1; assumption. 
    + rewrite ctx_pullback_app. apply IHd2. eapply wf_ctx_pullback; [apply (@BT_Fst Sign I A) | assumption].
Defined.

Definition hyper_comp_deriv {Sign : Type} (I : b_ty) (Phi Psi Chi : @obj_hyper Sign I)
  (tf tg : @h_tm Sign)
  (df : @h_derivation Sign I ((Phi : h_ty) :: nil) tf Psi)
  (dg : @h_derivation Sign I ((Psi : h_ty) :: nil) tg Chi) :
  @h_derivation Sign I ((Phi : h_ty) :: nil) (hyper_comp_term Psi tf tg) Chi.
Proof.
  unfold hyper_comp_term.
  eapply HD_App.
  - apply (@hd_weakening_append Sign I nil ((Phi : h_ty) :: nil)).
    + apply obj_ctx_wf.
    + apply HD_Lam. exact dg.
  - exact df.
Defined.

Definition hyper_comp {Sign : Type} (I : b_ty) (Phi Psi Chi : @obj_hyper Sign I)
  (g : @hom_hyper Sign I Psi Chi) (f : @hom_hyper Sign I Phi Psi) : @hom_hyper Sign I Phi Chi :=
  @mk_hom_hyper Sign I Phi Chi 
    (hyper_comp_term Psi (h_tm_of f) (h_tm_of g)) 
    (@hyper_comp_deriv Sign I Phi Psi Chi (h_tm_of f) (h_tm_of g) (h_deriv_of f) (h_deriv_of g)).

Definition hyper_hom_equiv {Sign : Type} (I : b_ty) (Phi Psi : @obj_hyper Sign I)
  (f g : @hom_hyper Sign I Phi Psi) : Prop :=
  @h_equiv_rel Sign I (h_tm_of f) (h_tm_of g).

Lemma hyper_hom_equiv_pi : forall {Sign : Type} 
  (I : b_ty) (Phi Psi : @obj_hyper Sign I) (f g : @hom_hyper Sign I Phi Psi),
  @hyper_hom_equiv Sign I Phi Psi f g.
Proof.
  intros Sign I Phi Psi f g.
  unfold hyper_hom_equiv.
  eapply hyper_pi.
  - exact (h_deriv_of f).
  - exact (h_deriv_of g).
Qed.

(* ================================================================= *)
(* 3. THE SYNTACTIC FIBER CATEGORY                                   *)
(* ================================================================= *)

Instance Syntactic_Fiber {Sign : Type} (I : b_ty) : SetoidCategory.
Proof.
  refine (mk_SetoidCategory 
    (@obj_hyper Sign I)
    (@hom_hyper Sign I)
    (@hyper_id Sign I)
    (@hyper_comp Sign I)
    (@hyper_hom_equiv Sign I)
    _ _ _ _ _).
  - (* Equivalence *)
    intros A B. split.
    + intros f. apply hyper_hom_equiv_pi.
    + intros f g H. apply hyper_hom_equiv_pi.
    + intros f g h H1 H2. apply hyper_hom_equiv_pi.
  - (* Assoc *) intros A B C D f g h. apply hyper_hom_equiv_pi.
  - (* IdR *) intros A B f. apply hyper_hom_equiv_pi.
  - (* IdL *) intros A B f. apply hyper_hom_equiv_pi.
  - (* Proper *) unfold Proper, respectful. intros A B C f f' Hf g g' Hg. apply hyper_hom_equiv_pi.
Defined.

(* ================================================================= *)
(* 3.5 OBJECT BUILDERS (Axiom-Free Well-Formedness!)                 *)
(* ================================================================= *)

Definition syn_terminal_obj {Sign : Type} (I : b_ty) : @obj_hyper Sign I :=
  @mk_obj_hyper Sign I Ty_Unit (@WF_Unit Sign I).

Definition syn_prod_obj {Sign : Type} (I : b_ty) (Phi Psi : @obj_hyper Sign I) : @obj_hyper Sign I :=
  @mk_obj_hyper Sign I (Ty_Prod Phi Psi) (@WF_Prod Sign I Phi Psi (ty_wf I Phi) (ty_wf I Psi)).

Definition syn_exp_obj {Sign : Type} (I : b_ty) (S T : @obj_hyper Sign I) : @obj_hyper Sign I :=
  @mk_obj_hyper Sign I (Ty_Arrow S T) (@WF_Arrow Sign I S T (ty_wf I S) (ty_wf I T)).

Definition syn_initial_obj {Sign : Type} (I : b_ty) : @obj_hyper Sign I :=
  @mk_obj_hyper Sign I Ty_Void (@WF_Void Sign I).

Definition syn_coprod_obj {Sign : Type} (I : b_ty) (Phi Psi : @obj_hyper Sign I) : @obj_hyper Sign I :=
  @mk_obj_hyper Sign I (Ty_Sum Phi Psi) (@WF_Sum Sign I Phi Psi (ty_wf I Phi) (ty_wf I Psi)).

Lemma double_ctx_wf : forall {Sign : Type} I (A C : @obj_hyper Sign I), @wf_ctx Sign I ((A:h_ty) :: (C:h_ty) :: nil).
Proof.
  intros Sign I A C. apply WFC_cons. exact (ty_wf I A). apply WFC_cons. exact (ty_wf I C). apply WFC_nil.
Qed.

(* ================================================================= *)
(* 4. THE SYNTACTIC HYPERDOCTRINE                                    *)
(* ================================================================= *)

Instance Syntactic_Cartesian {Sign : Type} (I : b_ty) : CartesianCategory (@Syntactic_Fiber Sign I).
Proof.
  refine (mk_CartesianCategory (@Syntactic_Fiber Sign I)
    
    (@syn_terminal_obj Sign I)
    
    (fun (Phi : @obj_hyper Sign I) => @mk_hom_hyper Sign I Phi (@syn_terminal_obj Sign I) tm_unit 
       (@HD_Unit Sign I ((Phi : h_ty) :: nil) (obj_ctx_wf I Phi)))
    
    _ (* terminal_map_unique law *)
    
    (@syn_prod_obj Sign I)
    
    (fun (Phi Psi Chi : @obj_hyper Sign I) f g => @mk_hom_hyper Sign I Phi (@syn_prod_obj Sign I Psi Chi) (tm_pair (h_tm_of f) (h_tm_of g)) 
       ltac:(apply HD_Pair; [ exact (h_deriv_of f) | exact (h_deriv_of g) ]))
       
    (fun (Phi Psi : @obj_hyper Sign I) => @mk_hom_hyper Sign I (@syn_prod_obj Sign I Phi Psi) Phi (tm_fst (tm_var 0)) 
       ltac:(eapply HD_Fst; exact (hyper_id_deriv I (@syn_prod_obj Sign I Phi Psi))))
       
    (fun (Phi Psi : @obj_hyper Sign I) => @mk_hom_hyper Sign I (@syn_prod_obj Sign I Phi Psi) Psi (tm_snd (tm_var 0)) 
       ltac:(eapply HD_Snd; exact (hyper_id_deriv I (@syn_prod_obj Sign I Phi Psi))))
    
    _ _ _ _ (* Category laws *)
  ).
  - intros x f. apply hyper_hom_equiv_pi.
  - intros A B C f g. apply hyper_hom_equiv_pi.
  - intros A B C f g. apply hyper_hom_equiv_pi.
  - intros A B C h. apply hyper_hom_equiv_pi.
  - unfold Proper, respectful. intros A B C f f' Hf g g' Hg. apply hyper_hom_equiv_pi.
Defined.

Instance Syntactic_Closed {Sign : Type} (I : b_ty) : CartesianClosedCategory (@Syntactic_Fiber Sign I).
Proof.
  refine (mk_CartesianClosedCategory (@Syntactic_Fiber Sign I) (@Syntactic_Cartesian Sign I)
    
    (* 1. exp mapping *)
    (fun Tgt Src => @syn_exp_obj Sign I Src Tgt)

    (* 2. Curry *)
    (fun (C A B : @obj_hyper Sign I) f => @mk_hom_hyper Sign I C (@syn_exp_obj Sign I A B) 
       (tm_lam A (tm_app (tm_lam (Ty_Prod C A) (h_tm_of f)) (tm_pair (tm_var 1) (tm_var 0)))) 
       
       ltac:(apply HD_Lam; eapply HD_App; 
             [ apply HD_Lam; apply (@hd_weakening_append Sign I ((Ty_Prod C A : h_ty) :: nil) ((A : h_ty) :: (C : h_ty) :: nil)); [ apply (double_ctx_wf I A C) | exact (h_deriv_of f) ]
             | apply HD_Pair; 
               [ exact (@HD_VarS Sign I ((C:h_ty)::nil) C A 0 (hyper_id_deriv I C) (ty_wf I A)) 
               | exact (@HD_Var0 Sign I ((C:h_ty)::nil) A (obj_ctx_wf I C) (ty_wf I A)) ] ]))

    (* 3. Eval *)
    (fun (A B : @obj_hyper Sign I) => @mk_hom_hyper Sign I (@syn_prod_obj Sign I (@syn_exp_obj Sign I A B) A) B 
       (tm_app (tm_fst (tm_var 0)) (tm_snd (tm_var 0))) 
       
       ltac:(eapply HD_App;
             [ eapply HD_Fst; exact (hyper_id_deriv I (@syn_prod_obj Sign I (@syn_exp_obj Sign I A B) A)) 
             | eapply HD_Snd; exact (hyper_id_deriv I (@syn_prod_obj Sign I (@syn_exp_obj Sign I A B) A)) ]))
           
    _ _ _ (* Category laws *)
  ).
  - intros A B C f. apply hyper_hom_equiv_pi.
  - intros A B C h. apply hyper_hom_equiv_pi.
  - unfold Proper, respectful. intros A B C f f' Hf. apply hyper_hom_equiv_pi.
Defined.

Instance Syntactic_BiClosed {Sign : Type} (I : b_ty) : BiCartesianClosedCategory (@Syntactic_Closed Sign I).
Proof.
  refine (mk_BiCartesianClosedCategory (@Syntactic_Fiber Sign I) (@Syntactic_Cartesian Sign I) (@Syntactic_Closed Sign I)
    
    (@syn_initial_obj Sign I)
    
    (fun (Phi : @obj_hyper Sign I) => @mk_hom_hyper Sign I (@syn_initial_obj Sign I) Phi (tm_absurd Phi (tm_var 0)) 
       ltac:(apply HD_Absurd; [exact (hyper_id_deriv I (@syn_initial_obj Sign I)) | exact (ty_wf I Phi)]))
       
    _ (* initial_map_unique law *)
    
    (@syn_coprod_obj Sign I)
   
    (fun (Phi Psi : @obj_hyper Sign I) => @mk_hom_hyper Sign I Phi (@syn_coprod_obj Sign I Phi Psi) (tm_inl Psi (tm_var 0)) 
       ltac:(apply HD_Inl; [exact (hyper_id_deriv I Phi) | exact (ty_wf I Psi)]))
       
    (fun (Phi Psi : @obj_hyper Sign I) => @mk_hom_hyper Sign I Psi (@syn_coprod_obj Sign I Phi Psi) (tm_inr Phi (tm_var 0)) 
       ltac:(apply HD_Inr; [exact (hyper_id_deriv I Psi) | exact (ty_wf I Phi)]))
       
    (fun (Phi Psi Chi : @obj_hyper Sign I) f g => @mk_hom_hyper Sign I (@syn_coprod_obj Sign I Phi Psi) Chi 
   
       (tm_case (tm_var 0) (h_tm_of f) (h_tm_of g)) 
       ltac:(eapply HD_Case; 
             [ exact (hyper_id_deriv I (@syn_coprod_obj Sign I Phi Psi)) 
             | apply (@hd_weakening_append Sign I ((Phi:h_ty) :: nil) ((Ty_Sum Phi Psi : h_ty) :: nil));
               [ apply (obj_ctx_wf I (@syn_coprod_obj Sign I Phi Psi)) | exact (h_deriv_of f) ]
             | apply (@hd_weakening_append Sign I ((Psi:h_ty) :: nil) ((Ty_Sum Phi Psi : h_ty) :: nil));
               [ apply (obj_ctx_wf I (@syn_coprod_obj Sign I Phi Psi)) | exact (h_deriv_of g) ] ]))
             
    _ _ _ _ (* Category laws *)
  ).
  - intros x f. apply hyper_hom_equiv_pi.
  - intros A B C f g. apply hyper_hom_equiv_pi.
  - intros A B C f g. apply hyper_hom_equiv_pi.
  - intros A B C h. apply hyper_hom_equiv_pi.
  - unfold Proper, respectful. intros A B C f f' Hf g g' Hg. apply hyper_hom_equiv_pi.
Defined.


(* ================================================================= *)
(* 5. THE SYNTACTIC SUBSTITUTION FUNCTOR (PULLBACK)                  *)
(* ================================================================= *)

Fixpoint h_tm_pullback {Sign : Type} (f : @b_tm Sign) (p : @h_tm Sign) : @h_tm Sign :=
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

(* ================================================================= *)
(* 5.5 STRUCTURAL EQUIVALENCE LEMMAS                                 *)
(* ================================================================= *)

Lemma form_equiv_pullback_comp : forall {Sign : Type} I J K (f g : @b_tm Sign) (df : @base_typing Sign J f K) (dg : @base_typing Sign I g J) (Phi : @obj_hyper Sign K),
  @form_equiv Sign I (form_pullback g (form_pullback f Phi)) (form_pullback (b_comp f g) Phi).
  Proof.
    intros. eapply FE_Pullback_Comp.
    - exact df.
    - exact dg.
    - exact (ty_wf K Phi).
  Qed.

Lemma form_equiv_pullback_ext_comm : forall {Sign : Type} I J A (g : @b_tm Sign) (dg : @base_typing Sign I g J) (Phi : @obj_hyper Sign J),
  @form_equiv Sign (b_Prod I A) 
             (form_pullback b_fst (form_pullback g Phi)) 
             (form_pullback (b_pullback_ext g) (form_pullback b_fst Phi)).
Proof.
  intros Sign I J A g dg Phi.
  eapply FE_Trans.
  - eapply FE_Pullback_Comp; [exact dg | apply (@BT_Fst Sign I A) | exact (ty_wf J Phi)].
  - eapply FE_Trans.
    + eapply FE_Pullback_Cong.
      * apply BE_Sym. eapply BE_BetaFst.
      * exact (ty_wf J Phi).
    + eapply FE_Sym. eapply FE_Pullback_Comp.
      * apply (@BT_Fst Sign J A).
      * eapply BT_Pair; [eapply BT_Comp; [exact dg | apply (@BT_Fst Sign I A)] | apply (@BT_Snd Sign I A)].
      * exact (ty_wf J Phi).
(* Itt jön a varázslat: lehívjuk a polcról a hiányzó levezetéseket! *)
Unshelve.
  all: try exact A.
  all: try (eapply BT_Comp; [exact dg | apply (@BT_Fst Sign I A)]).
  all: try apply (@BT_Snd Sign I A).
Defined.

Lemma ctx_equiv_pullback_ext_comm : forall {Sign : Type} I J A (g : @b_tm Sign) (dg : @base_typing Sign I g J) (G : @h_context Sign),
  @wf_ctx Sign J G ->
  @ctx_equiv Sign (b_Prod I A)
            (ctx_pullback b_fst (ctx_pullback g G)) 
            (ctx_pullback (b_pullback_ext g) (ctx_pullback b_fst G)).
Proof.
  intros Sign I J A g dg G Hwf.
  induction Hwf; simpl.
  - apply CEQ_nil.
  - apply CEQ_cons.
    + apply (form_equiv_pullback_ext_comm I J A g dg (mk_obj_hyper Sign J Phi w)).
    + exact IHHwf.
Qed.

Lemma form_pullback_equiv : forall {Sign : Type} I J (f : @b_tm Sign) (df : @base_typing Sign I f J) Phi Psi,
  @form_equiv Sign J Phi Psi -> @form_equiv Sign I (form_pullback f Phi) (form_pullback f Psi).
Proof.
  intros Sign I J f df Phi Psi f_eq.
  revert I f df.
  induction f_eq; intros; simpl; eauto.
  - eapply FE_Atom. eapply BE_CongComp; [first [exact b | apply BE_Refl] | first [exact b | apply BE_Refl]].
  - apply FE_Refl. eapply wf_pullback; eauto.
  - apply FE_Sym; eauto.
  - eapply FE_Trans; eauto.
  - apply FE_Prod; eauto.
  - apply FE_Sum; eauto.
  - apply FE_Arrow; eauto.
  - apply FE_All. apply IHf_eq. eapply BT_Pair; [eapply BT_Comp; [exact df | apply (@BT_Fst Sign I0 D)] | apply (@BT_Snd Sign I0 D)].
  - apply FE_Ex. apply IHf_eq. eapply BT_Pair; [eapply BT_Comp; [exact df | apply (@BT_Fst Sign I0 D)] | apply (@BT_Snd Sign I0 D)].
  - eapply FE_Trans.
    + eapply FE_Pullback_Comp; [apply (@BT_Id Sign I) | exact df | exact w].
    + eapply FE_Pullback_Cong; [apply BE_IdL | exact w].
  - eapply FE_Trans.
    + eapply FE_Pullback_Comp; [exact dg | exact df0 | eapply wf_pullback; [exact df | exact w]].
    + eapply FE_Trans.
      * eapply FE_Pullback_Comp; [exact df | eapply BT_Comp; [exact dg | exact df0] | exact w].
      * eapply FE_Trans.
        { eapply FE_Pullback_Cong; [apply BE_Assoc | exact w]. }
        { eapply FE_Sym. eapply FE_Pullback_Comp; [eapply BT_Comp; [exact df | exact dg] | exact df0 | exact w]. }
  - eapply FE_Trans.
    + eapply FE_Pullback_Comp; [exact df | exact df0 | exact w].
    + eapply FE_Trans.
      * eapply FE_Pullback_Cong.
        { eapply BE_CongComp; [first [exact b | apply BE_Refl] | first [exact b | apply BE_Refl]]. }
        { exact w. }
      * eapply FE_Sym. eapply FE_Pullback_Comp; [exact dg | exact df0 | exact w].
Unshelve.
  all: try exact df.
  all: try exact dg.
  all: try exact df0.
  all: try apply (@BT_Id Sign I).
Qed.

Lemma ctx_pullback_equiv_lemma : forall {Sign : Type} I J (f : @b_tm Sign) (df : @base_typing Sign I f J) G1 G2,
  @ctx_equiv Sign J G1 G2 -> @ctx_equiv Sign I (ctx_pullback f G1) (ctx_pullback f G2).
Proof.
  intros Sign I J f df G1 G2 c_eq.
  induction c_eq; simpl.
  - apply CEQ_nil.
  - apply CEQ_cons.
    + eapply form_pullback_equiv; eauto.
    + exact IHc_eq.
Qed.

Lemma ext_ex : forall {Sign : Type} {I A : b_ty} {Phi : @h_ty Sign},
  @WellFormed Sign I (Ty_Ex A Phi) -> @WellFormed Sign (b_Prod I A) Phi.
Proof.
  intros Sign I A Phi Hwf. inversion Hwf; subst; assumption.
Defined.

Lemma derivation_pullback : forall {Sign : Type} {I J : b_ty} (f : @b_tm Sign) (df : @base_typing Sign I f J) 
  {G : @h_context Sign} {p : @h_tm Sign} {Phi : @h_ty Sign},
  @h_derivation Sign J G p Phi -> 
  @h_derivation Sign I (ctx_pullback f G) (h_tm_pullback f p) (form_pullback f Phi).
Proof.
  intros Sign I J f df G p Phi d.
  revert I f df.
  induction d; intros I_src g dg; simpl.
  - apply HD_Var0; [eapply wf_ctx_pullback; [exact dg | exact w] | eapply wf_pullback; [exact dg | exact w0]].
  - apply HD_VarS; [apply IHd; exact dg | eapply wf_pullback; [exact dg | exact w]].
  - eapply HD_Conv. 
    + apply IHd; exact dg.
    + eapply form_pullback_equiv; [exact dg | exact f].
    + eapply wf_pullback; [exact dg | exact w].
  - eapply HD_Unit; eapply wf_ctx_pullback; [exact dg | exact w].
  - apply HD_Lam. apply IHd; exact dg.
  - eapply HD_App; [apply IHd1; exact dg | apply IHd2; exact dg].
  - apply HD_Pair; [apply IHd1; exact dg | apply IHd2; exact dg].
  - eapply HD_Fst; apply IHd; exact dg.
  - eapply HD_Snd; apply IHd; exact dg.
  - apply HD_Inl; [apply IHd; exact dg | eapply wf_pullback; [exact dg | exact w]].
  - apply HD_Inr; [apply IHd; exact dg | eapply wf_pullback; [exact dg | exact w]].
  - eapply HD_Case; [apply IHd1; exact dg | apply IHd2; exact dg | apply IHd3; exact dg].
  - apply HD_Absurd; [apply IHd; exact dg | eapply wf_pullback; [exact dg | exact w]].
  - apply HD_All_Intro.
    + eapply wf_ctx_pullback; [exact dg | exact w].
    + eapply HD_Ctx_Conv.
      * apply IHd. eapply BT_Pair; [eapply BT_Comp; [exact dg | apply (@BT_Fst Sign I_src A)] | apply (@BT_Snd Sign I_src A)].
      * apply ctx_equiv_sym. eapply ctx_equiv_pullback_ext_comm; [exact dg | exact w].
      * eapply wf_ctx_pullback. apply (@BT_Fst Sign I_src A). eapply wf_ctx_pullback; [exact dg | exact w].
  - (* 15. HD_All_Elim *)
    eapply HD_Conv.
    + eapply HD_All_Elim; [apply IHd; exact dg | eapply BT_Comp; [exact b | exact dg]].
    + eapply FE_Trans.
      * eapply FE_Pullback_Comp.
        { eapply BT_Pair; [eapply BT_Comp; [exact dg | apply (@BT_Fst Sign I_src A)] | apply (@BT_Snd Sign I_src A)]. }
        { eapply BT_Pair; [apply (@BT_Id Sign I_src) | eapply BT_Comp; [exact b | exact dg]]. }
        { pose proof (well_formed_target _ _ _ _ d) as Hwf; exact (ext_all Hwf). }
      * eapply FE_Trans.
        { eapply FE_Pullback_Cong.
          - eapply BE_Trans. { eapply BE_Sym. eapply BE_EtaPair; eauto 10 using base_typing. }
            eapply BE_Trans. 2: { eapply BE_EtaPair; eauto 10 using base_typing. }
            eapply BE_CongPair.
            + eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
              eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_Refl; eauto 10 using base_typing | eapply BE_BetaFst; eauto 10 using base_typing ]. }
              eapply BE_Trans. { eapply BE_Sym. eapply BE_Assoc; eauto 10 using base_typing. }
              eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_BetaFst; eauto 10 using base_typing | eapply BE_Refl; eauto 10 using base_typing ]. }
              eapply BE_Trans. { eapply BE_IdR; eauto 10 using base_typing. }
              eapply BE_Sym. 
              eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
              eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_Refl; eauto 10 using base_typing | eapply BE_BetaFst; eauto 10 using base_typing ]. }
              eapply BE_IdL; eauto 10 using base_typing.
            + eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
              eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_Refl; eauto 10 using base_typing | eapply BE_BetaSnd; eauto 10 using base_typing ]. }
              eapply BE_Trans. { eapply BE_BetaSnd; eauto 10 using base_typing. }
              eapply BE_Sym. 
              eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
              eapply BE_CongComp; [ eapply BE_Refl; eauto 10 using base_typing | eapply BE_BetaSnd; eauto 10 using base_typing ].
          - pose proof (well_formed_target _ _ _ _ d) as Hwf; exact (ext_all Hwf). }
        { eapply FE_Sym. eapply FE_Pullback_Comp.
          - eapply BT_Pair; [apply (@BT_Id Sign I) | exact b].
          - exact dg.
          - pose proof (well_formed_target _ _ _ _ d) as Hwf; exact (ext_all Hwf). }
    + eapply wf_pullback.
      * exact dg.
      * eapply wf_pullback.
        { eapply BT_Pair; [apply (@BT_Id Sign I) | exact b]. }
        { pose proof (well_formed_target _ _ _ _ d) as Hwf; exact (ext_all Hwf). }
- (* 16. HD_Ex_Intro *)
    eapply HD_Ex_Intro.
    + eapply wf_pullback; [eapply BT_Pair; [eapply BT_Comp; [exact dg | apply (@BT_Fst Sign I_src A)] | apply (@BT_Snd Sign I_src A)] | exact w].
    + eapply BT_Comp; [exact b | exact dg].
    + eapply HD_Conv.
      * apply IHd; exact dg.
      * eapply FE_Trans.
        { eapply FE_Pullback_Comp.
          - eapply BT_Pair; [apply (@BT_Id Sign I) | exact b].
          - exact dg.
          - exact w. }
        { eapply FE_Trans.
          - eapply FE_Pullback_Cong.
            + eapply BE_Sym.
              eapply BE_Trans. { eapply BE_Sym. eapply BE_EtaPair; eauto 10 using base_typing. }
              eapply BE_Trans. 2: { eapply BE_EtaPair; eauto 10 using base_typing. }
              eapply BE_CongPair.
              * eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
                eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_Refl; eauto 10 using base_typing | eapply BE_BetaFst; eauto 10 using base_typing ]. }
                eapply BE_Trans. { eapply BE_Sym. eapply BE_Assoc; eauto 10 using base_typing. }
                eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_BetaFst; eauto 10 using base_typing | eapply BE_Refl; eauto 10 using base_typing ]. }
                eapply BE_Trans. { eapply BE_IdR; eauto 10 using base_typing. }
                eapply BE_Sym.
                eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
                eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_Refl; eauto 10 using base_typing | eapply BE_BetaFst; eauto 10 using base_typing ]. }
                eapply BE_IdL; eauto 10 using base_typing.
              * eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
                eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_Refl; eauto 10 using base_typing | eapply BE_BetaSnd; eauto 10 using base_typing ]. }
                eapply BE_Trans. { eapply BE_BetaSnd; eauto 10 using base_typing. }
                eapply BE_Sym.
                eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
                eapply BE_CongComp; [ eapply BE_Refl; eauto 10 using base_typing | eapply BE_BetaSnd; eauto 10 using base_typing ].
            + exact w.
          - eapply FE_Sym. eapply FE_Pullback_Comp.
            + eapply BT_Pair; [eapply BT_Comp; [exact dg | apply (@BT_Fst Sign I_src A)] | apply (@BT_Snd Sign I_src A)].
            + eapply BT_Pair; [apply (@BT_Id Sign I_src) | eapply BT_Comp; [exact b | exact dg]].
            + exact w. }
      * eapply wf_pullback.
        { eapply BT_Pair; [apply (@BT_Id Sign I_src) | eapply BT_Comp; [exact b | exact dg]]. }
        { eapply wf_pullback; [eapply BT_Pair; [eapply BT_Comp; [exact dg | apply (@BT_Fst Sign I_src A)] | apply (@BT_Snd Sign I_src A)] | exact w]. }
  - (* 17. HD_Ctx_Conv (Nálad ez került a 17. helyre!) *)
    eapply HD_Ctx_Conv.
    + apply IHd; exact dg.
    + eapply ctx_pullback_equiv_lemma; [exact dg | exact c].
    + eapply wf_ctx_pullback; [exact dg | exact w].

  - (* 18. HD_Ex_Elim (És ez csúszott a 18. helyre) *)
   eapply HD_Ex_Elim.
    + eapply wf_pullback; [exact dg | exact w].
    + apply IHd1; exact dg.
    + eapply HD_Ctx_Conv.
      * eapply HD_Conv.
        { apply IHd2. eapply BT_Pair; [eapply BT_Comp; [exact dg | apply (@BT_Fst Sign I_src A)] | apply (@BT_Snd Sign I_src A)]. }
        { apply FE_Sym. exact (form_equiv_pullback_ext_comm I_src I A g dg (mk_obj_hyper Sign I Chi w)). }
        { eapply wf_pullback. apply (@BT_Fst Sign I_src A). eapply wf_pullback; [exact dg | exact w]. }
      * apply CEQ_cons.
        { apply FE_Refl. eapply wf_pullback.
          - eapply BT_Pair; [eapply BT_Comp; [exact dg | apply (@BT_Fst Sign I_src A)] | apply (@BT_Snd Sign I_src A)].
          - pose proof (well_formed_target _ _ _ _ d1) as Hwf; exact (ext_ex Hwf). }
        { apply ctx_equiv_sym. eapply ctx_equiv_pullback_ext_comm; [exact dg | pose proof (well_formed_ctx _ _ _ _ d1) as Hctx; exact Hctx]. }
      * apply WFC_cons.
        { eapply wf_pullback. 
          - eapply BT_Pair; [eapply BT_Comp; [exact dg | apply (@BT_Fst Sign I_src A)] | apply (@BT_Snd Sign I_src A)].
          - pose proof (well_formed_target _ _ _ _ d1) as Hwf; exact (ext_ex Hwf). }
        { eapply wf_ctx_pullback. apply (@BT_Fst Sign I_src A). eapply wf_ctx_pullback; [exact dg | pose proof (well_formed_ctx _ _ _ _ d1) as Hctx; exact Hctx]. }
  Unshelve.
  all: try exact dg.
  all: try exact b.
  all: try apply (@BT_Id Sign I_src).
  all: try apply (@BT_Id Sign I).
  all: try (eapply BT_Comp; [exact b | exact dg]).
  all: try (eapply BT_Pair; [apply (@BT_Id Sign I_src) | eapply BT_Comp; [exact b | exact dg]]).
  all: try (eapply BT_Pair; [apply (@BT_Id Sign I) | exact b]).
Defined.


(* ================================================================= *)
(* 6.8 THE CATEGORICAL ISOMORPHISM BUILDERS                          *)
(* ================================================================= *)

(** HELPER 1: For Strict Equalities (Identities) *)
Lemma syn_iso_from_eq {Sign : Type} (I : b_ty) (Phi Psi : @obj_hyper Sign I) :
  (Phi : h_ty) = (Psi : h_ty) -> (Phi : @obj (Syntactic_Fiber I)) ≅O (Psi : @obj (Syntactic_Fiber I)).
Proof.
  intros Heq.
  
  (* 'unshelve' forces Coq to ask for the morphisms BEFORE the proofs! *)
  unshelve econstructor.
  - (* 1. iso_to *)
    refine (@mk_hom_hyper Sign I Phi Psi (tm_var 0) _).
    rewrite <- Heq. exact (@hyper_id_deriv Sign I Phi).
    
  - (* 2. iso_from *)
    refine (@mk_hom_hyper Sign I Psi Phi (tm_var 0) _).
    rewrite Heq. exact (@hyper_id_deriv Sign I Psi).
    
  - (* 3. Iso Law 1 *) apply hyper_hom_equiv_pi.
  - (* 4. Iso Law 2 *) apply hyper_hom_equiv_pi.
Defined.


(** HELPER 2: For Logical Equivalences (The Bypass Killer!) *)
Lemma syn_iso_from_equiv {Sign : Type} (I : b_ty) (Phi Psi : @obj_hyper Sign I) :
  @form_equiv Sign I Phi Psi -> (Phi : @obj (Syntactic_Fiber I)) ≅O (Psi : @obj (Syntactic_Fiber I)).
Proof.
  intros Heq.
  
  (* 'unshelve' forces Coq to ask for the morphisms BEFORE the proofs! *)
  unshelve econstructor.
  - (* 1. iso_to *)
    refine (@mk_hom_hyper Sign I Phi Psi (tm_var 0) _).
    eapply HD_Conv.
    + exact (@hyper_id_deriv Sign I Phi).
    + exact Heq.
    + exact (ty_wf _ Psi).
    
  - (* 2. iso_from *)
    refine (@mk_hom_hyper Sign I Psi Phi (tm_var 0) _).
    eapply HD_Conv.
    + exact (@hyper_id_deriv Sign I Psi).
    + apply FE_Sym. exact Heq.
    + exact (ty_wf _ Phi).
    
  - (* 3. Iso Law 1 *) apply hyper_hom_equiv_pi.
  - (* 4. Iso Law 2 *) apply hyper_hom_equiv_pi.
Defined.
(* ================================================================= *)
(* 5. PULLBACK FUNCTOR OF THE SYNTACTIC FIBER                        *)
(* ================================================================= *)



Definition syn_pullback_obj {Sign : Type} (I J : b_ty) (f : @b_tm Sign) (df : @base_typing Sign I f J) (Phi : @obj_hyper Sign J) : @obj_hyper Sign I :=
  @mk_obj_hyper Sign I (form_pullback f Phi) (wf_pullback I J f Phi df (ty_wf J Phi)).


Definition syn_pullback_mor {Sign : Type} (I J : b_ty) (f : @b_tm Sign) (df : @base_typing Sign I f J)
  (Phi Psi : @obj_hyper Sign J) (m : @hom_hyper Sign J Phi Psi) :
  @hom_hyper Sign I (@syn_pullback_obj Sign I J f df Phi) (@syn_pullback_obj Sign I J f df Psi).
Proof.
  refine (@mk_hom_hyper Sign I (@syn_pullback_obj Sign I J f df Phi) (@syn_pullback_obj Sign I J f df Psi) (h_tm_pullback f (h_tm_of m)) _).
  (* Itt hívjuk meg a nehezen kiharcolt lemmánkat! *)
  exact (@derivation_pullback Sign I J f df ((Phi:h_ty) :: nil) (h_tm_of m) Psi (h_deriv_of m)).
Defined.

Instance Syntactic_Pullback {Sign : Type} (I J : b_ty) (f : @b_tm Sign) (df : @base_typing Sign I f J) :
  Functor (@Syntactic_Fiber Sign J) (@Syntactic_Fiber Sign I).
Proof.
  refine (@mk_Functor (@Syntactic_Fiber Sign J) (@Syntactic_Fiber Sign I) 
    (@syn_pullback_obj Sign I J f df) 
    (@syn_pullback_mor Sign I J f df) _ _ _).
  - (* Proper: A funktor tiszteletben tartja az egyenlőséget *)
    unfold Proper, respectful. intros. apply hyper_hom_equiv_pi.
  - (* F_id: Visszahúzott identitás = identitás *)
    intros. apply hyper_hom_equiv_pi.
  - (* F_comp: Visszahúzott kompozíció = kompozíciók visszahúzva *)
    intros. apply hyper_hom_equiv_pi.
Defined.

(* ================================================================= *)
(* 6. THE SYNTACTIC QUANTIFIERS (ADJOINTS)                           *)
(* ================================================================= *)

(** 6.1 THE RIGHT ADJOINT (FORALL) *)

Definition syn_all_obj {Sign : Type} (I A : b_ty) (Phi : @obj_hyper Sign (b_Prod I A)) : @obj_hyper Sign I := 
  @mk_obj_hyper Sign I (Ty_All A Phi) (@WF_All Sign I A Phi (ty_wf (b_Prod I A) Phi)).

Definition syn_all_counit {Sign : Type} (I A : b_ty) (dfst : @base_typing Sign (b_Prod I A) b_fst I) (Psi : @obj_hyper Sign (b_Prod I A)) : 
  @hom_hyper Sign (b_Prod I A) (@syn_pullback_obj Sign (b_Prod I A) I b_fst dfst (@syn_all_obj Sign I A Psi)) Psi.
Proof.
  refine (@mk_hom_hyper Sign (b_Prod I A) (@syn_pullback_obj Sign (b_Prod I A) I b_fst dfst (@syn_all_obj Sign I A Psi)) Psi (tm_all_elim (tm_var 0) b_snd) _).
  assert (H_der : @h_derivation Sign (b_Prod I A) ((form_pullback b_fst (Ty_All A Psi)) :: nil) (tm_all_elim (tm_var 0) b_snd) 
                               (form_pullback (b_pair b_id b_snd) (form_pullback (b_pullback_ext b_fst) Psi))).
  { eapply HD_All_Elim.
    - exact (@HD_Var0 Sign (b_Prod I A) nil (form_pullback b_fst (Ty_All A Psi)) (@WFC_nil Sign _) (@wf_pullback Sign _ _ _ _ dfst (@WF_All Sign I A Psi (ty_wf _ Psi)))).
    - exact (@BT_Snd Sign I A). }
  eapply HD_Conv. 
  - exact H_der. 
  - eapply FE_Trans.
    { eapply FE_Pullback_Comp. 
      - eapply typing_pullback_ext; exact dfst.
      - eapply BT_Pair; [apply (@BT_Id Sign (b_Prod I A)) | apply (@BT_Snd Sign I A)].
      - exact (ty_wf _ Psi). }
    eapply FE_Trans.
    { eapply FE_Pullback_Cong.
      - eapply BE_Trans. { eapply BE_Sym. eapply BE_EtaPair; eauto 10 using base_typing. }
        eapply BE_Trans. 2: { eapply BE_EtaPair; eauto 10 using base_typing. }
        eapply BE_CongPair.
        + eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
          eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_Refl; eauto 10 using base_typing | eapply BE_BetaFst; eauto 10 using base_typing ]. }
          eapply BE_Trans. { eapply BE_Sym. eapply BE_Assoc; eauto 10 using base_typing. }
          eapply BE_CongComp; [ eapply BE_BetaFst; eauto 10 using base_typing | eapply BE_Refl; eauto 10 using base_typing ].
        + eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
          eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_Refl; eauto 10 using base_typing | eapply BE_BetaSnd; eauto 10 using base_typing ]. }
          eapply BE_Trans. { eapply BE_BetaSnd; eauto 10 using base_typing. }
          eapply BE_Sym. eapply BE_IdR; eauto 10 using base_typing.
      - exact (ty_wf _ Psi). }
    eapply FE_Pullback_Id; exact (ty_wf _ Psi).
  - exact (ty_wf _ Psi).
Unshelve.
  all: try exact dfst.
  all: try apply (@BT_Id Sign (b_Prod I A)).
  all: try apply (@BT_Snd Sign I A).
  all: try apply (@BT_Fst Sign I A).
  all: try apply (@BT_Fst Sign (b_Prod I A) A).
  all: try apply (@BT_Snd Sign (b_Prod I A) A).
  all: try (eapply BT_Comp; [exact dfst | apply (@BT_Fst Sign (b_Prod I A) A)]).
  all: try (eapply BT_Comp; [exact dfst | apply (@BT_Fst Sign I A)]).
  all: try (eapply BT_Pair; [apply (@BT_Id Sign (b_Prod I A)) | apply (@BT_Snd Sign I A)]).
Defined.

Definition syn_all_mor {Sign : Type} (I A : b_ty) (dfst : @base_typing Sign (b_Prod I A) b_fst I) (Y : @obj_hyper Sign I) (X : @obj_hyper Sign (b_Prod I A)) 
  (f : @hom_hyper Sign (b_Prod I A) (@syn_pullback_obj Sign (b_Prod I A) I b_fst dfst Y) X) : 
  @hom_hyper Sign I Y (@syn_all_obj Sign I A X).
Proof.
  refine (@mk_hom_hyper Sign I Y (@syn_all_obj Sign I A X) (tm_all_intro (h_tm_of f)) _).
  apply HD_All_Intro.
  - apply obj_ctx_wf.
  - exact (h_deriv_of f).
Defined.


Instance Syntactic_All_Adjunction {Sign : Type} (I A : b_ty) (dfst : @base_typing Sign (b_Prod I A) b_fst I) :
  IsLeftAdjoint (@Syntactic_Pullback Sign (b_Prod I A) I b_fst dfst).
Proof.
  refine (@mk_IsLeftAdjoint (@Syntactic_Fiber Sign (b_Prod I A)) (@Syntactic_Fiber Sign I) (@Syntactic_Pullback Sign (b_Prod I A) I b_fst dfst) 
    (@syn_all_obj Sign I A) (@syn_all_counit Sign I A dfst) (@syn_all_mor Sign I A dfst) _ _ _).
  - unfold Proper, respectful. intros Y X f g Hfg. apply hyper_hom_equiv_pi.
  - intros. apply hyper_hom_equiv_pi.
  - intros. apply hyper_hom_equiv_pi.
Defined.

(** 6.2 THE LEFT ADJOINT (EXISTS) *)

Definition syn_ex_obj {Sign : Type} (I A : b_ty) (Phi : @obj_hyper Sign (b_Prod I A)) : @obj_hyper Sign I := 
  @mk_obj_hyper Sign I (Ty_Ex A Phi) (@WF_Ex Sign I A Phi (ty_wf (b_Prod I A) Phi)).

Definition syn_ex_unit {Sign : Type} (I A : b_ty) (dfst : @base_typing Sign (b_Prod I A) b_fst I) (Y : @obj_hyper Sign (b_Prod I A)) : 
  @hom_hyper Sign (b_Prod I A) Y (@syn_pullback_obj Sign (b_Prod I A) I b_fst dfst (@syn_ex_obj Sign I A Y)).
Proof.
  refine (@mk_hom_hyper Sign (b_Prod I A) Y (@syn_pullback_obj Sign (b_Prod I A) I b_fst dfst (@syn_ex_obj Sign I A Y)) (tm_ex_intro b_snd (tm_var 0)) _).
  assert (H_inner : @h_derivation Sign (b_Prod I A) ((Y:h_ty) :: nil) (tm_var 0) (form_pullback (b_pair b_id b_snd) (form_pullback (b_pullback_ext b_fst) Y))).
  { eapply HD_Conv. 
    - exact (@HD_Var0 Sign (b_Prod I A) nil Y (@WFC_nil Sign _) (ty_wf _ Y)). 
    - eapply FE_Sym.
      eapply FE_Trans.
      { eapply FE_Pullback_Comp. 
        - eapply typing_pullback_ext; exact dfst.
        - eapply BT_Pair; [apply (@BT_Id Sign (b_Prod I A)) | apply (@BT_Snd Sign I A)].
        - exact (ty_wf _ Y). }
      eapply FE_Trans.
      { eapply FE_Pullback_Cong.
        - eapply BE_Trans. { eapply BE_Sym. eapply BE_EtaPair; eauto 10 using base_typing. }
          eapply BE_Trans. 2: { eapply BE_EtaPair; eauto 10 using base_typing. }
          eapply BE_CongPair.
          + eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
            eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_Refl; eauto 10 using base_typing | eapply BE_BetaFst; eauto 10 using base_typing ]. }
            eapply BE_Trans. { eapply BE_Sym. eapply BE_Assoc; eauto 10 using base_typing. }
            eapply BE_CongComp; [ eapply BE_BetaFst; eauto 10 using base_typing | eapply BE_Refl; eauto 10 using base_typing ].
          + eapply BE_Trans. { eapply BE_Assoc; eauto 10 using base_typing. }
            eapply BE_Trans. { eapply BE_CongComp; [ eapply BE_Refl; eauto 10 using base_typing | eapply BE_BetaSnd; eauto 10 using base_typing ]. }
            eapply BE_Trans. { eapply BE_BetaSnd; eauto 10 using base_typing. }
            eapply BE_Sym. eapply BE_IdR; eauto 10 using base_typing.
        - exact (ty_wf _ Y). }
      eapply FE_Pullback_Id; exact (ty_wf _ Y).
    - eapply wf_pullback.
      + eapply BT_Pair; [apply (@BT_Id Sign (b_Prod I A)) | apply (@BT_Snd Sign I A)].
      + eapply wf_pullback.
        * eapply BT_Pair; [eapply BT_Comp; [exact dfst | apply (@BT_Fst Sign (b_Prod I A) A)] | apply (@BT_Snd Sign (b_Prod I A) A)].
        * exact (ty_wf _ Y). }
  
  assert (H_outer : @h_derivation Sign (b_Prod I A) ((Y:h_ty) :: nil) (tm_ex_intro b_snd (tm_var 0)) (Ty_Ex A (form_pullback (b_pullback_ext b_fst) Y))).
  { eapply HD_Ex_Intro.
    - eapply wf_pullback; [eapply BT_Pair; [eapply BT_Comp; [exact dfst | apply (@BT_Fst Sign (b_Prod I A) A)] | apply (@BT_Snd Sign (b_Prod I A) A)] | exact (ty_wf _ Y)].
    - exact (@BT_Snd Sign I A).
    - exact H_inner. }
    
  eapply HD_Conv.
  - exact H_outer. 
  - apply FE_Refl. eapply wf_pullback; [exact dfst | apply WF_Ex; exact (ty_wf _ Y)].
  - eapply wf_pullback; [exact dfst | apply WF_Ex; exact (ty_wf _ Y)].
Unshelve.
  all: try exact dfst.
  all: try apply (@BT_Id Sign (b_Prod I A)).
  all: try apply (@BT_Snd Sign I A).
  all: try apply (@BT_Fst Sign I A).
  all: try apply (@BT_Fst Sign (b_Prod I A) A).
  all: try apply (@BT_Snd Sign (b_Prod I A) A).
  all: try (eapply BT_Comp; [exact dfst | apply (@BT_Fst Sign (b_Prod I A) A)]).
  all: try (eapply BT_Comp; [exact dfst | apply (@BT_Fst Sign I A)]).
  all: try (eapply BT_Pair; [apply (@BT_Id Sign (b_Prod I A)) | apply (@BT_Snd Sign I A)]).
Defined.

Definition syn_ex_mor {Sign : Type} (I A : b_ty) (dfst : @base_typing Sign (b_Prod I A) b_fst I) (Y : @obj_hyper Sign (b_Prod I A)) (X : @obj_hyper Sign I) 
  (f : @hom_hyper Sign (b_Prod I A) Y (@syn_pullback_obj Sign (b_Prod I A) I b_fst dfst X)) : 
  @hom_hyper Sign I (@syn_ex_obj Sign I A Y) X.
Proof.
  refine (@mk_hom_hyper Sign I (@syn_ex_obj Sign I A Y) X (tm_ex_elim (tm_var 0) (h_tm_of f)) _).
  eapply HD_Ex_Elim.
  - exact (ty_wf _ X). 
  - exact (@HD_Var0 Sign I nil (Ty_Ex A Y) (@WFC_nil Sign I) (@WF_Ex Sign I A Y (ty_wf _ Y))).
  - change ((Y:h_ty) :: ctx_pullback b_fst ((syn_ex_obj I A Y : h_ty) :: nil)) 
      with (((Y:h_ty) :: nil) ++ ctx_pullback b_fst ((syn_ex_obj I A Y : h_ty) :: nil)).
    eapply hd_weakening_append.
    + (* 1. Cél: A kontextus jólformáltsága (wf_ctx) *)
      apply WFC_cons.
      * eapply wf_pullback; [exact dfst | exact (ty_wf I (syn_ex_obj I A Y))].
      * apply WFC_nil.
    + (* 2. Cél: A levezetés átemelése (h_derivation) *)
      exact (h_deriv_of f).
Defined.

Instance Syntactic_Ex_Adjunction {Sign : Type} (I A : b_ty) (dfst : @base_typing Sign (b_Prod I A) b_fst I) :
  IsRightAdjoint (@Syntactic_Pullback Sign (b_Prod I A) I b_fst dfst).
Proof.
  refine (@mk_IsRightAdjoint (@Syntactic_Fiber Sign I) (@Syntactic_Fiber Sign (b_Prod I A)) (@Syntactic_Pullback Sign (b_Prod I A) I b_fst dfst) 
    (@syn_ex_obj Sign I A) (@syn_ex_unit Sign I A dfst) (@syn_ex_mor Sign I A dfst) _ _ _).
  - unfold Proper, respectful. intros Y X f g Hfg. apply hyper_hom_equiv_pi.
  - intros. apply hyper_hom_equiv_pi.
  - intros. apply hyper_hom_equiv_pi.
Defined.

(* ================================================================= *)
(* 6.5 THE SYNTACTIC BASE CATEGORY (STLC)                            *)
(* ================================================================= *)

Record hom_base {Sign : Type} (I J : b_ty) : Type := mk_hom_base {
  b_tm_of : b_tm;
  b_deriv_of : @base_typing Sign I b_tm_of J
}.

Definition base_hom_equiv {Sign : Type} (I J : b_ty) (f g : hom_base I J) : Prop :=
  base_equiv (@b_deriv_of Sign I J f) (@b_deriv_of Sign I J g).

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
  - (* Equivalence Relation *)
    intros A B. split.
    + intros [tf df]. eapply BE_Refl.
    + intros [tf df] [tg dg] H. apply BE_Sym. exact H.
    + intros [tf df] [tg dg] [th dh] H1 H2. eapply BE_Trans; eassumption.
  - (* Associativity *)
    intros A B C D [tf df] [tg dg] [th dh]. 
    simpl. eapply BE_Assoc; eassumption.
  - (* Identity Right *)
    intros A B [tf df]. 
    simpl. eapply BE_IdR; eassumption.
  - (* Identity Left *)
    intros A B [tf df]. 
    simpl. eapply BE_IdL; eassumption.
  - (* Properness / Congruence *)
    unfold Proper, respectful.
    intros A B C [tf df] [tf' df'] [tg dg] [tg' dg'] Hf Hg.
    unfold base_hom_equiv in *.
    simpl in *.
    eapply BE_CongComp; eassumption.
Defined.

(* ================================================================= *)
(* 6.6 THE SYNTACTIC BASE CARTESIAN CATEGORY                         *)
(* ================================================================= *)

Instance Base_CartesianCategory {Sign : Type} : CartesianCategory (@Base_SetoidCategory Sign).
Proof.
  refine (mk_CartesianCategory (@Base_SetoidCategory Sign)
    b_Unit
    (fun I => mk_hom_base Sign I b_Unit b_unit BT_Unit)
    _ (* terminal_map_unique law *)
    b_Prod
    (fun I J K f g => mk_hom_base Sign I (b_Prod J K) (b_pair (b_tm_of I J f) (b_tm_of I K g)) 
                        (BT_Pair (b_deriv_of I J f) (b_deriv_of I K g)))
    (fun I J => mk_hom_base Sign (b_Prod I J) I b_fst BT_Fst)
    (fun I J => mk_hom_base Sign (b_Prod I J) J b_snd BT_Snd)
    _ _ _ _ 
  ).
  - intros x [tf df]. simpl. eapply BE_EtaUnit.
  - intros A B C [tf df] [tg dg]. simpl. eapply BE_BetaFst; eassumption.
  - intros A B C [tf df] [tg dg]. simpl. eapply BE_BetaSnd; eassumption.
  - intros A B C [th dh]. simpl. eapply BE_EtaPair; eassumption.
  - unfold Proper, respectful. 
    intros A B C [tf df] [tf' df'] Hf [tg dg] [tg' dg'] Hg.
    simpl. eapply BE_CongPair; eassumption.
Defined.

(* ================================================================= *)
(* 6.7 THE SYNTACTIC TWO-SORT CATEGORY                               *)
(* ================================================================= *)

Instance Base_TwoSortCategory {Sign : Type} : TwoSortCategory (@Base_SetoidCategory Sign).
Proof.
  econstructor.
  assert (H : b_S <> b_Unit) by (intro Heq; discriminate).
  exact H.
Defined.

(* ================================================================= *)
(* 7. THE SYNTACTIC GOOD FIBRATION & HYPERMODEL                      *)
(* ================================================================= *)

(* Híd a bázis kategória és a szintaxis között *)
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
      Syntactic_Pullback (syn_obj I) (syn_obj J) 
                         (@b_tm_of Sign (syn_obj I) (syn_obj J) (syn_hom f)) 
                         (@b_deriv_of Sign (syn_obj I) (syn_obj J) (syn_hom f)) ;
    pullback_has_left_adjoint  := fun I A => 
      Syntactic_Ex_Adjunction (syn_obj I) (syn_obj A) (@BT_Fst Sign (syn_obj I) (syn_obj A)) ;
    pullback_has_right_adjoint := fun I A => 
      Syntactic_All_Adjunction (syn_obj I) (syn_obj A) (@BT_Fst Sign (syn_obj I) (syn_obj A))
  |}.
  - intros I A. apply syn_iso_from_equiv. apply FE_Pullback_Id. exact (ty_wf _ A).
  - intros I J K g f A. apply syn_iso_from_equiv. eapply FE_Sym. eapply FE_Pullback_Comp.
    + exact (@b_deriv_of Sign _ _ (syn_hom g)). 
    + exact (@b_deriv_of Sign _ _ (syn_hom f)).
    + exact (ty_wf _ A).
  - intros I J f. apply syn_iso_from_eq. reflexivity.
  - intros I J f A B. apply syn_iso_from_eq. reflexivity.
  - intros I J f. apply syn_iso_from_eq. reflexivity.
  - intros I J f A B. apply syn_iso_from_eq. reflexivity.
  - intros I J f A B. apply syn_iso_from_eq. reflexivity.
  - intros I J K f A. apply syn_iso_from_equiv. apply FE_Refl. apply WF_Ex. eapply wf_pullback.
    + eapply BT_Pair; [eapply BT_Comp; [exact (@b_deriv_of Sign _ _ (syn_hom f)) | apply (@BT_Fst Sign (syn_obj K) (syn_obj J))] | apply (@BT_Snd Sign (syn_obj K) (syn_obj J))].
    + exact (ty_wf _ A).
  - intros I J K f A. apply syn_iso_from_equiv. apply FE_Refl. apply WF_All. eapply wf_pullback.
    + eapply BT_Pair; [eapply BT_Comp; [exact (@b_deriv_of Sign _ _ (syn_hom f)) | apply (@BT_Fst Sign (syn_obj K) (syn_obj J))] | apply (@BT_Snd Sign (syn_obj K) (syn_obj J))].
    + exact (ty_wf _ A).
  - intros I J f g Hfg A. apply syn_iso_from_equiv. eapply FE_Pullback_Cong.
    + exact Hfg.
    + exact (ty_wf _ A).
Defined.


(* ================================================================= *)
(* 7.5 THE SYNTACTIC STRICT GOOD FIBRATION                           *)
(* ================================================================= *)

Instance Syntactic_StrictGoodFibration {Sign : Type} : 
  StrictGoodFibration (@Base_SetoidCategory Sign) (@Syntactic_GoodFibration Sign).
Proof.
  econstructor.
  intros X Y M1 M2 Hbase.
  assert (Hrev : h_base M2 ≅ h_base M1) by (symmetry; exact Hbase).
  exists Hrev.
  apply hyper_hom_equiv_pi.
Defined.

(* ================================================================= *)
(* 7.6 THE SYNTACTIC EPSILON MODEL (CONSTANTS)                       *)
(* ================================================================= *)

(* ================================================================= *)
(* ÚJRA DEFINIÁLT LEMMA A SIMPLE_EXT KATEGÓRIÁKHOZ                   *)
(* ================================================================= *)

Lemma interp_ty_id : forall {Sign : Type} (I : b_ty), 
  @interp_ty (@Base_SetoidCategory Sign) (@Base_CartesianCategory Sign) (@Base_TwoSortCategory Sign) I = I.
Proof.
  intros S I. induction I; simpl; auto.
  - rewrite IHI1, IHI2; reflexivity.
Defined.

Instance Syntactic_SignatureModel {Sign : Type} : 
  @BaseSignatureModel Sign (@Base_SetoidCategory Sign) (@Base_CartesianCategory Sign) (@Base_TwoSortCategory Sign).
Proof.
  econstructor.
  intros I A s.
  
  (* 1. Átváltjuk az absztrakt objektumokat (obj) konkrét típusokra (b_ty) a 'syn_obj' segítségével! *)
  change (@hom_base Sign 
           (syn_obj (@interp_ty (@Base_SetoidCategory Sign) (@Base_CartesianCategory Sign) (@Base_TwoSortCategory Sign) I)) 
           (syn_obj (@interp_ty (@Base_SetoidCategory Sign) (@Base_CartesianCategory Sign) (@Base_TwoSortCategory Sign) A))).
  
  (* 2. Létrehozzuk az egyenlőségeket szigorúan a 'b_ty' típusokon. *)
  assert (EqI : syn_obj (@interp_ty (@Base_SetoidCategory Sign) (@Base_CartesianCategory Sign) (@Base_TwoSortCategory Sign) I) = I).
  { unfold syn_obj. apply (@interp_ty_id Sign). }
  assert (EqA : syn_obj (@interp_ty (@Base_SetoidCategory Sign) (@Base_CartesianCategory Sign) (@Base_TwoSortCategory Sign) A) = A).
  { unfold syn_obj. apply (@interp_ty_id Sign). }
  
  (* 3. Végrehajtjuk a helyettesítést (mindkét oldal b_ty, így a Coq rewrite azonnal elfogadja): *)
  rewrite EqI.
  rewrite EqA.
  
  (* 4. A cél most már hajszálpontosan: hom_base Sign I A 
     Beadjuk az új b_const terminust és az explicit @BT_Const levezetést. *)
  exact (mk_hom_base Sign I A (b_const A s) (@BT_Const Sign I A s)).
Defined.
(* ================================================================= *)
(* THE SYNTACTIC HYPERMODEL & COMPLETENESS                           *)
(* ================================================================= *)

(* Segédlemma: A terminus interpretációja visszadja önmagát a szintaktikus bázisban. *)
Lemma interp_tm_erasure : forall {Sign : Type} {I J : b_ty} {f : b_tm} (df : base_typing I f J),
  @b_tm_of Sign 
    (syn_obj (@interp_ty (@Base_SetoidCategory Sign) (@Base_CartesianCategory Sign) (@Base_TwoSortCategory Sign) I)) 
    (syn_obj (@interp_ty (@Base_SetoidCategory Sign) (@Base_CartesianCategory Sign) (@Base_TwoSortCategory Sign) J)) 
    (syn_hom (@interp_tm Sign (@Base_SetoidCategory Sign) (@Base_CartesianCategory Sign) (@Base_TwoSortCategory Sign) (@Syntactic_SignatureModel Sign) I J f df)) = f.
Proof.
  intros S I J f df.
  induction df; simpl; try reflexivity; try (f_equal; eauto).
  
  (* ÚJ RÉSZ: A BT_Const eset kezelése. 
     Itt lebontjuk az egyenlőség bizonyításokat, amitől az eq_rect-ek eltűnnek. *)
  - destruct (interp_ty_id A).
    destruct (interp_ty_id I).
    reflexivity.
Defined.

Instance Base_SyntacticCoherentModel {Sign : Type} : 
  @CoherentBaseModel Sign (@Base_SetoidCategory Sign) 
    (@Base_CartesianCategory Sign) (@Base_TwoSortCategory Sign) 
    (@Syntactic_SignatureModel Sign).
Proof.
  constructor.
  intros A B f d1 d2.
  cbn.
  (* Megadjuk a d1 és d2 fákat is, így semmi nem marad a polcon! *)
  eapply base_equiv_cast with (A' := A) (B' := B) (f' := f) (g' := f) (df' := d1) (dg' := d2).
  - symmetry. apply interp_ty_id.
  - symmetry. apply interp_ty_id.
  - symmetry. apply interp_tm_erasure. (* Ha a te fájlodban az interp_tm_term a neve, használd azt! *)
  - symmetry. apply interp_tm_erasure.
  - apply BE_Refl.
Defined.

(* A VÉGSŐ HIPER-MODELL PÉLDÁNYOSÍTÁSA *)
Instance Syntactic_HyperModel {Sign : Type} : 
  Simple_Ext_Soundness.HyperModel (@Syntactic_SignatureModel Sign) (@Base_SyntacticCoherentModel Sign).
Proof.
  unshelve econstructor.
  
  - (* 1. Cél: i_atom definíciója *)
    intros p t I A dt.
    exists (Ty_Atom p t).
    rewrite (@interp_ty_id Sign I).
    
    (* A sima constructor helyett econstructor kell, hogy a Coq 
       létrehozzon egy lyukat a hiányzó 'A' típusnak! *)
    econstructor. 
    
    (* A dt pontosan a base_typing I t A levezetést tartalmazza, 
       így azonnal be is tömi az imént létrehozott lyukat: *)
    exact dt.

  - (* 2. Cél: i_atom_pb *)
    intros p t I J A f df dt.
    apply syn_iso_from_eq.
    simpl. f_equal. 
    
    (* A rewrite "benyúl" a b_comp mögé, és f-re cseréli a b_tm_of kifejezést: *)
    rewrite interp_tm_erasure.
    
    (* A csere után a két oldal triviálisan megegyezik: *)
    reflexivity.
    
  - (* 3. Cél: i_atom_cong_global *)
    intros p t1 t2 I A d1 d2 HeqEq.
    apply syn_iso_from_equiv. simpl.
    (* A kongruenciánál a bizonyítások illesztése miatt kell a rewrite: *)
    rewrite (@interp_ty_id Sign I).
    eapply FE_Atom.
    exact HeqEq.
Defined.

Theorem hyper_completeness_equational {Sign : Type} : 
  forall {I : b_ty} {G : h_context} {Phi : h_ty} {p q : h_tm}
  (dp : h_derivation I G p Phi) (dq : h_derivation I G q Phi),
  (forall (C : SetoidCategory) (CC : CartesianCategory C) 
          (TSC : TwoSortCategory C) 
          (BSM : BaseSignatureModel) 
          (CBM : CoherentBaseModel) 
          (GF : GoodFibration C) (SGF : StrictGoodFibration C GF) 
          (HM : Simple_Ext_Soundness.HyperModel BSM CBM) (* JAVÍTVA: Névtérrel együtt hivatkozunk rá! *)
          (wfc : wf_ctx I G) (wf_Phi : WellFormed I Phi),
      @hyper_soundness_inhabited Sign C CC TSC GF SGF BSM CBM HM _ _ _ _ dp wfc wf_Phi ≅
      @hyper_soundness_inhabited Sign C CC TSC GF SGF BSM CBM HM _ _ _ _ dq wfc wf_Phi) ->
  h_equiv_rel I p q.
Proof.
  intros I G Phi p q dp dq H_univ.
  pose proof (well_formed_ctx _ _ _ _ dp) as wfc_syn.
  pose proof (well_formed_target _ _ _ _ dp) as wf_Phi_syn.
  
  pose proof (@H_univ 
               (@Base_SetoidCategory Sign) 
               (@Base_CartesianCategory Sign)
               (@Base_TwoSortCategory Sign)
               (@Syntactic_SignatureModel Sign)
               (@Base_SyntacticCoherentModel Sign) 
               (@Syntactic_GoodFibration Sign)
               (@Syntactic_StrictGoodFibration Sign)
               (@Syntactic_HyperModel Sign)
               wfc_syn wf_Phi_syn) as H_syn.
               
  unfold hyper_hom_equiv in H_syn.
  eapply hyper_pi; [exact dp | exact dq].
Qed.



Lemma interp_h_ty_id {Sign : Type} : 
  forall (I : b_ty) (Phi : h_ty) (wf_Phi : WellFormed I Phi),
  (@Simple_Ext_Soundness.interp_h_ty Sign 
    (@Base_SetoidCategory Sign) 
    (@Base_CartesianCategory Sign)
    (@Base_TwoSortCategory Sign)
    (@Syntactic_GoodFibration Sign)         (* 1. GF *)
    (@Syntactic_StrictGoodFibration Sign)   (* 2. SGF *)
    (@Syntactic_SignatureModel Sign)        (* 3. BSM *)
    (@Base_SyntacticCoherentModel Sign)     (* 4. CBM *)
    (@Syntactic_HyperModel Sign)            (* 5. HM *)
    I Phi wf_Phi : h_ty) = Phi.
Proof.
  intros I Phi wf_Phi.
  induction wf_Phi.
  all: simpl.
  all: try reflexivity.
  (* A f_equal szétbontja a konstruktorokat, az eauto elvégzi az 
     indukciós lépést (IHwf_Phi), az apply pedig átlát a 'fix' blokkon! *)
  all: try (f_equal; eauto; apply interp_ty_id).
Qed.

Fixpoint h_make_ctx_ty {Sign : Type} (G : list (@h_ty Sign)) : @h_ty Sign :=
  match G with
  | nil => Ty_Unit
  | cons A G' => Ty_Prod (@h_make_ctx_ty Sign G') A
  end.


Lemma h_ctx_identity {Sign : Type} : 
  forall (I : b_ty) (G : h_context) (wfc : wf_ctx I G),
  (@Simple_Ext_Soundness.interp_h_ctx Sign 
    (@Base_SetoidCategory Sign) 
    (@Base_CartesianCategory Sign)
    (@Base_TwoSortCategory Sign)
    (@Syntactic_GoodFibration Sign)         (* 1. GF *)
    (@Syntactic_StrictGoodFibration Sign)   (* 2. SGF *)
    (@Syntactic_SignatureModel Sign)        (* 3. BSM *)
    (@Base_SyntacticCoherentModel Sign)     (* 4. CBM *)
    (@Syntactic_HyperModel Sign)            (* 5. HM *)
    I G wfc : h_ty) = h_make_ctx_ty G.
Proof.
  intros I G wfc.
  induction wfc.
  
  - (* 1. eset: Üres kontextus (nil) *)
    simpl. 
    (* Ha itt maradna egy interp_ty a bázis típuson, azt a múltkori trükk elintézi: *)
    repeat rewrite interp_ty_id. 
    unfold syn_obj.
    try reflexivity.
    
  - (* 2. eset: Bővített kontextus (cons) *)
    simpl.
    (* Az f_equal szétbontja a Ty_Prod-ot két külön célra: 
       a kontextus egyenlőségére és az új típus egyenlőségére *)
    f_equal.
    + (* Az első célt (A = C) megoldja az Indukciós Hipotézis: *)
      exact IHwfc.
    + (* A második célt (B = D) megoldja a másik lemmánk: *)
      apply interp_h_ty_id.
Qed.

Theorem hyper_completeness_inhabitational {Sign : Type} : 
  forall {I : b_ty} {Phi : h_ty} (wf_Phi : WellFormed I Phi),
  (forall (C : SetoidCategory) (CC : CartesianCategory C)
          (TSC : TwoSortCategory C) 
          (BSM : BaseSignatureModel) 
          (CBM : CoherentBaseModel) 
          (GF : GoodFibration C) (SGF : StrictGoodFibration C GF) 
          (HM : Simple_Ext_Soundness.HyperModel BSM CBM)
          (wfc : wf_ctx I nil) (wf_Phi' : WellFormed I Phi),
      inhabited (hom (@Simple_Ext_Soundness.interp_h_ctx Sign C CC TSC GF SGF BSM CBM HM I nil wfc) 
                     (@Simple_Ext_Soundness.interp_h_ty Sign C CC TSC GF SGF BSM CBM HM I Phi wf_Phi'))) ->
  exists (p : h_tm), inhabited (h_derivation I nil p Phi).
Proof.
  intros I Phi wf_Phi H_univ.
  
  (* 1. Universal hypothesis példányosítása a Szintaktikus Modellel *)
  pose proof (@H_univ 
               (@Base_SetoidCategory Sign) 
               (@Base_CartesianCategory Sign)
               (@Base_TwoSortCategory Sign)
               (@Syntactic_SignatureModel Sign)
               (@Base_SyntacticCoherentModel Sign) 
               (@Syntactic_GoodFibration Sign)
               (@Syntactic_StrictGoodFibration Sign)
               (@Syntactic_HyperModel Sign)
               (@WFC_nil Sign I) wf_Phi) as [[p_syn dp_syn]].
               
  (* 2. Cél Típus (Phi) tisztítása a már bizonyított lemmával *)
  pose proof (@interp_h_ty_id Sign I Phi wf_Phi) as Heq_Phi.
  rewrite Heq_Phi in dp_syn.
    
  (* 3. Forrás Kontextus (nil -> Ty_Unit) tisztítása a másik lemmával *)
  pose proof (@h_ctx_identity Sign I nil (@WFC_nil Sign I)) as Heq_Ctx.
  rewrite Heq_Ctx in dp_syn.
  
  (* 4. Bázis Típus (I) tisztítása *)
  unfold syn_obj in dp_syn.
  pose proof (@interp_ty_id Sign I) as Heq_I.
  rewrite Heq_I in dp_syn.
  
  (* 5. Végső levezetés (nil |- Phi) felépítése 
        A dp_syn típusa most: h_derivation I [Ty_Unit] p_syn Phi 
        Egy egyszerű Lam-App kombóval a tm_unit-ot bedobjuk neki! *)
  exists (tm_app (tm_lam Ty_Unit p_syn) tm_unit).
  constructor.
  eapply HD_App.
  - apply HD_Lam. exact dp_syn.
  - apply HD_Unit. apply WFC_nil.
Qed.

Theorem hyper_completeness_inhabitational_gen {Sign : Type} : 
  forall {I : b_ty} {G : h_context} {Phi : h_ty} 
         (wfc : wf_ctx I G) (wf_Phi : WellFormed I Phi),
  (forall (C : SetoidCategory) (CC : CartesianCategory C)
          (TSC : TwoSortCategory C) 
          (BSM : BaseSignatureModel) 
          (CBM : CoherentBaseModel) 
          (GF : GoodFibration C) (SGF : StrictGoodFibration C GF) 
          (HM : Simple_Ext_Soundness.HyperModel BSM CBM)
          (wfc' : wf_ctx I G) (wf_Phi' : WellFormed I Phi),
      inhabited (hom (@Simple_Ext_Soundness.interp_h_ctx Sign C CC TSC GF SGF BSM CBM HM I G wfc') 
                     (@Simple_Ext_Soundness.interp_h_ty Sign C CC TSC GF SGF BSM CBM HM I Phi wf_Phi'))) ->
  exists (p : h_tm), inhabited (h_derivation I G p Phi).
Proof.
  intros I G Phi wfc wf_Phi H_univ.
  
  (* 1. Universal hypothesis példányosítása *)
  pose proof (@H_univ 
               (@Base_SetoidCategory Sign) 
               (@Base_CartesianCategory Sign)
               (@Base_TwoSortCategory Sign)
               (@Syntactic_SignatureModel Sign)
               (@Base_SyntacticCoherentModel Sign) 
               (@Syntactic_GoodFibration Sign)
               (@Syntactic_StrictGoodFibration Sign)
               (@Syntactic_HyperModel Sign)
               wfc wf_Phi) as [[p_syn dp_syn]].
               
  (* 2. Cél Típus (Phi) tisztítása *)
  (* Dobjuk az explicit assert-et! A lemma pontosan definiálja az egyenlőséget 
     a rejtett coercion-nel együtt, így a rewrite azonnal célba talál! *)
  pose proof (@interp_h_ty_id Sign I Phi wf_Phi) as Heq_Phi.
  rewrite Heq_Phi in dp_syn.
    
  (* 3. Kontextus (G) tisztítása *)
  pose proof (@h_ctx_identity Sign I G wfc) as Heq_Ctx.
  rewrite Heq_Ctx in dp_syn.
  
  (* 4. Index (I) tisztítása *)
  unfold syn_obj in dp_syn.
  pose proof (@interp_ty_id Sign I) as Heq_I.
  rewrite Heq_I in dp_syn.
  
  (* 5. Végső levezetés konstruálása (Változatlan marad) *)
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