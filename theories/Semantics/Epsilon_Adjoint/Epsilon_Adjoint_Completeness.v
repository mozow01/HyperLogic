(* theories/Semantics/Epsilon_Adjoint/Epsilon_Adjoint_Completeness.v *)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Equality.
Require Import List. 
Import ListNotations.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Fibration.

Require Import HyperLogic.Logic.Base.Epsilon_Adjoint.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon_Adjoint.Hyper_Syntax.
Require Import HyperLogic.Semantics.Epsilon_Adjoint.Epsilon_Adjoint_Fibration.

(* Beimportáljuk a bázis szintaktikus modellt! *)
Require Import HyperLogic.Semantics.Epsilon_Adjoint.Base_Epsilon_Completeness.

(* ================================================================= *)
(* 1. A SZÁLAK (FIBERS) KATEGÓRIÁJA ÉS MORFIZMUSAI                   *)
(* ================================================================= *)

(* Egy morfizmus a szálban a Phi premisszából a Psi konklúzióba menő levezetés *)
Class hom_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) (Phi Psi : @h_ty Sign) : Type := mk_hom_fiber {
  h_tm_of : @h_tm Sign;
  h_deriv_of : @h_derivation Sign SM I (Phi :: nil) h_tm_of Psi
}.

Arguments h_tm_of {Sign SM I Phi Psi} _.
Arguments h_deriv_of {Sign SM I Phi Psi} _.

Definition fiber_cut {Sign : Type} {SM : SkolemMapping Sign} {I : b_ty} {Phi Psi Chi : @h_ty Sign}
  (t_f t_g : @h_tm Sign) 
  (d_f : h_derivation I (Phi :: nil) t_f Psi) 
  (d_g : h_derivation I (Psi :: nil) t_g Chi) : 
  { t_comp : @h_tm Sign & h_derivation I (Phi :: nil) t_comp Chi }.
Proof.
  (* Ezt a részt a meglévő helyettesítési (h_subst) vagy gyengítési 
     (h_weaken) függvényeidre támaszkodva tudod majd megírni a 
     Hyper_Lemmas.v fájlodban. *)
  admit.
Admitted.

(* A kompozíció immár egy tiszta, funkcionális program! *)
Definition h_compose {Sign : Type} {SM : SkolemMapping Sign} {I : b_ty} {Phi Psi Chi : @h_ty Sign}
  (g : @hom_fiber Sign SM I Psi Chi) (f : @hom_fiber Sign SM I Phi Psi) : @hom_fiber Sign SM I Phi Chi.
Proof.
  (* 1. Kinyerjük a bizonyítás-termeket és a derivációkat a bejövő morfizmusokból *)
  pose (t_f := h_tm_of f).
  pose (t_g := h_tm_of g).
  pose (d_f := h_deriv_of f).
  pose (d_g := h_deriv_of g).
  
  (* 2. Alkalmazzuk a szintaktikus vágást (Cut), ami ad egy új termet és levezetést *)
  destruct (fiber_cut t_f t_g d_f d_g) as [t_comp d_comp].
  
  (* 3. Becsomagoljuk és visszaadjuk a kész Fiber morfizmust *)
  apply (@mk_hom_fiber Sign SM I Phi Chi t_comp d_comp).
Defined.

(* ================================================================= *)
(* 1.5 PROOF IRRELEVANCE LOGIC FOR FIBERS                            *)
(* ================================================================= *)

(* Az explicit tárgynyelvi ekvivalencia reláció a hiper-termekre *)
Inductive h_tm_equiv_rel {Sign : Type} `{SkolemMapping Sign} (I : b_ty) : 
  @h_context Sign -> @h_ty Sign -> @h_tm Sign -> @h_tm Sign -> Prop :=
  | HPI_rule : forall G Psi t s,
      h_derivation I G t Psi -> h_derivation I G s Psi -> h_tm_equiv_rel I G Psi t s.

(* Az ekvivalencia kiterjesztése a szál morfizmusaira (hom_fiber) *)
Definition fiber_equiv {Sign : Type} {SM : SkolemMapping Sign} {I : b_ty} {Phi Psi : @h_ty Sign} 
  (f g : @hom_fiber Sign SM I Phi Psi) : Prop :=
  h_tm_equiv_rel I (Phi :: nil) Psi (h_tm_of f) (h_tm_of g).

Lemma fiber_equiv_refl : forall {Sign : Type} {SM : SkolemMapping Sign} {I : b_ty} {Phi Psi : @h_ty Sign} 
  (f : @hom_fiber Sign SM I Phi Psi), fiber_equiv f f.
Proof.
  intros Sign SM I Phi Psi f.
  unfold fiber_equiv.
  apply (HPI_rule I (Phi :: nil) Psi).
  - exact (h_deriv_of f).
  - exact (h_deriv_of f).
Defined.

Lemma fiber_equiv_sym : forall {Sign : Type} {SM : SkolemMapping Sign} {I : b_ty} {Phi Psi : @h_ty Sign} 
  (f g : @hom_fiber Sign SM I Phi Psi), fiber_equiv f g -> fiber_equiv g f.
Proof.
  intros Sign SM I Phi Psi f g H.
  unfold fiber_equiv.
  apply (HPI_rule I (Phi :: nil) Psi).
  - exact (h_deriv_of g).
  - exact (h_deriv_of f).
Qed.

Lemma fiber_equiv_trans : forall {Sign : Type} {SM : SkolemMapping Sign} {I : b_ty} {Phi Psi : @h_ty Sign} 
  (f g h : @hom_fiber Sign SM I Phi Psi), fiber_equiv f g -> fiber_equiv g h -> fiber_equiv f h.
Proof.
  intros Sign SM I Phi Psi f g h H1 H2.
  unfold fiber_equiv.
  apply (HPI_rule I (Phi :: nil) Psi).
  - exact (h_deriv_of f).
  - exact (h_deriv_of h).
Qed.

(* A mindent vivő lemma: Bármely két érvényes levezetés ekvivalens *)
Lemma fiber_generic_axiom_proof : forall {Sign : Type} {SM : SkolemMapping Sign} {I : b_ty} {Phi Psi : @h_ty Sign} 
  (f g : @hom_fiber Sign SM I Phi Psi), fiber_equiv f g.
Proof.
  intros Sign SM I Phi Psi f g.
  unfold fiber_equiv.
  apply (HPI_rule I (Phi :: nil) Psi).
  - exact (h_deriv_of f).
  - exact (h_deriv_of g).
Defined.

(* ================================================================= *)
(* 2. FIBER: SETOID ÉS CARTESIAN STRUKTÚRA                           *)
(* ================================================================= *)

Instance Fiber_SetoidCategory {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) : SetoidCategory.
Proof.
  refine (mk_SetoidCategory 
    (@h_ty Sign) 
    (@hom_fiber Sign SM I) 
    (fun Phi => @mk_hom_fiber Sign SM I Phi Phi (tm_var 0) (HD_Var0 I [] Phi))
    (fun Phi Psi Chi g f => @h_compose Sign SM I Phi Psi Chi g f)
    (@fiber_equiv Sign SM I)
    _ _ _ _ _).
  - intros X Y. constructor.
    + intros f. apply fiber_equiv_refl.
    + intros f g H. apply fiber_equiv_sym. exact H.
    + intros f g h H1 H2. exact (fiber_equiv_trans f g h H1 H2).
  - intros X Y Z W f g h. apply fiber_generic_axiom_proof.
  - intros X Y f. apply fiber_generic_axiom_proof.
  - intros X Y f. apply fiber_generic_axiom_proof.
  - unfold Proper, respectful. intros X Y Z f g Hfg h i Hhi. apply fiber_generic_axiom_proof.
Defined.

(* A Terminális és Szorzat morfizmusok közvetlen megfeleltetése *)
Definition h_terminal_map {Sign : Type} {SM : SkolemMapping Sign} {I : b_ty} (Phi : @h_ty Sign) : 
  @hom_fiber Sign SM I Phi Ty_Unit.
Proof.
  apply (@mk_hom_fiber Sign SM I Phi Ty_Unit tm_unit).
  apply HD_Unit.
Defined.

Definition h_prod_map {Sign : Type} {SM : SkolemMapping Sign} {I : b_ty} {Phi Psi Chi : @h_ty Sign}
  (f : @hom_fiber Sign SM I Phi Psi) (g : @hom_fiber Sign SM I Phi Chi) : 
  @hom_fiber Sign SM I Phi (Ty_Prod Psi Chi).
Proof.
  apply (@mk_hom_fiber Sign SM I Phi (Ty_Prod Psi Chi) (tm_pair (h_tm_of f) (h_tm_of g))).
  apply HD_Pair.
  - exact (h_deriv_of f).
  - exact (h_deriv_of g).
Defined.

Definition h_prod_fst {Sign : Type} {SM : SkolemMapping Sign} {I : b_ty} (Phi Psi : @h_ty Sign) : 
  @hom_fiber Sign SM I (Ty_Prod Phi Psi) Phi.
Proof.
  apply (@mk_hom_fiber Sign SM I (Ty_Prod Phi Psi) Phi (tm_fst (tm_var 0))).
  eapply HD_Fst.
  apply HD_Var0.
Defined.

Definition h_prod_snd {Sign : Type} {SM : SkolemMapping Sign} {I : b_ty} (Phi Psi : @h_ty Sign) : 
  @hom_fiber Sign SM I (Ty_Prod Phi Psi) Psi.
Proof.
  apply (@mk_hom_fiber Sign SM I (Ty_Prod Phi Psi) Psi (tm_snd (tm_var 0))).
  eapply HD_Snd.
  apply HD_Var0.
Defined.

Instance Fiber_CartesianCategory {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) : 
  CartesianCategory (@Fiber_SetoidCategory Sign SM I).
Proof.
  refine (mk_CartesianCategory 
    (@Fiber_SetoidCategory Sign SM I)
    Ty_Unit
    (@h_terminal_map Sign SM I)
    _ (* terminal_map_unique *)
    Ty_Prod
    (@h_prod_map Sign SM I)
    (@h_prod_fst Sign SM I)
    (@h_prod_snd Sign SM I)
    _ _ _ _).
  - intros X f. apply fiber_generic_axiom_proof.
  - intros X Y Z f g. apply fiber_generic_axiom_proof.
  - intros X Y Z f g. apply fiber_generic_axiom_proof.
  - intros X Y Z h. apply fiber_generic_axiom_proof.
  - unfold Proper, respectful. intros X Y Z f f' Hf g g' Hg. apply fiber_generic_axiom_proof.
Defined. 

(* ================================================================= *)
(* 3. FIBER: CARTESIAN CLOSED (CCC) STRUKTÚRA                        *)
(* ================================================================= *)

Definition h_exp_eval {Sign : Type} {SM : SkolemMapping Sign} {I : b_ty} (Phi Psi : @h_ty Sign) : 
  @hom_fiber Sign SM I (Ty_Prod (Ty_Arrow Phi Psi) Phi) Psi.
Proof. 
  (* Term: app (fst (var 0)) (snd (var 0)) *)
  apply (@mk_hom_fiber Sign SM I (Ty_Prod (Ty_Arrow Phi Psi) Phi) Psi
    (tm_app (tm_fst (tm_var 0)) (tm_snd (tm_var 0)))).
  eapply HD_App.
  - eapply HD_Fst. apply HD_Var0. (* (Phi -> Psi) kinyerése a szorzatból *)
  - eapply HD_Snd. apply HD_Var0. (* Phi kinyerése a szorzatból *)
Defined.

Definition h_exp_map {Sign : Type} {SM : SkolemMapping Sign} {I : b_ty} {Phi Psi Chi : @h_ty Sign}
  (f : @hom_fiber Sign SM I (Ty_Prod Phi Psi) Chi) : 
  @hom_fiber Sign SM I Phi (Ty_Arrow Psi Chi).
Proof.
  (* Term: lam Psi. (f [ (var 1, var 0) ]) *)
  (* Itt f-et alkalmazzuk egy párra, amit a lambda kötése (var 0) és a külső kontextus (var 1) alkot *)
  apply (@mk_hom_fiber Sign SM I Phi (Ty_Arrow Psi Chi)
    (tm_lam Psi (tm_app (h_tm_of f) (tm_pair (tm_var 1) (tm_var 0))))).
  apply HD_Lam.
  eapply HD_App.
  - (* f derivációjának beillesztése weakening-gel (most admit-elve a vágás miatt) *)
    admit. 
  - apply HD_Pair.
    + apply HD_VarS. apply HD_Var0. (* Phi elérése (var 1) *)
    + apply HD_Var0.               (* Psi elérése (var 0) *)
Admitted.

(*

Instance Fiber_CartesianClosedCategory {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) : 
  CartesianClosedCategory (@Fiber_SetoidCategory Sign SM I).
Proof.
  refine (mk_CartesianClosedCategory 
    (@Fiber_SetoidCategory Sign SM I) 
    (@Fiber_CartesianCategory Sign SM I) 
    Ty_Arrow 
    (@h_exp_map Sign SM I)   (* <-- CSERÉLVE: A Curry (exp_map) jön a 4. helyre! *)
    (@h_exp_eval Sign SM I)  (* <-- CSERÉLVE: Az Eval (apply) jön az 5. helyre! *)
    _ _ _ _).
  - intros X Y Z f. apply fiber_generic_axiom_proof.
  - intros X Y Z h. apply fiber_generic_axiom_proof.
  - intros X Y Z W f g Hfg. apply fiber_generic_axiom_proof.
  - intros X Y Z f. apply fiber_generic_axiom_proof.
Defined.

(* ================================================================= *)
(* 4. FIBER: BI-CARTESIAN CLOSED (BiCCC) STRUKTÚRA                   *)
(* ================================================================= *)

Instance Fiber_BiCartesianClosedCategory {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) : 
  BiCartesianClosedCategory (@Fiber_SetoidCategory Sign SM I).
Proof.
  refine (mk_BiCartesianClosedCategory 
    (@Fiber_SetoidCategory Sign SM I) 
    (@Fiber_CartesianCategory Sign SM I)       (* Cartesian struktúra *)
    (@Fiber_CartesianClosedCategory Sign SM I) (* CCC struktúra *)
    Ty_Void 
    (@h_initial_map Sign SM I) 
    _ (* initial_map_unique *)
    Ty_Sum 
    (@h_coprod_inl Sign SM I) 
    (@h_coprod_inr Sign SM I) 
    (@h_coprod_map Sign SM I) 
    _ _ _ _).
  - intros X f. apply fiber_generic_axiom_proof.
  - intros X Y Z f g. apply fiber_generic_axiom_proof.
  - intros X Y Z f g. apply fiber_generic_axiom_proof.
  - intros X Y Z h. apply fiber_generic_axiom_proof.
  - unfold Proper, respectful. intros X Y Z f f' Hf g g' Hg. apply fiber_generic_axiom_proof.
Defined.

(* ================================================================= *)
(* 5. A HELYETTESÍTÉS MINT PULLBACK FUNKTOR                          *)
(* ================================================================= *)

Definition syn_pullback_fobj {Sign : Type} {SM : SkolemMapping Sign} {I J : b_ty} 
  (f : @hom_base Sign I J) (Phi : @h_ty Sign) : @h_ty Sign :=
  form_subst (tm_of f) Phi.

Definition syn_pullback_fmap {Sign : Type} {SM : SkolemMapping Sign} {I J : b_ty} 
  (f : @hom_base Sign I J) {Phi Psi : @h_ty Sign} (g : @hom_fiber Sign SM J Phi Psi) : 
  @hom_fiber Sign SM I (syn_pullback_fobj f Phi) (syn_pullback_fobj f Psi).
Proof. admit. Admitted.

Instance Syn_Pullback {Sign : Type} {SM : SkolemMapping Sign} {I J : b_ty} (f : @hom_base Sign I J) : 
  Functor (@Fiber_SetoidCategory Sign SM J) (@Fiber_SetoidCategory Sign SM I).
Proof.
  refine (mk_Functor 
    (@Fiber_SetoidCategory Sign SM J) 
    (@Fiber_SetoidCategory Sign SM I) 
    (@syn_pullback_fobj Sign SM I J f) 
    (@syn_pullback_fmap Sign SM I J f) 
    _ _ _).
  - intros X Y g h H. apply fiber_generic_axiom_proof.
  - intros X. apply fiber_generic_axiom_proof.
  - intros X Y Z g h. apply fiber_generic_axiom_proof.
Defined.

*)