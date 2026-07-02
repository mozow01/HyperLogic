(* theories/Logic/Hyper/Individual/Hyper_Syntax.v *)

Require Import List.
Import ListNotations.

Require Export HyperLogic.Logic.Base.Individual.Base_Syntax.
Require Export HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.

(* Intuitionistic first-order fragment of EpsilonFull.

   We deliberately reuse the EpsilonFull formula and term language, so predicates,
   function symbols, products, sums, implication, forall, and exists are shared.
   The fragment is cut at the proof-system/equivalence layer: no epsilon
   equivalence constructor and no epsilon derivation constructor is available
   here. *)

Inductive ifol_form_equiv {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} (I : b_ty)
  : @h_ty Sign Func Pred -> @h_ty Sign Func Pred -> Type :=
  | IFE_Atom : forall (p : Pred) (t1 t2 : @b_tm Sign Func)
      (d1 : base_typing I t1 (pred_dom p)) (d2 : base_typing I t2 (pred_dom p)),
      base_equiv d1 d2 -> ifol_form_equiv I (Ty_Atom p t1) (Ty_Atom p t2)
  | IFE_Refl : forall Phi, WellFormed I Phi -> ifol_form_equiv I Phi Phi
  | IFE_Sym : forall Phi Psi,
      ifol_form_equiv I Phi Psi -> ifol_form_equiv I Psi Phi
  | IFE_Trans : forall Phi Psi Chi,
      ifol_form_equiv I Phi Psi ->
      ifol_form_equiv I Psi Chi ->
      ifol_form_equiv I Phi Chi
  | IFE_Prod : forall A B A' B',
      ifol_form_equiv I A A' ->
      ifol_form_equiv I B B' ->
      ifol_form_equiv I (Ty_Prod A B) (Ty_Prod A' B')
  | IFE_Sum : forall A B A' B',
      ifol_form_equiv I A A' ->
      ifol_form_equiv I B B' ->
      ifol_form_equiv I (Ty_Sum A B) (Ty_Sum A' B')
  | IFE_Arrow : forall A B A' B',
      ifol_form_equiv I A A' ->
      ifol_form_equiv I B B' ->
      ifol_form_equiv I (Ty_Arrow A B) (Ty_Arrow A' B')
  | IFE_All : forall D Body Body',
      ifol_form_equiv (b_Prod I D) Body Body' ->
      ifol_form_equiv I (Ty_All D Body) (Ty_All D Body')
  | IFE_Ex : forall D Body Body',
      ifol_form_equiv (b_Prod I D) Body Body' ->
      ifol_form_equiv I (Ty_Ex D Body) (Ty_Ex D Body')
  | IFE_Pullback_Id : forall Phi,
      WellFormed I Phi ->
      ifol_form_equiv I (form_subst b_id Phi) Phi
  | IFE_Pullback_Comp : forall J K (f g : @b_tm Sign Func) Phi
      (df : base_typing J f K) (dg : base_typing I g J),
      WellFormed K Phi ->
      ifol_form_equiv I (form_subst g (form_subst f Phi)) (form_subst (b_comp f g) Phi)
  | IFE_Pullback_Cong : forall J (f g : @b_tm Sign Func) Phi
      (df : base_typing I f J) (dg : base_typing I g J),
      base_equiv df dg ->
      WellFormed J Phi ->
      ifol_form_equiv I (form_subst f Phi) (form_subst g Phi).

Inductive ifol_ctx_equiv {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} (I : b_ty)
  : @h_context Sign Func Pred -> @h_context Sign Func Pred -> Type :=
  | ICEq_Nil : ifol_ctx_equiv I [] []
  | ICEq_Cons : forall Phi Psi G1 G2,
      ifol_form_equiv I Phi Psi ->
      ifol_ctx_equiv I G1 G2 ->
      ifol_ctx_equiv I (Phi :: G1) (Psi :: G2).

Inductive ifol_h_typing {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} (I : b_ty)
  : @h_context Sign Func Pred -> @h_tm Sign Func Pred -> @h_ty Sign Func Pred -> Prop :=
  | IHT_Var0 : forall G Phi, ifol_h_typing I (Phi :: G) (tm_var 0) Phi
  | IHT_VarS : forall G Phi Psi i,
      ifol_h_typing I G (tm_var i) Phi ->
      ifol_h_typing I (Psi :: G) (tm_var (S i)) Phi
  | IHT_Conv : forall G p Phi Psi,
      ifol_h_typing I G p Phi ->
      ifol_form_equiv I Phi Psi ->
      ifol_h_typing I G p Psi
  | IHT_Ctx_Conv : forall G1 G2 p Phi,
      ifol_ctx_equiv I G1 G2 ->
      ifol_h_typing I G1 p Phi ->
      ifol_h_typing I G2 p Phi
  | IHT_Unit : forall G, ifol_h_typing I G tm_unit Ty_Unit
  | IHT_Lam : forall G p Phi Psi,
      ifol_h_typing I (Phi :: G) p Psi ->
      ifol_h_typing I G (tm_lam Phi p) (Ty_Arrow Phi Psi)
  | IHT_App : forall G p1 p2 Phi Psi,
      ifol_h_typing I G p1 (Ty_Arrow Phi Psi) ->
      ifol_h_typing I G p2 Phi ->
      ifol_h_typing I G (tm_app p1 p2) Psi
  | IHT_Pair : forall G p1 p2 Phi Psi,
      ifol_h_typing I G p1 Phi ->
      ifol_h_typing I G p2 Psi ->
      ifol_h_typing I G (tm_pair p1 p2) (Ty_Prod Phi Psi)
  | IHT_Fst : forall G p Phi Psi,
      ifol_h_typing I G p (Ty_Prod Phi Psi) ->
      ifol_h_typing I G (tm_fst p) Phi
  | IHT_Snd : forall G p Phi Psi,
      ifol_h_typing I G p (Ty_Prod Phi Psi) ->
      ifol_h_typing I G (tm_snd p) Psi
  | IHT_Inl : forall G p Phi Psi,
      ifol_h_typing I G p Phi ->
      ifol_h_typing I G (tm_inl Psi p) (Ty_Sum Phi Psi)
  | IHT_Inr : forall G p Phi Psi,
      ifol_h_typing I G p Psi ->
      ifol_h_typing I G (tm_inr Phi p) (Ty_Sum Phi Psi)
  | IHT_Case : forall G p p1 p2 Phi Psi Chi,
      ifol_h_typing I G p (Ty_Sum Phi Psi) ->
      ifol_h_typing I (Phi :: G) p1 Chi ->
      ifol_h_typing I (Psi :: G) p2 Chi ->
      ifol_h_typing I G (tm_case p p1 p2) Chi
  | IHT_Absurd : forall G p Phi,
      ifol_h_typing I G p Ty_Void ->
      ifol_h_typing I G (tm_absurd Phi p) Phi
  | IHT_All_Intro : forall G p A Phi,
      ifol_h_typing (b_Prod I A) (ctx_subst b_fst G) p Phi ->
      ifol_h_typing I G (tm_all_intro p) (Ty_All A Phi)
  | IHT_All_Elim : forall G p A Phi f,
      ifol_h_typing I G p (Ty_All A Phi) ->
      base_typing I f A ->
      ifol_h_typing I G (tm_all_elim p f) (form_subst (b_pair b_id f) Phi)
  | IHT_Ex_Intro : forall G p A Phi f,
      base_typing I f A ->
      ifol_h_typing I G p (form_subst (b_pair b_id f) Phi) ->
      ifol_h_typing I G (tm_ex_intro f p) (Ty_Ex A Phi)
  | IHT_Ex_Elim : forall G p p2 A Phi Chi,
      ifol_h_typing I G p (Ty_Ex A Phi) ->
      ifol_h_typing (b_Prod I A) (Phi :: ctx_subst b_fst G) p2 (form_subst b_fst Chi) ->
      ifol_h_typing I G (tm_ex_elim p p2) Chi.

Inductive ifol_h_derivation {Sign Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} :
  b_ty -> @h_context Sign Func Pred -> @h_tm Sign Func Pred -> @h_ty Sign Func Pred -> Type :=
  | IHD_Var0 : forall (I : b_ty) (Phi : @h_ty Sign Func Pred) (G : @h_context Sign Func Pred),
      All_WellFormed I (Phi :: G) ->
      ifol_h_derivation I (Phi :: G) (tm_var 0) Phi
  | IHD_VarS : forall (I : b_ty) (Phi Psi : @h_ty Sign Func Pred) (G : @h_context Sign Func Pred) (n : nat),
      WellFormed I Psi ->
      ifol_h_derivation I G (tm_var n) Phi ->
      ifol_h_derivation I (Psi :: G) (tm_var (S n)) Phi
  | IHD_Unit : forall (I : b_ty) (G : @h_context Sign Func Pred),
      All_WellFormed I G ->
      ifol_h_derivation I G tm_unit Ty_Unit
  | IHD_Conv : forall (I : b_ty) (G : @h_context Sign Func Pred) (p : @h_tm Sign Func Pred) (Phi Psi : @h_ty Sign Func Pred),
      ifol_h_derivation I G p Phi ->
      ifol_form_equiv I Phi Psi ->
      ifol_h_derivation I G p Psi
  | IHD_Ctx_Conv : forall (I : b_ty) (G1 G2 : @h_context Sign Func Pred) (p : @h_tm Sign Func Pred) (Phi : @h_ty Sign Func Pred),
      ifol_ctx_equiv I G1 G2 ->
      ifol_h_derivation I G1 p Phi ->
      ifol_h_derivation I G2 p Phi
  | IHD_Lam : forall (I : b_ty) (G : @h_context Sign Func Pred) (p : @h_tm Sign Func Pred) (Phi Psi : @h_ty Sign Func Pred),
      ifol_h_derivation I (Phi :: G) p Psi ->
      ifol_h_derivation I G (tm_lam Phi p) (Ty_Arrow Phi Psi)
  | IHD_App : forall (I : b_ty) (G : @h_context Sign Func Pred) (p1 p2 : @h_tm Sign Func Pred) (Phi Psi : @h_ty Sign Func Pred),
      ifol_h_derivation I G p1 (Ty_Arrow Phi Psi) ->
      ifol_h_derivation I G p2 Phi ->
      ifol_h_derivation I G (tm_app p1 p2) Psi
  | IHD_Pair : forall (I : b_ty) (G : @h_context Sign Func Pred) (p1 p2 : @h_tm Sign Func Pred) (Phi Psi : @h_ty Sign Func Pred),
      ifol_h_derivation I G p1 Phi ->
      ifol_h_derivation I G p2 Psi ->
      ifol_h_derivation I G (tm_pair p1 p2) (Ty_Prod Phi Psi)
  | IHD_Fst : forall (I : b_ty) (G : @h_context Sign Func Pred) (p : @h_tm Sign Func Pred) (Phi Psi : @h_ty Sign Func Pred),
      ifol_h_derivation I G p (Ty_Prod Phi Psi) ->
      ifol_h_derivation I G (tm_fst p) Phi
  | IHD_Snd : forall (I : b_ty) (G : @h_context Sign Func Pred) (p : @h_tm Sign Func Pred) (Phi Psi : @h_ty Sign Func Pred),
      ifol_h_derivation I G p (Ty_Prod Phi Psi) ->
      ifol_h_derivation I G (tm_snd p) Psi
  | IHD_Inl : forall {I G p Phi Psi},
      WellFormed I Psi ->
      ifol_h_derivation I G p Phi ->
      ifol_h_derivation I G (tm_inl Psi p) (Ty_Sum Phi Psi)
  | IHD_Inr : forall {I G p Phi Psi},
      WellFormed I Phi ->
      ifol_h_derivation I G p Psi ->
      ifol_h_derivation I G (tm_inr Phi p) (Ty_Sum Phi Psi)
  | IHD_Case : forall (I : b_ty) (G : @h_context Sign Func Pred) (p p1 p2 : @h_tm Sign Func Pred) (Phi Psi Chi : @h_ty Sign Func Pred),
      ifol_h_derivation I G p (Ty_Sum Phi Psi) ->
      ifol_h_derivation I (Phi :: G) p1 Chi ->
      ifol_h_derivation I (Psi :: G) p2 Chi ->
      ifol_h_derivation I G (tm_case p p1 p2) Chi
  | IHD_Absurd : forall {I G p Phi},
      WellFormed I Phi ->
      ifol_h_derivation I G p Ty_Void ->
      ifol_h_derivation I G (tm_absurd Phi p) Phi
  | IHD_All_Intro : forall (I A : b_ty) (G : @h_context Sign Func Pred) (p : @h_tm Sign Func Pred) (Phi : @h_ty Sign Func Pred),
      ifol_h_derivation (b_Prod I A) (ctx_subst b_fst G) p Phi ->
      ifol_h_derivation I G (tm_all_intro p) (Ty_All A Phi)
  | IHD_All_Elim : forall (I A : b_ty) (G : @h_context Sign Func Pred) (p : @h_tm Sign Func Pred) (Phi : @h_ty Sign Func Pred) (f : @b_tm Sign Func),
      ifol_h_derivation I G p (Ty_All A Phi) ->
      base_typing I f A ->
      ifol_h_derivation I G (tm_all_elim p f) (form_subst (b_pair b_id f) Phi)
  | IHD_Ex_Intro : forall (I A : b_ty) (G : @h_context Sign Func Pred) (p : @h_tm Sign Func Pred) (Phi : @h_ty Sign Func Pred) (f : @b_tm Sign Func),
      base_typing I f A ->
      ifol_h_derivation I G p (form_subst (b_pair b_id f) Phi) ->
      ifol_h_derivation I G (tm_ex_intro f p) (Ty_Ex A Phi)
  | IHD_Ex_Elim : forall (I A : b_ty) (G : @h_context Sign Func Pred) (p p2 : @h_tm Sign Func Pred) (Phi Chi : @h_ty Sign Func Pred),
      ifol_h_derivation I G p (Ty_Ex A Phi) ->
      ifol_h_derivation (b_Prod I A) (Phi :: ctx_subst b_fst G) p2 (form_subst b_fst Chi) ->
      ifol_h_derivation I G (tm_ex_elim p p2) Chi.

Notation "I '∙' G '⊢ifol' p ':' Phi" := (ifol_h_derivation I G p Phi)
  (at level 99, p at next level, no associativity).
