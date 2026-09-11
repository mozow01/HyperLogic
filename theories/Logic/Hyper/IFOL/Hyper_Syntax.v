(* theories/Logic/Hyper/IFOL/Hyper_Syntax.v *)

Require Import List.
Import ListNotations.

Require Import HyperLogic.Logic.Base.IFOL.Base_Syntax.

(* ================================================================= *)
(* 0. PREDIKÁTUMSZIGNATÚRA                                           *)
(* ================================================================= *)

Class PredicateSignature (Pred : Type) : Type := {
  pred_dom : Pred -> b_ty
}.

(* ================================================================= *)
(* 1. FORMULÁK                                                       *)
(* ================================================================= *)

Inductive h_ty {Func Pred : Type} : Type :=
  | Ty_Unit   : h_ty
  | Ty_Void   : h_ty
  | Ty_Prod   : h_ty -> h_ty -> h_ty
  | Ty_Sum    : h_ty -> h_ty -> h_ty
  | Ty_Arrow  : h_ty -> h_ty -> h_ty
  | Ty_Atom   : Pred -> @b_tm Func -> h_ty
  | Ty_All    : b_ty -> h_ty -> h_ty
  | Ty_Ex     : b_ty -> h_ty -> h_ty.

Definition h_context {Func Pred : Type} := list (@h_ty Func Pred).

(* ================================================================= *)
(* 2. BIZONYÍTÁSTERMEK                                               *)
(* ================================================================= *)

Inductive h_tm {Func Pred : Type} : Type :=
  | tm_unit   : h_tm
  | tm_var    : nat -> h_tm
  | tm_lam    : @h_ty Func Pred -> h_tm -> h_tm
  | tm_app    : h_tm -> h_tm -> h_tm
  | tm_pair   : h_tm -> h_tm -> h_tm
  | tm_fst    : h_tm -> h_tm
  | tm_snd    : h_tm -> h_tm
  | tm_inl    : @h_ty Func Pred -> h_tm -> h_tm
  | tm_inr    : @h_ty Func Pred -> h_tm -> h_tm
  | tm_case   : h_tm -> h_tm -> h_tm -> h_tm
  | tm_absurd : @h_ty Func Pred -> h_tm -> h_tm
  | tm_all_intro : h_tm -> h_tm
  | tm_all_elim  : h_tm -> @b_tm Func -> h_tm
  | tm_ex_intro  : @b_tm Func -> h_tm -> h_tm
  | tm_ex_elim   : h_tm -> h_tm -> h_tm.

(* ================================================================= *)
(* BÁZIS HELYETTESÍTÉS ÉS PULLBACK                                   *)
(* ================================================================= *)

Definition b_subst_ext {Func : Type} (f : @b_tm Func) : @b_tm Func :=
  b_pair (b_comp f b_fst) b_snd.

Fixpoint form_subst {Func Pred : Type}
  (f : @b_tm Func) (Phi : @h_ty Func Pred) : @h_ty Func Pred :=
  match Phi with
  | Ty_Unit => Ty_Unit
  | Ty_Void => Ty_Void
  | Ty_Prod A B => Ty_Prod (form_subst f A) (form_subst f B)
  | Ty_Sum A B => Ty_Sum (form_subst f A) (form_subst f B)
  | Ty_Arrow A B => Ty_Arrow (form_subst f A) (form_subst f B)
  | Ty_Atom p t => Ty_Atom p (b_comp t f)
  | Ty_All A Body => Ty_All A (form_subst (b_subst_ext f) Body)
  | Ty_Ex A Body => Ty_Ex A (form_subst (b_subst_ext f) Body)
  end.

Definition ctx_subst {Func Pred : Type}
  (f : @b_tm Func) (G : @h_context Func Pred) : @h_context Func Pred :=
  map (form_subst f) G.

Declare Scope surface_scope.
Notation "Phi .[ t ]" := (form_subst (b_pair b_id t) Phi) (at level 40, left associativity) : surface_scope.
Open Scope surface_scope.

(* ================================================================= *)
(* WELLFORMED FORMULAS (WFF)                                         *)
(* ================================================================= *)

Inductive WellFormed {Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} (I : b_ty) : @h_ty Func Pred -> Type :=
  | WF_Unit   : WellFormed I Ty_Unit
  | WF_Void   : WellFormed I Ty_Void
  | WF_Prod   : forall Phi Psi, WellFormed I Phi -> WellFormed I Psi -> WellFormed I (Ty_Prod Phi Psi)
  | WF_Sum    : forall Phi Psi, WellFormed I Phi -> WellFormed I Psi -> WellFormed I (Ty_Sum Phi Psi)
  | WF_Arrow  : forall Phi Psi, WellFormed I Phi -> WellFormed I Psi -> WellFormed I (Ty_Arrow Phi Psi)
  | WF_Atom   : forall (p : Pred) t, base_typing I t (pred_dom p) -> WellFormed I (Ty_Atom p t)
  | WF_All    : forall A Phi, WellFormed (b_Prod I A) Phi -> WellFormed I (Ty_All A Phi)
  | WF_Ex     : forall A Phi, WellFormed (b_Prod I A) Phi -> WellFormed I (Ty_Ex A Phi).

(* ================================================================= *)
(* 2.5 FORMULA EKVIVALENCIA                                          *)
(* ================================================================= *)

Inductive form_equiv {Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} (I : b_ty)
  : @h_ty Func Pred -> @h_ty Func Pred -> Type :=

  | FE_Atom : forall (p : Pred) (t1 t2 : @b_tm Func)
      (d1 : base_typing I t1 (pred_dom p)) (d2 : base_typing I t2 (pred_dom p)),
      base_equiv d1 d2 -> form_equiv I (Ty_Atom p t1) (Ty_Atom p t2)
  | FE_Refl : forall Phi, WellFormed I Phi -> form_equiv I Phi Phi
  | FE_Sym  : forall Phi Psi, form_equiv I Phi Psi -> form_equiv I Psi Phi
  | FE_Trans : forall Phi Psi Chi, form_equiv I Phi Psi -> form_equiv I Psi Chi -> form_equiv I Phi Chi
  | FE_Prod : forall A B A' B', form_equiv I A A' -> form_equiv I B B' -> form_equiv I (Ty_Prod A B) (Ty_Prod A' B')
  | FE_Sum  : forall A B A' B', form_equiv I A A' -> form_equiv I B B' -> form_equiv I (Ty_Sum A B) (Ty_Sum A' B')
  | FE_Arrow : forall A B A' B', form_equiv I A A' -> form_equiv I B B' -> form_equiv I (Ty_Arrow A B) (Ty_Arrow A' B')
  | FE_All  : forall D Body Body', form_equiv (b_Prod I D) Body Body' -> form_equiv I (Ty_All D Body) (Ty_All D Body')
  | FE_Ex   : forall D Body Body', form_equiv (b_Prod I D) Body Body' -> form_equiv I (Ty_Ex D Body) (Ty_Ex D Body')
  | FE_Pullback_Id : forall Phi, WellFormed I Phi -> form_equiv I (form_subst b_id Phi) Phi
  | FE_Pullback_Comp : forall J K (f g : @b_tm Func) Phi
      (df : base_typing J f K) (dg : base_typing I g J),
      WellFormed K Phi ->
      form_equiv I (form_subst g (form_subst f Phi)) (form_subst (b_comp f g) Phi)
  | FE_Pullback_Cong : forall J (f g : @b_tm Func) Phi
      (df : base_typing I f J) (dg : base_typing I g J),
      base_equiv df dg ->
      WellFormed J Phi ->
      form_equiv I (form_subst f Phi) (form_subst g Phi).

(* ================================================================= *)
(* 2.6 KONTEXTUS EKVIVALENCIA                                        *)
(* ================================================================= *)

Inductive All_WellFormed {Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} (J : b_ty) : @h_context Func Pred -> Type :=
  | AWF_Nil : All_WellFormed J nil
  | AWF_Cons : forall (Phi : @h_ty Func Pred) (G : @h_context Func Pred),
      WellFormed J Phi -> All_WellFormed J G -> All_WellFormed J (Phi :: G).

Inductive ctx_equiv {Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} (I : b_ty)
  : @h_context Func Pred -> @h_context Func Pred -> Type :=
  | CEq_Nil : ctx_equiv I [] []
  | CEq_Cons : forall Phi Psi G1 G2,
      form_equiv I Phi Psi ->
      ctx_equiv I G1 G2 ->
      ctx_equiv I (Phi :: G1) (Psi :: G2).

(* ================================================================= *)
(* 3. DUAL CONTEXT TYPING                                            *)
(* ================================================================= *)

Inductive h_typing {Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} (I : b_ty)
  : @h_context Func Pred -> @h_tm Func Pred -> @h_ty Func Pred -> Prop :=
  | HT_Var0 : forall G Phi, h_typing I (Phi :: G) (tm_var 0) Phi
  | HT_VarS : forall G Phi Psi i,
      h_typing I G (tm_var i) Phi ->
      h_typing I (Psi :: G) (tm_var (S i)) Phi
  | HT_Conv : forall G p Phi Psi,
      h_typing I G p Phi ->
      form_equiv I Phi Psi ->
      h_typing I G p Psi
  | HT_Ctx_Conv : forall G1 G2 p Phi,
      ctx_equiv I G1 G2 ->
      h_typing I G1 p Phi ->
      h_typing I G2 p Phi
  | HT_Unit : forall G, h_typing I G tm_unit Ty_Unit
  | HT_Lam : forall G p Phi Psi,
      h_typing I (Phi :: G) p Psi ->
      h_typing I G (tm_lam Phi p) (Ty_Arrow Phi Psi)
  | HT_App : forall G p1 p2 Phi Psi,
      h_typing I G p1 (Ty_Arrow Phi Psi) ->
      h_typing I G p2 Phi ->
      h_typing I G (tm_app p1 p2) Psi
  | HT_Pair : forall G p1 p2 Phi Psi,
      h_typing I G p1 Phi ->
      h_typing I G p2 Psi ->
      h_typing I G (tm_pair p1 p2) (Ty_Prod Phi Psi)
  | HT_Fst : forall G p Phi Psi,
      h_typing I G p (Ty_Prod Phi Psi) ->
      h_typing I G (tm_fst p) Phi
  | HT_Snd : forall G p Phi Psi,
      h_typing I G p (Ty_Prod Phi Psi) ->
      h_typing I G (tm_snd p) Psi
  | HT_Inl : forall G p Phi Psi,
      h_typing I G p Phi ->
      h_typing I G (tm_inl Psi p) (Ty_Sum Phi Psi)
  | HT_Inr : forall G p Phi Psi,
      h_typing I G p Psi ->
      h_typing I G (tm_inr Phi p) (Ty_Sum Phi Psi)
  | HT_Case : forall G p p1 p2 Phi Psi Chi,
      h_typing I G p (Ty_Sum Phi Psi) ->
      h_typing I (Phi :: G) p1 Chi ->
      h_typing I (Psi :: G) p2 Chi ->
      h_typing I G (tm_case p p1 p2) Chi
  | HT_Absurd : forall G p Phi,
      h_typing I G p Ty_Void ->
      h_typing I G (tm_absurd Phi p) Phi
  | HT_All_Intro : forall G p A Phi,
      h_typing (b_Prod I A) (ctx_subst b_fst G) p Phi ->
      h_typing I G (tm_all_intro p) (Ty_All A Phi)
  | HT_All_Elim : forall G p A Phi f,
      h_typing I G p (Ty_All A Phi) ->
      base_typing I f A ->
      h_typing I G (tm_all_elim p f) (form_subst (b_pair b_id f) Phi)
  | HT_Ex_Intro : forall G p A Phi f,
      base_typing I f A ->
      h_typing I G p (form_subst (b_pair b_id f) Phi) ->
      h_typing I G (tm_ex_intro f p) (Ty_Ex A Phi)
  | HT_Ex_Elim : forall G p p2 A Phi Chi,
      h_typing I G p (Ty_Ex A Phi) ->
      h_typing (b_Prod I A) (Phi :: ctx_subst b_fst G) p2 (form_subst b_fst Chi) ->
      h_typing I G (tm_ex_elim p p2) Chi.

(* ================================================================= *)
(* 4. DUAL CONTEXT DERIVATION (Set-alapú)                            *)
(* ================================================================= *)

Inductive h_derivation {Func Pred : Type}
  `{FunctionSignature Func} `{PredicateSignature Pred} :
  b_ty -> h_context (Func:=Func) (Pred:=Pred) -> @h_tm Func Pred -> h_ty (Func:=Func) (Pred:=Pred) -> Type :=
  | HD_Var0 : forall (I : b_ty) (Phi : @h_ty Func Pred) (G : @h_context Func Pred),
      All_WellFormed I (Phi :: G) ->
      h_derivation I (Phi :: G) (tm_var 0) Phi
  | HD_VarS : forall (I : b_ty) (Phi Psi : @h_ty Func Pred) (G : @h_context Func Pred) (n : nat),
      WellFormed I Psi ->
      h_derivation I G (tm_var n) Phi ->
      h_derivation I (Psi :: G) (tm_var (S n)) Phi
  | HD_Unit : forall (I : b_ty) (G : @h_context Func Pred),
      All_WellFormed I G ->
      h_derivation I G tm_unit Ty_Unit
  | HD_Conv : forall (I : b_ty) (G : @h_context Func Pred) (p : @h_tm Func Pred) (Phi Psi : @h_ty Func Pred),
      h_derivation I G p Phi ->
      form_equiv I Phi Psi ->
      h_derivation I G p Psi
  | HD_Ctx_Conv : forall (I : b_ty) (G1 G2 : @h_context Func Pred) (p : @h_tm Func Pred) (Phi : @h_ty Func Pred),
      ctx_equiv I G1 G2 ->
      h_derivation I G1 p Phi ->
      h_derivation I G2 p Phi
  | HD_Lam : forall (I : b_ty) (G : @h_context Func Pred) (p : @h_tm Func Pred) (Phi Psi : @h_ty Func Pred),
      h_derivation I (Phi :: G) p Psi ->
      h_derivation I G (tm_lam Phi p) (Ty_Arrow Phi Psi)
  | HD_App : forall (I : b_ty) (G : @h_context Func Pred) (p1 p2 : @h_tm Func Pred) (Phi Psi : @h_ty Func Pred),
      h_derivation I G p1 (Ty_Arrow Phi Psi) ->
      h_derivation I G p2 Phi ->
      h_derivation I G (tm_app p1 p2) Psi
  | HD_Pair : forall (I : b_ty) (G : @h_context Func Pred) (p1 p2 : @h_tm Func Pred) (Phi Psi : @h_ty Func Pred),
      h_derivation I G p1 Phi ->
      h_derivation I G p2 Psi ->
      h_derivation I G (tm_pair p1 p2) (Ty_Prod Phi Psi)
  | HD_Fst : forall (I : b_ty) (G : @h_context Func Pred) (p : @h_tm Func Pred) (Phi Psi : @h_ty Func Pred),
      h_derivation I G p (Ty_Prod Phi Psi) ->
      h_derivation I G (tm_fst p) Phi
  | HD_Snd : forall (I : b_ty) (G : @h_context Func Pred) (p : @h_tm Func Pred) (Phi Psi : @h_ty Func Pred),
      h_derivation I G p (Ty_Prod Phi Psi) ->
      h_derivation I G (tm_snd p) Psi
  | HD_Inl : forall {I G p Phi Psi},
      WellFormed I Psi ->
      h_derivation I G p Phi ->
      h_derivation I G (tm_inl Psi p) (Ty_Sum Phi Psi)
  | HD_Inr : forall {I G p Phi Psi},
      WellFormed I Phi ->
      h_derivation I G p Psi ->
      h_derivation I G (tm_inr Phi p) (Ty_Sum Phi Psi)
  | HD_Case : forall (I : b_ty) (G : @h_context Func Pred) (p p1 p2 : @h_tm Func Pred) (Phi Psi Chi : @h_ty Func Pred),
      h_derivation I G p (Ty_Sum Phi Psi) ->
      h_derivation I (Phi :: G) p1 Chi ->
      h_derivation I (Psi :: G) p2 Chi ->
      h_derivation I G (tm_case p p1 p2) Chi
  | HD_Absurd : forall {I G p Phi},
      WellFormed I Phi ->
      h_derivation I G p Ty_Void ->
      h_derivation I G (tm_absurd Phi p) Phi
  | HD_All_Intro : forall (I A : b_ty) (G : @h_context Func Pred) (p : @h_tm Func Pred) (Phi : @h_ty Func Pred),
      h_derivation (b_Prod I A) (ctx_subst b_fst G) p Phi ->
      h_derivation I G (tm_all_intro p) (Ty_All A Phi)
  | HD_All_Elim : forall (I A : b_ty) (G : @h_context Func Pred) (p : @h_tm Func Pred) (Phi : @h_ty Func Pred) (f : @b_tm Func),
      h_derivation I G p (Ty_All A Phi) ->
      base_typing I f A ->
      h_derivation I G (tm_all_elim p f) (form_subst (b_pair b_id f) Phi)
  | HD_Ex_Intro : forall (I A : b_ty) (G : @h_context Func Pred) (p : @h_tm Func Pred) (Phi : @h_ty Func Pred) (f : @b_tm Func),
      base_typing I f A ->
      h_derivation I G p (form_subst (b_pair b_id f) Phi) ->
      h_derivation I G (tm_ex_intro f p) (Ty_Ex A Phi)
  | HD_Ex_Elim : forall (I A : b_ty) (G : @h_context Func Pred) (p p2 : @h_tm Func Pred) (Phi Chi : @h_ty Func Pred),
      h_derivation I G p (Ty_Ex A Phi) ->
      h_derivation (b_Prod I A) (Phi :: ctx_subst b_fst G) p2 (form_subst b_fst Chi) ->
      h_derivation I G (tm_ex_elim p p2) Chi.

Fixpoint tm_subst {Func Pred : Type}
  (f : @b_tm Func) (p : @h_tm Func Pred) : @h_tm Func Pred :=
  match p with
  | tm_unit => tm_unit
  | tm_var i => tm_var i
  | tm_lam Phi p' => tm_lam (form_subst f Phi) (tm_subst f p')
  | tm_app p1 p2 => tm_app (tm_subst f p1) (tm_subst f p2)
  | tm_pair p1 p2 => tm_pair (tm_subst f p1) (tm_subst f p2)
  | tm_fst p' => tm_fst (tm_subst f p')
  | tm_snd p' => tm_snd (tm_subst f p')
  | tm_inl Psi p' => tm_inl (form_subst f Psi) (tm_subst f p')
  | tm_inr Phi p' => tm_inr (form_subst f Phi) (tm_subst f p')
  | tm_case p' p1 p2 => tm_case (tm_subst f p') (tm_subst f p1) (tm_subst f p2)
  | tm_absurd Phi p' => tm_absurd (form_subst f Phi) (tm_subst f p')
  | tm_all_intro p' => tm_all_intro (tm_subst (b_subst_ext f) p')
  | tm_all_elim p' t => tm_all_elim (tm_subst f p') (b_comp t f)
  | tm_ex_intro t p' => tm_ex_intro (b_comp t f) (tm_subst f p')
  | tm_ex_elim p1 p2 => tm_ex_elim (tm_subst f p1) (tm_subst (b_subst_ext f) p2)
  end.
