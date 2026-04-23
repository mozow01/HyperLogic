(* theories/Logic/Hyper/Epsilon_Adjoint/Hyper_Syntax.v *)

Require Import List.
Import ListNotations.
Require Import HyperLogic.Logic.Base.Epsilon_Adjoint.Base_Syntax.
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum.

(* ================================================================= *)
(* 1. FORMULÁK                                                       *)
(* ================================================================= *)

Inductive h_ty {Sign : Type} : Type :=
  | Ty_Unit   : h_ty
  | Ty_Void   : h_ty
  | Ty_Prod   : h_ty -> h_ty -> h_ty
  | Ty_Sum    : h_ty -> h_ty -> h_ty
  | Ty_Arrow  : h_ty -> h_ty -> h_ty
  | Ty_Atom   : nat -> @b_tm Sign -> h_ty
  | Ty_All    : b_ty -> h_ty -> h_ty
  | Ty_Ex     : b_ty -> h_ty -> h_ty.

Definition h_context {Sign : Type} := list (@h_ty Sign).

(* ================================================================= *)
(* 1.5 AZ ORÁKULUM OSZTÁLY                                           *)
(* ================================================================= *)

Class SkolemMapping (Sign : Type) := {
  skolem_index : forall (A : b_ty), @h_ty Sign -> Sign ;
  skolem_inj : forall A B Phi Psi,
                 skolem_index A Phi = skolem_index B Psi ->
                 A = B /\ Phi = Psi
}.

(* ================================================================= *)
(* 2. BIZONYÍTÁSTERMEK (Explicit Epszilon termekkel)                 *)
(* ================================================================= *)

Inductive h_tm {Sign : Type} : Type :=
  | tm_unit   : h_tm
  | tm_var    : nat -> h_tm
  | tm_lam    : @h_ty Sign -> h_tm -> h_tm
  | tm_app    : h_tm -> h_tm -> h_tm
  | tm_pair   : h_tm -> h_tm -> h_tm
  | tm_fst    : h_tm -> h_tm
  | tm_snd    : h_tm -> h_tm
  | tm_inl    : @h_ty Sign -> h_tm -> h_tm
  | tm_inr    : @h_ty Sign -> h_tm -> h_tm
  | tm_case   : h_tm -> h_tm -> h_tm -> h_tm
  | tm_absurd : @h_ty Sign -> h_tm -> h_tm
  | tm_all_intro : h_tm -> h_tm
  | tm_all_elim  : h_tm -> @b_tm Sign -> h_tm
  | tm_ex_intro  : @b_tm Sign -> h_tm -> h_tm
  | tm_ex_elim   : h_tm -> h_tm -> h_tm
  | tm_eps_intro : @b_tm Sign -> h_tm -> h_tm
  | tm_eps_elim  : h_tm -> h_tm -> h_tm.

(* ================================================================= *)
(* BÁZIS HELYETTESÍTÉS ÉS PULLBACK                                   *)
(* ================================================================= *)

Definition b_subst_ext {Sign : Type} (f : @b_tm Sign) : @b_tm Sign :=
  b_pair (b_comp f b_fst) b_snd.

Fixpoint form_subst {Sign : Type} (f : @b_tm Sign) (Phi : @h_ty Sign) : @h_ty Sign :=
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

Definition ctx_subst {Sign : Type} (f : @b_tm Sign) (G : @h_context Sign) : @h_context Sign :=
  map (form_subst f) G.

Declare Scope surface_scope.
Notation "Phi .[ t ]" := (form_subst (b_pair b_id t) Phi) (at level 40, left associativity) : surface_scope.
Notation "'ε' D , Phi" := (b_const D (skolem_index D Phi)) (at level 50) : surface_scope.
Open Scope surface_scope.

(* ================================================================= *)
(* WELLFORMED FORMULAS (WFF)                                         *)
(* ================================================================= *)

Inductive WellFormed {Sign : Type} (I : b_ty) : @h_ty Sign -> Type :=
  | WF_Unit   : WellFormed I Ty_Unit
  | WF_Void   : WellFormed I Ty_Void
  | WF_Prod   : forall Phi Psi, WellFormed I Phi -> WellFormed I Psi -> WellFormed I (Ty_Prod Phi Psi)
  | WF_Sum    : forall Phi Psi, WellFormed I Phi -> WellFormed I Psi -> WellFormed I (Ty_Sum Phi Psi)
  | WF_Arrow  : forall Phi Psi, WellFormed I Phi -> WellFormed I Psi -> WellFormed I (Ty_Arrow Phi Psi)
  | WF_Atom   : forall p t A, base_typing I t A -> WellFormed I (Ty_Atom p t)
  | WF_All    : forall A Phi, WellFormed (b_Prod I A) Phi -> WellFormed I (Ty_All A Phi)
  | WF_Ex     : forall A Phi, WellFormed (b_Prod I A) Phi -> WellFormed I (Ty_Ex A Phi).

(* ================================================================= *)
(* 2.5 FORMULA EKVIVALENCIA (Az Adjungált Modellhez)                 *)
(* ================================================================= *)

Inductive form_equiv {Sign : Type} `{SkolemMapping Sign} (I : b_ty) : @h_ty Sign -> @h_ty Sign -> Type :=

  | FE_Atom : forall p (t1 t2 : @b_tm Sign) A (d1 : @base_typing Sign I t1 A) (d2 : @base_typing Sign I t2 A),
      @base_equiv Sign I A t1 t2 d1 d2 -> form_equiv I (Ty_Atom p t1) (Ty_Atom p t2)
  | FE_Refl : forall Phi, WellFormed I Phi -> form_equiv I Phi Phi
  | FE_Sym  : forall Phi Psi, form_equiv I Phi Psi -> form_equiv I Psi Phi
  | FE_Trans: forall Phi Psi Chi, form_equiv I Phi Psi -> form_equiv I Psi Chi -> form_equiv I Phi Chi
  | FE_Prod : forall A B A' B', form_equiv I A A' -> form_equiv I B B' -> form_equiv I (Ty_Prod A B) (Ty_Prod A' B')
  | FE_Sum  : forall A B A' B', form_equiv I A A' -> form_equiv I B B' -> form_equiv I (Ty_Sum A B) (Ty_Sum A' B')
  | FE_Arrow: forall A B A' B', form_equiv I A A' -> form_equiv I B B' -> form_equiv I (Ty_Arrow A B) (Ty_Arrow A' B')
  | FE_All  : forall D Body Body', form_equiv (b_Prod I D) Body Body' -> form_equiv I (Ty_All D Body) (Ty_All D Body')
  | FE_Ex   : forall D Body Body', form_equiv (b_Prod I D) Body Body' -> form_equiv I (Ty_Ex D Body) (Ty_Ex D Body')

  (* --- ÚJ: ADJUNGÁLT EPSZILON AXIÓMÁK --- *)
  | FE_Eps_Adjoint_Iso : forall A Phi,
      WellFormed (b_Prod I A) Phi ->
      form_equiv I (Ty_Ex A Phi) (Phi .[ ε A, Phi ])

  | FE_Eps_Functorial : forall A Phi Psi,
      form_equiv (b_Prod I A) Phi Psi ->
      form_equiv I (Phi .[ ε A, Phi ]) (Psi .[ ε A, Psi ])

  (* --- FIBRÁCIÓS FUNKTOR SZABÁLYOK --- *)
  | FE_Pullback_Id : forall Phi, WellFormed I Phi -> form_equiv I (form_subst b_id Phi) Phi
  | FE_Pullback_Comp : forall J K (f g : @b_tm Sign) Phi (df : base_typing J f K) (dg : base_typing I g J),
      WellFormed K Phi -> form_equiv I (form_subst g (form_subst f Phi)) (form_subst (b_comp f g) Phi)
  | FE_Pullback_Cong : forall J (f g : @b_tm Sign) Phi (df : base_typing I f J) (dg : base_typing I g J),
      @base_equiv Sign I J f g df dg -> WellFormed J Phi -> form_equiv I (form_subst f Phi) (form_subst g Phi).

(* ================================================================= *)
(* 2.6 KONTEXTUS EKVIVALENCIA (A Completenesshez)                    *)
(* ================================================================= *)

Inductive ctx_equiv {Sign : Type} `{SkolemMapping Sign} (I : b_ty) : @h_context Sign -> @h_context Sign -> Type :=
  | CEq_Nil  : ctx_equiv I [] []
  | CEq_Cons : forall Phi Psi G1 G2,
                 form_equiv I Phi Psi ->
                 ctx_equiv I G1 G2 ->
                 ctx_equiv I (Phi :: G1) (Psi :: G2).

(* ================================================================= *)
(* 3. DUAL CONTEXT TYPING                                            *)
(* ================================================================= *)

Inductive h_typing {Sign : Type} `{SkolemMapping Sign} (I : b_ty) : @h_context Sign -> @h_tm Sign -> @h_ty Sign -> Prop :=
  | HT_Var0 : forall G Phi, h_typing I (Phi :: G) (tm_var 0) Phi
  | HT_VarS : forall G Phi Psi i, h_typing I G (tm_var i) Phi -> h_typing I (Psi :: G) (tm_var (S i)) Phi

  | HT_Conv : forall G p Phi Psi, h_typing I G p Phi -> form_equiv I Phi Psi -> h_typing I G p Psi
  | HT_Ctx_Conv : forall G1 G2 p Phi, ctx_equiv I G1 G2 -> h_typing I G1 p Phi -> h_typing I G2 p Phi

  | HT_Unit : forall G, h_typing I G tm_unit Ty_Unit
  | HT_Lam : forall G p Phi Psi, h_typing I (Phi :: G) p Psi -> h_typing I G (tm_lam Phi p) (Ty_Arrow Phi Psi)
  | HT_App : forall G p1 p2 Phi Psi, h_typing I G p1 (Ty_Arrow Phi Psi) -> h_typing I G p2 Phi -> h_typing I G (tm_app p1 p2) Psi
  | HT_Pair : forall G p1 p2 Phi Psi, h_typing I G p1 Phi -> h_typing I G p2 Psi -> h_typing I G (tm_pair p1 p2) (Ty_Prod Phi Psi)
  | HT_Fst : forall G p Phi Psi, h_typing I G p (Ty_Prod Phi Psi) -> h_typing I G (tm_fst p) Phi
  | HT_Snd : forall G p Phi Psi, h_typing I G p (Ty_Prod Phi Psi) -> h_typing I G (tm_snd p) Psi
  | HT_Inl : forall G p Phi Psi, h_typing I G p Phi -> h_typing I G (tm_inl Psi p) (Ty_Sum Phi Psi)
  | HT_Inr : forall G p Phi Psi, h_typing I G p Psi -> h_typing I G (tm_inr Phi p) (Ty_Sum Phi Psi)
  | HT_Case : forall G p p1 p2 Phi Psi Chi, h_typing I G p (Ty_Sum Phi Psi) -> h_typing I (Phi :: G) p1 Chi -> h_typing I (Psi :: G) p2 Chi -> h_typing I G (tm_case p p1 p2) Chi
  | HT_Absurd : forall G p Phi, h_typing I G p Ty_Void -> h_typing I G (tm_absurd Phi p) Phi

  | HT_All_Intro : forall G p A Phi, h_typing (b_Prod I A) (ctx_subst b_fst G) p Phi -> h_typing I G (tm_all_intro p) (Ty_All A Phi)
  | HT_All_Elim : forall G p A Phi f, h_typing I G p (Ty_All A Phi) -> base_typing I f A -> h_typing I G (tm_all_elim p f) (form_subst (b_pair b_id f) Phi)

  | HT_Ex_Intro : forall G p A Phi f, base_typing I f A -> h_typing I G p (form_subst (b_pair b_id f) Phi) -> h_typing I G (tm_ex_intro f p) (Ty_Ex A Phi)
  | HT_Ex_Elim : forall G p p2 A Phi Chi, h_typing I G p (Ty_Ex A Phi) -> h_typing (b_Prod I A) (Phi :: ctx_subst b_fst G) p2 (form_subst b_fst Chi) -> h_typing I G (tm_ex_elim p p2) Chi

  (* --- INTENZIONÁLIS EPSZILON SZABÁLYOK --- *)
  | HT_Eps_Intro : forall G p A Phi f,
      base_typing I f A ->
      h_typing I G p (form_subst (b_pair b_id f) Phi) ->
      h_typing I G (tm_eps_intro f p)
                   (form_subst (b_pair b_id (b_const A (skolem_index A Phi))) Phi)

  | HT_Eps_Elim : forall G p p2 A Phi Chi,
      h_typing I G p (form_subst (b_pair b_id (b_const A (skolem_index A Phi))) Phi) ->
      h_typing (b_Prod I A) (Phi :: ctx_subst b_fst G) p2 (form_subst b_fst Chi) ->
      h_typing I G (tm_eps_elim p p2) Chi.

(* ================================================================= *)
(* 4. DUAL CONTEXT DERIVATION (Set-alapú)                            *)
(* ================================================================= *)

Inductive h_derivation {Sign : Type} `{SkolemMapping Sign} (I : b_ty) : @h_context Sign -> @h_tm Sign -> @h_ty Sign -> Type :=
  | HD_Var0 : forall G Phi, h_derivation I (Phi :: G) (tm_var 0) Phi
  | HD_VarS : forall G Phi Psi i, h_derivation I G (tm_var i) Phi -> h_derivation I (Psi :: G) (tm_var (S i)) Phi

  | HD_Conv : forall G p Phi Psi, h_derivation I G p Phi -> form_equiv I Phi Psi -> h_derivation I G p Psi
  | HD_Ctx_Conv : forall G1 G2 p Phi, ctx_equiv I G1 G2 -> h_derivation I G1 p Phi -> h_derivation I G2 p Phi

  | HD_Unit : forall G, h_derivation I G tm_unit Ty_Unit
  | HD_Lam : forall G p Phi Psi, h_derivation I (Phi :: G) p Psi -> h_derivation I G (tm_lam Phi p) (Ty_Arrow Phi Psi)
  | HD_App : forall G p1 p2 Phi Psi, h_derivation I G p1 (Ty_Arrow Phi Psi) -> h_derivation I G p2 Phi -> h_derivation I G (tm_app p1 p2) Psi
  | HD_Pair : forall G p1 p2 Phi Psi, h_derivation I G p1 Phi -> h_derivation I G p2 Psi -> h_derivation I G (tm_pair p1 p2) (Ty_Prod Phi Psi)
  | HD_Fst : forall G p Phi Psi, h_derivation I G p (Ty_Prod Phi Psi) -> h_derivation I G (tm_fst p) Phi
  | HD_Snd : forall G p Phi Psi, h_derivation I G p (Ty_Prod Phi Psi) -> h_derivation I G (tm_snd p) Psi
  | HD_Inl : forall G p Phi Psi, h_derivation I G p Phi -> h_derivation I G (tm_inl Psi p) (Ty_Sum Phi Psi)
  | HD_Inr : forall G p Phi Psi, h_derivation I G p Psi -> h_derivation I G (tm_inr Phi p) (Ty_Sum Phi Psi)
  | HD_Case : forall G p p1 p2 Phi Psi Chi, h_derivation I G p (Ty_Sum Phi Psi) -> h_derivation I (Phi :: G) p1 Chi -> h_derivation I (Psi :: G) p2 Chi -> h_derivation I G (tm_case p p1 p2) Chi
  | HD_Absurd : forall G p Phi, h_derivation I G p Ty_Void -> h_derivation I G (tm_absurd Phi p) Phi

  | HD_All_Intro : forall G p A Phi, h_derivation (b_Prod I A) (ctx_subst b_fst G) p Phi -> h_derivation I G (tm_all_intro p) (Ty_All A Phi)
  | HD_All_Elim : forall G p A Phi f, h_derivation I G p (Ty_All A Phi) -> base_typing I f A -> h_derivation I G (tm_all_elim p f) (form_subst (b_pair b_id f) Phi)

  | HD_Ex_Intro : forall G p A Phi f, base_typing I f A -> h_derivation I G p (form_subst (b_pair b_id f) Phi) -> h_derivation I G (tm_ex_intro f p) (Ty_Ex A Phi)
  | HD_Ex_Elim : forall G p p2 A Phi Chi, h_derivation I G p (Ty_Ex A Phi) -> h_derivation (b_Prod I A) (Phi :: ctx_subst b_fst G) p2 (form_subst b_fst Chi) -> h_derivation I G (tm_ex_elim p p2) Chi

  | HD_Eps_Intro : forall G p A Phi f,
      base_typing I f A ->
      h_derivation I G p (form_subst (b_pair b_id f) Phi) ->
      h_derivation I G (tm_eps_intro f p)
                   (form_subst (b_pair b_id (b_const A (skolem_index A Phi))) Phi)

  | HD_Eps_Elim : forall G p p2 A Phi Chi,
      h_derivation I G p (form_subst (b_pair b_id (b_const A (skolem_index A Phi))) Phi) ->
      h_derivation (b_Prod I A) (Phi :: ctx_subst b_fst G) p2 (form_subst b_fst Chi) ->
      h_derivation I G (tm_eps_elim p p2) Chi.
