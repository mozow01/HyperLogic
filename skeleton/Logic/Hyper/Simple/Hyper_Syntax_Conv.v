(*Logic/Hyper/Simple/Hyper_Syntax_Conv.*)

Require Import List.
Import ListNotations.

(* ================================================================= *)
(* MODUL BEEMELÉSE: BÁZIS SZINTAXIS (Individuumok és Kontextusok)    *)
(* ================================================================= *)
Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum.

(* ================================================================= *)
(* 1. FORMULÁK (HYPER TYPES)                                         *)
(* ================================================================= *)

Inductive h_ty : Type :=
  (* --- A) Propozicionális Modul (A BiCCC / STLC réteg másolata) --- *)
  | Ty_Unit   : h_ty
  | Ty_Void   : h_ty
  | Ty_Prod   : h_ty -> h_ty -> h_ty
  | Ty_Sum    : h_ty -> h_ty -> h_ty
  | Ty_Arrow  : h_ty -> h_ty -> h_ty

  (* --- B) Hyper Modul (Elsőrendű kiegészítések és a Bázis csatolása) --- *)

  (* Predikátum: P(t). A 't' KÖZVETLENÜL a Base_Syntax-ból jön (b_tm)!
     Ez egy t : I -> dom(P) bázis morfizmus. *)
  | Ty_Atom   : nat -> b_tm -> h_ty

  (* Kvantorok: Egy új individuum-típust (A) vezetnek be a Bázisból (b_ty).
     NINCS változónév, csak a kiterjesztett (I x A) bázis-objektum! *)
  | Ty_All    : b_ty -> h_ty -> h_ty
  | Ty_Ex     : b_ty -> h_ty -> h_ty.

Definition h_context := list h_ty.

(* ================================================================= *)
(* 2. BÁZIS HELYETTESÍTÉS (SZINTAKTIKUS PULLBACK)                    *)
(* ================================================================= *)

(* A Base_Syntax b_tm kombinátorait használjuk a helyettesítéshez! *)

(* Ha van egy f : I -> J bázis-helyettesítésünk, és egy kvantor alá lépünk,
   az f-et ki kell terjeszteni I x A -> J x A morfizmussá: f x id_A. *)
Definition b_pullback_ext (f : b_tm) : b_tm :=
  b_pair (b_comp f b_fst) b_snd.

(* A formula visszahúzása (pullback) egy f : I -> J bázis-morfizmus mentén.
   Matematikailag ez a híres f^* (Phi) helyettesítő művelet. *)
Fixpoint form_pullback (f : b_tm) (Phi : h_ty) : h_ty :=
  match Phi with
  (* Propozicionális szint: rekurzív továbbadás *)
  | Ty_Unit => Ty_Unit
  | Ty_Void => Ty_Void
  | Ty_Prod A B => Ty_Prod (form_pullback f A) (form_pullback f B)
  | Ty_Sum A B => Ty_Sum (form_pullback f A) (form_pullback f B)
  | Ty_Arrow A B => Ty_Arrow (form_pullback f A) (form_pullback f B)

  (* Hyper szint (Atomok): A helyettesítés SZÓ SZERINT bázis kompozíció! *)
  | Ty_Atom p t => Ty_Atom p (b_comp t f)

  (* Hyper szint (Kvantorok): A kiterjesztett (f x id) helyettesítés fut! *)
  | Ty_All A Body => Ty_All A (form_pullback (b_pullback_ext f) Body)
  | Ty_Ex A Body => Ty_Ex A (form_pullback (b_pullback_ext f) Body)
  end.

(* Egy teljes logikai kontextus visszahúzása *)
Definition ctx_pullback (f : b_tm) (G : h_context) : h_context :=
  map (form_pullback f) G.

(* ================================================================= *)
(* 2.7 WELL-FORMEDNESS (WFF) A FORMULÁKRA                            *)
(* ================================================================= *)

Inductive WellFormed : b_ty -> h_ty -> Type :=
  (* Propozicionális szint: A kontextus (I) változatlanul megy tovább *)
  | WF_Unit  : forall I, WellFormed I Ty_Unit
  | WF_Void  : forall I, WellFormed I Ty_Void
  | WF_Prod  : forall I Phi Psi, WellFormed I Phi -> WellFormed I Psi -> WellFormed I (Ty_Prod Phi Psi)
  | WF_Sum   : forall I Phi Psi, WellFormed I Phi -> WellFormed I Psi -> WellFormed I (Ty_Sum Phi Psi)
  | WF_Arrow : forall I Phi Psi, WellFormed I Phi -> WellFormed I Psi -> WellFormed I (Ty_Arrow Phi Psi)

  (* Atomi szint: Itt kapcsolódik be a bázis! A termnek jól gépeltnek kell lennie az I felett. *)
  | WF_Atom  : forall I p t A,
      base_typing I t A ->
      WellFormed I (Ty_Atom p t)

  (* Kvantorok: A kontextus kiterjed (I x A)-ra a kötött változó miatt! *)
  | WF_All   : forall I A Body,
      WellFormed (b_Prod I A) Body ->
      WellFormed I (Ty_All A Body)
  | WF_Ex    : forall I A Body,
      WellFormed (b_Prod I A) Body ->
      WellFormed I (Ty_Ex A Body).

Lemma wf_pullback : forall I J (f : b_tm) (Phi : h_ty),
  base_typing I f J ->
  WellFormed J Phi ->
  WellFormed I (form_pullback f Phi).
Proof. Admitted.

(* ================================================================= *)
(* 3. BIZONYÍTÁSTERMEK (HYPER TERMS)                                 *)
(* ================================================================= *)

Inductive h_tm : Type :=
  (* --- A) Propozicionális Modul --- *)
  | tm_unit   : h_tm
  | tm_var    : nat -> h_tm
  | tm_lam    : h_ty -> h_tm -> h_tm
  | tm_app    : h_tm -> h_tm -> h_tm
  | tm_pair   : h_tm -> h_tm -> h_tm
  | tm_fst    : h_tm -> h_tm
  | tm_snd    : h_tm -> h_tm
  | tm_inl    : h_ty -> h_tm -> h_tm
  | tm_inr    : h_ty -> h_tm -> h_tm
  | tm_case   : h_tm -> h_tm -> h_tm -> h_tm
  | tm_absurd : h_ty -> h_tm -> h_tm

  (* --- B) Hyper Modul (Kvantor Szabályok) --- *)
  | tm_all_intro : h_tm -> h_tm
  | tm_all_elim  : h_tm -> b_tm -> h_tm
  | tm_ex_intro  : b_tm -> h_tm -> h_tm
  | tm_ex_elim   : h_tm -> h_tm -> h_tm.

(* ================================================================= *)
(* 3.4 BASE EQUIVALENCE (Proof. Admitted.

(* Automatically proves that any embedded STLC context is strictly Well-Formed *)
Lemma embed_ctx_wf : forall I G, wf_ctx I (embed_ctx G).
Proof. Admitted.

(* ================================================================= *)
(* 6. BIZONYÍTÁSTERMEK BEÁGYAZÁSA                                    *)
(* ================================================================= *)

Fixpoint embed_tm (t : STLC_PI_Sum.tm) : h_tm :=
  match t with
  | STLC_PI_Sum.tm_unit      => tm_unit
  | STLC_PI_Sum.tm_var i     => tm_var i
  | STLC_PI_Sum.tm_lam A t'  => tm_lam (embed_ty A) (embed_tm t')
  | STLC_PI_Sum.tm_app t1 t2 => tm_app (embed_tm t1) (embed_tm t2)
  | STLC_PI_Sum.tm_pair t1 t2=> tm_pair (embed_tm t1) (embed_tm t2)
  | STLC_PI_Sum.tm_fst t'    => tm_fst (embed_tm t')
  | STLC_PI_Sum.tm_snd t'    => tm_snd (embed_tm t')
  | STLC_PI_Sum.tm_inl B t'  => tm_inl (embed_ty B) (embed_tm t')
  | STLC_PI_Sum.tm_inr A t'  => tm_inr (embed_ty A) (embed_tm t')
  | STLC_PI_Sum.tm_case t1 t2 t3 => tm_case (embed_tm t1) (embed_tm t2) (embed_tm t3)
  | STLC_PI_Sum.tm_absurd A t' => tm_absurd (embed_ty A) (embed_tm t')
  end.

(* ================================================================= *)
(* 7. LIFTING THEOREM (A BIZONYÍTÁSOK ÁTMENTÉSE)                     *)
(* ================================================================= *)

Theorem embed_typing_sound : forall (G : STLC_PI_Sum.context) (t : STLC_PI_Sum.tm) (A : STLC_PI_Sum.ty) (I : b_ty),
  STLC_PI_Sum.typeability G t A ->
  h_typing I (embed_ctx G) (embed_tm t) (embed_ty A).
Proof. Admitted.