(*Logic/Hyper/Simple/Hyper_Syntax.*)

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
  (* Az eliminációhoz a Bázisból kérünk egy 'witness' morfizmust (b_tm)! *)
  | tm_all_elim  : h_tm -> b_tm -> h_tm   
  | tm_ex_intro  : b_tm -> h_tm -> h_tm   
  | tm_ex_elim   : h_tm -> h_tm -> h_tm.

(* ================================================================= *)
(* 4. DUAL CONTEXT TYPING (Bizonyíthatóság)                          *)
(* ================================================================= *)

(* Jelölés: I | Gamma |- p : Phi 
   I: b_ty (A Base kontextus, ahol az individuumok élnek)
   G: h_context (A logikai kontextus) *)
Inductive h_typing (I : b_ty) : h_context -> h_tm -> h_ty -> Prop :=

  (* --- Strukturális Szabályok --- *)
  | HT_Var0 : forall G Phi,
      h_typing I (Phi :: G) (tm_var 0) Phi

  | HT_VarS : forall G Phi Psi i,
      h_typing I G (tm_var i) Phi ->
      h_typing I (Psi :: G) (tm_var (S i)) Phi

  (* --- Propozicionális Modul (Az 'I' bázis passzív marad) --- *)
  | HT_Unit : forall G,
      h_typing I G tm_unit Ty_Unit

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

  (* --- Hyper Modul (Dual Context interakció a Bázissal!) --- *)

  (* ALL Intro: A bázist megnöveljük (I x A)-ra. 
     A kontextust visszahúzzuk a pi_1 mentén (Weakening) *)
  | HT_All_Intro : forall G p A Phi,
      h_typing (b_Prod I A) (ctx_pullback b_fst G) p Phi ->
      h_typing I G (tm_all_intro p) (Ty_All A Phi)

  (* ALL Elim: f : I -> A bázis-morfizmussal (b_typing) specializálunk.
     A form_pullback <id_I, f> húzza vissza a formulát I-re! *)
  | HT_All_Elim : forall G p A Phi f,
      h_typing I G p (Ty_All A Phi) ->
      base_typing I f A ->
      h_typing I G (tm_all_elim p f) (form_pullback (b_pair b_id f) Phi)

  (* EX Intro: f : I -> A bázis-morfizmussal adunk egy tanút. *)
  | HT_Ex_Intro : forall G p A Phi f,
      base_typing I f A ->
      h_typing I G p (form_pullback (b_pair b_id f) Phi) ->
      h_typing I G (tm_ex_intro f p) (Ty_Ex A Phi)

  (* EX Elim: Dual Context csere a bal adjungálthoz. *)
  | HT_Ex_Elim : forall G p p2 A Phi Chi,
      h_typing I G p (Ty_Ex A Phi) ->
      h_typing (b_Prod I A) (Phi :: ctx_pullback b_fst G) p2 (form_pullback b_fst Chi) ->
      h_typing I G (tm_ex_elim p p2) Chi.
      
(* ================================================================= *)
(* 4.5 DERIVATION TREES (DATA LAYER - Set)                           *)
(* ================================================================= *)

Inductive h_derivation (I : b_ty) : h_context -> h_tm -> h_ty -> Set :=

  (* --- Strukturális Szabályok --- *)
  | HD_Var0 : forall G Phi,
      h_derivation I (Phi :: G) (tm_var 0) Phi
  | HD_VarS : forall G Phi Psi i,
      h_derivation I G (tm_var i) Phi ->
      h_derivation I (Psi :: G) (tm_var (S i)) Phi

  (* --- Propozicionális Modul --- *)
  | HD_Unit : forall G, h_derivation I G tm_unit Ty_Unit
  | HD_Lam : forall G p Phi Psi,
      h_derivation I (Phi :: G) p Psi ->
      h_derivation I G (tm_lam Phi p) (Ty_Arrow Phi Psi)
  | HD_App : forall G p1 p2 Phi Psi,
      h_derivation I G p1 (Ty_Arrow Phi Psi) ->
      h_derivation I G p2 Phi ->
      h_derivation I G (tm_app p1 p2) Psi
  | HD_Pair : forall G p1 p2 Phi Psi,
      h_derivation I G p1 Phi ->
      h_derivation I G p2 Psi ->
      h_derivation I G (tm_pair p1 p2) (Ty_Prod Phi Psi)
  | HD_Fst : forall G p Phi Psi,
      h_derivation I G p (Ty_Prod Phi Psi) ->
      h_derivation I G (tm_fst p) Phi
  | HD_Snd : forall G p Phi Psi,
      h_derivation I G p (Ty_Prod Phi Psi) ->
      h_derivation I G (tm_snd p) Psi
  | HD_Inl : forall G p Phi Psi,
      h_derivation I G p Phi ->
      h_derivation I G (tm_inl Psi p) (Ty_Sum Phi Psi)
  | HD_Inr : forall G p Phi Psi,
      h_derivation I G p Psi ->
      h_derivation I G (tm_inr Phi p) (Ty_Sum Phi Psi)
  | HD_Case : forall G p p1 p2 Phi Psi Chi,
      h_derivation I G p (Ty_Sum Phi Psi) ->
      h_derivation I (Phi :: G) p1 Chi ->
      h_derivation I (Psi :: G) p2 Chi ->
      h_derivation I G (tm_case p p1 p2) Chi
  | HD_Absurd : forall G p Phi,
      h_derivation I G p Ty_Void ->
      h_derivation I G (tm_absurd Phi p) Phi

  (* --- Hyper Modul --- *)
  | HD_All_Intro : forall G p A Phi,
      h_derivation (b_Prod I A) (ctx_pullback b_fst G) p Phi ->
      h_derivation I G (tm_all_intro p) (Ty_All A Phi)
  | HD_All_Elim : forall G p A Phi f,
      h_derivation I G p (Ty_All A Phi) ->
      base_typing I f A ->
      h_derivation I G (tm_all_elim p f) (form_pullback (b_pair b_id f) Phi)
  | HD_Ex_Intro : forall G p A Phi f,
      base_typing I f A ->
      h_derivation I G p (form_pullback (b_pair b_id f) Phi) ->
      h_derivation I G (tm_ex_intro f p) (Ty_Ex A Phi)
  | HD_Ex_Elim : forall G p p2 A Phi Chi,
      h_derivation I G p (Ty_Ex A Phi) ->
      h_derivation (b_Prod I A) (Phi :: ctx_pullback b_fst G) p2 (form_pullback b_fst Chi) ->
      h_derivation I G (tm_ex_elim p p2) Chi.

(* Bridge a Set és Prop között 
Fixpoint forget_h_derivation {I G p Phi} (D : h_derivation I G p Phi) : h_typing I G p Phi.
Proof. Admitted. *)

(* ================================================================= *)
(* 5. PROOF IRRELEVANCE EKVIVALENCIA                                 *)
(* ================================================================= *)

(* Ez mondja ki, hogy a szálak Thin kategóriák: minden, ami azonos 
   típussal (Phi) bizonyítható, az triviálisan ekvivalens! *)
Inductive h_equiv_rel (I : b_ty) : h_tm -> h_tm -> Prop :=
  | PI_rule : forall G Phi p q,
      h_typing I G p Phi ->
      h_typing I G q Phi ->
      h_equiv_rel I p q.
      
(* ================================================================= *)
(*          TÍPUSOK (FORMULÁK) BEÁGYAZÁSA (EMBEDDING)                *)
(* ================================================================= *)
      
Fixpoint embed_ty (A : STLC_PI_Sum.ty) : h_ty :=
  match A with
  (* Az STLC atomi kijelentéseit 0-változós predikátumként ágyazzuk be, 
     amit a bázis 'b_unit' (üres/triviális) termjére alkalmazunk! *)
  | STLC_PI_Sum.Ty_Atomic p  => Ty_Atom p b_unit
  | STLC_PI_Sum.Ty_Unit      => Ty_Unit
  | STLC_PI_Sum.Ty_Void      => Ty_Void
  | STLC_PI_Sum.Ty_Arrow A B => Ty_Arrow (embed_ty A) (embed_ty B)
  | STLC_PI_Sum.Ty_Prod A B  => Ty_Prod (embed_ty A) (embed_ty B)
  | STLC_PI_Sum.Ty_Sum A B   => Ty_Sum (embed_ty A) (embed_ty B)
  end.

(* Egy teljes logikai kontextus lefordítása *)
Definition embed_ctx (G : STLC_PI_Sum.context) : h_context :=
  map embed_ty G.

(* ================================================================= *)
(* 2. BIZONYÍTÁSTERMEK BEÁGYAZÁSA                                    *)
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
(* 3. LIFTING THEOREM (A BIZONYÍTÁSOK ÁTMENTÉSE)                     *)
(* ================================================================= *)

(** Ez a tétel mondja ki: ami bizonyítható a propozicionális STLC-ben,
    az automatikusan bizonyítható a Hyper logikában (bármely I bázis felett)! *)
Theorem embed_typing_sound : forall (G : STLC_PI_Sum.context) (t : STLC_PI_Sum.tm) (A : STLC_PI_Sum.ty) (I : b_ty),
  STLC_PI_Sum.typeability G t A ->
  h_typing I (embed_ctx G) (embed_tm t) (embed_ty A).
Proof.
  intros G t A I H.
  
  (* Mivel a szerkezet 1-1-ben megegyezik, a Coq indukcióval 
     automatikusan végig tud menni az összes eseten! *)
  induction H.
  - apply HT_Unit.
  - apply HT_Var0.
  - apply HT_VarS. assumption.
  - apply HT_Lam. assumption.
  - eapply HT_App; eassumption.
  - apply HT_Pair; assumption.
  - eapply HT_Fst; eassumption.
  - eapply HT_Snd; eassumption.
  - apply HT_Inl; assumption.
  - apply HT_Inr; assumption.
  - eapply HT_Case; eassumption.
  - apply HT_Absurd; assumption.
Defined.