Require Import List.
Import ListNotations.

(* Importáljuk a letisztult (kombinátoros) bázis szintaxist *)
Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.

(* ================================================================= *)
(* 1. FORMULÁK (HYPER TYPES)                                         *)
(* ================================================================= *)

Inductive h_ty : Type :=
  (* --- BiCCC Logikai Operátorok --- *)
  | Ty_Unit   : h_ty
  | Ty_Void   : h_ty
  | Ty_Prod   : h_ty -> h_ty -> h_ty
  | Ty_Sum    : h_ty -> h_ty -> h_ty
  | Ty_Arrow  : h_ty -> h_ty -> h_ty

  (* --- Elsőrendű kiegészítések (Kapcsolat a Bázissal) --- *)
  
  (* Predikátum: P(t). A 't' egy bázis morfizmus: I -> dom(P) *)
  | Ty_Atom   : nat -> b_tm -> h_ty  
  
  (* Kvantorok: Egy új individuum-típust (A) vezetnek be. 
     NINCS változónév, csak a kiterjesztett I x A bázis-objektum! *)
  | Ty_All    : b_ty -> h_ty -> h_ty
  | Ty_Ex     : b_ty -> h_ty -> h_ty.

Definition h_context := list h_ty.

(* ================================================================= *)
(* 2. BÁZIS HELYETTESÍTÉS (CATEGORICAL PULLBACK)                     *)
(* ================================================================= *)

(* Ha van egy f : I -> J bázis-helyettesítésünk, és egy kvantor alá lépünk,
   akkor az f-et ki kell terjeszteni I x A -> J x A morfizmussá: f x id_A.
   A kombinátor bázisunkban ez pontosan a következő pár: *)
Definition b_pullback_ext (f : b_tm) : b_tm :=
  b_pair (b_comp f b_fst) b_snd.

(* A formula visszahúzása (pullback) egy f : I -> J bázis-morfizmus mentén.
   Matematikailag ez az f^* (Phi) művelet. *)
Fixpoint form_pullback (f : b_tm) (Phi : h_ty) : h_ty :=
  match Phi with
  | Ty_Unit => Ty_Unit
  | Ty_Void => Ty_Void
  | Ty_Prod A B => Ty_Prod (form_pullback f A) (form_pullback f B)
  | Ty_Sum A B => Ty_Sum (form_pullback f A) (form_pullback f B)
  | Ty_Arrow A B => Ty_Arrow (form_pullback f A) (form_pullback f B)
  
  (* Az atomoknál a helyettesítés SZÓ SZERINT kompozíció! *)
  | Ty_Atom p t => Ty_Atom p (b_comp t f)
  
  (* A kvantorok alatt a kiterjesztett helyettesítést (f x id) futtatjuk! *)
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
  (* --- BiCCC Konstruktorok --- *)
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
  
  (* --- Kvantor Szabályok Bizonyítástermjei --- *)
  | tm_all_intro : h_tm -> h_tm
  | tm_all_elim  : h_tm -> b_tm -> h_tm   (* Az eliminációhoz kell a b_tm witness *)
  | tm_ex_intro  : b_tm -> h_tm -> h_tm   (* Az intro-hoz kell a b_tm witness *)
  | tm_ex_elim   : h_tm -> h_tm -> h_tm.

(* ================================================================= *)
(* 4. DUAL CONTEXT TYPING (Bizonyíthatóság Prop-ban)                 *)
(* ================================================================= *)

(* Jelölés: I | Gamma |- p : Phi *)
Inductive h_typing (I : b_ty) : h_context -> h_tm -> h_ty -> Prop :=

  (* --- Struktúrális Szabályok (De Bruijn a Gamma-ra) --- *)
  | HT_Var0 : forall G Phi,
      h_typing I (Phi :: G) (tm_var 0) Phi

  | HT_VarS : forall G Phi Psi i,
      h_typing I G (tm_var i) Phi ->
      h_typing I (Psi :: G) (tm_var (S i)) Phi

  (* --- BiCCC Szabályok (Az 'I' bázis passzív marad) --- *)
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

  (* --- Kvantor Szabályok (Itt él a Dual Context varázslat!) --- *)

  (* ALL Intro: A bázist I x A-ra növeljük. A kontextust visszahúzzuk pi_1 mentén (Weakening) *)
  | HT_All_Intro : forall G p A Phi,
      h_typing (b_Prod I A) (ctx_pullback b_fst G) p Phi ->
      h_typing I G (tm_all_intro p) (Ty_All A Phi)

  (* ALL Elim: f : I -> A morfizmussal specializáljuk a tételt. 
     A <id_I, f> bázismorfizmussal húzzuk vissza a formulát I-re! *)
  | HT_All_Elim : forall G p A Phi f,
      h_typing I G p (Ty_All A Phi) ->
      base_typing I f A ->
      h_typing I G (tm_all_elim p f) (form_pullback (b_pair b_id f) Phi)

  (* EX Intro: f : I -> A morfizmussal adunk egy tanút. *)
  | HT_Ex_Intro : forall G p A Phi f,
      base_typing I f A ->
      h_typing I G p (form_pullback (b_pair b_id f) Phi) ->
      h_typing I G (tm_ex_intro f p) (Ty_Ex A Phi)

  (* EX Elim: Ha Phi(A) implikálja Chi-t az I x A bázison, akkor Ex(A).Phi is implikálja Chi-t I-n. *)
  | HT_Ex_Elim : forall G p p2 A Phi Chi,
      h_typing I G p (Ty_Ex A Phi) ->
      h_typing (b_Prod I A) (Phi :: ctx_pullback b_fst G) p2 (form_pullback b_fst Chi) ->
      h_typing I G (tm_ex_elim p p2) Chi.

 
(* ================================================================= *)
(* 3.5. PREDICATE SIGNATURES & WELL-FORMEDNESS (Set-ben!)            *)
(* ================================================================= *)

(* A szignatúra osztály, ami biztosítja az axióma-mentes (zöld) kódot.
   Megmondja, hogy az n-edik predikátum milyen bázis-objektumot vár. *)
Class Signature := {
  pred_arity : nat -> b_ty
}.

(* formula_wf I Phi : Bizonyítja, hogy Phi egy helyes formula az 'I' bázis felett. *)
Inductive formula_wf {Sig : Signature} (I : b_ty) : h_ty -> Set :=
  | WF_Unit : formula_wf I Ty_Unit
  | WF_Void : formula_wf I Ty_Void
  | WF_Prod : forall A B, formula_wf I A -> formula_wf I B -> formula_wf I (Ty_Prod A B)
  | WF_Sum  : forall A B, formula_wf I A -> formula_wf I B -> formula_wf I (Ty_Sum A B)
  | WF_Arr  : forall A B, formula_wf I A -> formula_wf I B -> formula_wf I (Ty_Arrow A B)
  
  (* AZ ATOM: t egy bázis morfizmus az 'I' kontextusból a predikátum által elvárt típusba! *)
  | WF_Atom : forall p t,
      base_typing I t (pred_arity p) -> 
      formula_wf I (Ty_Atom p t)
      
  (* KVANTOROK: A bázis-kontextust (I) kiterjesztjük a szorzattal (I x A) *)
  | WF_All  : forall A Phi,
      formula_wf (b_Prod I A) Phi -> 
      formula_wf I (Ty_All A Phi)
      
  | WF_Ex   : forall A Phi,
      formula_wf (b_Prod I A) Phi -> 
      formula_wf I (Ty_Ex A Phi).

(* Logikai kontextus (Gamma) jól-formáltsága *)
Inductive context_wf {Sig : Signature} (I : b_ty) : h_context -> Set :=
  | CWF_Nil  : context_wf I nil
  | CWF_Cons : forall Phi G, formula_wf I Phi -> context_wf I G -> context_wf I (Phi :: G).

(* ================================================================= *)
(* 4. DUAL CONTEXT DERIVATION (Set-ben a Soundnesshez!)              *)
(* ================================================================= *)

(* Jelölés: I | Gamma |- p : Phi *)
Inductive h_derivation {Sig : Signature} (I : b_ty) : h_context -> h_tm -> h_ty -> Set :=

  (* --- Struktúrális Szabályok (De Bruijn a Gamma-ra) --- *)
  | HD_Var0 : forall G Phi,
      context_wf I (Phi :: G) ->
      h_derivation I (Phi :: G) (tm_var 0) Phi

  | HD_VarS : forall G Phi Psi i,
      h_derivation I G (tm_var i) Phi ->
      formula_wf I Psi ->
      h_derivation I (Psi :: G) (tm_var (S i)) Phi

  (* --- BiCCC Szabályok (Az 'I' bázis passzív marad) --- *)
  | HD_Unit : forall G,
      context_wf I G ->
      h_derivation I G tm_unit Ty_Unit

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
      formula_wf I Psi ->
      h_derivation I G (tm_inl Psi p) (Ty_Sum Phi Psi)

  | HD_Inr : forall G p Phi Psi,
      formula_wf I Phi ->
      h_derivation I G p Psi ->
      h_derivation I G (tm_inr Phi p) (Ty_Sum Phi Psi)

  | HD_Case : forall G p p1 p2 Phi Psi Chi,
      h_derivation I G p (Ty_Sum Phi Psi) ->
      h_derivation I (Phi :: G) p1 Chi ->
      h_derivation I (Psi :: G) p2 Chi ->
      h_derivation I G (tm_case p p1 p2) Chi

  | HD_Absurd : forall G p Phi,
      h_derivation I G p Ty_Void ->
      formula_wf I Phi ->
      h_derivation I G (tm_absurd Phi p) Phi

  (* --- Kvantor Szabályok (Itt él a Dual Context varázslat!) --- *)

  (* ALL Intro: A bázist I x A-ra növeljük. *)
  | HD_All_Intro : forall G p A Phi,
      h_derivation (b_Prod I A) (ctx_pullback b_fst G) p Phi ->
      h_derivation I G (tm_all_intro p) (Ty_All A Phi)

  (* ALL Elim: f : I -> A morfizmussal specializáljuk a tételt. *)
  | HD_All_Elim : forall G p A Phi f,
      h_derivation I G p (Ty_All A Phi) ->
      base_typing I f A ->
      h_derivation I G (tm_all_elim p f) (form_pullback (b_pair b_id f) Phi)

  (* EX Intro: f : I -> A morfizmussal adunk egy tanút. *)
  | HD_Ex_Intro : forall G p A Phi f,
      base_typing I f A ->
      h_derivation I G p (form_pullback (b_pair b_id f) Phi) ->
      h_derivation I G (tm_ex_intro f p) (Ty_Ex A Phi)

  (* EX Elim: Ha Phi(A) implikálja Chi-t az I x A bázison, akkor Ex(A).Phi is implikálja Chi-t I-n. *)
  | HD_Ex_Elim : forall G p p2 A Phi Chi,
      h_derivation I G p (Ty_Ex A Phi) ->
      h_derivation (b_Prod I A) (Phi :: ctx_pullback b_fst G) p2 (form_pullback b_fst Chi) ->
      h_derivation I G (tm_ex_elim p p2) Chi.

(* ================================================================= *)
(* 5. PROOF IRRELEVANCE (A szálakon a logika Thin kategória)         *)
(* ================================================================= *)

Inductive h_equiv_rel {Sig : Signature} (I : b_ty) : h_tm -> h_tm -> Prop :=
  | PI_rule : forall G Phi p q 
      (d1 : h_derivation I G p Phi) 
      (d2 : h_derivation I G q Phi),
      h_equiv_rel I p q.
 