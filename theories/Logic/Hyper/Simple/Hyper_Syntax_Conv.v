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
Proof.
  intros I J f Phi Hf Hwf.
  
  (* VISSZADOBJUK I-t és f-et, hogy a kvantorok alatti indukció működjön! *)
  revert I f Hf.
  induction Hwf; intros I' f' Hf'.
  - simpl. apply WF_Unit.
  - simpl. apply WF_Void.
  - simpl. apply WF_Prod; auto.
  - simpl. apply WF_Sum; auto.
  - simpl. apply WF_Arrow; auto.
  
  - (* Atomi eset *)
    simpl. eapply WF_Atom. 
    eapply BT_Comp.
    + exact b.
    + exact Hf'.

  - (* Ty_All eset *)
    simpl. apply WF_All. apply IHHwf.
    unfold b_pullback_ext.
    eapply BT_Pair.
    + eapply BT_Comp. exact Hf'. apply BT_Fst.
    + apply BT_Snd.

  - (* Ty_Ex eset *)
    simpl. apply WF_Ex. apply IHHwf.
    unfold b_pullback_ext.
    eapply BT_Pair.
    + eapply BT_Comp. exact Hf'. apply BT_Fst.
    + apply BT_Snd.
Qed.

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
(* 3.4 BASE EQUIVALENCE (Proof Irrelevance for Base Terms)           *)
(* ================================================================= *)

Inductive base_equiv_untyped : b_tm -> b_tm -> Prop :=
  | Base_PI : forall I J t1 t2,
      base_typing I t1 J -> 
      base_typing I t2 J -> 
      base_equiv_untyped t1 t2
  | Base_Refl : forall t, base_equiv_untyped t t.

(* ================================================================= *)
(* 3.5 FORMULA EKVIVALENCIA (Már a WFF és a Bázis kontextus védelmében!) *)
(* ================================================================= *)

Inductive form_equiv (I : b_ty) : h_ty -> h_ty -> Type :=
  
  | FEQ_Atom : forall p t1 t2 A (d1 : base_typing I t1 A) (d2 : base_typing I t2 A),
      base_equiv_untyped t1 t2 ->
      form_equiv I (Ty_Atom p t1) (Ty_Atom p t2)
      
  (* Strukturális szabályok (Alapeseteknél megköveteljük a WFF-et!) *)
  | FEQ_Refl : forall Phi, 
      WellFormed I Phi -> 
      form_equiv I Phi Phi
      
  | FEQ_Sym  : forall Phi Psi, 
      form_equiv I Phi Psi -> 
      form_equiv I Psi Phi
      
  | FEQ_Trans: forall Phi Psi Chi, 
      form_equiv I Phi Psi -> 
      form_equiv I Psi Chi -> 
      form_equiv I Phi Chi
  
  (* Kongruencia a logikai kötőszavakra *)
  | FEQ_Prod : forall A B A' B', form_equiv I A A' -> form_equiv I B B' -> form_equiv I (Ty_Prod A B) (Ty_Prod A' B')
  | FEQ_Sum  : forall A B A' B', form_equiv I A A' -> form_equiv I B B' -> form_equiv I (Ty_Sum A B) (Ty_Sum A' B')
  | FEQ_Arrow: forall A B A' B', form_equiv I A A' -> form_equiv I B B' -> form_equiv I (Ty_Arrow A B) (Ty_Arrow A' B')
  
  (* Kvantorok: Az ekvivalenciát a kiterjesztett (I x D) kontextusban vizsgáljuk! *)
  | FEQ_All  : forall D Body Body', 
      form_equiv (b_Prod I D) Body Body' -> 
      form_equiv I (Ty_All D Body) (Ty_All D Body')
      
  | FEQ_Ex   : forall D Body Body', 
      form_equiv (b_Prod I D) Body Body' -> 
      form_equiv I (Ty_Ex D Body) (Ty_Ex D Body')
  
  (* --- FIBRÁCIÓS FUNKTOR SZABÁLYOK (WFF premisszákkal!) --- *)
  
  | FEQ_Pullback_Id : forall Phi, 
      WellFormed I Phi ->
      form_equiv I (form_pullback b_id Phi) Phi
      
  | FEQ_Pullback_Comp : forall J K (f g : b_tm) Phi
                              (df : base_typing J f K) (dg : base_typing I g J),
      WellFormed K Phi ->
      form_equiv I (form_pullback g (form_pullback f Phi)) (form_pullback (b_comp f g) Phi)
      
  | FEQ_Pullback_Cong : forall J (f g : b_tm) Phi 
                              (df : base_typing I f J) (dg : base_typing I g J), 
      base_equiv_untyped f g -> 
      WellFormed J Phi ->
      form_equiv I (form_pullback f Phi) (form_pullback g Phi).

(* Context Equivalence: Lifts indexed formula equivalence to lists *)
Inductive ctx_equiv (I : b_ty) : h_context -> h_context -> Type :=
  | CEQ_nil  : ctx_equiv I nil nil
  | CEQ_cons : forall Phi Psi G1 G2,
      form_equiv I Phi Psi -> 
      ctx_equiv I G1 G2 -> 
      ctx_equiv I (Phi :: G1) (Psi :: G2).

(* ================================================================= *)
(* 4. DUAL CONTEXT TYPING (Bizonyíthatóság)                          *)
(* ================================================================= *)

(* Well formed contexts *)
Inductive wf_ctx (I : b_ty) : h_context -> Type :=
  | WFC_nil  : wf_ctx I nil
  | WFC_cons : forall Phi G, WellFormed I Phi -> wf_ctx I G -> wf_ctx I (Phi :: G).


Inductive h_typing (I : b_ty) : h_context -> h_tm -> h_ty -> Prop :=

  (* --- Strukturális Szabályok --- *)
  | HT_Var0 : forall G Phi,
      wf_ctx I G -> WellFormed I Phi -> 
      h_typing I (Phi :: G) (tm_var 0) Phi

  | HT_VarS : forall G Phi Psi i,
      WellFormed I Psi -> 
      h_typing I G (tm_var i) Phi ->
      h_typing I (Psi :: G) (tm_var (S i)) Phi

  (* --- Propozicionális Modul (Az 'I' bázis passzív marad) --- *)
  | HT_Unit : forall G,
      wf_ctx I G -> 
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
      WellFormed I Psi ->                 (* <--- NEW PREMISE *)
      h_typing I G p Phi ->
      h_typing I G (tm_inl Psi p) (Ty_Sum Phi Psi)

  | HT_Inr : forall G p Phi Psi,
      WellFormed I Phi ->                 (* <--- NEW PREMISE *)
      h_typing I G p Psi ->
      h_typing I G (tm_inr Phi p) (Ty_Sum Phi Psi)

  | HT_Case : forall G p p1 p2 Phi Psi Chi,
      h_typing I G p (Ty_Sum Phi Psi) ->
      h_typing I (Phi :: G) p1 Chi ->
      h_typing I (Psi :: G) p2 Chi ->
      h_typing I G (tm_case p p1 p2) Chi

  | HT_Absurd : forall G p Phi,
      WellFormed I Phi ->                 (* <--- NEW PREMISE *)
      h_typing I G p Ty_Void ->
      h_typing I G (tm_absurd Phi p) Phi

  | HT_All_Intro : forall G p A Phi,
      wf_ctx I G ->                       (* <--- NEW PREMISE *)
      h_typing (b_Prod I A) (ctx_pullback b_fst G) p Phi ->
      h_typing I G (tm_all_intro p) (Ty_All A Phi)

  | HT_All_Elim : forall G p A Phi f,
      h_typing I G p (Ty_All A Phi) ->
      base_typing I f A ->
      h_typing I G (tm_all_elim p f) (form_pullback (b_pair b_id f) Phi)

  | HT_Ex_Intro : forall G p A Phi f,
      WellFormed (b_Prod I A) Phi ->      (* <--- NEW PREMISE *)
      base_typing I f A ->
      h_typing I G p (form_pullback (b_pair b_id f) Phi) ->
      h_typing I G (tm_ex_intro f p) (Ty_Ex A Phi)

  | HT_Ex_Elim : forall G p p2 A Phi Chi,
      WellFormed I Chi ->                 (* <--- NEW PREMISE *)
      h_typing I G p (Ty_Ex A Phi) ->
      h_typing (b_Prod I A) (Phi :: ctx_pullback b_fst G) p2 (form_pullback b_fst Chi) ->
      h_typing I G (tm_ex_elim p p2) Chi

  (* --- CONVERSION RULE --- *)
  | HT_Conv : forall G1 G2 p Phi Psi,
      ctx_equiv I G1 G2 ->
      form_equiv I Phi Psi ->
      h_typing I G1 p Phi ->
      h_typing I G2 p Psi.

(* ================================================================= *)
(* 4.5 DERIVATION TREES (DATA LAYER - Set)                           *)
(* ================================================================= *)

Inductive h_derivation (I : b_ty) : h_context -> h_tm -> h_ty -> Type :=

  (* --- Strukturális Szabályok --- *)
  | HD_Var0 : forall G Phi,
      wf_ctx I G -> WellFormed I Phi -> 
      h_derivation I (Phi :: G) (tm_var 0) Phi
  | HD_VarS : forall G Phi Psi i,
      WellFormed I Psi -> 
      h_derivation I G (tm_var i) Phi ->
      h_derivation I (Psi :: G) (tm_var (S i)) Phi

  (* --- Propozicionális Modul --- *)
  | HD_Unit : forall G, 
      wf_ctx I G -> 
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
      WellFormed I Psi ->  
      h_derivation I G p Phi ->
      h_derivation I G (tm_inl Psi p) (Ty_Sum Phi Psi)
  | HD_Inr : forall G p Phi Psi,
      WellFormed I Phi ->  
      h_derivation I G p Psi ->
      h_derivation I G (tm_inr Phi p) (Ty_Sum Phi Psi)
  | HD_Case : forall G p p1 p2 Phi Psi Chi,
      h_derivation I G p (Ty_Sum Phi Psi) ->
      h_derivation I (Phi :: G) p1 Chi ->
      h_derivation I (Psi :: G) p2 Chi ->
      h_derivation I G (tm_case p p1 p2) Chi
  | HD_Absurd : forall G p Phi,
      WellFormed I Phi ->
      h_derivation I G p Ty_Void ->
      h_derivation I G (tm_absurd Phi p) Phi

  (* --- Hyper Modul --- *)
  | HD_All_Intro : forall G p A Phi,
      wf_ctx I G ->
      h_derivation (b_Prod I A) (ctx_pullback b_fst G) p Phi ->
      h_derivation I G (tm_all_intro p) (Ty_All A Phi)
  | HD_All_Elim : forall G p A Phi f,
      h_derivation I G p (Ty_All A Phi) ->
      base_typing I f A ->
      h_derivation I G (tm_all_elim p f) (form_pullback (b_pair b_id f) Phi)
  | HD_Ex_Intro : forall G p A Phi f,
      WellFormed (b_Prod I A) Phi ->
      base_typing I f A ->
      h_derivation I G p (form_pullback (b_pair b_id f) Phi) ->
      h_derivation I G (tm_ex_intro f p) (Ty_Ex A Phi)
  | HD_Ex_Elim : forall G p p2 A Phi Chi,
      WellFormed I Chi ->
      h_derivation I G p (Ty_Ex A Phi) ->
      h_derivation (b_Prod I A) (Phi :: ctx_pullback b_fst G) p2 (form_pullback b_fst Chi) ->
      h_derivation I G (tm_ex_elim p p2) Chi
      
  (* --- CONVERSION RULE --- *)
  | HD_Conv : forall G1 G2 p Phi Psi,
      ctx_equiv I G1 G2 ->
      form_equiv I Phi Psi ->
      h_derivation I G1 p Phi ->
      h_derivation I G2 p Psi.

(* ================================================================= *)
(* 5. PROOF IRRELEVANCE EKVIVALENCIA                                 *)
(* ================================================================= *)

Inductive h_equiv_rel (I : b_ty) : h_tm -> h_tm -> Prop :=
  | PI_rule : forall G Phi p q,
      h_typing I G p Phi ->
      h_typing I G q Phi ->
      h_equiv_rel I p q.

(* ================================================================= *)
(* 5. TÍPUSOK (FORMULÁK) BEÁGYAZÁSA (EMBEDDING)                      *)
(* ================================================================= *)
      
Fixpoint embed_ty (A : STLC_PI_Sum.ty) : h_ty :=
  match A with
  | STLC_PI_Sum.Ty_Atomic p  => Ty_Atom p b_unit
  | STLC_PI_Sum.Ty_Unit      => Ty_Unit
  | STLC_PI_Sum.Ty_Void      => Ty_Void
  | STLC_PI_Sum.Ty_Arrow A B => Ty_Arrow (embed_ty A) (embed_ty B)
  | STLC_PI_Sum.Ty_Prod A B  => Ty_Prod (embed_ty A) (embed_ty B)
  | STLC_PI_Sum.Ty_Sum A B   => Ty_Sum (embed_ty A) (embed_ty B)
  end.

Definition embed_ctx (G : STLC_PI_Sum.context) : h_context :=
  map embed_ty G.

(* Automatically proves that any embedded STLC type is strictly Well-Formed *)
Lemma embed_ty_wf : forall I A, WellFormed I (embed_ty A).
Proof.
  intros I A. induction A; simpl.
  - eapply WF_Atom. apply BT_Unit.
  - apply WF_Unit.
  - apply WF_Void.
  - apply WF_Arrow; auto.
  - apply WF_Prod; auto.
  - apply WF_Sum; auto.
Qed.

(* Automatically proves that any embedded STLC context is strictly Well-Formed *)
Lemma embed_ctx_wf : forall I G, wf_ctx I (embed_ctx G).
Proof.
  intros I G. induction G; simpl.
  - apply WFC_nil.
  - apply WFC_cons.
    + apply embed_ty_wf.
    + apply IHG.
Qed.

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
Proof.
  intros G t A I H.
  induction H; simpl.
  - apply HT_Unit. apply embed_ctx_wf.
  - apply HT_Var0. 
    + apply embed_ctx_wf. 
    + apply embed_ty_wf.
  - apply HT_VarS. 
    + apply embed_ty_wf. 
    + exact IHtypeability.
  - apply HT_Lam. exact IHtypeability.
  - eapply HT_App; eassumption.
  - apply HT_Pair; assumption.
  - eapply HT_Fst; eassumption.
  - eapply HT_Snd; eassumption.
  - apply HT_Inl; [apply embed_ty_wf | assumption].
  - apply HT_Inr; [apply embed_ty_wf | assumption].
  - eapply HT_Case; eassumption.
  - apply HT_Absurd; [apply embed_ty_wf | assumption].
Defined.