(*Logic/Hyper/Epsilon/Hyper_Syntax.*)

Require Import List.
Import ListNotations.
Require Import HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum.

(* ================================================================= *)
(* 1. FORMULÁK (A {Sign} paraméter végigvitele)                      *)
(* ================================================================= *)

Inductive h_ty {Sign : Type} : Type :=
  | Ty_Unit   : h_ty
  | Ty_Void   : h_ty
  | Ty_Prod   : h_ty -> h_ty -> h_ty
  | Ty_Sum    : h_ty -> h_ty -> h_ty
  | Ty_Arrow  : h_ty -> h_ty -> h_ty
  (* A (Sign:=Sign) helyett a @ operátort használjuk: *)
  | Ty_Atom   : nat -> @b_tm Sign -> h_ty
  | Ty_All    : b_ty -> h_ty -> h_ty
  | Ty_Ex     : b_ty -> h_ty -> h_ty.

Definition h_context {Sign : Type} := list (@h_ty Sign).

(* ... (b_pullback_ext, form_pullback, ctx_pullback marad a régi,
   csak az implicit {Sign} paraméterrel kiegészítve) ... *)

(* ================================================================= *)
(* 1.5 AZ ORÁKULUM OSZTÁLY (TYPECLASS)                               *)
(* ================================================================= *)

(* Ez a Class fogja be a Gödel-számozást / Skolemizációt *)
Class SkolemMapping (Sign : Type) := {
  (* A függvény, ami kijelöl egy egyedi azonosítót a szignatúrában *)
  skolem_index : forall (A : b_ty), @h_ty Sign -> Sign ;

  (* A Gödel-számozás injektivitása (Névütközések kizárása) *)
  skolem_inj : forall A B Phi Psi,
                 skolem_index A Phi = skolem_index B Psi ->
                 A = B /\ Phi = Psi
}.

(* ================================================================= *)
(* 2. BIZONYÍTÁSTERMEK                                               *)
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
  (* ÚJ EPSZILON TERMEK: *)
  | tm_eps_intro : @b_tm Sign -> h_tm -> h_tm
  | tm_eps_elim  : h_tm -> h_tm -> h_tm.

(* ================================================================= *)
(* 2. BÁZIS HELYETTESÍTÉS (SZINTAKTIKUS PULLBACK)                    *)
(* ================================================================= *)

(* A b_pullback_ext megkapja a {Sign} paramétert és a @ hivatkozást *)
Definition b_pullback_ext {Sign : Type} (f : @b_tm Sign) : @b_tm Sign :=
  b_pair (b_comp f b_fst) b_snd.

(* A formula visszahúzása (pullback) egy f : I -> J bázis-morfizmus mentén.
   Matematikailag ez a híres f^* (Phi) helyettesítő művelet. *)
Fixpoint form_pullback {Sign : Type} (f : @b_tm Sign) (Phi : @h_ty Sign) : @h_ty Sign :=
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
Definition ctx_pullback {Sign : Type} (f : @b_tm Sign) (G : @h_context Sign) : @h_context Sign :=
  map (form_pullback f) G.

Declare Scope surface_scope.

Notation "Phi .[ t ]" := (form_pullback (b_pair b_id t) Phi) (at level 40, left associativity) : surface_scope.
(* Epszilon jelölés *)
Notation "'ε' D , Phi" := (b_const D (skolem_index D Phi)) (at level 50) : surface_scope.

Open Scope surface_scope.

(* ================================================================= *)
(* 2.7 WELL-FORMEDNESS (WFF) A FORMULÁKRA                            *)
(* ================================================================= *)

Inductive WellFormed {Sign : Type} : b_ty -> @h_ty Sign -> Type :=
  (* Propozicionális szint: A kontextus (I) változatlanul megy tovább *)
  | WF_Unit  : forall I, WellFormed I Ty_Unit
  | WF_Void  : forall I, WellFormed I Ty_Void
  | WF_Prod  : forall I Phi Psi, WellFormed I Phi -> WellFormed I Psi -> WellFormed I (Ty_Prod Phi Psi)
  | WF_Sum   : forall I Phi Psi, WellFormed I Phi -> WellFormed I Psi -> WellFormed I (Ty_Sum Phi Psi)
  | WF_Arrow : forall I Phi Psi, WellFormed I Phi -> WellFormed I Psi -> WellFormed I (Ty_Arrow Phi Psi)

  (* Atomi szint: Itt kapcsolódik be a bázis! A termnek jól gépeltnek kell lennie az I felett. *)
  | WF_Atom  : forall I p (t : @b_tm Sign) A,
      @base_typing Sign I t A ->
      WellFormed I (Ty_Atom p t)

  (* Kvantorok: A kontextus kiterjed (I x A)-ra a kötött változó miatt! *)
  | WF_All   : forall I A Body,
      WellFormed (b_Prod I A) Body ->
      WellFormed I (Ty_All A Body)
  | WF_Ex    : forall I A Body,
      WellFormed (b_Prod I A) Body ->
      WellFormed I (Ty_Ex A Body).

Lemma wf_pullback : forall {Sign : Type} I J (f : @b_tm Sign) (Phi : @h_ty Sign),
  @base_typing Sign I f J ->
  WellFormed J Phi ->
  WellFormed I (form_pullback f Phi).
Proof. Admitted.

(* ================================================================= *)
(* 2.5 FORMULA EKVIVALENCIA (Már a WFF és a Bázis kontextus védelmében!) *)
(* ================================================================= *)

Inductive form_equiv {Sign : Type} `{SkolemMapping Sign} (I : b_ty) : @h_ty Sign -> @h_ty Sign -> Type :=

  | FE_Atom : forall p (t1 t2 : @b_tm Sign) A
                     (d1 : @base_typing Sign I t1 A)
                     (d2 : @base_typing Sign I t2 A),
      @base_equiv Sign I A t1 t2 d1 d2 ->
      form_equiv I (Ty_Atom p t1) (Ty_Atom p t2)

  (* Strukturális szabályok (Alapeseteknél megköveteljük a WFF-et!) *)
  | FE_Refl : forall Phi,
      WellFormed I Phi ->
      form_equiv I Phi Phi

  | FE_Sym  : forall Phi Psi,
      form_equiv I Phi Psi ->
      form_equiv I Psi Phi

  | FE_Trans: forall Phi Psi Chi,
      form_equiv I Phi Psi ->
      form_equiv I Psi Chi ->
      form_equiv I Phi Chi

  (* Kongruencia a logikai kötőszavakra *)
  | FE_Prod : forall A B A' B', form_equiv I A A' -> form_equiv I B B' -> form_equiv I (Ty_Prod A B) (Ty_Prod A' B')
  | FE_Sum  : forall A B A' B', form_equiv I A A' -> form_equiv I B B' -> form_equiv I (Ty_Sum A B) (Ty_Sum A' B')
  | FE_Arrow: forall A B A' B', form_equiv I A A' -> form_equiv I B B' -> form_equiv I (Ty_Arrow A B) (Ty_Arrow A' B')

  (* Kvantorok: Az ekvivalenciát a kiterjesztett (I x D) kontextusban vizsgáljuk! *)
  | FE_All  : forall D Body Body',
      form_equiv (b_Prod I D) Body Body' ->
      form_equiv I (Ty_All D Body) (Ty_All D Body')

  | FE_Ex   : forall D Body Body',
      form_equiv (b_Prod I D) Body Body' ->
      form_equiv I (Ty_Ex D Body) (Ty_Ex D Body')

 (* Beck-Chevalley epszilon lift - Általánosítva bármely g morfizmusra! *)
  | FE_Eps_Lift : forall J (g : @b_tm Sign) D Phi (dg : @base_typing Sign I g J),
      WellFormed (b_Prod J D) Phi ->
      form_equiv I ((form_pullback (b_pullback_ext g) Phi) .[ ε D, form_pullback (b_pullback_ext g) Phi ])
                   (form_pullback g (Phi .[ ε D, Phi ]))
  (* --- FIBRÁCIÓS FUNKTOR SZABÁLYOK (WFF premisszákkal!) --- *)

  | FE_Pullback_Id : forall Phi,
      WellFormed I Phi ->
      form_equiv I (form_pullback b_id Phi) Phi

  | FE_Pullback_Comp : forall J K (f g : @b_tm Sign) Phi
                              (df : base_typing J f K) (dg : base_typing I g J),
      WellFormed K Phi ->
      form_equiv I (form_pullback g (form_pullback f Phi)) (form_pullback (b_comp f g) Phi)

  (* ÍME A VARÁZSLAT: Nincs több I_curr vs I probléma, a gépelés az I-ből indul! *)
  | FE_Pullback_Cong : forall J (f g : @b_tm Sign) Phi
                              (df : base_typing I f J) (dg : base_typing I g J),
      @base_equiv Sign I J f g df dg ->
      WellFormed J Phi ->
      form_equiv I (form_pullback f Phi) (form_pullback g Phi).

(* ================================================================= *)
(* 3. DUAL CONTEXT TYPING (Az Epsilon Szabályokkal!)                 *)
(* ================================================================= *)

(* A típusolás most már megköveteli, hogy legyen a környezetben egy Orákulum! *)
Inductive h_typing {Sign : Type} `{SkolemMapping Sign} (I : b_ty) : @h_context Sign -> @h_tm Sign -> @h_ty Sign -> Prop :=

   (* --- Strukturális Szabályok --- *)
  | HT_Var0 : forall G Phi,
      h_typing I (Phi :: G) (tm_var 0) Phi

  | HT_VarS : forall G Phi Psi i,
      h_typing I G (tm_var i) Phi ->
      h_typing I (Psi :: G) (tm_var (S i)) Phi

  | HT_Conv : forall G p Phi Psi,
      h_typing I G p Phi ->
      form_equiv I Phi Psi ->   (* <--- IDE KELL AZ I *)
      h_typing I G p Psi
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

  (* Hagyományos Egzisztenciális Intro (Összehasonlításképp) *)
  | HT_Ex_Intro : forall G p A Phi f,
      base_typing I f A ->
      h_typing I G p (form_pullback (b_pair b_id f) Phi) ->
      h_typing I G (tm_ex_intro f p) (Ty_Ex A Phi)

  (* Hagyományos Egzisztenciális Elim (Összehasonlításképp) *)
  | HT_Ex_Elim : forall G p p2 A Phi Chi,
      h_typing I G p (Ty_Ex A Phi) ->
      h_typing (b_Prod I A) (Phi :: ctx_pullback b_fst G) p2 (form_pullback b_fst Chi) ->
      h_typing I G (tm_ex_elim p p2) Chi

  (* --- ÚJ: INTENZIONÁLIS EPSZILON SZABÁLYOK --- *)

  (* EPSZILON INTRO: Pontosan mint az Ex_Intro, de (Ty_Ex A Phi) helyett
     behelyettesítjük az Orákulum által adott konstanst a formulába! *)
  | HT_Eps_Intro : forall G p A Phi f,
      base_typing I f A ->
      h_typing I G p (form_pullback (b_pair b_id f) Phi) ->
      h_typing I G (tm_eps_intro f p)
                   (form_pullback (b_pair b_id (b_const A (skolem_index A Phi))) Phi)

  (* EPSZILON ELIM: Pontosan mint az Ex_Elim, de a bal oldali premisszában
     (Ty_Ex A Phi) helyett a behelyettesített epszilon-formula áll! *)
  | HT_Eps_Elim : forall G p p2 A Phi Chi,
      h_typing I G p (form_pullback (b_pair b_id (b_const A (skolem_index A Phi))) Phi) ->
      h_typing (b_Prod I A) (Phi :: ctx_pullback b_fst G) p2 (form_pullback b_fst Chi) ->
      h_typing I G (tm_eps_elim p p2) Chi.

Inductive h_derivation {Sign : Type} `{SkolemMapping Sign} (I : b_ty) : @h_context Sign -> @h_tm Sign -> @h_ty Sign -> Type :=

   (* --- Strukturális Szabályok --- *)
  | HD_Var0 : forall G Phi,
      h_derivation I (Phi :: G) (tm_var 0) Phi

  | HD_VarS : forall G Phi Psi i,
      h_derivation I G (tm_var i) Phi ->
      h_derivation I (Psi :: G) (tm_var (S i)) Phi

  (* --- ÚJ: KONVERZIÓS SZABÁLY (h_derivation szinten) --- *)
 | HD_Conv : forall G p Phi Psi,
      h_derivation I G p Phi ->
      form_equiv I Phi Psi ->   (* <--- IDE IS KELL AZ I *)
      h_derivation I G p Psi
  (* --- Propozicionális Modul (Az 'I' bázis passzív marad) --- *)
  | HD_Unit : forall G,
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

  (* --- Hyper Modul (Dual Context interakció a Bázissal!) --- *)

  (* ALL Intro: A bázist megnöveljük (I x A)-ra.
     A kontextust visszahúzzuk a pi_1 mentén (Weakening) *)
  | HD_All_Intro : forall G p A Phi,
      h_derivation (b_Prod I A) (ctx_pullback b_fst G) p Phi ->
      h_derivation I G (tm_all_intro p) (Ty_All A Phi)

  (* ALL Elim: f : I -> A bázis-morfizmussal (b_typing) specializálunk.
     A form_pullback <id_I, f> húzza vissza a formulát I-re! *)
  | HD_All_Elim : forall G p A Phi f,
      h_derivation I G p (Ty_All A Phi) ->
      base_typing I f A ->
      h_derivation I G (tm_all_elim p f) (form_pullback (b_pair b_id f) Phi)

  (* Hagyományos Egzisztenciális Intro (Összehasonlításképp) *)
  | HD_Ex_Intro : forall G p A Phi f,
      base_typing I f A ->
      h_derivation I G p (form_pullback (b_pair b_id f) Phi) ->
      h_derivation I G (tm_ex_intro f p) (Ty_Ex A Phi)

  (* Hagyományos Egzisztenciális Elim (Összehasonlításképp) *)
  | HD_Ex_Elim : forall G p p2 A Phi Chi,
      h_derivation I G p (Ty_Ex A Phi) ->
      h_derivation (b_Prod I A) (Phi :: ctx_pullback b_fst G) p2 (form_pullback b_fst Chi) ->
      h_derivation I G (tm_ex_elim p p2) Chi

  (* --- ÚJ: INTENZIONÁLIS EPSZILON SZABÁLYOK --- *)

  (* EPSZILON INTRO: Pontosan mint az Ex_Intro, de (Ty_Ex A Phi) helyett
     behelyettesítjük az Orákulum által adott konstanst a formulába! *)
  | HD_Eps_Intro : forall G p A Phi f,
      base_typing I f A ->
      h_derivation I G p (form_pullback (b_pair b_id f) Phi) ->
      h_derivation I G (tm_eps_intro f p)
                   (form_pullback (b_pair b_id (b_const A (skolem_index A Phi))) Phi)

  (* EPSZILON ELIM: Pontosan mint az Ex_Elim, de a bal oldali premisszában
     (Ty_Ex A Phi) helyett a behelyettesített epszilon-formula áll! *)
  | HD_Eps_Elim : forall G p p2 A Phi Chi,
      h_derivation I G p (form_pullback (b_pair b_id (b_const A (skolem_index A Phi))) Phi) ->
      h_derivation (b_Prod I A) (Phi :: ctx_pullback b_fst G) p2 (form_pullback b_fst Chi) ->
      h_derivation I G (tm_eps_elim p p2) Chi.

(* ================================================================= *)
(* 5. PROOF IRRELEVANCE EKVIVALENCIA                                 *)
(* ================================================================= *)

(* Ez mondja ki, hogy a szálak Thin kategóriák: minden, ami azonos
   típussal (Phi) bizonyítható, az triviálisan ekvivalens! *)
(* FIGYELEM: Mivel h_typing-ot hívunk, be kell hozni a SkolemMapping-et! *)
Inductive h_equiv_rel {Sign : Type} `{SkolemMapping Sign} (I : b_ty) : @h_tm Sign -> @h_tm Sign -> Prop :=
  | PI_rule : forall G Phi p q,
      h_typing I G p Phi ->
      h_typing I G q Phi ->
      h_equiv_rel I p q.

(* ================================================================= *)
(* TÍPUSOK (FORMULÁK) BEÁGYAZÁSA (EMBEDDING)                *)
(* ================================================================= *)

Fixpoint embed_ty {Sign : Type} (A : STLC_PI_Sum.ty) : @h_ty Sign :=
  match A with
  (* Az STLC atomi kijelentéseit 0-változós predikátumként ágyazzuk be,
     amit a bázis 'b_unit' (üres/triviális) termjére alkalmazunk!
     Itt expliciten meg kell adni a Sign-t a @b_unit-nek! *)
  | STLC_PI_Sum.Ty_Atomic p  => Ty_Atom p (@b_unit Sign)
  | STLC_PI_Sum.Ty_Unit      => Ty_Unit
  | STLC_PI_Sum.Ty_Void      => Ty_Void
  | STLC_PI_Sum.Ty_Arrow A B => Ty_Arrow (embed_ty A) (embed_ty B)
  | STLC_PI_Sum.Ty_Prod A B  => Ty_Prod (embed_ty A) (embed_ty B)
  | STLC_PI_Sum.Ty_Sum A B   => Ty_Sum (embed_ty A) (embed_ty B)
  end.

(* Egy teljes logikai kontextus lefordítása *)
Definition embed_ctx {Sign : Type} (G : STLC_PI_Sum.context) : @h_context Sign :=
  map embed_ty G.

(* ================================================================= *)
(* 2. BIZONYÍTÁSTERMEK BEÁGYAZÁSA                                    *)
(* ================================================================= *)

Fixpoint embed_tm {Sign : Type} (t : STLC_PI_Sum.tm) : @h_tm Sign :=
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
(* FIGYELEM: A {Sign} és `{SkolemMapping Sign} a "forall" elé került,
   így a Coq tudja, hogy a globális környezetből kell vennie őket. *)
Theorem embed_typing_sound {Sign : Type} `{SkolemMapping Sign} :
  forall (G : STLC_PI_Sum.context) (t : STLC_PI_Sum.tm) (A : STLC_PI_Sum.ty) (I : b_ty),
  STLC_PI_Sum.typeability G t A ->
  h_typing I (embed_ctx G) (embed_tm t) (embed_ty A).
Proof. Admitted.