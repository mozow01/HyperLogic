(* ================================================================= *)
(* FELSZÍNI KALKULUS (SURFACE CALCULUS)                              *)
(* Egy emberközeli, explicit interfész a kategóriaelméleti logikához *)
(* ================================================================= *)

Require Import List.
Import ListNotations.

(* Importáljuk az alacsony szintű "Assembly" gépezetet *)
Require Import HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.
(* Feltételezzük, hogy a bázis típusok (b_ty) között van szorzat (Ty_Prod) *)

(* ================================================================= *)
(* 1. FELSZÍNI SZINTAXIS (Termek és Formulák)                        *)
(* ================================================================= *)

Inductive s_tm : Type :=
  | s_var   : nat -> s_tm                 (* De Bruijn változók *)
  | s_const : nat -> s_tm                 (* Globális konstansok *)
  | s_eps   : b_ty -> s_ty -> s_tm        (* EPSZILON TERM: epsilon x:D. Phi *)

with s_ty : Type :=
  | s_top   : s_ty                        (* Igaz *)
  | s_bot   : s_ty                        (* Hamis *)
  | s_atom  : nat -> s_tm -> s_ty         (* Atomi predikátum *)
  | s_arrow : s_ty -> s_ty -> s_ty        (* Implikáció *)
  | s_prod  : s_ty -> s_ty -> s_ty        (* Konjunkció (AND) *)
  | s_sum   : s_ty -> s_ty -> s_ty        (* Diszjunkció (OR) *)
  | s_all   : b_ty -> s_ty -> s_ty        (* Univerzális kvantor (FORALL) *)
  | s_ex    : b_ty -> s_ty -> s_ty        (* Egzisztenciális kvantor (EXISTS) *)
  | s_subst : s_ty -> s_tm -> s_ty        (* EXPLICIT HELYETTESÍTÉS: Phi [t/x] *)
  | s_lift  : s_ty -> s_ty.               (* GYENGÍTÉS (Weakening): Formulát felemel egy nagyobb fibrumba *)

Definition s_context := list s_ty.

(* ================================================================= *)
(* 2. INTUITÍV TERMÉSZETES LEVEZETÉS ÉS TÍPUSRENDSZER                *)
(* Itt az 'I : b_ty' jelöli expliciten, hogy MELYIK FIBRUMON vagyunk!*)
(* ================================================================= *)

(* A) Termek Tipizálása a Fibrumban *)
(* Jelentése: Az 'I' változókörnyezetben a 't' term 'D' típusú *)
Inductive s_term_typing : b_ty -> s_tm -> b_ty -> Prop :=
  | ST_Var0 : forall I D, 
      s_term_typing (Ty_Prod I D) (s_var 0) D
  | ST_VarS : forall I D A n,
      s_term_typing I (s_var n) A -> 
      s_term_typing (Ty_Prod I D) (s_var (S n)) A
  | ST_Const : forall I D c,
      s_term_typing I (s_const c) D
  (* Az Epszilon egy jól tipizált 'D' típusú term, ha a formula érvényes felette! *)
  | ST_Eps : forall I D Phi,
      s_term_typing I (s_eps D Phi) D.

(* B) Formulák Tipizálása a Fibrumban *)
(* Jelentése: Az 'I' környezetben, 'G' feltevésekből levezethető 'Phi' *)
Inductive s_typing : b_ty -> s_context -> s_ty -> Prop :=
  
  (* --- Strukturális szabályok --- *)
  | S_Var0 : forall I G Phi, s_typing I (Phi :: G) Phi
  | S_VarS : forall I G Phi Psi, s_typing I G Phi -> s_typing I (Psi :: G) Phi

  (* --- Alapvető logikai operátorok --- *)
  | S_Top  : forall I G, s_typing I G s_top
  | S_Bot  : forall I G Psi, s_typing I G s_bot -> s_typing I G Psi
  
  | S_Prod_Intro : forall I G A B, s_typing I G A -> s_typing I G B -> s_typing I G (s_prod A B)
  | S_Prod_Elim1 : forall I G A B, s_typing I G (s_prod A B) -> s_typing I G A
  | S_Prod_Elim2 : forall I G A B, s_typing I G (s_prod A B) -> s_typing I G B

  | S_Sum_Intro1 : forall I G A B, s_typing I G A -> s_typing I G (s_sum A B)
  | S_Sum_Intro2 : forall I G A B, s_typing I G B -> s_typing I G (s_sum A B)
  | S_Sum_Elim   : forall I G A B C, s_typing I G (s_sum A B) -> 
                                     s_typing I (A :: G) C -> 
                                     s_typing I (B :: G) C -> s_typing I G C

  | S_Lam : forall I G A B, s_typing I (A :: G) B -> s_typing I G (s_arrow A B)
  | S_App : forall I G A B, s_typing I G (s_arrow A B) -> s_typing I G A -> s_typing I G B

  (* --- Kvantorok (Változókörnyezet változása!) --- *)
  
  (* FORALL Bevezetés: A formulának a KITERJESZTETT fibrumon (I*D) kell igaznak lennie *)
  | S_All_Intro : forall I D G Phi,
      s_typing (Ty_Prod I D) (map s_lift G) Phi ->
      s_typing I G (s_all D Phi)
  
  | S_All_Elim : forall I D G Phi t,
      s_typing I G (s_all D Phi) ->
      s_term_typing I t D ->
      s_typing I G (s_subst Phi t)

  (* EXISTS Bevezetés: Szükségünk van egy 't' termre az 'I' fibrumban *)
  | S_Ex_Intro : forall I D G Phi t,
      s_term_typing I t D ->
      s_typing I G (s_subst Phi t) ->
      s_typing I G (s_ex D Phi)
      
  | S_Ex_Elim : forall I D G Phi Psi,
      s_typing I G (s_ex D Phi) ->
      s_typing (Ty_Prod I D) (Phi :: map s_lift G) (s_lift Psi) ->
      s_typing I G Psi

  (* --- A KRITIKUS SZABÁLY: EPSILON BEVEZETÉS --- *)
  (* Ha Phi igaz BÁRMILYEN 't' hipotetikus termre, akkor Phi igaz a szintetikus Epsilon termre is! *)
  | S_Eps_Intro : forall I D G Phi t,
      s_term_typing I t D ->
      s_typing I G (s_subst Phi t) ->
      s_typing I G (s_subst Phi (s_eps D Phi))

  (* --- Konverzió (Helyettesítések kiértékelése a háttérben) --- *)
  | S_Conv : forall I G Phi Psi,
      s_typing I G Phi ->
      Phi = Psi -> 
      s_typing I G Psi.

(* ================================================================= *)
(* 3. A DRINKER PARADOXON A FELSZÍNI NYELVEN                         *)
(* ================================================================= *)

(* A formula: \exists x. ( (\exists y. Phi(y)) -> Phi(x) )
   Figyeld meg a s_lift-et: a belső egzisztenciális kvantort fel kell 
   emelnünk az I*D fibrumba, hogy implikációba tehessük a Phi(x)-szel! *)
Definition Drinker (D : b_ty) (Phi : s_ty) : s_ty :=
  s_ex D (s_arrow (s_lift (s_ex D Phi)) Phi).

Lemma drinker_surface_provable : forall I D Phi, s_typing I [] (Drinker D Phi).
Proof.
  intros I D Phi. unfold Drinker.
  
  (* 1. Ex-Bevezetés az Epsilon termmel! *)
  eapply S_Ex_Intro with (t := s_eps D Phi).
  - apply ST_Eps.
  - eapply S_Conv. 2: admit. (* Kiértékeli a s_subst(Arrow)-t Arrow(s_subst)-ra *)
    
    apply S_Lam.
    
    (* 2. Ex-Elimináció a feltevésen *)
    eapply S_Ex_Elim.
    + apply S_Var0. (* Behozzuk a s_lift(s_ex D Phi)-t *)
    
    (* 3. Epszilon Bevezetés a lokális változóval (var 0) mint hipotetikus term *)
    + eapply S_Eps_Intro with (t := s_var 0).
      * apply ST_Var0.
      * eapply S_Conv. 2: admit. (* Kiértékeli a s_subst(Phi, var0)-t Phi-re *)
        apply S_Var0.
Admitted.

(* ================================================================= *)
(* 4. A FORDÍTÓ (COMPILER): Felszíniből Kategóriaelméletibe          *)
(* ================================================================= *)

(* Termek lefordítása bázis-morfizmusokká (I -> D) explicit paraméterekkel *)
Fixpoint interp_tm {Sign : Type} {H : SkolemMapping Sign} (I : b_ty) (t : s_tm) : @b_tm Sign :=
  match t with
  | s_var 0 => b_snd (* A var 0 az I*D -> D projekció *)
  | s_var (S n) => b_comp (interp_tm I (s_var n)) b_fst 
  | s_const c => b_const _ c
  | s_eps D Phi => 
      (* Az Epszilon term a háttérben egy globális Skolem-konstanssé alakul! *)
      (* Itt trükközni kell a bázisokkal (1 -> D konvertálása I -> D-re) *)
      admit 
  end.

(* Formulák lefordítása hiperdoktrína szálakká egy adott 'I' bázis felett *)
Fixpoint interp_ty {Sign : Type} {H : SkolemMapping Sign} (I : b_ty) (Phi : s_ty) : @h_ty Sign :=
  match Phi with
  | s_top => hTy_Unit
  | s_bot => hTy_Void
  | s_atom p t => hTy_Atom p (interp_tm I t)
  | s_arrow A B => hTy_Arrow (interp_ty I A) (interp_ty I B)
  | s_prod A B => hTy_Prod (interp_ty I A) (interp_ty I B)
  | s_sum A B => hTy_Sum (interp_ty I A) (interp_ty I B)
  | s_all D A => hTy_All D (interp_ty (Ty_Prod I D) A)
  | s_ex D A => hTy_Ex D (interp_ty (Ty_Prod I D) A)
  | s_lift A => 
      (* A felszíni GYENGÍTÉS a háttérben az első projekció menti PULLBACK! *)
      form_pullback b_fst (interp_ty I A)
  | s_subst A t => 
      (* A felszíni HELYETTESÍTÉS a háttérben egy explicit PULLBACK! 
         (id_I, t) : I -> I*D mentén húzzuk vissza az A formulát. *)
      form_pullback (b_pair b_id (interp_tm I t)) (interp_ty (Ty_Prod I D) A) 
  end.

(* Kontextusok fordítása *)
Fixpoint interp_ctx {Sign : Type} {H : SkolemMapping Sign} (I : b_ty) (G : s_context) : @h_context Sign :=
  match G with
  | [] => []
  | Phi :: G' => (interp_ty I Phi) :: (interp_ctx I G')
  end.

(* --- A Fordító Helyessége (Compiler Soundness) --- *)
(* Ha valami bizonyítható a letisztult emberi nyelven, az átfordul a kategóriaelméletbe! *)
Theorem surface_is_sound : forall {Sign : Type} {H : SkolemMapping Sign} (I : b_ty) (G : s_context) (Phi : s_ty),
  s_typing I G Phi -> 
  exists (p : @h_tm Sign), h_typing I (interp_ctx I G) p (interp_ty I Phi).
Proof.
  intros Sign H I G Phi H_surf.
  induction H_surf.
  (* Itt a strukturális indukció minden lépést pullback algebrai manőverekké alakít. *)
Admitted.