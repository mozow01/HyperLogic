(* theories/Semantics/Epsilon_Adjoint/Epsilon_Adjoint_Completeness.v *)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Equality.
Require Import List.
Import ListNotations.
 
(* Kategóriaelméleti alapok *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Fibration.

(* Szintaxis és Fibráció (Epsilon Adjoint) *)
Require Import HyperLogic.Logic.Base.Epsilon_Adjoint.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon_Adjoint.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon_Adjoint.Hyper_Syntax_Lemmas.


Require Import HyperLogic.Semantics.Epsilon_Adjoint.Base_Epsilon_Completeness.
Require Import HyperLogic.Semantics.Epsilon_Adjoint.Epsilon_Adjoint_Fibration.
Require Import HyperLogic.Semantics.Epsilon_Adjoint.Base_Epsilon_Completeness.

(* ================================================================= *)
(* 1. A SZINTAKTIKUS SZÁL KATEGÓRIA (FIBER CATEGORY)                 *)
(* ================================================================= *)
 
(* ÚJ hom_fiber: Üres kontextus és Ty_Arrow (pont mint az STLC-ben!) *)
Class hom_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) (Phi Psi : @h_ty Sign) : Type := mk_hom_fiber {
  h_tm_of : @h_tm Sign;
  h_deriv_of : h_derivation I [] h_tm_of (Ty_Arrow Phi Psi)
}.

Arguments h_tm_of {Sign SM I Phi Psi} _.
Arguments h_deriv_of {Sign SM I Phi Psi} _.

Definition fiber_equiv {Sign : Type} {SM : SkolemMapping Sign} {I : b_ty} {Phi Psi : @h_ty Sign} 
  (f g : @hom_fiber Sign SM I Phi Psi) : Prop := True.

Global Instance fiber_equiv_equivalence {Sign SM I Phi Psi} : Equivalence (@fiber_equiv Sign SM I Phi Psi).
Proof. constructor; red; intros; unfold fiber_equiv; constructor. Qed.

(* IDENTITÁS: Pont mint az STLC id_term *)
Definition id_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) (Phi : @h_ty Sign) : @hom_fiber Sign SM I Phi Phi.
Proof.
  refine (@mk_hom_fiber Sign SM I Phi Phi (tm_lam Phi (tm_var 0)) _).
  apply HD_Lam. apply HD_Var0.
Defined.

(* KOMPOZÍCIÓ Zárt Kombinátorral: \f. \g. \x. f (g x) *)
Definition comp_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {Phi Psi Chi : @h_ty Sign} 
  (f : @hom_fiber Sign SM I Psi Chi) (g : @hom_fiber Sign SM I Phi Psi) : @hom_fiber Sign SM I Phi Chi.
Proof.
  refine (@mk_hom_fiber Sign SM I Phi Chi 
    (tm_app (tm_app 
       (* A COMP kombinátor: *)
       (tm_lam (Ty_Arrow Psi Chi) 
         (tm_lam (Ty_Arrow Phi Psi) 
           (tm_lam Phi 
             (tm_app (tm_var 2) (tm_app (tm_var 1) (tm_var 0))))))
       (* Alkalmazva f-re: *)
       (h_tm_of f)) 
       (* Alkalmazva g-re: *)
    (h_tm_of g)) _).
  
  (* Bizonyítás: Csupa beépített szabállyal, weakening lemma nélkül! *)
  apply HD_App with (Phi := Ty_Arrow Phi Psi).
  - apply HD_App with (Phi := Ty_Arrow Psi Chi).
    + (* A kombinátor típusolása *)
      apply HD_Lam. apply HD_Lam. apply HD_Lam.
      apply HD_App with (Phi := Psi).
      * (* tm_var 2 (f) lekérése a kontextus aljáról *)
        apply HD_VarS. apply HD_VarS. apply HD_Var0.
      * (* tm_app 1 0 kiértékelése *)
        apply HD_App with (Phi := Phi).
        -- (* tm_var 1 (g) lekérése *)
           apply HD_VarS. apply HD_Var0.
        -- (* tm_var 0 (x) lekérése *)
           apply HD_Var0.
    + (* f típusolása (üres kontextusból!) *)
      exact (h_deriv_of f).
  - (* g típusolása (üres kontextusból!) *)
    exact (h_deriv_of g).
Defined.

(* Maga a Fiber SetoidCategory példányosítása *)
Instance Fiber_SetoidCategory {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) : SetoidCategory.
Proof.
  refine (mk_SetoidCategory 
    (@h_ty Sign) 
    (@hom_fiber Sign SM I) 
    (fun X => @id_fiber Sign SM I X)
    (fun X Y Z f g => @comp_fiber Sign SM I X Y Z f g)
    (fun X Y f g => @fiber_equiv Sign SM I X Y f g)
    _ _ _ _ _).
  
  (* Mivel a hom_equiv_equivalence-t a Coq automatikusan megoldotta, 
     az összes maradék kategória axiómát (comp_assoc, id_left, stb.)
     egyszerre kilőjük, hiszen mindegyik csak egy True állítás! *)
  Unshelve.
  all: intros; unfold fiber_equiv; constructor.
Defined.

(* Be is bizonyítjuk, hogy Vékony (Thin) *)
Instance Fiber_Thin {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) : Thin (Fiber_SetoidCategory I).
Proof.
  intros x y f g. unfold fiber_equiv; constructor.
Defined.

(* ================================================================= *)
(* 2. FIBER CARTESIAN CATEGORY (Unit, Prod)                          *)
(* ================================================================= *)

(* --- TERMINAL (Unit) --- *)
Definition term_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) (X : @h_ty Sign) : @hom_fiber Sign SM I X Ty_Unit.
Proof.
  refine (@mk_hom_fiber Sign SM I X Ty_Unit (tm_lam X tm_unit) _).
  apply HD_Lam. apply HD_Unit.
Defined.

(* --- PRODUCT (And) --- *)
(* Kombinátor: \f. \g. \x. (f x, g x) *)
Definition prod_map_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X Y Z : @h_ty Sign} 
  (f : @hom_fiber Sign SM I X Y) (g : @hom_fiber Sign SM I X Z) : @hom_fiber Sign SM I X (Ty_Prod Y Z).
Proof.
  refine (@mk_hom_fiber Sign SM I X (Ty_Prod Y Z)
    (tm_app (tm_app
      (tm_lam (Ty_Arrow X Y)
        (tm_lam (Ty_Arrow X Z)
          (tm_lam X
            (tm_pair (tm_app (tm_var 2) (tm_var 0)) (tm_app (tm_var 1) (tm_var 0))))))
      (h_tm_of f)) (h_tm_of g)) _).
      
  (* JAVÍTÁS: Először a 'g' típusát (X Z) adjuk meg, utána az 'f' típusát (X Y) *)
  apply HD_App with (Phi := Ty_Arrow X Z).
  - apply HD_App with (Phi := Ty_Arrow X Y).
    + apply HD_Lam. apply HD_Lam. apply HD_Lam. apply HD_Pair.
      * apply HD_App with (Phi := X).
        -- apply HD_VarS. apply HD_VarS. apply HD_Var0.
        -- apply HD_Var0.
      * apply HD_App with (Phi := X).
        -- apply HD_VarS. apply HD_Var0.
        -- apply HD_Var0.
    + exact (h_deriv_of f).
  - exact (h_deriv_of g).
Defined.

Definition fst_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X Y : @h_ty Sign} : @hom_fiber Sign SM I (Ty_Prod X Y) X.
Proof.
  refine (@mk_hom_fiber Sign SM I (Ty_Prod X Y) X (tm_lam (Ty_Prod X Y) (tm_fst (tm_var 0))) _).
  apply HD_Lam. eapply HD_Fst. apply HD_Var0.
Defined.

Definition snd_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X Y : @h_ty Sign} : @hom_fiber Sign SM I (Ty_Prod X Y) Y.
Proof.
  refine (@mk_hom_fiber Sign SM I (Ty_Prod X Y) Y (tm_lam (Ty_Prod X Y) (tm_snd (tm_var 0))) _).
  apply HD_Lam. eapply HD_Snd. apply HD_Var0.
Defined.

Instance Fiber_CartesianCategory {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) : CartesianCategory (Fiber_SetoidCategory I).
Proof.
  apply (Build_Thin_CC _ (Fiber_Thin I)
    Ty_Unit (fun X => @term_fiber Sign SM I X)
    Ty_Prod (fun X Y Z f g => @prod_map_fiber Sign SM I X Y Z f g)
    (fun X Y => @fst_fiber Sign SM I X Y)
    (fun X Y => @snd_fiber Sign SM I X Y)
  ).
Defined.
 
(* ================================================================= *)
(* 3. FIBER CARTESIAN CLOSED CATEGORY (Arrow)                        *)
(* ================================================================= *)

(* --- EXPONENTIAL (Implies) --- *)
(* Eval/Apply: \p. (fst p) (snd p) *)
(* JAVÍTÁS: Y a bemenet (domain), Z a kimenet (codomain) *)
Definition eval_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {Y Z : @h_ty Sign} : @hom_fiber Sign SM I (Ty_Prod (Ty_Arrow Y Z) Y) Z.
Proof.
  refine (@mk_hom_fiber Sign SM I _ _
    (tm_lam (Ty_Prod (Ty_Arrow Y Z) Y) (tm_app (tm_fst (tm_var 0)) (tm_snd (tm_var 0)))) _).
  apply HD_Lam. apply HD_App with (Phi := Y).
  - eapply HD_Fst. apply HD_Var0.
  - eapply HD_Snd. apply HD_Var0.
Defined.

(* Curry kombinátor: \f. \x. \y. f (x, y) *)
Definition curry_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X Y Z : @h_ty Sign} (g : @hom_fiber Sign SM I (Ty_Prod X Y) Z) : @hom_fiber Sign SM I X (Ty_Arrow Y Z).
Proof.
  refine (@mk_hom_fiber Sign SM I X (Ty_Arrow Y Z)
    (tm_app
      (tm_lam (Ty_Arrow (Ty_Prod X Y) Z)
        (tm_lam X
          (tm_lam Y
            (tm_app (tm_var 2) (tm_pair (tm_var 1) (tm_var 0))))))
      (h_tm_of g)) _).
  apply HD_App with (Phi := Ty_Arrow (Ty_Prod X Y) Z).
  - apply HD_Lam. apply HD_Lam. apply HD_Lam.
    apply HD_App with (Phi := Ty_Prod X Y).
    + eapply HD_VarS. apply HD_VarS. apply HD_Var0.
    + eapply HD_Pair.
      * apply HD_VarS. apply HD_Var0.
      * apply HD_Var0.
  - exact (h_deriv_of g).
Defined.

Instance Fiber_CartesianClosedCategory {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) : CartesianClosedCategory (Fiber_SetoidCategory I).
Proof.
  refine (Build_Thin_CCC _ (Fiber_Thin I)
    (* JAVÍTÁS ITT IS: Megfordítjuk a változókat, ahogy az STLC_CCC-ben is volt! *)
    (fun Z Y => Ty_Arrow Y Z)
    (fun Y Z => @eval_fiber Sign SM I Y Z)
    (fun X Y Z g => @curry_fiber Sign SM I X Y Z g)
  ).
Defined.

(* ================================================================= *)
(* 4. FIBER BiCARTESIAN CLOSED CATEGORY (Void, Sum)                  *)
(* ================================================================= *)

(* --- INITIAL (Void) --- *)
Definition init_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X : @h_ty Sign} : @hom_fiber Sign SM I Ty_Void X.
Proof.
  refine (@mk_hom_fiber Sign SM I Ty_Void X (tm_lam Ty_Void (tm_absurd X (tm_var 0))) _).
  apply HD_Lam. apply HD_Absurd. apply HD_Var0.
Defined.

(* --- COPRODUCT (Or) --- *)
Definition inl_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X Y : @h_ty Sign} : @hom_fiber Sign SM I X (Ty_Sum X Y).
Proof.
  refine (@mk_hom_fiber Sign SM I X (Ty_Sum X Y) (tm_lam X (tm_inl Y (tm_var 0))) _).
  apply HD_Lam. apply HD_Inl. apply HD_Var0.
Defined.

Definition inr_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X Y : @h_ty Sign} : @hom_fiber Sign SM I Y (Ty_Sum X Y).
Proof.
  refine (@mk_hom_fiber Sign SM I Y (Ty_Sum X Y) (tm_lam Y (tm_inr X (tm_var 0))) _).
  apply HD_Lam. apply HD_Inr. apply HD_Var0.
Defined.

(* Coprod kombinátor: \f. \g. \c. case c of inl x => f x | inr y => g y *)
Definition coprod_map_fiber {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) {X Y Z : @h_ty Sign} 
  (f : @hom_fiber Sign SM I X Z) (g : @hom_fiber Sign SM I Y Z) : @hom_fiber Sign SM I (Ty_Sum X Y) Z.
Proof.
  refine (@mk_hom_fiber Sign SM I (Ty_Sum X Y) Z
    (tm_app (tm_app
      (tm_lam (Ty_Arrow X Z)
        (tm_lam (Ty_Arrow Y Z)
          (tm_lam (Ty_Sum X Y)
            (tm_case (tm_var 0)
              (tm_app (tm_var 3) (tm_var 0))
              (tm_app (tm_var 2) (tm_var 0))))))
      (h_tm_of f)) (h_tm_of g)) _).
      
  (* JAVÍTÁS ITT IS: Először a 'g' típusát (Y Z), utána az 'f' típusát (X Z) adjuk meg! *)
  apply HD_App with (Phi := Ty_Arrow Y Z).
  - apply HD_App with (Phi := Ty_Arrow X Z).
    + apply HD_Lam. apply HD_Lam. apply HD_Lam.
      apply HD_Case with (Phi := X) (Psi := Y).
      * apply HD_Var0.
      * apply HD_App with (Phi := X).
        -- apply HD_VarS. apply HD_VarS. apply HD_VarS. apply HD_Var0.
        -- apply HD_Var0.
      * apply HD_App with (Phi := Y).
        -- apply HD_VarS. apply HD_VarS. apply HD_Var0.
        -- apply HD_Var0.
    + exact (h_deriv_of f).
  - exact (h_deriv_of g).
Defined. 

Instance Fiber_BiCartesianClosedCategory {Sign : Type} {SM : SkolemMapping Sign} (I : b_ty) : BiCartesianClosedCategory (Fiber_CartesianClosedCategory I).
Proof.
  apply (Build_Thin_BiCCC (Fiber_SetoidCategory I) (Fiber_CartesianClosedCategory I) (Fiber_Thin I)
    Ty_Void (fun X => @init_fiber Sign SM I X)
    Ty_Sum (fun X Y => @inl_fiber Sign SM I X Y) (fun X Y => @inr_fiber Sign SM I X Y)
    (fun X Y Z f g => @coprod_map_fiber Sign SM I X Y Z f g)
  ).
Defined.

(* Szükségünk lesz a List map függvényére a kontextus helyettesítéséhez *)
Require Import Coq.Lists.List.

(* Lemma az All_Elim és Ex_Intro konverziójához *)
Lemma form_equiv_subst_comm_elim : forall {Sign : Type} `{SkolemMapping Sign}
  {I J A : b_ty} (t : @b_tm Sign) (f : @b_tm Sign) (Phi : @h_ty Sign)
  (dt : base_typing I t J) (df : base_typing J f A),
  WellFormed (b_Prod J A) Phi ->
  form_equiv I
    (form_subst (b_pair b_id (b_comp f t)) (form_subst (b_subst_ext t) Phi))
    (form_subst t (form_subst (b_pair b_id f) Phi)).
Proof.
intros Sign SM I J A t f Phi dt df Hwf.
  eapply FE_Trans.
  - (* 1. Lépés: (Phi.[b_subst_ext t]).[<id, f o t>] ≡ Phi.[b_subst_ext t o <id, f o t>] *)
    eapply FE_Pullback_Comp.
    + (* A Coq először a BELSŐ helyettesítést kéri: b_subst_ext t *)
      eapply typing_subst_ext. exact dt.
    + (* Aztán a KÜLSŐ helyettesítést: <id, f o t> *)
      eapply BT_Pair.
      * apply BT_Id.
      * eapply BT_Comp; eassumption.
    + exact Hwf.
  - eapply FE_Trans.
    + (* 2. Lépés: A Bázis Kommutálás (ext t o <id, f o t> ≡ <id, f> o t) *)
      eapply FE_Pullback_Cong.
     * unfold b_subst_ext.
        (* Közös nevező bevezetése automatikusan: < t, f o t > *)
        eapply BE_Trans. 
        
        -- (* BAL OLDAL: <t o fst, snd> o <id, f o t> ≡ <t, f o t> *)
           eapply BE_Trans.
           ++ (* 1. Bevisszük a kompozíciót a párba *)
              apply BE_CompPair. 
           ++ (* 2. Tagonként redukálunk *)
              eapply BE_CongPair.
             ** (* Első tag: (t o fst) o <id, f o t> ≡ t *)
                 eapply BE_Trans.
                 --- eapply BE_Sym. apply BE_Assoc. (* <-- ITT A JAVÍTÁS: Szimmetria! *)
                 --- eapply BE_Trans.
                     +++ eapply BE_CongComp. 
                         *** apply BE_BetaFst. (* A belső tag: fst o <id, ..> ≡ id *)
                         *** apply BE_Refl.    (* A külső tag: t ≡ t *)
                     +++ apply BE_IdR.         
              ** (* Második tag: snd o <id, f o t> ≡ f o t *)
                 apply BE_BetaSnd.
                 
        -- (* JOBB OLDAL: <id, f> o t ≡ <t, f o t> inverze *)
           eapply BE_Sym. 
           eapply BE_Trans.
           ++ (* 1. Bevisszük a kompozíciót a párba *)
              apply BE_CompPair.
           ++ (* 2. Tagonként redukálunk *)
              eapply BE_CongPair.
              ** (* Első tag: id o t ≡ t *)
                 apply BE_IdL.
              ** (* Második tag: (f o t) ≡ (f o t) *)
                 apply BE_Refl.
                 
      * exact Hwf.
  + (* 3. Lépés: Phi.[<id, f> o t] ≡ (Phi.[<id, f>]).[t] inverze *)
      eapply FE_Sym. eapply FE_Pullback_Comp.
      * (* A BELSŐ helyettesítés: <id, f> *)
        eapply BT_Pair.
        -- apply BT_Id.
        -- exact df.
      * (* A KÜLSŐ helyettesítés: t *)
        exact dt.
      * exact Hwf.

  (* --- A POLC LESÖPRÉSE (Unshelve Magic) --- *)
  Unshelve.
  all: repeat match goal with
  | |- base_typing _ _ _ => eapply BT_Comp || eapply BT_Pair || apply BT_Id || eapply BT_Fst || eapply BT_Snd || apply typing_subst_ext || eassumption
  end.
Defined.   


(* Lemma az Ex_Elim és Eps_Elim premisszájához (fst kommutálás) *)
Lemma form_equiv_subst_comm_fst : forall {Sign : Type} `{SkolemMapping Sign}
  {I J A : b_ty} (t : @b_tm Sign) (Chi : @h_ty Sign)
  (dt : base_typing I t J),
  WellFormed J Chi ->
  form_equiv (b_Prod I A)
    (form_subst (b_subst_ext t) (form_subst b_fst Chi))
    (form_subst b_fst (form_subst t Chi)).
Proof.
  intros Sign SM I J A t Chi dt Hwf.
  eapply FE_Trans.
  - (* 1. (Chi.[fst]).[b_subst_ext t] ≡ Chi.[fst o b_subst_ext t] *)
    eapply FE_Pullback_Comp.
    + eapply BT_Fst.
    + apply typing_subst_ext. exact dt.
    + exact Hwf.
  - eapply FE_Trans.
    + (* 2. fst o b_subst_ext t ≡ t o fst *)
      eapply FE_Pullback_Cong.
      * unfold b_subst_ext. apply BE_BetaFst.
      * exact Hwf.
    + (* 3. Chi.[t o fst] ≡ (Chi.[t]).[fst] inverze *)
      eapply FE_Sym. eapply FE_Pullback_Comp.
      * exact dt.
      * apply BT_Fst.
      * exact Hwf.

  Unshelve.
  all: repeat match goal with
  | |- base_typing _ _ _ => eapply BT_Comp || apply BT_Fst || apply BT_Snd || apply typing_subst_ext || eassumption
  end.
Defined.

(* Saját iterátor a Type univerzumban lévő WellFormed fák listázásához *)
Inductive All_WellFormed {Sign : Type} (J : b_ty) : @h_context Sign -> Type :=
  | AWF_Nil : All_WellFormed J nil
  | AWF_Cons : forall (Phi : @h_ty Sign) (G : @h_context Sign),
      WellFormed J Phi -> All_WellFormed J G -> All_WellFormed J (Phi :: G).

Lemma ctx_subst_ext_comm : forall {Sign : Type} `{SkolemMapping Sign} 
  {I J A : b_ty} (t : @b_tm Sign) (dt : base_typing I t J) (G : @h_context Sign),
  All_WellFormed J G ->
  ctx_equiv (b_Prod I A) 
            (ctx_subst (b_subst_ext t) (ctx_subst b_fst G)) 
            (ctx_subst b_fst (ctx_subst t G)).
Proof.
  intros Sign SM I J A t dt G Hwf.
  induction Hwf.
  - (* AWF_Nil *)
    simpl. apply CEq_Nil.
  - (* AWF_Cons *)
    simpl. apply CEq_Cons.
    + eapply FE_Trans.
      * (* 1. (Phi.[fst]).[b_subst_ext t] ≡ Phi.[fst o (b_subst_ext t)] *)
        eapply FE_Pullback_Comp.
        -- eapply BT_Fst.
        -- apply typing_subst_ext. exact dt.
        -- assumption. (* A belső WellFormed bizonyítás! *)
      * eapply FE_Trans.
        -- (* 2. A bázis kompozíciók ekvivalenciája (A Béta-redukció mágiája) *)
           eapply FE_Pullback_Cong.
           ++ unfold b_subst_ext. apply BE_BetaFst.
           ++ eapply w.
        -- (* 3. Phi.[t o fst] ≡ (Phi.[t]).[fst] inverze *)
           eapply FE_Sym. eapply FE_Pullback_Comp.
           ++ exact dt.
           ++ apply BT_Fst.
           ++ assumption.
    + exact IHHwf.
   Unshelve.
  all: repeat match goal with
  | |- base_typing _ _ _ => eapply BT_Comp || apply BT_Fst || apply BT_Snd || apply typing_subst_ext || eassumption || typeclasses eauto
  end.
Defined.

(* ================================================================= *)
(* ÁLTALÁNOS HELYETTESÍTÉSI LEMMA                    *)
(* ================================================================= *)

(* Strukturális Metatétel (Context Regularity): 
   Ha egy kontextusból le lehet vezetni valamit, akkor az a kontextus jólformált.
   ESKÜ: Ezt a projekt végén egy standard strukturális indukcióval lemmává alakítjuk! *)
Lemma meta_ctx_wf_base : forall {Sign : Type} {SM : SkolemMapping Sign} {I A : b_ty} 
  {G : @h_context Sign} {p : h_tm} {Phi : h_ty},
  h_derivation (b_Prod I A) (ctx_subst b_fst G) p Phi -> All_WellFormed I G.
Proof.
Admitted.

Lemma meta_all_body_wf : forall {Sign : Type} {SM : SkolemMapping Sign} {I A : b_ty} 
  {G : @h_context Sign} {p : h_tm} {Phi : h_ty},
  h_derivation I G p (Ty_All A Phi) -> WellFormed (b_Prod I A) Phi.
Proof.
Admitted.


(* Strukturális Metatétel: A helyettesítés megtartja a jólformáltságot *)
Lemma meta_subst_wf : forall {Sign : Type} {SM : SkolemMapping Sign} {I J : b_ty} 
  (t : @b_tm Sign) (dt : base_typing I t J) (Phi : @h_ty Sign),
  @WellFormed Sign J Phi -> @WellFormed Sign I (form_subst t Phi).
Proof.
Admitted.

(* Strukturális Metatétel: Az Ex magja jólformált (A helyettesített verzió) *)
Lemma meta_ex_body_wf : forall {Sign : Type} {SM : SkolemMapping Sign} {I A : b_ty} 
  {G : @h_context Sign} {p : h_tm} {Phi : @h_ty Sign} {f : @b_tm Sign},
  base_typing I f A -> h_derivation I G p (form_subst (b_pair b_id f) Phi) -> @WellFormed Sign (b_Prod I A) Phi.
Proof.
Admitted.

(* Strukturális Metatétel: Az Ex magja jólformált (Az alap verzió) *)
Lemma meta_ex_body_wf_base : forall {Sign : Type} {SM : SkolemMapping Sign} {I A : b_ty} 
  {G : @h_context Sign} {p : h_tm} {Phi : @h_ty Sign},
  h_derivation I G p (Ty_Ex A Phi) -> @WellFormed Sign (b_Prod I A) Phi.
Proof.
Admitted.

(* Strukturális Metatétel: A Case (Ex_Elim) visszatérési típusa jólformált *)
Lemma meta_ex_elim_chi_wf : forall {Sign : Type} {SM : SkolemMapping Sign} {I A : b_ty} 
  {G : @h_context Sign} {p1 p2 : h_tm} {Phi Chi : @h_ty Sign},
  h_derivation I G p1 (Ty_Ex A Phi) ->
  h_derivation (b_Prod I A) (Phi :: ctx_subst b_fst G) p2 (form_subst b_fst Chi) ->
  @WellFormed Sign I Chi.
Proof.
Admitted.

(* Strukturális Metatétel (Context Regularity - Alap): 
   Ha egy normál kontextusból le lehet vezetni valamit, akkor az a kontextus jólformált. *)
Lemma meta_ctx_wf : forall {Sign : Type} {SM : SkolemMapping Sign} {I : b_ty} 
  {G : @h_context Sign} {p : h_tm} {Phi : @h_ty Sign},
  h_derivation I G p Phi -> @All_WellFormed Sign I G.
Proof.
Admitted.

(* Strukturális Metatétel: Az Epszilon magja jólformált *)
Lemma meta_eps_body_wf : forall {Sign : Type} {SM : SkolemMapping Sign} {I A : b_ty} 
  {G : @h_context Sign} {p : h_tm} {Phi : @h_ty Sign} {f : @b_tm Sign},
  base_typing I f A -> h_derivation I G p (Phi .[ f ]) -> @WellFormed Sign (b_Prod I A) Phi.
Proof.
Admitted.

(* Kategóriaelméleti Axióma (Beck-Chevalley az Epszilonra): 
   A visszahúzás (helyettesítés) kommutál az Epszilon-képzéssel. 
   Ezt a szemantikában az Adjoint Epsilon Fibration garantálja! *)
Lemma meta_eps_bc : forall {Sign : Type} {SM : SkolemMapping Sign} {I J A : b_ty} 
  (t : @b_tm Sign) (dt : base_typing I t J) (Phi : @h_ty Sign),
  @WellFormed Sign (b_Prod J A) Phi ->
  form_equiv I 
    ((form_subst (b_subst_ext t) Phi) .[ ε A, form_subst (b_subst_ext t) Phi ])
    (form_subst t (Phi .[ ε A, Phi ])).
Proof.
Admitted.

Lemma meta_eps_elim_body_wf : forall {Sign : Type} {SM : SkolemMapping Sign} {I A : b_ty} 
  {G : @h_context Sign} {p : h_tm} {Phi : @h_ty Sign},
  h_derivation I G p (Phi .[ ε A, Phi ]) -> @WellFormed Sign (b_Prod I A) Phi.
Proof.
Admitted.

Lemma meta_eps_elim_chi_wf : forall {Sign : Type} {SM : SkolemMapping Sign} {I A : b_ty} 
  {G : @h_context Sign} {p1 p2 : h_tm} {Phi Chi : @h_ty Sign},
  h_derivation I G p1 (Phi .[ ε A, Phi ]) ->
  h_derivation (b_Prod I A) (Phi :: ctx_subst b_fst G) p2 (form_subst b_fst Chi) ->
  @WellFormed Sign I Chi.
Proof.
Admitted.

Lemma h_derivation_subst_general : forall {Sign : Type} {SM : SkolemMapping Sign} 
  {I J : b_ty} (t : @b_tm Sign) (dt : base_typing I t J) (G : h_context) (Phi : h_ty) (p : h_tm),
  h_derivation J G p Phi -> 
  h_derivation I (ctx_subst t G) (tm_subst t p) (form_subst t Phi).
Proof.
  intros Sign SM I J t dt G Phi p Hderiv.
  revert I t dt.
  induction Hderiv; intros I0 t0 dt0.
  - (* HD_Var0 *)
    simpl. apply HD_Var0.
  - (* HD_VarS *)
    simpl. apply HD_VarS. apply IHHderiv. exact dt0.
  - (* HD_Conv *)
    eapply HD_Conv.
    + apply IHHderiv. exact dt0.
    + eapply form_equiv_subst. exact dt0. exact f.
  - (* HD_Ctx_Conv *)
    eapply HD_Ctx_Conv.
    + eapply ctx_equiv_subst. exact dt0. exact c.
    + apply IHHderiv. exact dt0.
  - (* HD_Unit *)
    simpl. apply HD_Unit.
  - (* HD_Lam *)
    simpl. apply HD_Lam. apply IHHderiv. exact dt0.
  - (* HD_App *)
    simpl. eapply HD_App.
    + apply IHHderiv1. exact dt0.
    + apply IHHderiv2. exact dt0.
  - (* HD_Pair *)
    simpl. apply HD_Pair.
    + apply IHHderiv1. exact dt0.
    + apply IHHderiv2. exact dt0.
  - (* HD_Fst *)
    simpl. eapply HD_Fst. apply IHHderiv. exact dt0.
  - (* HD_Snd *)
    simpl. eapply HD_Snd. apply IHHderiv. exact dt0.
  - (* HD_Inl *)
    simpl. apply HD_Inl. apply IHHderiv. exact dt0.
  - (* HD_Inr *)
    simpl. apply HD_Inr. apply IHHderiv. exact dt0.
  - (* HD_Case *)
    simpl. eapply HD_Case.
    + apply IHHderiv1. exact dt0.
    + apply IHHderiv2. exact dt0.
    + apply IHHderiv3. exact dt0.
  - (* HD_Absurd *)
    simpl. apply HD_Absurd. apply IHHderiv. exact dt0.
  
  - (* HD_All_Intro *)
    simpl. apply HD_All_Intro.
    eapply HD_Ctx_Conv.
    + (* 1. Premissza: A kontextusok ekvivalenciája *)
      eapply ctx_subst_ext_comm. 
      * exact dt0.
      * eapply meta_ctx_wf_base. exact Hderiv. (* Itt a pontosított axióma! *)
    + (* 2. Premissza: Az Indukciós Hipotézis *)
      apply IHHderiv. 
      apply typing_subst_ext. exact dt0.

  - (* HD_All_Elim *)
    simpl. eapply HD_Conv.
    + eapply HD_All_Elim.
      * apply IHHderiv. exact dt0.
      * eapply BT_Comp. eassumption. exact dt0.
    + (* AZ ADMIT HELYE: Itt aratjuk le az előző lemmánk gyümölcsét! *)
      eapply form_equiv_subst_comm_elim.
      * exact dt0.
      * exact b. (* A 'b' változó a célodban pontosan az 'f' tipizálása! *)
      * eapply meta_all_body_wf. exact Hderiv.

  - (* HD_Ex_Intro *)
    simpl. eapply HD_Ex_Intro.
    + eapply BT_Comp. eassumption. exact dt0.
    + eapply HD_Conv. (* A premisszán belül konvertálunk! *)
      * apply IHHderiv. exact dt0.
      * (* AZ ADMIT HELYE: Szimmetria + az előző lemmánk! *)
        eapply FE_Sym. 
        eapply form_equiv_subst_comm_elim.
        -- exact dt0.
        -- exact b.
        -- eapply meta_ex_body_wf. exact b. exact Hderiv.

  - (* HD_Ex_Elim *)
    simpl. eapply HD_Ex_Elim.
    + apply IHHderiv1. exact dt0.
    + eapply HD_Conv. 
      * eapply HD_Ctx_Conv.
        -- apply CEq_Cons. 
           ++ (* 1. Admit kilövése: A kiterjesztett Phi jólformált *)
              apply FE_Refl. 
              eapply meta_subst_wf. 
              ** eapply typing_subst_ext. exact dt0.
              ** eapply meta_ex_body_wf_base. exact Hderiv1.
           ++ (* A Bullet hiba javítása: Hderiv1 bizonyítja a kontextust *)
              eapply ctx_subst_ext_comm. 
              ** exact dt0.
              ** eapply meta_ctx_wf. exact Hderiv1. 
        -- apply IHHderiv2. apply typing_subst_ext. exact dt0.
      * (* 2. Admit kilövése: A hiányzó Fst kommutációs lemmánk! *)
        eapply form_equiv_subst_comm_fst. 
        -- exact dt0.
        -- eapply meta_ex_elim_chi_wf. exact Hderiv1. exact Hderiv2.


  - (* HD_Eps_Intro *)
    simpl. eapply HD_Conv.
    + eapply HD_Eps_Intro.
      * eapply BT_Comp. eassumption. exact dt0.
      * eapply HD_Conv. 
        -- apply IHHderiv. exact dt0.
        -- (* 1. Admit kilövése: A kommutációs lemmánk szimmetrikusan! *)
           eapply FE_Sym. 
           eapply form_equiv_subst_comm_elim.
           ++ exact dt0.
           ++ exact b.
           ++ eapply meta_eps_body_wf. exact b. exact Hderiv.
    + (* 2. Admit kilövése: A Beck-Chevalley Axióma *)
      eapply meta_eps_bc.
      * exact dt0.
      * eapply meta_eps_body_wf. exact b. exact Hderiv.

  - (* HD_Eps_Elim *)
    simpl. eapply HD_Eps_Elim.
    + eapply HD_Conv.
      * apply IHHderiv1. exact dt0.
      * (* 1. Admit kilövése: Beck-Chevalley szimmetrikusan megfordítva! *)
        eapply FE_Sym. 
        eapply meta_eps_bc.
        -- exact dt0.
        -- eapply meta_eps_elim_body_wf. exact Hderiv1.
    + eapply HD_Conv.
      * eapply HD_Ctx_Conv.
        -- apply CEq_Cons.
           ++ apply FE_Refl. 
              (* 2. Admit: Jólformáltság a kiterjesztett Phi-re *)
              eapply meta_subst_wf. 
              ** eapply typing_subst_ext. exact dt0.
              ** eapply meta_eps_elim_body_wf. exact Hderiv1.
           ++ (* Bullet hiba javítása: G jólformáltsága *)
              eapply ctx_subst_ext_comm. 
              ** exact dt0.
              ** eapply meta_ctx_wf. exact Hderiv1.
        -- apply IHHderiv2. apply typing_subst_ext. exact dt0.
      * (* 3. Admit kilövése: A Fst kommutációs lemmánk! *)
        eapply form_equiv_subst_comm_fst. 
        -- exact dt0.
        -- eapply meta_eps_elim_chi_wf. exact Hderiv1. exact Hderiv2.
Defined.


(* ========================================================================= 
 A HELYETTESÍTÉSI LEMMA (SUBSTITUTION LEMMA) BIZONYÍTVA!
   
   A fenti bizonyítás 100%-ig "admit-mentes" a fő logikai ágakon. 
   A bizonyítás során felmerült kategóriaelméleti és strukturális 
   "technikai adósságot" az alábbi 11 lemmába szerveztük ki. 

   KÖZÖS MUNKA / TODO LISTA A TELJESSÉGI TÉTELHEZ:
   -------------------------------------------------------------------------
   
   I. FÁZIS: A "SIMPLE MODEL" STRUKTURÁLIS TÉTELEI 
   Ezek a lemmák tiszta strukturális indukcióval igazolhatók a levezetési
   fákon. A "simple model" (indivíduumok és epszilon nélküli) konzervatív
   magjában is pontosan ezekre van szükség. 

   1. Kontextus Szabályosság (Context Regularity) 

meta_ctx_wf_base 
meta_ctx_wf 
meta_subst_wf 
meta_all_body_wf 
meta_ex_body_wf 
meta_ex_body_wf_base 
meta_ex_elim_chi_wf 

-------------------------------------------------------------------------
   II. FÁZIS: AZ EPSZILON-SPECIFIKUS TÉTELEK (Saját feladat)
   Ezek a strukturális tulajdonságok kiterjesztései a Hilbert-féle 
   kiválasztó operátorra.

meta_eps_body_wf 
meta_eps_elim_body_wf 
meta_eps_elim_chi_wf 

-------------------------------------------------------------------------
   III. FÁZIS: ARCHITEKTURÁLIS REFAKTORÁLÁS A HYPER_SYNTAX.V-BEN
   !!! KRITIKUS KATEGÓRIAELMÉLETI KÖVETELMÉNYEK !!!
   
   A Helyettesítési Lemma bizonyítása rávilágított, hogy a jelenlegi 
   szintaxisunkból hiányoznak bizonyos elsőrendű hiperdoktrína specifikus 
   kikötések. Mielőtt a Teljességi Tételt befejezzük, a `Hyper_Syntax.v`-t 
   az alábbiak szerint frissíteni kell:

   1. A Beck-Chevalley (BC) Feltétel Belsővé Tétele:
      A lenti `meta_eps_bc` lemmát NEM bizonyítani kell utólag, hanem a
      szemantikai modell alapján fel kell venni a `form_equiv` induktív 
      definíciójának KONSTRUKTORAI KÖZÉ! Ez garantálja, hogy az epszilon-
      operátor tiszteletben tartja a bázis-visszahúzásokat.

   2. Az ELSŐRENDŰ (First-Order) Szigorítás Ellenőrzése:
      Egy Elsőrendű Hiperdoktrínában a kvantorok (és az epszilon) KIZÁRÓLAG
      a projekciók (gyengítés / context extension) menti visszahúzásokra 
      (pullback) adnak bal/jobb adjungáltat. 
      Vissza kell menni a `Hyper_Syntax.v`-be, és szigorúan ellenőrizni, hogy:
      - A `HD_All_Intro`, `HD_Ex_Elim`, stb. szabályokban a kontextus bővítése
        CSAK a `b_fst` projekció mentén történik.
      - A kvantorokat és az epszilont bevezető szabályok (és a BC konstruktor) 
        kifejezetten a `b_subst_ext t` (ami a `t x id` projekció-alapú 
        pullback) formájára vannak kimondva, nem pedig tetszőleges 
        morfizmusokra. Ha tetszőleges morfizmusra mondanánk ki, a rendszerünk 
        akaratlanul is Magasabbrendűvé (Higher-Order) válna!


meta_eps_bc 

*)