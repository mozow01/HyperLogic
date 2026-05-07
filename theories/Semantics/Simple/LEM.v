(*theories/Semantics/Simple/LEM.v*)

Require Import Coq.Logic.Classical.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Classes.Morphisms.

(* Importáljuk az eddigi fájlokat a szintaxishoz és a kategóriákhoz *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import HyperLogic.Cat.Fibration.

Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Lemmas.
Require Import HyperLogic.Semantics.Simple.Base_Simple_Soundness.
Require Import HyperLogic.Semantics.Simple.Simple_Soundness.

(* Tegyük fel, hogy a Simple_Completeness.v-ben van a Base_SetoidCategory nat *)
Require Import HyperLogic.Semantics.Simple.Simple_Completeness.

(* ================================================================= *)
(* 1. A 3-ELEMŰ HEYTING ALGEBRA (H3)                                 *)
(* ================================================================= *)

Inductive H3 : Type := HBot | HMid | HTop.

(* Részbenrendezés: Bot <= Mid <= Top *)
Definition H3_le (x y : H3) : Prop :=
  match x, y with
  | HBot, _ => True
  | _, HTop => True
  | HMid, HMid => True
  | _, _ => False
  end.

Lemma H3_le_refl : forall x, H3_le x x. 
Proof. destruct x; simpl; exact I. Defined.

Lemma H3_le_trans : forall x y z, H3_le y z -> H3_le x y -> H3_le x z.
Proof. destruct x, y, z; simpl; tauto. Defined.

(* Logikai művelet H3-on (inf)*)
Definition H3_meet (x y : H3) : H3 :=
  match x, y with
  | HBot, _ | _, HBot => HBot
  | HTop, a | a, HTop => a
  | HMid, HMid => HMid
  end.

(* Logikai művelet H3-on (sup)*)
Definition H3_join (x y : H3) : H3 :=
  match x, y with
  | HTop, _ | _, HTop => HTop
  | HBot, a | a, HBot => a
  | HMid, HMid => HMid
  end.

(* Logikai művelet H3-on (imp)*)
Definition H3_impl (x y : H3) : H3 :=
  match x, y with
  | HBot, _ => HTop
  | HMid, HBot => HBot
  | HMid, HMid => HTop
  | HMid, HTop => HTop
  | HTop, a => a
  end.

(* A Végleges Fázisos Favágó Taktika *)
Ltac h3_crush :=
  (* 1. FÁZIS: Kvantorok behúzása és osztályok kibontása *)
  repeat intro;
  repeat match goal with
  | |- Proper _ _ => red
  | |- respectful _ _ _ _ => red
  | |- RelationClasses.Equivalence _ => split; red
  end;
  
  (* 2. FÁZIS: Újabb kvantorok behúzása és teljes kiértékelés *)
  repeat intro;
  simpl in *;
  
  (* 3. FÁZIS: A triviális célok azonnali kivégzése (Ez zárja be a 4 célodat!) *)
  try exact I;
  try constructor;
  
  (* 4. FÁZIS: Csak az maradt, ami tényleg H3_le kiértékelés. Jöhet a bontás! *)
  repeat match goal with
  | x : H3 |- _ => destruct x
  end;
  
  (* 5. FÁZIS: Utolsó simítások az esetszétválasztás után *)
  simpl in *;
  auto.
(* ================================================================= *)
(* 2. A H3 KATEGÓRIA (BiCartesian Closed)                            *)
(* ================================================================= *)

(* A Poset miatt bármely két párhuzamos morfizmus definíciósan egyenlő *)
Instance H3_Setoid : SetoidCategory.
Proof.
  refine (mk_SetoidCategory H3 H3_le
    H3_le_refl H3_le_trans (fun _ _ _ _ => True) _ _ _ _ _); h3_crush.
Defined.

Instance H3_Cartesian : CartesianCategory H3_Setoid.
Proof.
  refine (mk_CartesianCategory H3_Setoid
    HTop (fun x => _) _
    H3_meet (fun x y z f g => _) (fun x y => _) (fun x y => _)
    _ _ _ _); h3_crush.
    Unshelve. all: h3_crush.
Defined.

Instance H3_Closed : CartesianClosedCategory H3_Setoid.
Proof.
  refine (mk_CartesianClosedCategory H3_Setoid H3_Cartesian
    (fun a b => H3_impl b a) _ _   (* <--- ITT MEGFORDÍTOTTUK A BEMENETEKET! *)
    _ _ _).
  Unshelve.
  all: h3_crush.
Defined.

Instance H3_BiClosed : BiCartesianClosedCategory H3_Closed.
Proof.
  refine (mk_BiCartesianClosedCategory H3_Setoid H3_Cartesian H3_Closed
    HBot _ _
    H3_join _ _ _
    _ _ _ _).
  Unshelve.
  all: h3_crush.
Defined.


(* ================================================================= *)
(* 3. A KONSTANS H3 FIBRÁCIÓ                                         *)
(* ================================================================= *)

(* Mivel a fibráció konstans, a Pullback egyszerűen csak az Identitás funktor! *)
Instance H3_IdentityFunctor : Functor H3_Setoid H3_Setoid.
Proof.
  refine (mk_Functor H3_Setoid H3_Setoid (fun x => x) _ _ _ _).
  Unshelve.
  all: h3_crush.
Defined.

(* Az Identitás funktor saját magának bal és jobb adjungáltja is! *)
Instance H3_AdjointL : IsLeftAdjoint H3_IdentityFunctor.
Proof.
  refine (mk_IsLeftAdjoint _ _ _ (fun x => x) _ _ _ _ _).
  Unshelve.
  all: h3_crush.
Defined.

Instance H3_AdjointR : IsRightAdjoint H3_IdentityFunctor.
Proof.
  refine (mk_IsRightAdjoint _ _ _ (fun x => x) _ _ _ _ _).
  Unshelve.
  all: h3_crush.
Defined.

(* A GoodFibration felépítése: Minden paramétert eldobunk (alsóvonás), 
   és mindig az Identitás funktort és annak adjungáltjait adjuk vissza. *)
Instance H3_GoodFibration : GoodFibration (@Base_SetoidCategory nat).
Proof.
  refine {|
    Fiber := fun _ => H3_Setoid;
    fiber_is_thin := fun _ x y f g => I;
    Fiber_is_Cartesian := fun _ => H3_Cartesian;
    Fiber_is_Closed := fun _ => H3_Closed;
    Fiber_is_BiClosed := fun _ => H3_BiClosed;
    Pullback := fun _ _ _ => H3_IdentityFunctor;
    pullback_has_left_adjoint  := fun _ _ => H3_AdjointR;
    pullback_has_right_adjoint := fun _ _ => H3_AdjointL
  |}.
  Unshelve.
  all: intros; h3_crush. all: reflexivity.
Defined.

Instance H3_StrictGoodFibration : StrictGoodFibration (@Base_SetoidCategory nat) H3_GoodFibration.
Proof.
  econstructor. 
  intros X Y M1 M2 H.
  
  (* 1. Létrehozunk egy fordított egyenlőséget (M2 ≅ M1) a szimmetria használatával *)
  assert (H_sym : h_base M2 ≅ h_base M1).
  { symmetry. exact H. }
  
  (* 2. Most már ezt a megfordított bizonyítást adjuk oda a létezési kvantornak *)
  exists H_sym. 
  
  (* 3. A szál-egyenlőség (mivel Poset) továbbra is azonnal True *)
  exact I.
Defined.

(* ================================================================= *)
(* 4. A H3 HIPERMODELL                                               *)
(* ================================================================= *)

Instance H3_HyperModel : HyperModel H3_StrictGoodFibration.
Proof.
  (* Az unshelve econstructor minden elrejtett mezőt (az i_atom-ot is) aktív célként ad ki! *)
  unshelve econstructor.
  
  - (* 1. Cél: Az i_atom függvény megadása (Adat) *)
    exact (fun p t I A dt => HMid).
    
  - (* 2. Cél: Atom Pullback izomorfizmus (Bizonyítás) *)
    intros. reflexivity. 
    
  - (* 3. Cél: A bázis kategória (STLC) helyessége (Bizonyítás) *)
    intros I J f g df dg Heq. 
    apply base_soundness_equational. 
    exact Heq.
    
  - (* 4. Cél: Atom kongruencia (Bizonyítás) *)
    intros. reflexivity.
Defined.

(* ================================================================= *)
(* 5. A KIZÁRT HARMADIK CÁFOLATA                                     *)
(* ================================================================= *)

(* Egy tetszőleges P atomi formula *)
Definition P_atom (I : b_ty) : h_ty := 
  Ty_Atom 0 b_unit.

(* A formula: P V ~P *)
Definition LEM_Formula (I : b_ty) : h_ty := 
  Ty_Sum (P_atom I) (Ty_Arrow (P_atom I) Ty_Void).
  


(* Tétel: A LEM-nek nincs univerzális szemantikus bizonyítása a Hiperdoktrínában! *)
Theorem LEM_Refuted : 
  ~ (forall (C : SetoidCategory) (CC : CartesianCategory C)
            (TSC : TwoSortCategory C) (GF : GoodFibration C) 
            (SGF : StrictGoodFibration C GF) (HM : HyperModel SGF)
            (I : b_ty) (wfc : wf_ctx I nil) (wf_Phi : WellFormed I (LEM_Formula I)),
       inhabited (hom (interp_h_ctx I nil wfc) (interp_h_ty I (LEM_Formula I) wf_Phi))).
Proof.
  intro H_univ.
  
  (* 1. HELYETTESÍTSD BE A SAJÁT BÁZIS TÍPUSODAT A 'b_unit_ty' HELYÉRE! *)
  assert (wf_LEM : WellFormed b_Unit (LEM_Formula b_Unit)).
  { apply WF_Sum.
    - eapply WF_Atom. apply BT_Unit.
    - apply WF_Arrow. eapply WF_Atom. apply BT_Unit. apply WF_Void. }
    
  (* 2. A specializálásnál is add meg ezt a bázis típust! *)
  specialize (H_univ 
               (@Base_SetoidCategory nat) 
               (@Base_CartesianCategory nat)
               (@Base_TwoSortCategory nat)
               H3_GoodFibration 
               H3_StrictGoodFibration 
               H3_HyperModel 
               b_Unit            (* <--- ITT IS *)
               (WFC_nil b_Unit)  (* <--- ÉS ITT IS *)
               wf_LEM).
               
  (* 3. Csomagoljuk ki az 'inhabited' létezési kvantort, ami egy morfizmust ad *)
  destruct H_univ as [f_lem].
  
  (* 4. Számítsuk ki, mit is jelent ez a morfizmus a H3 kategóriában! *)
  simpl in f_lem.
  
  (* A kiértékelés alapján f_lem típusa: False. Azonnal bezárjuk a cáfolatot! *)
  exact f_lem.
Defined.

Theorem LEM_Underivable : 
  (forall (I : b_ty) (wfc : wf_ctx I nil) (wf_Phi : WellFormed I (LEM_Formula I)),
       { p : h_tm & h_derivation I nil p (LEM_Formula I) }) -> False.
Proof.
  (* 1. Feltesszük indirekt módon, hogy minden I-re létezik (Type szinten) levezetés *)
  intro H_all_der.
  
  (* 2. Alkalmazzuk a kolléga cáfolatát, ami a False-ra vezet *)
  apply LEM_Refuted.
  
  (* 3. A Coq kéri a modelleket és egy tetszőleges I_any-t *)
  intros C CC TSC GF SGF HM I_any wfc_any wf_Phi_any.
  
  (* 4. Alkalmazzuk az indirekt feltevésünket az I_any-ra. 
        Mivel ez egy { p & ... } szigma-típus, a 'destruct' 
        szépen kettébontja a 'p' termre és a 'H_der' levezetésre! *)
  destruct (H_all_der I_any wfc_any wf_Phi_any) as [p H_der].
  
  (* 5. Átlépünk a Prop univerzumba a constructor-ral (inhabits). *)
  constructor.
  
  (* 6. Rászabadítjuk a Soundness tételt a H_der-re! *)
  apply (hyper_soundness_inhabited H_der wfc_any wf_Phi_any).
Defined.

(* ----------------------------------------------------------------- *)
(* SEGÉDLEMMÁK (Tisztán, 'inhabited' nélkül, hogy használhatóak legyenek!) *)

Lemma LEM_WellFormed : forall (I : b_ty), WellFormed I (LEM_Formula I).
Proof.
  intro I.
  apply WF_Sum.
  - eapply WF_Atom. apply BT_Unit.
  - apply WF_Arrow. eapply WF_Atom. apply BT_Unit. apply WF_Void.
Defined. (* Fontos a Defined, hogy a simpl ki tudja értékelni! *)

Lemma wf_ctx_nil_valid : forall (I : b_ty), wf_ctx I nil.
Proof.
  intro I.
  constructor.
Defined.

(* ----------------------------------------------------------------- *)
(* A CÁFOLAT (Letisztítva) *)

(* Mivel a lemmáink globálisak, a tétel állításából kivehetjük a wfc és wf_Phi feltételeket! *)
Theorem LEM_Refuted_WF : 
  ~ (forall (C : SetoidCategory) (CC : CartesianCategory C)
            (TSC : TwoSortCategory C) (GF : GoodFibration C) 
            (SGF : StrictGoodFibration C GF) (HM : HyperModel SGF)
            (I : b_ty),
       inhabited (hom (interp_h_ctx I nil (wf_ctx_nil_valid I)) 
                      (interp_h_ty I (LEM_Formula I) (LEM_WellFormed I)))).
Proof.
  intro H_univ.
  
  (* A specializálás is zseniálisan leegyszerűsödik: csak a b_Unit bázist kell megadni, 
     a formáltsági bizonyításokat a Coq maga helyettesíti be a lemmáinkból! *)
  specialize (H_univ 
               (@Base_SetoidCategory nat) 
               (@Base_CartesianCategory nat)
               (@Base_TwoSortCategory nat)
               H3_GoodFibration 
               H3_StrictGoodFibration 
               H3_HyperModel 
               b_Unit).
               
  destruct H_univ as [f_lem].
  simpl in f_lem.
  exact f_lem.
Defined.

(* ----------------------------------------------------------------- *)
(* A FŐTÉTEL: A LEM NEM LEVEZETHETŐ *)

Theorem LEM_Underivable_WF : 
  (* Így már a tétel gyönyörű matematikai formát ölt: *)
  (forall (I : b_ty), { p : h_tm & h_derivation I nil p (LEM_Formula I) }) -> False.
Proof.
  intro H_all_der.
  
  (* 1. Hívjuk segítségül a cáfolatunkat *)
  apply LEM_Refuted.
  intros C CC TSC GF SGF HM I_any.
  
  (* 2. Szedjük ki a szintaktikus levezetést az adott I_any bázisra *)
  destruct (H_all_der I_any) as [p H_der].
  
  (* 3. Lépjünk be a Prop univerzumba a morfizmus létezéséhez *)
  constructor.
  
  (* A soundness tétel pontosan azokat a formáltsági bizonyításokat kéri, 
     amik a kontextusodban (wfc, wf_Phi) már szerepelnek! *)
  apply (hyper_soundness_inhabited H_der wfc wf_Phi).
Defined.