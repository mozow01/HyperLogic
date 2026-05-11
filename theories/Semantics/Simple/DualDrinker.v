(*theories/Semantics/Simple/DualDrinker.v*)
(*theories/Semantics/Simple/LEM.v*)

Require Import Stdlib.Logic.Classical.
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.Logic.ProofIrrelevance.
Require Import Stdlib.Classes.Morphisms.

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
(* 1. A 5-ELEMŰ "SÁRKÁNY" (KITE) HEYTING ALGEBRA (H5)                *)
(* ================================================================= *)

Inductive H5 : Type := HBot | H1 | H2 | H12 | HTop.

Definition H5_le (x y : H5) : Prop :=
  match x, y with
  | HBot, _ => True
  | _, HTop => True
  | H1, H1 | H1, H12 => True
  | H2, H2 | H2, H12 => True
  | H12, H12 => True
  | _, _ => False
  end.

Lemma H5_le_refl : forall x, H5_le x x. Proof. destruct x; exact I. Defined.
Lemma H5_le_trans : forall x y z, H5_le y z -> H5_le x y -> H5_le x z.
Proof. destruct x, y, z; simpl; tauto. Defined.

Definition H5_meet (x y : H5) : H5 :=
  match x, y with
  | HBot, _ | _, HBot => HBot
  | HTop, a | a, HTop => a
  | H1, H1 | H1, H12 | H12, H1 => H1
  | H2, H2 | H2, H12 | H12, H2 => H2
  | H12, H12 => H12
  | H1, H2 | H2, H1 => HBot
  end.

Definition H5_join (x y : H5) : H5 :=
  match x, y with
  | HTop, _ | _, HTop => HTop
  | HBot, a | a, HBot => a
  | H12, _ | _, H12 => H12
  | H1, H1 => H1
  | H2, H2 => H2
  | H1, H2 | H2, H1 => H12
  end.

Definition H5_impl (x y : H5) : H5 :=
  match x, y with
  | HBot, _ | _, HTop => HTop
  | HTop, a => a
  | H12, H1 => H1
  | H12, H2 => H2
  | H12, HBot => HBot
  | H1, H1 | H1, H12 => HTop
  | H1, H2 | H1, HBot => H2
  | H2, H2 | H2, H12 => HTop
  | H2, H1 | H2, HBot => H1
  | H12, H12 => HTop
  end.



(* ================================================================= *)
(* 2. A PREDIKÁTUM SZÁLAK ÉS A FIBRÁCIÓ                              *)
(* ================================================================= *)

Definition H5_Pred (X : Type) := X -> H5.
Definition H5_Pred_le {X : Type} (P Q : H5_Pred X) : Prop := forall x, H5_le (P x) (Q x).
(* A VÉGSŐ, TÖKÉLETESÍTETT Favágó Taktika (Kifejezés-alapú specializációval!) *)
Ltac h5_pred_crush :=
  repeat intro;
  
  (* 1. Alapvető relációk kibontása *)
  repeat match goal with
  | |- Proper _ _ => red
  | |- respectful _ _ _ _ => red
  | |- RelationClasses.Equivalence _ => split; red
  end;
  
  (* 2. Kategóriaelméleti dobozok feltörése *)
  cbn in *;
  try unfold hom in *;
  try unfold H5_Pred_le in *; 
  
  (* 3. Elrejtett forall-ok kényszerített láthatóvá tétele *)
  repeat match goal with
  | H : ?T |- _ => 
      let T' := eval hnf in T in
      lazymatch T with
      | forall _, _ => fail
      | _ => lazymatch T' with
             | forall _, _ => change T' in H
             | _ => fail
             end
      end
  end;
  
  match goal with
  | |- ?G => let G' := eval hnf in G in change G'
  end;
  
  repeat intro;
  
  (* 4. INTELLIGENS SPECIALIZÁCIÓ: Kifejezéseket keresünk, nem csak változókat! *)
  (* Ha P-t vagy Q-t valamilyen 'z' kifejezéssel (pl. f y) hívják meg, azzal specializálunk! *)
  repeat match goal with
  | H : forall w, H5_le (?P w) _ |- context [ ?P ?z ] => 
      specialize (H z)
  | H : forall w, H5_le _ (?Q w) |- context [ ?Q ?z ] => 
      specialize (H z)
  | H : forall w, H5_le (?P w) _, H2 : context [ ?P ?z ] |- _ => 
      specialize (H z)
  | H : forall w, H5_le _ (?Q w), H2 : context [ ?Q ?z ] |- _ => 
      specialize (H z)
  end;
  
  simpl in *;
  
  (* 5. LÉZERPONTOS BONTÁS AZ 'is_var' TRÜKKEL *)
  repeat match goal with
  | |- context [ ?P ?x ] =>
      is_var P;
      let T := type of P in
      lazymatch eval hnf in T with
      | _ -> H5 => destruct (P x); simpl in *
      end
      
  | H : context [ ?P ?x ] |- _ =>
      is_var P;
      let T := type of P in
      lazymatch eval hnf in T with
      | _ -> H5 => destruct (P x); simpl in *
      end
      
  | y : H5 |- _ => is_var y; destruct y; simpl in *
  end;
  
  (* 6. Tisztítás *)
  intuition; auto; try exact I.

Instance H5_Pred_Setoid (X : Type) : SetoidCategory.
Proof. 
  refine (mk_SetoidCategory (H5_Pred X) H5_Pred_le _ _ (fun _ _ _ _ => True) _ _ _ _ _). 
  Unshelve. all: h5_pred_crush.  
Defined.

Instance H5_Pred_Cartesian (X : Type) : CartesianCategory (H5_Pred_Setoid X).
Proof. 
  refine (mk_CartesianCategory (H5_Pred_Setoid X) 
    (fun _ => HTop) (fun _ => _) _ 
    (fun P Q x => H5_meet (P x) (Q x)) 
    (fun P Q R f g => _) (fun P Q => _) (fun P Q => _) _ _ _ _). 
  Unshelve. all: h5_pred_crush. 
Defined.

Instance H5_Pred_Closed (X : Type) : CartesianClosedCategory (H5_Pred_Setoid X).
Proof. 
  refine (mk_CartesianClosedCategory _ (H5_Pred_Cartesian X) 
    (fun P Q x => H5_impl (Q x) (P x)) (* <--- HIER SIND DIE BEMENETEK UMGEKEHRT! *)
    _ _ _ _ _). 
  Unshelve. all: h5_pred_crush. 
Defined.

Instance H5_Pred_BiClosed (X : Type) : BiCartesianClosedCategory (H5_Pred_Closed X).
Proof. 
  refine (mk_BiCartesianClosedCategory _ _ (H5_Pred_Closed X) 
    (fun _ => HBot) _ _ 
    (fun P Q x => H5_join (P x) (Q x)) _ _ _ _ _ _ _). 
  Unshelve. all: h5_pred_crush. 
Defined.

(* ================================================================= *)
(* 3. A VISSZAHÚZÁS (Pullback / Substitution Functor)                *)
(* ================================================================= *)

Instance Subst_Functor {X Y : Type} (f : Y -> X) : Functor (H5_Pred_Setoid X) (H5_Pred_Setoid Y).
Proof. 
  refine (mk_Functor (H5_Pred_Setoid X) (H5_Pred_Setoid Y) 
          (* Itt a varázslat: Explicit megmondjuk, hogy P egy H5_Pred X függvény! *)
          (fun (P : H5_Pred X) (y : Y) => P (f y)) 
          _ _ _ _). 
  Unshelve. all: h5_pred_crush. 
Defined.


(* ================================================================= *)
(* 3. A VÉGES BÁZISKATEGÓRIA (FinObj)                                *)
(* ================================================================= *)

(* 1. A Kategória Objektumai: Csak a Terminális, a Bool és a Szorzat létezik *)
Inductive FinObj : Type :=
  | F_Unit : FinObj
  | F_Bool : FinObj
  | F_Prod : FinObj -> FinObj -> FinObj.

(* 2. Az objektumok "lefordítása" valódi Coq típusokra *)
Fixpoint interp_F (A : FinObj) : Type :=
  match A with
  | F_Unit => Corelib.Init.Datatypes.unit
  | F_Bool => bool
  | F_Prod A B => Corelib.Init.Datatypes.prod (interp_F A) (interp_F B)
  end.

(* 3. A Morfizmusok (Sima függvények a lefordított típusok között) *)
Definition FinHom (A B : FinObj) := interp_F A -> interp_F B.
Definition FinEquiv {A B : FinObj} (f g : FinHom A B) : Prop := forall x, f x = g x.

(* Egy villámgyors favágó taktika a kategória törvényeihez *)
Ltac fin_crush :=
  repeat intro;
  repeat match goal with
  | |- Proper _ _ => red
  | |- respectful _ _ _ _ => red
  | |- RelationClasses.Equivalence _ => split; red
  end;
  repeat intro; simpl in *; auto; try congruence.

Instance Fin_Setoid : SetoidCategory.
Proof.
  refine (mk_SetoidCategory FinObj FinHom
    (fun A x => x)                   (* Identitás *)
    (fun A B C f g x => f (g x))     (* Kompozíció *)
    (@FinEquiv)                      (* Egyenlőség *)
    _ _ _ _ _).
  Unshelve. all: fin_crush.
Defined.

Instance Fin_Cartesian : CartesianCategory Fin_Setoid.
Proof.
  refine (mk_CartesianCategory Fin_Setoid
    F_Unit (fun A x => tt) _
    F_Prod (fun A B C f g x => (f x, g x))
    (fun A B xy => fst xy) (fun A B xy => snd xy)
    _ _ _ _).
  Unshelve.
  all: fin_crush.
  (* 1. A Terminális objektumba menő morfizmusok egyenlősége *)
  - destruct (f x0). reflexivity.
  (* 2. A Szorzat morfizmus unicitása (Párok egyenlősége) *)
  - destruct (h x0). reflexivity.
Defined.

(* ================================================================= *)
(* 4. A KÉT-FAJTÁJÚ (Two-Sort) STRUKTÚRA                             *)
(* ================================================================= *)

Instance Fin_TwoSort : TwoSortCategory Fin_Setoid.
Proof.
  unshelve econstructor.
  - exact F_Bool. (* A megkülönböztetett tartomány a 'bool' *)
  - (* Itt jön a mágia: mivel a FinObj egy Inductive típus, a Coq 
       számára triviális, hogy a F_Bool konstruktor nem egyenlő a F_Unit-tal! *)
    intro Heq. discriminate Heq.
Defined.

Require Import Coq.Bool.Bool.

(* ================================================================= *)
(* 4. A KISZÁMÍTHATÓ KVANTOROK (Adjunktok) Véges Típusokon           *)
(* ================================================================= *)

(* 1. Szuprémum (Létezik) kiszámítása véges iterációval *)
Fixpoint Fin_sup {Y : FinObj} : (interp_F Y -> H5) -> H5 :=
  match Y return (interp_F Y -> H5) -> H5 with
  | F_Unit => fun P => P tt
  | F_Bool => fun P => H5_join (P true) (P false)
  | F_Prod A B => fun P => Fin_sup (fun a => Fin_sup (fun b => P (a, b)))
  end.

(* 2. Infimum (Minden) kiszámítása véges iterációval *)
Fixpoint Fin_inf {Y : FinObj} : (interp_F Y -> H5) -> H5 :=
  match Y return (interp_F Y -> H5) -> H5 with
  | F_Unit => fun P => P tt
  | F_Bool => fun P => H5_meet (P true) (P false)
  | F_Prod A B => fun P => Fin_inf (fun a => Fin_inf (fun b => P (a, b)))
  end.

(* 3. Egyenlőség-vizsgáló algoritmus véges típusokon (az inverz képhez) *)
Fixpoint eq_fin {X : FinObj} : interp_F X -> interp_F X -> bool :=
  match X return interp_F X -> interp_F X -> bool with
  | F_Unit => fun _ _ => true
  | F_Bool => fun b1 b2 => Bool.eqb b1 b2
  | F_Prod A B => fun p1 p2 => andb (eq_fin (fst p1) (fst p2)) (eq_fin (snd p1) (snd p2))
  end.

(* ================================================================= *)
(* 5. AZ ADJUNGÁLTAK FUNKTORAI ÉS A BIZONYÍTÁSOK                     *)
(* ================================================================= *)

(* Létezik (Bal Adjungált) Algoritmusa: *)
Definition Fin_Exists_val {X Y : FinObj} (f : FinHom Y X) (P : interp_F Y -> H5) (x : interp_F X) : H5 :=
  Fin_sup (fun y => if eq_fin x (f y) then P y else HBot).

(* Minden (Jobb Adjungált) Algoritmusa: *)
Definition Fin_Forall_val {X Y : FinObj} (f : FinHom Y X) (P : interp_F Y -> H5) (x : interp_F X) : H5 :=
  Fin_inf (fun y => if eq_fin x (f y) then P y else HTop).

Require Import Coq.Bool.Bool.

(* ================================================================= *)
(* 5. A VÉGES KVANTOROK MATEMATIKAI BIZONYÍTÁSAI                     *)
(* ================================================================= *)

Lemma eq_fin_refl : forall (X : FinObj) (x : interp_F X), eq_fin x x = true.
Proof.
  induction X; simpl; intros.
  - destruct x. reflexivity.
  - destruct x; reflexivity.
  - destruct x. rewrite IHX1, IHX2. reflexivity.
Qed.

Lemma eq_fin_eq : forall (X : FinObj) (x1 x2 : interp_F X), eq_fin x1 x2 = true -> x1 = x2.
Proof.
  induction X; simpl; intros.
  - destruct x1, x2. reflexivity.
  - destruct x1, x2; simpl in H; try discriminate H; reflexivity.
  - destruct x1 as [a1 b1], x2 as [a2 b2].
    apply Bool.andb_true_iff in H. destruct H.
    apply IHX1 in H. apply IHX2 in H0. subst. simpl in H. simpl in H0. subst. reflexivity.
Qed.

Lemma Fin_sup_upper_bound : forall (Y : FinObj) (F : interp_F Y -> H5) (y : interp_F Y), H5_le (F y) (@Fin_sup Y F).
Proof.
  induction Y; simpl; intros.
  - destruct y. destruct (F tt); exact I.
  - destruct y; destruct (F true); destruct (F false); exact I.
  - destruct y as [a b].
    assert (H1 := IHY2 (fun b' => F (a, b')) b).
    assert (H2 := IHY1 (fun a' => Fin_sup (fun b' => F (a', b'))) a).
    exact (H5_le_trans _ _ _ H2 H1).
Qed.

Lemma Fin_sup_least_bound : forall (Y : FinObj) (F : interp_F Y -> H5) (bound : H5),
  (forall y, H5_le (F y) bound) -> H5_le (@Fin_sup Y F) bound.
Proof.
  induction Y; simpl; intros.
  - apply H.
  - pose proof (H true). pose proof (H false).
    destruct bound; destruct (F true); destruct (F false); simpl in *; tauto || exact I.
  - apply IHY1. intros a. apply IHY2. intros b. apply H.
Qed.

Lemma Fin_inf_lower_bound : forall (Y : FinObj) (F : interp_F Y -> H5) (y : interp_F Y), H5_le (@Fin_inf Y F) (F y).
Proof.
  induction Y; simpl; intros.
  - destruct y. destruct (F tt); exact I.
  - destruct y; destruct (F true); destruct (F false); exact I.
  - destruct y as [a b].
    assert (H1 := IHY2 (fun b' => F (a, b')) b).
    assert (H2 := IHY1 (fun a' => Fin_inf (fun b' => F (a', b'))) a).
    exact (H5_le_trans _ _ _ H1 H2).
Qed.

Lemma Fin_inf_greatest_bound : forall (Y : FinObj) (F : interp_F Y -> H5) (bound : H5),
  (forall y, H5_le bound (F y)) -> H5_le bound (@Fin_inf Y F).
Proof.
  induction Y; simpl; intros.
  - apply H.
  - pose proof (H true). pose proof (H false).
    destruct bound; destruct (F true); destruct (F false); simpl in *; tauto || exact I.
  - apply IHY1. intros a. apply IHY2. intros b. apply H.
Qed.

(* ================================================================= *)
(* 5.5. AZ ADJUNKCIÓK (KVANTOROK) PÉLDÁNYOSÍTÁSA                     *)
(* ================================================================= *)

Instance Fin_Subst_Functor {X Y : FinObj} (f : FinHom Y X) : Functor (H5_Pred_Setoid (interp_F X)) (H5_Pred_Setoid (interp_F Y)).
Proof. 
  refine (mk_Functor (H5_Pred_Setoid (interp_F X)) (H5_Pred_Setoid (interp_F Y)) 
          (fun (P : H5_Pred (interp_F X)) (y : interp_F Y) => P (f y)) 
          _ _ _ _). 
  Unshelve. all: h5_pred_crush. 
Defined.

(* 1. A HELYETTESÍTÉS MINT JOBB ADJUNGÁLT (Ez adja az Egzisztenciális Kvantort!) *)
Instance Fin_Subst_IsRightAdjoint {X Y : FinObj} (f : FinHom Y X) : IsRightAdjoint (Fin_Subst_Functor f).
Proof.
  refine (mk_IsRightAdjoint _ _ (Fin_Subst_Functor f)
    (fun P => Fin_Exists_val f P)
    
    (* Unit: P(y) <= Exists P (f y) *)
    ltac:(
      intros P y; unfold Fin_Exists_val;
      pose proof (Fin_sup_upper_bound Y (fun y' => if eq_fin (f y) (f y') then P y' else HBot) y) as Hsup;
      simpl in Hsup; (* <--- KIKÉNYSZERÍTJÜK A FÜGGVÉNY KIÉRTÉKELÉSÉT *)
      rewrite eq_fin_refl in Hsup; 
      exact Hsup
    )
    
    (* Bal Adjungált Morfizmus: Ha P <= Subst Q, akkor Exists P <= Q *)
    ltac:(
      intros P Q Hle x; unfold Fin_Exists_val;
      apply Fin_sup_least_bound; intro y;
      simpl; (* <--- KIKÉNYSZERÍTJÜK A CÉL KIÉRTÉKELÉSÉT A DESTRUCT ELŐTT *)
      destruct (eq_fin x (f y)) eqn:Heq;
      [ apply eq_fin_eq in Heq; subst; apply Hle | exact I ]
    )
    
    _ _ _).
  Unshelve.
  all: h5_pred_crush.
Defined.

(* 2. A HELYETTESÍTÉS MINT BAL ADJUNGÁLT (Ez adja az Univerzális Kvantort!) *)
Instance Fin_Subst_IsLeftAdjoint {X Y : FinObj} (f : FinHom Y X) : IsLeftAdjoint (Fin_Subst_Functor f).
Proof.
  refine (mk_IsLeftAdjoint _ _ (Fin_Subst_Functor f)
    (fun P => Fin_Forall_val f P)
    
    (* Counit: Forall P (f y) <= P(y) *)
    ltac:(
      intros P y; unfold Fin_Forall_val;
      pose proof (Fin_inf_lower_bound Y (fun y' => if eq_fin (f y) (f y') then P y' else HTop) y) as Hinf;
      simpl in Hinf; (* <--- ITT IS *)
      rewrite eq_fin_refl in Hinf; 
      exact Hinf
    )
    
    (* Jobb Adjungált Morfizmus: Ha Subst Q <= P, akkor Q <= Forall P *)
    ltac:(
      intros Q P Hle x; unfold Fin_Forall_val;
      apply Fin_inf_greatest_bound; intro y;
      simpl; (* <--- ÉS ITT IS *)
      destruct (eq_fin x (f y)) eqn:Heq;
      [ apply eq_fin_eq in Heq; subst; apply Hle | destruct (Q x); exact I ]
    )
    
    _ _ _).
  Unshelve.
  all: h5_pred_crush.
Defined.

(* ================================================================= *)
(* 6. A FIBRÁCIÓ ÉS A HIPERMODELL                                    *)
(* ================================================================= *)

Instance Fin_GoodFibration : GoodFibration Fin_Setoid.
Proof.
  refine {|
    Fiber := fun X => H5_Pred_Setoid (interp_F X);
    fiber_is_thin := fun _ _ _ _ _ => I;
    Fiber_is_Cartesian := fun X => H5_Pred_Cartesian (interp_F X);
    Fiber_is_Closed := fun X => H5_Pred_Closed (interp_F X);
    Fiber_is_BiClosed := fun X => H5_Pred_BiClosed (interp_F X);
    Pullback := fun X Y f => Fin_Subst_Functor f;
    pullback_has_left_adjoint := fun X Y => Fin_Subst_IsRightAdjoint _;
    pullback_has_right_adjoint := fun X Y => Fin_Subst_IsLeftAdjoint _
  |}.
  Unshelve.
 (* ÚJ TAKTIKA: A triviális izomorfizmusok bizonyításához *)
  (* Ezzel soha semmi nem kerül a polcra, mindent azonnal megoldunk! *)
 (* ÚJ TAKTIKA: A triviális izomorfizmusok bizonyításához *)
  (* A 'try' kombinációval kezeljük az elvont egyenlőségeket ÉS a True-ra egyszerűsödőket is! *)
  Ltac solve_trivial_iso :=
    intros; unshelve econstructor;
    [ intros x; simpl; try apply H5_le_refl; try exact Logic.I
    | intros x; simpl; try apply H5_le_refl; try exact Logic.I
    | unfold hom_equiv; compute; exact Logic.I
    | unfold hom_equiv; compute; exact Logic.I ].

  - solve_trivial_iso. (* 1. Identitás *)
  - solve_trivial_iso. (* 2. Kompozíció *)
  - solve_trivial_iso. (* 3. Terminális *)
  - solve_trivial_iso. (* 4. Szorzat *)
  - solve_trivial_iso. (* 5. Kezdeti *)
  - solve_trivial_iso. (* 6. Koszorzat *)
  - solve_trivial_iso. (* 7. Exponenciális *)
(* 8. Beck-Chevalley (Bal) - Egzisztenciális Kvantor felcserélhetősége *)
  - intros I J K f A.
    unshelve econstructor.
    + (* LHS <= RHS *)
      intros k. simpl. unfold Fin_Exists_val. simpl.
      (* Sima apply-ok, a Coq magától kitalálja a rétegeket! *)
      apply Fin_sup_least_bound. intros i.
      apply Fin_sup_least_bound. intros j.
      destruct (eq_fin (f k) i) eqn:Heq.
      * apply eq_fin_eq in Heq. subst i.
        assert (H1 := Fin_sup_upper_bound K (fun a => Fin_sup (fun b : interp_F J => if eq_fin k a then A (f a, b) else HBot)) k).
        assert (H2 := Fin_sup_upper_bound J (fun b => if eq_fin k k then A (f k, b) else HBot) j).
        simpl in H1; rewrite eq_fin_refl in H1. 
        simpl in H2; rewrite eq_fin_refl in H2.
        exact (H5_le_trans _ _ _ H1 H2).
      * simpl. reflexivity.
    + (* RHS <= LHS *)
      intros k. simpl. unfold Fin_Exists_val. simpl.
      apply Fin_sup_least_bound. intros k'.
      apply Fin_sup_least_bound. intros j.
      destruct (eq_fin k k') eqn:Heq.
      * apply eq_fin_eq in Heq. subst k'.
        assert (H1 := Fin_sup_upper_bound I (fun a => Fin_sup (fun b : interp_F J => if eq_fin (f k) a then A (a, b) else HBot)) (f k)).
        assert (H2 := Fin_sup_upper_bound J (fun b => if eq_fin (f k) (f k) then A (f k, b) else HBot) j).
        simpl in H1; rewrite eq_fin_refl in H1.
        simpl in H2; rewrite eq_fin_refl in H2.
        exact (H5_le_trans _ _ _ H1 H2).
      * simpl. reflexivity.
    + unfold hom_equiv; compute; reflexivity.
    + unfold hom_equiv; compute; reflexivity.

  (* 9. Beck-Chevalley (Jobb) - Univerzális Kvantor felcserélhetősége *)
  - intros I_obj J_obj K_obj f A.
    unshelve econstructor.
    + (* LHS <= RHS *)
      intros k. simpl. unfold Fin_Forall_val. simpl.
      apply Fin_inf_greatest_bound. intros k'.
      apply Fin_inf_greatest_bound. intros j.
      destruct (eq_fin k k') eqn:Heq.
      * apply eq_fin_eq in Heq. subst k'.
        assert (H1 := Fin_inf_lower_bound I_obj (fun a => Fin_inf (fun b : interp_F J_obj => if eq_fin (f k) a then A (a, b) else HTop)) (f k)).
        assert (H2 := Fin_inf_lower_bound J_obj (fun b => if eq_fin (f k) (f k) then A (f k, b) else HTop) j).
        simpl in H1; rewrite eq_fin_refl in H1.
        simpl in H2; rewrite eq_fin_refl in H2.
        exact (H5_le_trans _ _ _ H2 H1).
      * match goal with |- H5_le ?x _ => destruct x; exact Logic.I end.
    + (* RHS <= LHS *)
      intros k. simpl. unfold Fin_Forall_val. simpl.
      apply Fin_inf_greatest_bound. intros i.
      apply Fin_inf_greatest_bound. intros j.
      destruct (eq_fin (f k) i) eqn:Heq.
      * apply eq_fin_eq in Heq. subst i.
        assert (H1 := Fin_inf_lower_bound K_obj (fun a => Fin_inf (fun b : interp_F J_obj => if eq_fin k a then A (f a, b) else HTop)) k).
        assert (H2 := Fin_inf_lower_bound J_obj (fun b => if eq_fin k k then A (f k, b) else HTop) j).
        simpl in H1; rewrite eq_fin_refl in H1.
        simpl in H2; rewrite eq_fin_refl in H2.
        exact (H5_le_trans _ _ _ H2 H1).
      * match goal with |- H5_le ?x _ => destruct x; exact Logic.I end.
    + unfold hom_equiv; compute; reflexivity.
    + unfold hom_equiv; compute; reflexivity.

  (* 10. Morfizmusok egyenlősége *)
  - intros I_obj J_obj f g Heq A.
    unshelve econstructor.
    + intros x; simpl; rewrite (Heq x); apply H5_le_refl.
    + intros x; simpl; rewrite (Heq x); apply H5_le_refl.
    + unfold hom_equiv; compute; reflexivity.
    + unfold hom_equiv; compute; reflexivity.

  (* ITT JÖN A POLC TAKARÍTÁSA *)
  Unshelve.
  all: try (intros; econstructor; h5_pred_crush).
Defined.


Instance Fin_StrictGoodFibration : StrictGoodFibration Fin_Setoid Fin_GoodFibration.
Proof.
  econstructor.
  intros X Y M1 M2 H.
  (* Kézzel adjuk meg a bázisbeli egyenlőség megfordítását! *)
  exists (fun x => eq_sym (H x)).
  exact I.
Defined.

Instance Fin_HyperModel : HyperModel Fin_StrictGoodFibration.
Proof.
  unshelve econstructor.
  - intros p t I A dt. exact (fun x => HBot).
  - intros. simpl. reflexivity.
  - intros. apply base_soundness_equational. exact H.
  - intros. simpl. reflexivity.
Defined.

(* ================================================================= *)
(* 7. A DUAL DRINKER CÁFOLATA (A Végkifejlet)                        *)
(* ================================================================= *)

(* 1. A cáfoló predikátum (A bool-on): P(true)=H1, P(false)=H2 *)
Definition Drinker_Pred (b : bool) : H5 :=
  if b then H1 else H2.

(* 2. A Formula kiértékelése a Coq számítógépével *)
(* Közvetlenül a szemantikai kvantorokat (Fin_Exists_val, Fin_sup) hívjuk meg!
   A @ jelekkel expliciten megadjuk a típusokat, hogy a Coq ne zavarodjon össze. *)
Theorem Drinker_Is_Not_HTop : 
  let formula_val := @Fin_Exists_val F_Unit F_Bool (fun _ : bool => tt) 
      (fun x => H5_impl (@Fin_sup F_Bool Drinker_Pred) (Drinker_Pred x)) tt in
  formula_val = H12. (* Az eredmény H12, ami nem HTop (Abszolút Igazság)! *)
Proof.
  intros.
  (* A 'simpl' parancs kiszámolja a Fin_sup-ot (H1 v H2 = H12) 
     és lefuttatja a H5_impl-eket, majd a külső egzisztenciális kvantort. *)
  simpl. 
  reflexivity.
Qed.

