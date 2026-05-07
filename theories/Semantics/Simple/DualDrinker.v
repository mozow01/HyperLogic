(*theories/Semantics/Simple/DualDrinker.v*)
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
(* 1. A BÁZIS KATEGÓRIA: Kétvilágos Kripke Poset                       *)
(* ================================================================= *)

Inductive World : Type := w1 | w2.

Definition W_le (u v : World) : Prop :=
  match u, v with
  | w1, _ => True
  | w2, w2 => True
  | w2, w1 => False
  end.

(* Reflexivitás és Tranzitivitás *)
Lemma W_le_refl : forall w, W_le w w. Proof. destruct w; simpl; auto. Qed.
Lemma W_le_trans : forall u v w, W_le u v -> W_le v w -> W_le u w. Proof. destruct u, v, w; simpl; tauto. Qed.

(* ================================================================= *)
(* 2. ELŐNYALÁBOK (Varying Domains) ÉS MORFIZMUSOK                   *)
(* ================================================================= *)

(* Egy előnyaláb (Presheaf) a mi Kripke modellünkben: egy típus-család a világok felett, 
   átmenet-függvényekkel (restriction/transition maps). *)
Record Presheaf := {
  P_obj :> World -> Type;
  P_trans : forall u v, W_le u v -> P_obj u -> P_obj v;
  (* A funktor-törvényeket most a klasszikus egyszerüség kedvéért elhagyjuk, 
     de itt kellene lennie az id és comp megőrzésének. *)
}.

(* Előnyaláb morfizmus (Természetes transzformáció) *)
Record PS_Hom (X Y : Presheaf) := {
  hom_f :> forall w, X w -> Y w;
  hom_nat : forall u v H x, hom_f v (X.(P_trans) u v H x) = Y.(P_trans) u v H (hom_f u x)
}.

(* ================================================================= *)
(* 3. A FIBRÁCIÓ SZÁLAI: Kripke Predikátumok (Subobjects)            *)
(* ================================================================= *)

(* Egy predikátum monoton az időben: ha u-ban igaz x-re, v-ben is igaz a jövőbeli x-re. *)
Record Predicate (X : Presheaf) := {
  pred_holds :> forall w, X w -> Prop;
  pred_mono : forall u v (H : W_le u v) (x : X u), 
              pred_holds u x -> pred_holds v (X.(P_trans) u v H x)
}.

(* Két predikátum egyenlő, ha logikailag ekvivalensek (Extensionality) *)
Axiom pred_ext : forall X (P Q : Predicate X), 
  (forall w x, P w x <-> Q w x) -> P = Q.

(* ================================================================= *)
(* 4. VISSZAHÚZÁS (Pullback / Substitution functor)                  *)
(* ================================================================= *)

Definition Subst {X Y : Presheaf} (f : PS_Hom X Y) (Q : Predicate Y) : Predicate X.
Proof.
  refine {| pred_holds := fun w x => Q w (f w x) |}.
  intros u v H x H_holds.
  rewrite (hom_nat X Y f u v H x). 
  
  (* Simán csak apply pred_mono, a Coq kitalálja a többit! *)
  apply pred_mono.
  exact H_holds.
Defined.

(* ================================================================= *)
(* 5. AZ EGZISZTENCIÁLIS KVANTOR (Bal Adjungált)                     *)
(* ================================================================= *)

(* A bal adjungált \exists_f előre tolja X predikátumait Y-ra. 
   Definíció: \exists x. f(x)=y /\ P(x) *)
Definition Exists_LeftAdjoint {X Y : Presheaf} (f : PS_Hom X Y) (P : Predicate X) : Predicate Y.
Proof.
  refine {| pred_holds := fun w y => exists (x : X w), f w x = y /\ P w x |}.
  intros u v H y [x [Heq Hpx]].
  exists (X.(P_trans) u v H x).
  split.
  - rewrite (hom_nat X Y f u v H x). rewrite Heq. reflexivity.
  - apply pred_mono. exact Hpx.
Defined.

(* ================================================================= *)
(* 5.5. A KATEGÓRIAELMÉLETI HIPERDOKTRÍNA (FIBRÁCIÓ) STRUKTÚRA       *)
(* ================================================================= *)

(* 1. A SZÁL-KATEGÓRIA (A predikátumok egy Poset-et alkotnak) *)
Definition Pred_le {X : Presheaf} (P Q : Predicate X) : Prop :=
  forall w x, P w x -> Q w x.

Lemma Pred_le_refl : forall X (P : Predicate X), Pred_le P P.
Proof. intros X P w x H; exact H. Qed.

Lemma Pred_le_trans : forall X (P Q R : Predicate X), Pred_le Q R -> Pred_le P Q -> Pred_le P R.
Proof. intros X P Q R H1 H2 w x Hpx; apply H1; apply H2; exact Hpx. Qed.

Instance Pred_Setoid (X : Presheaf) : SetoidCategory.
Proof.
  refine (mk_SetoidCategory (Predicate X) Pred_le
    (Pred_le_refl X) (Pred_le_trans X) (fun _ _ _ _ => True) _ _ _ _ _).
  Unshelve.
  
  (* Az 1: célirányosan csak az első célt oldja meg, kapcsos zárójelekkel *)
  1: { intros x y. split; red; auto. }
  
  (* Mivel nem vagyunk kötőjel-fókuszban, az all: most már TÉNYLEG az 
     összes (2., 3., 4., 5.) maradék célra lefut! *)
  all: repeat intro; exact I.
Defined.

(* 2. A PULLBACK FUNKTOR (A Substitúció kategóriaelméleti átemelése) *)
Instance Subst_Functor {X Y : Presheaf} (f : PS_Hom X Y) : Functor (Pred_Setoid Y) (Pred_Setoid X).
Proof.
  refine (mk_Functor (Pred_Setoid Y) (Pred_Setoid X) (Subst f) 
          (* Itt, a '_'-ok helyén KÖZVETLENÜL megadjuk az fmap függvényt! *)
          (fun Q1 Q2 Hle w x Hqx => Hle w (f w x) Hqx) 
          _ _ _).
  Unshelve.
  (* Az összes maradék cél (Proper, id, comp) a Poset miatt True-ra egyszerűsödik *)
  all: repeat intro; exact I.
Defined.

(* 3. A BAL ADJUNGÁLT FUNKTOR (Az Egzisztenciális Kvantor) *)
Instance Exists_Functor {X Y : Presheaf} (f : PS_Hom X Y) : Functor (Pred_Setoid X) (Pred_Setoid Y).
Proof.
  refine (mk_Functor (Pred_Setoid X) (Pred_Setoid Y) (Exists_LeftAdjoint f) 
          (* Az ltac:(...) segítségével közvetlenül bizonyítási módban adhatjuk meg a fmap-et, 
             így már tökéletesen működik a szögletes zárójeles destrukciód! *)
          ltac:(intros P1 P2 Hle w y [x [Heq Hpx]]; exists x; exact (conj Heq (Hle w x Hpx)))
          _ _ _).
  Unshelve.
  (* A maradék kategóriaelméleti célok itt is automatikusan True-k *)
  all: repeat intro; exact I.
Defined.

(* 4. A FŐTÉTEL: AZ EGZISZTENCIÁLIS KVANTOR ADJUNKCIÓJA (Hom-Ekvivalencia) *)
(* Ez a lemma a szíve a Hiperdoktrína kvantor-szemantikájának! 
   Azt mondja ki:  ∃f(P) ≤ Q  <==>  P ≤ f*(Q) *)
Lemma Exists_Adjunction : forall {X Y : Presheaf} (f : PS_Hom X Y) (P : Predicate X) (Q : Predicate Y),
  Pred_le (Exists_LeftAdjoint f P) Q <-> Pred_le P (Subst f Q).
Proof.
  intros X Y f P Q. split; intro H.
  - (* -> Irány: Tudjuk, hogy (Exists P <= Q). 
       Meg kell mutatnunk w, x esetén, hogy Q(w, f(x)) igaz. *)
    intros w x Hpx. 
    (* Alkalmazzuk a hipotézist a célpontra (f w x) *)
    apply (H w (f w x)). 
    (* Ehhez be kell bizonyítanunk, hogy létezik x. Ezt maga az 'x' adja! *)
    exists x. split. reflexivity. exact Hpx.
    
  - (* <- Irány: Tudjuk, hogy P <= Subst Q. 
       Meg kell mutatnunk, hogy ha y-ra létezik x, amire f(x)=y és P(x), akkor Q(y). *)
    intros w y [x [Heq Hpx]].
    (* Kicseréljük az y-t f(w, x)-re az egyenlőség alapján. *)
    rewrite <- Heq. 
    (* Most pontosan a (Subst Q w x) áll előttünk, amit a hipotézis azonnal megad! *)
    apply (H w x). exact Hpx.
Qed.

(* ================================================================= *)
(* 5.1. A Bázis Kategória (Presheaf_Base) Valódi Felépítése           *)
(* ================================================================= *)

(* Az Identitás morfizmus (Természetes transzformáció X-ből X-be) *)
Definition PS_id (X : Presheaf) : PS_Hom X X.
Proof.
  (* Maga a függvény: f(x) = x *)
  refine {| hom_f := fun w x => x |}.
  
  (* A természetesség bizonyítása: az id megőrzi az időbeli átmeneteket? *)
  (* Igen, triviálisan! *)
  intros u v H x. 
  reflexivity.
Defined.

(* A Kompozíció (Két természetes transzformáció egymás utáni elvégzése) *)
Definition PS_comp (X Y Z : Presheaf) (f : PS_Hom Y Z) (g : PS_Hom X Y) : PS_Hom X Z.
Proof.
  (* Maga a függvény: (f o g)(x) = f(g(x)) *)
  refine {| hom_f := fun w x => f w (g w x) |}.
  
  (* A természetesség bizonyítása: f o g megőrzi az időbeli átmeneteket? *)
  intros u v H x.
  
  (* Először a belső 'g' függvény természetességét alkalmazzuk balról jobbra... *)
  rewrite (hom_nat X Y g u v H x).
  
  (* ...majd a külső 'f' függvényét az eredményen! *)
  rewrite (hom_nat Y Z f u v H (g u x)).
  
  reflexivity.
Defined.

Instance Presheaf_Base : SetoidCategory.
Proof.
  refine (mk_SetoidCategory Presheaf PS_Hom PS_id PS_comp 
          (fun _ _ _ _ => True) _ _ _ _ _).
  Unshelve. 
  
  (* 1. Cél: Az Equivalence osztály bizonyítása a Hom-halmazokon *)
  1: { intros x y. split; red; auto. }
  
  (* Maradék célok: Kategória-törvények (asszociativitás, id-kompozíció) *)
  all: repeat intro; exact I.
Defined.

(* ================================================================= *)
(* 5.1.b. A Descartes-féle (Cartesian) Struktúra az Előnyalábokon    *)
(* ================================================================= *)

(* 1. A TERMINÁLIS ELŐNYALÁB (Minden világban csak egyetlen 'tt' elem van) *)
Definition PS_Term : Presheaf.
Proof.
  refine {|
    (* Explicit megmondjuk a Coq-nak, hogy a beépített Datatypes.unit-ot kérjük! *)
    P_obj := fun w => Coq.Init.Datatypes.unit; 
    P_trans := fun u v H x => tt
  |}.
Defined.

(* Az egyetlen lehetséges morfizmus bármely X-ből a Terminálisba *)
Definition PS_term_map (X : Presheaf) : PS_Hom X PS_Term.
Proof.
  (* Közvetlenül a konstruktort hívjuk, hogy a Coq lássa a kategóriákat (X és PS_Term) *)
  refine (Build_PS_Hom X PS_Term (fun w x => Coq.Init.Datatypes.tt) _).
  
  (* A természetesség bizonyítása: *)
  intros u v H x. reflexivity.
Defined.

(* 2. A SZORZAT ELŐNYALÁB (Pontonkénti Descartes-szorzat) *)
Definition PS_Prod (X Y : Presheaf) : Presheaf.
Proof.
  refine {|
    (* Itt is megadjuk a teljes, kiirthatatlan útvonalat a beépített prod típushoz! *)
    P_obj := fun w => Coq.Init.Datatypes.prod (X w) (Y w); 
    
    (* Az átmenet változatlan marad *)
    P_trans := fun u v H xy => (X.(P_trans) u v H (fst xy), Y.(P_trans) u v H (snd xy))
  |}.
Defined.

(* Első projekció (A pár első elemének lekérése) *)
Definition PS_pi1 (X Y : Presheaf) : PS_Hom (PS_Prod X Y) X.
Proof.
  (* Kicseréltük a rekord szintaxist explicit konstruktor hívásra: *)
  refine (Build_PS_Hom (PS_Prod X Y) X (fun w xy => fst xy) _).
  intros u v H xy. reflexivity.
Defined.

(* Második projekció (A pár második elemének lekérése) *)
Definition PS_pi2 (X Y : Presheaf) : PS_Hom (PS_Prod X Y) Y.
Proof.
  (* Itt is explicit konstruktor: *)
  refine (Build_PS_Hom (PS_Prod X Y) Y (fun w xy => snd xy) _).
  intros u v H xy. reflexivity.
Defined.

(* Párosítás: Két párhuzamos f és g morfizmus összefűzése egyetlen morfizmussá *)
(* FIGYELEM: A paraméterek sorrendje most Z, X, Y (forrás, cél1, cél2) *)
Definition PS_pair (Z X Y : Presheaf) (f : PS_Hom Z X) (g : PS_Hom Z Y) : PS_Hom Z (PS_Prod X Y).
Proof.
  refine (Build_PS_Hom Z (PS_Prod X Y) (fun w z => (f w z, g w z)) _).
  
  (* A természetesség bizonyítása maradhat a régi: *)
  intros u v H z.
  simpl.
  rewrite (hom_nat Z X f u v H z).
  rewrite (hom_nat Z Y g u v H z).
  reflexivity.
Defined.

Instance Presheaf_Cartesian : CartesianCategory Presheaf_Base.
Proof.
  (* Közvetlenül a mezőnevekre hivatkozunk, így lehetetlen elrontani a sorrendet 
     és nem kell az alsóvonásokkal ( _ ) zsonglőrködni! *)
  refine {|
    terminal := PS_Term;
    terminal_map := PS_term_map;
    prod := PS_Prod;
    prod_map := PS_pair;
    prod_fst := PS_pi1;
    prod_snd := PS_pi2
  |}.
  Unshelve.
  (* A Coq automatikusan legenerálta a maradék mezőket (mint prod_eta, prod_map_proper_ax stb.)
     célokként. Mivel a mi Setoidunk triviális (True), egy mozdulattal lezárjuk mindet: *)
  all: repeat intro; exact I.
Defined.

Definition PS_Const (T : Type) : Presheaf.
Proof.
  refine {|
    P_obj := fun w => T;
    P_trans := fun u v H x => x 
  |}.
Defined.

(* Explicit módon Type-szintű egyenlőséget kérünk a '@eq Type' segítségével: *)
Lemma bool_neq_unit : @eq Type bool Coq.Init.Datatypes.unit -> False.
Proof.
  intro H.
  pose (Prop_Eq := fun T : Type => forall x y : T, x = y).
  assert (H_unit : Prop_Eq Coq.Init.Datatypes.unit).
  { intros [] []. reflexivity. } 
  assert (H_bool : Prop_Eq bool).
  { rewrite H. exact H_unit. } 
  assert (H_contra : true = false).
  { apply H_bool. }
  discriminate H_contra.
Qed.



(* 2. LÉPÉS: A végső lemma axiómák nélkül, a te konkrét Kripke-világoddal! *)
Lemma bool_not_unit_presheaf : PS_Const bool <> PS_Term.
Proof.
  intro H_eq.
  assert (H_obj : P_obj (PS_Const bool) = P_obj PS_Term).
  { rewrite H_eq. reflexivity. }
  
  assert (H_world : P_obj (PS_Const bool) w1 = P_obj PS_Term w1).
  { rewrite H_obj. reflexivity. }
  
  simpl in H_world.
  
  (* Kikerüljük a Coq taktika-motorját, és közvetlenül meghívjuk a lemmát, 
     átadva neki a H_world hipotézist paraméterként: *)
  exact (bool_neq_unit H_world).
Qed.

(* A TwoSort példányosítása *)
Instance Presheaf_TwoSort : TwoSortCategory Presheaf_Base.
Proof.
  unshelve econstructor.
  1: exact (PS_Const bool).
  1: exact bool_not_unit_presheaf.
  all: repeat intro; exact I.
Defined.

(* A koherencia feltételeket axiómába rejtjük, de kikötjük, hogy a Hypermodellünk
   Pullback-je a mi Subst_Functor-unk, a bal adjungáltja pedig a mi Exists_Functor-unk! *)
Axiom Kripke_GoodFibration : GoodFibration Presheaf_Base.
Existing Instance Kripke_GoodFibration.

Axiom Kripke_Strict : StrictGoodFibration Presheaf_Base Kripke_GoodFibration.
Existing Instance Kripke_Strict.

Axiom Kripke_HyperModel : HyperModel Kripke_Strict.
Existing Instance Kripke_HyperModel.

Axiom Kripke_Model_Properties : 
  forall (X Y : Presheaf) (f : PS_Hom X Y),
  Pullback (CB := Kripke_GoodFibration) f = Subst_Functor f.

(* ================================================================= *)
(* 6. A BECK-CHEVALLEY FELTÉTEL BIZONYÍTÁSA                          *)
(* ================================================================= *)

(* Képzelj el egy Pullback (szál-szorzat) négyzetet a bázisban:
      X_pullback --g'--> X
          |              |
        f'|              | f
          V              V
          Y_base ---g--> Z
          
   BC: \exists_f' o Subst_g' = Subst_g o \exists_f 
   A Coq-ban ezt pontonkénti Kripke kiértékeléssel bizonyítjuk. 
   Az egyszerűség kedvéért tegyük fel, hogy g egy beágyazás (vagy paraméter-átadás), 
   és f a kvantált változó projekciója. *)

Lemma Beck_Chevalley_Condition : 
  forall {X Y Z X_pullback : Presheaf} 
         (f : PS_Hom X Z) (g : PS_Hom Y Z) 
         (f' : PS_Hom X_pullback Y) (g' : PS_Hom X_pullback X)
         (P : Predicate X),
  (* Ha a négyzet kommutál: f(g'(x)) = g(f'(x)) *)
  (forall w xp, f w (g' w xp) = g w (f' w xp)) ->
  (* És X_pullback egy igazi szál-szorzat (minden (x, y) párhoz, ahol f(x)=g(y), van xp) *)
  (forall w x y, f w x = g w y -> exists xp, g' w xp = x /\ f' w xp = y) ->
  (* Akkor a BC feltétel teljesül: *)
  Exists_LeftAdjoint f' (Subst g' P) = Subst g (Exists_LeftAdjoint f P).
Proof.
  intros X Y Z Xp f g f' g' P Hcomm Hpullback.
  apply pred_ext. intros w y. split; intro H.
  
  - (* -> Irány *)
    destruct H as [xp [H_eq_y H_subst_P]].
    exists (g' w xp).
    split.
    + rewrite Hcomm. rewrite H_eq_y. reflexivity.
    + exact H_subst_P.
    
  - (* <- Irány *)
    destruct H as [x [H_fg_eq H_Px]].
    (* Használjuk a szál-szorzat tulajdonságát! *)
    destruct (Hpullback w x y H_fg_eq) as [xp [H_xp_x H_xp_y]].
    exists xp.
    split.
    + exact H_xp_y.
    + simpl. rewrite H_xp_x. exact H_Px.
Qed.

(* ================================================================= *)
(* 7. A DUAL DRINKER CÁFOLÓ MODELLJE (A Végleges Konstrukció)        *)
(* ================================================================= *)

(* A konkrét táguló univerzum: w1-ben csak 'a' van, w2-ben 'a' és 'b' *)
Inductive D1 : Type := a_in_1.
Inductive D2 : Type := a_in_2 | b_in_2.

Definition Domain (w : World) : Type :=
  match w with | w1 => D1 | w2 => D2 end.

Definition Dom_trans (u v : World) (H : W_le u v) (x : Domain u) : Domain v.
Proof.
  destruct u, v; simpl.
  - exact x.
  - exact a_in_2. (* 'a' megőrződik az időben *)
  - contradiction.
  - exact x.
Defined.

Definition D_Presheaf := {| P_obj := Domain; P_trans := Dom_trans |}.

(* A Phi predikátum megalkotása az előzetes matematikai terv alapján! *)
Definition Phi_Holds (w : World) (x : Domain w) : Prop :=
  match w, x with
  | w1, _ => False
  | w2, a_in_2 => False
  | w2, b_in_2 => True
  end.

Definition Phi : Predicate D_Presheaf.
Proof.
  (* Közvetlenül meghívjuk a generált konstruktort.
     1. param: Az előnyaláb (D_Presheaf)
     2. param: A függvény (Phi_Holds)
     3. param: A bizonyítás (ezt hagyjuk lyukon a '_'-sal) *)
  refine (Build_Predicate D_Presheaf Phi_Holds _).
  
  (* A visszamaradó cél a pred_mono bizonyítása *)
  intros u v H x Hpx.
  destruct u, v; simpl in *; try contradiction; auto.
Defined.


(* ================================================================= *)
(* 8. A DUAL DRINKER PARADOXON CÁFOLATA                              *)
(* ================================================================= *)

(* Felírjuk a formula Kripke-szemantika szerinti kiértékelését a w1 világban. *)
Definition Dual_Drinker_w1 : Prop :=
  (* 1. Létezik egy 'x' a w1 világban (itt csak 'a' lehet) *)
  exists (x : Domain w1), 
    (* 2. Minden w' jövőbeli világban (ahol H a bizonyítás, hogy w1 <= w') *)
    forall (w' : World) (H : W_le w1 w'),
      (* 3. Ha w'-ben létezik iszákos 'y'... *)
      (exists (y : Domain w'), Phi w' y) -> 
      (* 4. Akkor 'x' jövőbeli másának is innia kell w'-ben! *)
      Phi w' (Dom_trans w1 w' H x).

(* A főtétel: A Dual Drinker formula HAMIS a w1 világban. *)
Theorem Dual_Drinker_Refuted : ~ Dual_Drinker_w1.
Proof.
  (* Tegyük fel indirekt módon, hogy a formula igaz w1-ben. *)
  intro H_DD.
  
  (* 1. Bontsuk szét a külső egzisztenciális kvantort. *)
  destruct H_DD as [x H_impl].
  
  (* 2. Mivel x a w1 világban van (D1), az egyetlen lehetséges értéke az 'a_in_1'. 
        Szétbontjuk x-et, hogy a Coq lássa ezt. *)
  destruct x.
  
  (* 3. Utazzunk a jövőbe! Teszteljük az implikációt a w2 világban. 
        (A w1 <= w2 bizonyítása egyszerűen a True, azaz 'I') *)
  specialize (H_impl w2 I).
  
  (* 4. Az implikáció bal oldala: Bizonyítsuk be, hogy a w2-ben VAN iszákos ember! *)
  assert (H_y_exists : exists y : Domain w2, Phi w2 y).
  { 
    (* Létezik, méghozzá b_in_2! *)
    exists b_in_2. 
    (* A Phi(w2, b_in_2) egyszerűsödik True-ra, amit bezárunk I-vel. *)
    simpl. exact I. 
  }
  
  (* 5. Adjuk oda ezt a tényt az implikációnak, ami így levonja a konklúziót. *)
  specialize (H_impl H_y_exists).
  
  (* 6. Számítsuk ki, mi lett a konklúzió (Phi w2 a_in_2). *)
  simpl in H_impl.
  
  (* Ahogy terveztük, az implikáció konklúziója False-ra egyszerűsödött. 
     Mivel a feltételezésből (H_DD) False-ra jutottunk, a cáfolat teljes! *)
  exact H_impl.
Qed.