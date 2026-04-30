Require Import Coq.Logic.Classical.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
(* Ide jöhet a Require Import LEM. is, ha szükséged van a régi taktikákra! *)

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