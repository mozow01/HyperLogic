Require Import List.
Require Import PeanoNat.  
Require Import Coq.Classes.Morphisms.
Import ListNotations.

(* Cat Imports *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Fibration.
Require Import HyperLogic.Cat.Adjoint.

(* Logic Imports *)
Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Logic.Base.Simple.Base_Typing.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Logic.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Typing.


(* ================================================================= *)
(* 1. MODEL DEFINITION                                               *)
(* ================================================================= *)

Class SimpleModel (B : SetoidCategory) {CB : CartesianCategory B} {GF : GoodFibration B} := {
  interp_sort : @obj B;
  interp_atom : forall (p : nat) (dom : @obj B), @obj (Fiber dom)
}.

(* ================================================================= *)
(* 2. BASE INTERPRETATION (Contexts & Terms)                         *)
(* ================================================================= *)

(* Típusok interpretációja *)
(* Fontos: Mindenhol explicit típusokat adunk meg a {..}-ben *)
Fixpoint interp_base_ty {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {M : SimpleModel B} 
  (A : b_ty) : @obj B :=
  match A with
  | b_Unit => terminal
  | b_Prod A B => prod (interp_base_ty A) (interp_base_ty B)
  | b_S => interp_sort
  end.

(* Kontextusok interpretációja *)
Fixpoint interp_ctx {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {M : SimpleModel B} 
  (G : b_context) : @obj B :=
  match G with
  | nil => terminal
  | A :: G' => prod (interp_ctx G') (interp_base_ty A)
  end.

(* ================================================================= *)
(* 3. BASE TERMS INTERPRETATION (Morphisms in B)                     *)
(* ================================================================= *)

(* Segédfüggvény a változók interpretálásához.
   Egy 'get_type n G = Some A' bizonyításból állít elő egy projekciós 
   morfizmust: interp_ctx G -> interp_base_ty A. *)
Fixpoint interp_var {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {M : SimpleModel B}
                    (G : b_context) (n : nat) (A : b_ty)
                    (H : get_type n G = Some A) {struct G}
                    : hom (interp_ctx G) (interp_base_ty A).
Proof.
  destruct G as [| B' G'].
  - (* G = nil esetén a get_type None lenne, ellentmondás *)
    simpl in H. destruct n; discriminate.
  - (* G = B' :: G' *) 
    destruct n as [| n'].
    + (* n = 0: Megtaláltuk a változót (A = B'). 
         A morfizmus a Descartes-i szorzat második komponense (prod_snd). *)
      simpl in H. injection H as Heq. subst B'.
      exact prod_snd.
    + (* n = S n': Tovább kell menni a kontextusban.
         A morfizmus a rekurzív hívás és az első komponensre (prod_fst) 
         való vetítés kompozíciója. *)
      simpl in H.
      exact (compose (interp_var B CB GF M G' n' A H) prod_fst).
Defined. (* 'Defined'-et használunk 'Qed' helyett, hogy a számítások redukálódhassanak! *)

(* A Bázis Termek (Morfizmusok) interpretációja a derivációs fa alapján. *)
Fixpoint interp_base_tm {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {M : SimpleModel B}
                        {G : b_context} {t : b_tm} {A : b_ty}
                        (D : base_typing G t A) {struct D}
                        : hom (interp_ctx G) (interp_base_ty A) :=
  match D in (base_typing G0 t0 A0) return (hom (interp_ctx G0) (interp_base_ty A0)) with
  
  (* Változó: Meghívjuk a segédfüggvényünket *)
  | BT_Var _ n _ H => interp_var _ n _ H
  
  (* Unit: Terminális leképezés a Cartesian kategóriából *)
  | BT_Unit _ => terminal_map
  
  (* Pár (Szorzat): A két interpretált részterm szorzata (prod_map) *)
  | BT_Pair _ _ _ _ _ D1 D2 => prod_map (interp_base_tm D1) (interp_base_tm D2)
  
  (* Első projekció: A kompozíció a bal oldali vetítéssel (prod_fst) *)
  | BT_Fst _ _ _ _ D1 => compose prod_fst (interp_base_tm D1)
  
  (* Második projekció: A kompozíció a jobb oldali vetítéssel (prod_snd) *)
  | BT_Snd _ _ _ _ D1 => compose prod_snd (interp_base_tm D1)
  
  end.
  
(* ================================================================= *)
(* 4. PREDICATE ARGUMENTS INTERPRETATION                             *)
(* ================================================================= *)

(* Az argumentum-lista interpretációja: egy morfizmust készítünk 
   a G kontextusból a predikátum szignatúrája (mint kontextus) felé. *)
Fixpoint interp_args {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {M : SimpleModel B}
                     {G : b_context} {ts : list b_tm} {As : list b_ty}
                     (ad : args_derivation G ts As) {struct ad}
                     : hom (interp_ctx G) (interp_ctx As) :=
  match ad in (args_derivation G0 ts0 As0) return (hom (interp_ctx G0) (interp_ctx As0)) with
  
  | AD_Nil G0 => 
      (* Üres lista esetén a terminális objektumba képezünk *)
      terminal_map
      
  | AD_Cons G0 t ts' A As' bt ad' => 
      (* A Coq most már tudja, hogy a kimenet típusa: 
         interp_ctx (A :: As') ami pontosan egyenlő azzal, hogy
         prod (interp_ctx As') (interp_base_ty A).
         A prod_map pont ezt a szorzatot gyártja le a két morfizmusból! *)
      prod_map (interp_args ad') (interp_base_tm bt)
      
  end.

(* ================================================================= *)
(* 5. HYPER FORMULA INTERPRETATION (Objects in Fiber Categories)     *)
(* ================================================================= *)

(* Egy 'G' kontextus kiterjesztésénél a projekció: G x A -> G *)
Definition ctx_proj {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {M : SimpleModel B} 
                    (G : b_context) (A : b_ty) : hom (interp_ctx (A :: G)) (interp_ctx G) :=
  @prod_fst B CB (interp_ctx G) (interp_base_ty A).
  
Fixpoint interp_formula {B : SetoidCategory} {CB : CartesianCategory B} 
                        {CC : CartesianClosedCategory B} 
                        {BiCC : BiCartesianClosedCategory CC} 
                        {GF : GoodFibration B} {M : SimpleModel B} 
                        {G : b_context} {Phi : h_ty} 
                        (fd : formula_derivation G Phi) 
                        : @obj (Fiber (interp_ctx G)) :=
  match fd in formula_derivation G' Phi' 
           return @obj (Fiber (interp_ctx G')) with
  
  | FD_Unit G' => 
      @terminal (Fiber (interp_ctx G')) (Fiber_is_Cartesian (interp_ctx G'))
      
  | FD_Void G' => 
      @initial (Fiber (interp_ctx G')) 
               (Fiber_is_Cartesian _) (Fiber_is_Closed _) (Fiber_is_BiClosed _)
  
  | FD_Prod G' A B d1 d2 => 
      (* Itt a visszatérési típus már @obj (Fiber (interp_ctx G')), ami egyezik d1-gyel! *)
      @prod (Fiber (interp_ctx G')) (Fiber_is_Cartesian _) 
            (interp_formula d1) 
            (interp_formula d2)
                 
  | FD_Sum G' A B d1 d2 => 
      @coprod (Fiber (interp_ctx G')) (Fiber_is_Cartesian _) (Fiber_is_Closed _) (Fiber_is_BiClosed _)
              (interp_formula d1) 
              (interp_formula d2)
                   
  | FD_Arr G' A B d1 d2 => 
      @exp (Fiber (interp_ctx G')) (Fiber_is_Cartesian _) (Fiber_is_Closed _)
           (interp_formula d2) 
           (interp_formula d1)
               
 | FD_Atom G' p ts ad => 
      (* A Pullback funktor hozza át a predikátumot a megfelelő fiberbe *)
      @fobj (Fiber (interp_ctx (predicate_sig p))) (* Forrás fiber *)
            (Fiber (interp_ctx G'))                 (* Cél fiber (ahol most vagyunk) *)
            (Pullback (interp_args ad))             (* Ez a funktor végzi a helyettesítést *)
            (@interp_atom B CB GF M p (interp_ctx (predicate_sig p))) (* Ez maga az objektum *)
            
  | FD_All G' A Phi0 d_body => 
      @fobj (Fiber (interp_ctx (A :: G'))) (Fiber (interp_ctx G')) (Pi_f (ctx_proj G' A)) 
            (interp_formula d_body)
            
  | FD_Ex G' A Phi0 d_body => 
      @fobj (Fiber (interp_ctx (A :: G'))) (Fiber (interp_ctx G')) (Sigma_f (ctx_proj G' A)) 
            (interp_formula d_body)
  end.
  
(* ================================================================= *)
(* 6. ENTAILS INTERPRETATION (Soundness of Deduction)                *)
(* ================================================================= *)


Require Import Coq.Program.Equality.
Require Import Coq.Logic.Eqdep_dec.

(* ================================================================= *)
(* COHERENCE: KATEGÓRIAELMÉLETI KONVERZIÓ (AXIÓMÁK NÉLKÜL!)          *)
(* ================================================================= *)

(* 1. LÉPÉS: A szintaxis egyenlőségének eldönthetősége *)
Lemma b_ty_eq_dec : forall (x y : b_ty), {x = y} + {x <> y}.
Proof. decide equality. Qed.

Lemma opt_b_ty_eq_dec : forall (x y : option b_ty), {x = y} + {x <> y}.
Proof. decide equality; apply b_ty_eq_dec. Qed.

(* 2. LÉPÉS: A get_type determinizmusa (UIP az opciókon, axióma nélkül!) *)
Lemma get_type_UIP : forall {G n A} (H1 H2 : get_type n G = Some A), H1 = H2.
Proof.
  intros. apply UIP_dec. apply opt_b_ty_eq_dec.
Qed.

(* 3. LÉPÉS: Bázis termek és argumentumok fa-függetlensége *)
Lemma interp_var_unique : forall {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {M : SimpleModel B} G n A (H1 H2 : get_type n G = Some A),
  @interp_var B CB GF M G n A H1 = @interp_var B CB GF M G n A H2.
Proof.
  intros. rewrite (get_type_UIP H1 H2). reflexivity.
Qed.

Lemma base_typing_unique : forall G t A1 A2 (d1 : base_typing G t A1) (d2 : base_typing G t A2), A1 = A2.
Proof.
  intros G t A1 A2 d1. generalize dependent A2.
  induction d1; intros A2 d2; dependent destruction d2.
  - (* BT_Var *) 
    (* A hibaüzenetedben e : get_type n G = Some A és e0 : get_type n G = Some A0 szerepel *)
    rewrite e in e0. 
    injection e0 as Heq. 
    exact Heq.
  - (* BT_Unit *) 
    reflexivity.
  - (* BT_Pair *) 
    f_equal.
    + apply IHd1_1. exact d2_1.
    + apply IHd1_2. exact d2_2.
  - (* BT_Fst *) 
    (* Itt az IHd1: forall A2, base_typing G t (b_Prod A A2) -> b_Prod A B = b_Prod A2 B0 *)
    apply IHd1 in d2. 
    injection d2 as Heq_A Heq_B. 
    exact Heq_A.
  - (* BT_Snd *) 
    apply IHd1 in d2. 
    injection d2 as Heq_A Heq_B. 
    exact Heq_B.
Qed.

Lemma interp_base_tm_unique : forall {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {M : SimpleModel B} G t A (d1 d2 : base_typing G t A),
  @interp_base_tm B CB GF M G t A d1 = @interp_base_tm B CB GF M G t A d2.
Proof.
  intros. generalize dependent d2. 
  induction d1; intro d2; dependent destruction d2; simpl.
  - apply interp_var_unique.
  - reflexivity.
  - f_equal. apply IHd1_1. apply IHd1_2.
  - (* BT_Fst *)
    pose proof (base_typing_unique _ _ _ _ d1 d2) as H_eq.
    injection H_eq. intros. subst. (* Ez beveszi az egyenlőséget és behelyettesíti *)
    f_equal. apply IHd1.
  - (* BT_Snd *)
    pose proof (base_typing_unique _ _ _ _ d1 d2) as H_eq.
    injection H_eq. intros. subst.
    f_equal. apply IHd1.
Qed.

Lemma interp_args_unique : forall {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {M : SimpleModel B} G ts As (d1 d2 : args_derivation G ts As),
  @interp_args B CB GF M G ts As d1 = @interp_args B CB GF M G ts As d2.
Proof.
  intros. generalize dependent d2.
  induction d1; intros d2; dependent destruction d2; simpl.
  - (* AD_Nil ág *)
    reflexivity.
  - (* AD_Cons ág *)
    f_equal.
    + apply IHd1.
    + apply interp_base_tm_unique. (* Vagy amilyen néven elmentetted *)
Qed.

Lemma formula_cast_iso {B : SetoidCategory} {CB : CartesianCategory B} 
                       {CC : CartesianClosedCategory B} 
                       {BiCC : BiCartesianClosedCategory CC} 
                       {GF : GoodFibration B} {M : SimpleModel B} : 
  forall {G : b_context} {A : h_ty} (d1 d2 : formula_derivation G A), 
  (hom (interp_formula d1) (interp_formula d2) * hom (interp_formula d2) (interp_formula d1))%type.
Proof.
  intros G A d1.
  induction d1; intros d2.

  - (* 1. FD_Unit *)
    (* d2 : formula_derivation G Ty_Unit. Csak FD_Unit lehet! *)
    dependent destruction d2. 
    split; apply id.

  - (* 2. FD_Void *)
    dependent destruction d2.
    split; apply id.

  - (* 3. FD_Prod *)
    dependent destruction d2.
    (* IHd1_1 és IHd1_2 tartalmazza az al-formulák izomorfizmusait *)
    split.
    + (* d1 -> d2 *)
      apply prod_map.
      * exact (compose (fst (IHd1_1 d2_1)) prod_fst).
      * exact (compose (fst (IHd1_2 d2_2)) prod_snd).
    + (* d2 -> d1 *)
      apply prod_map.
      * exact (compose (snd (IHd1_1 d2_1)) prod_fst).
      * exact (compose (snd (IHd1_2 d2_2)) prod_snd).

  - (* 4. FD_Sum *)
    dependent destruction d2.
    split.
    + apply coprod_map.
      * exact (compose coprod_inl (fst (IHd1_1 d2_1))).
      * exact (compose coprod_inr (fst (IHd1_2 d2_2))).
    + apply coprod_map.
      * exact (compose coprod_inl (snd (IHd1_1 d2_1))).
      * exact (compose coprod_inr (snd (IHd1_2 d2_2))).

  - (* 5. FD_Arr *)
    dependent destruction d2.
    (* Emlékeztető: interp_formula d1_1 d1_2 = [[d1_2]] ^ [[d1_1]] *)
    split.
    + (* d1 -> d2 : (B1^A1) -> (B2^A2) *)
      apply exp_map.
      (* Cél: [[d1_2^d1_1]] * [[d2_1]] -> [[d2_2]] *)
      (* 1. A domain-t (A2) visszavisszük A1-be (snd IH1) *)
      (* 2. Alkalmazzuk az evalt *)
      (* 3. A codomain-t (B1) elvisszük B2-be (fst IH2) *)
      exact (compose (fst (IHd1_2 d2_2)) 
              (compose eval 
                (prod_map prod_fst (compose (snd (IHd1_1 d2_1)) prod_snd)))).
    + (* d2 -> d1 : (B2^A2) -> (B1^A1) *)
      apply exp_map.
      exact (compose (snd (IHd1_2 d2_2)) 
              (compose eval 
                (prod_map prod_fst (compose (fst (IHd1_1 d2_1)) prod_snd)))).

  - (* 6. FD_Atom *)
    dependent destruction d2.
    assert (Heq : interp_args a = interp_args a0) by apply interp_args_unique.
    (* 1. Kibontjuk az interpretációt, hogy láthatóvá váljon az interp_args *)
    simpl interp_formula.
    (* 2. Most már a rewrite megtalálja a subterm-et *)
    rewrite Heq.
    (* 3. A két oldal most már teljesen azonos *)
    split; apply id.
  
  - (* 7. FD_All *)
    dependent destruction d2.
    (* A Pi_f funktorral visszük át az izomorfizmust *)
    split.
    + exact (@fmap _ _ (Pi_f (ctx_proj G A)) _ _ (fst (IHd1 d2))).
    + exact (@fmap _ _ (Pi_f (ctx_proj G A)) _ _ (snd (IHd1 d2))).

  - (* 8. FD_Ex *)
    dependent destruction d2.
    (* A Sigma_f funktorral visszük át az izomorfizmust *)
    split.
    + exact (@fmap _ _ (Sigma_f (ctx_proj G A)) _ _ (fst (IHd1 d2))).
    + exact (@fmap _ _ (Sigma_f (ctx_proj G A)) _ _ (snd (IHd1 d2))).
Defined.

Definition formula_cast {B : SetoidCategory} {CB : CartesianCategory B}
                        {CC : CartesianClosedCategory B}
                        {BiCC : BiCartesianClosedCategory CC}
                        {GF : GoodFibration B} {M : SimpleModel B}
                        {G : b_context} {A : h_ty} 
                        (d1 d2 : formula_derivation G A) :
  hom (@interp_formula B CB CC BiCC GF M G A d1) 
      (@interp_formula B CB CC BiCC GF M G A d2) :=
  fst (@formula_cast_iso B CB CC BiCC GF M G A d1 d2).

(* A logikai következtetés leképezése morfizmussá a szálkategóriában.
   Feltételezzük, hogy rendelkezésünkre áll a formulák helyességét igazoló fa (fd_phi, fd_psi). *)
   
Require Import Arith.
Require Import PeanoNat.

(* 1. A Base termek eltolása (b_tm) - A te logikád alapján! *)
Fixpoint b_lift (n : nat) (k : nat) (t : b_tm) : b_tm :=
  match t with
  | b_unit => b_unit
  | b_var i => if k <=? i then b_var (n + i) else b_var i
  | b_pair t1 t2 => b_pair (b_lift n k t1) (b_lift n k t2)
  | b_fst t' => b_fst (b_lift n k t')
  | b_snd t' => b_snd (b_lift n k t')
  end.

(* 2. A Hyper formulák eltolása (h_ty) *)
Fixpoint h_lift (n : nat) (k : nat) (Phi : h_ty) : h_ty :=
  match Phi with
  | Ty_Unit => Ty_Unit
  | Ty_Void => Ty_Void
  | Ty_Prod P1 P2 => Ty_Prod (h_lift n k P1) (h_lift n k P2)
  | Ty_Sum P1 P2  => Ty_Sum (h_lift n k P1) (h_lift n k P2)
  | Ty_Arr P1 P2  => Ty_Arr (h_lift n k P1) (h_lift n k P2)
  | Ty_Atom p ts  => Ty_Atom p (map (b_lift n k) ts)
  | Ty_All A P    => Ty_All A (h_lift n (Datatypes.S k) P) (* Így már tudja, hogy k+1 ! *)
  | Ty_Ex A P     => Ty_Ex A (h_lift n (Datatypes.S k) P)  (* Itt is Datatypes.S ! *)
  end.
  
(* 1. Beszúrás a b_context-be *)
Fixpoint insert_b_ty (k : nat) (B : b_ty) (G : b_context) : b_context :=
  match k, G with
  | 0, _ => B :: G
  | Datatypes.S k', A :: G' => A :: insert_b_ty k' B G'
  | Datatypes.S k', nil => nil 
  end.


(* A QED-ig levezetett segédlemma a kontextus indexeléséhez *)
Lemma insert_get_type : forall G n A B k,
  get_type n G = Some A ->
  get_type (if k <=? n then Datatypes.S n else n) (insert_b_ty k B G) = Some A.
Proof.
  induction G as [| C G' IH]; intros n A B0 k H.
  - (* G = nil *)
    destruct n; inversion H.
  - (* G = C :: G' *)
    destruct k as [|k'].
    + (* k = 0 *)
      simpl in *. destruct n; simpl in *; assumption.
    + (* k = S k' *)
      simpl. destruct n as [|n'].
      * (* n = 0 *)
        simpl in *. assumption.
      * (* n = S n' *)
            (* 1. Egyszerűsítjük H-t, hogy pontosan passzoljon az IH-hoz *)
            simpl in H. 
            
            (* 2. Ahelyett, hogy vakon apply-oznánk, "példányosítjuk" az IH-t *)
            specialize (IH n' A B0 k' H).
            
            (* 3. Szétbontjuk a beragadt if feltételt! *)
            destruct (k' <=? n') eqn:Heq.
            -- (* true ág: az index S (S n') lesz *)
               simpl. exact IH.
            -- (* false ág: az index S n' lesz *)
               simpl. exact IH.
Qed.

Lemma base_weakening_gen : forall G t A B k,
  base_typing G t A -> 
  base_typing (insert_b_ty k B G) (b_lift 1 k t) A.
Proof.
  intros G t A B k H.
  revert k.
  induction H; intros k; simpl.

  - (* 1. Var ág (Változó) *)
    (* Először kimentjük az igazságot a segédlemmából *)
    pose proof (insert_get_type G n A B k e) as H_get.
    
    (* Szétbontjuk az if feltételt! Így a Coq már b_var-t fog látni *)
    destruct (k <=? n) eqn:Heq.
    + (* true ág: b_var (S n) *)
      apply BT_Var. exact H_get.
    + (* false ág: b_var n *)
      apply BT_Var. exact H_get.

  - (* 2. Unit ág *)
    constructor.

  - (* 3. Pair ág *)
    constructor.
    + apply IHbase_typing1.
    + apply IHbase_typing2.

  - (* 4. Fst ág *)
    (* Itt econstructor kell, mert a Prod B felét a Coq-nak ki kell találnia az IH-ból *)
    econstructor. 
    apply IHbase_typing.

  - (* 5. Snd ág *)
    econstructor.
    apply IHbase_typing.
Qed.

(* És a végső gyengítés, amit a logikai fák (formula_weakening) használnak! *)
Theorem base_weakening : forall G t A B, 
  base_typing G t A -> base_typing (B :: G) (b_lift 1 0 t) A.
Proof.
  intros.
  exact (base_weakening_gen G t A B 0 H).
Qed.


(* 1. Argumentum-derivációk gyengítése (tetszőleges k mélységben) *)
Fixpoint args_weakening_gen {G ts As} B k (d : args_derivation G ts As) 
  : args_derivation (insert_b_ty k B G) (map (b_lift 1 k) ts) As :=
  match d in (args_derivation G' ts' As') 
    return (args_derivation (insert_b_ty k B G') (map (b_lift 1 k) ts') As') 
  with
  | AD_Nil G' => 
      AD_Nil (insert_b_ty k B G')
  | AD_Cons G' t ts' A' As' bt ad' => 
      AD_Cons (insert_b_ty k B G') _ _ _ _ 
              (base_weakening_gen G' t A' B k bt) 
              (args_weakening_gen B k ad')
  end.

(* 2. Formula-derivációk gyengítése (tetszőleges k mélységben) *)
Fixpoint formula_weakening_gen {G Phi} B k (d : formula_derivation G Phi) 
  : formula_derivation (insert_b_ty k B G) (h_lift 1 k Phi) :=
  match d with
  | FD_Unit _ => FD_Unit _
  | FD_Void _ => FD_Void _
  | FD_Prod _ _ _ d1 d2 => FD_Prod _ _ _ (formula_weakening_gen B k d1) (formula_weakening_gen B k d2)
  | FD_Sum _ _ _ d1 d2  => FD_Sum _ _ _ (formula_weakening_gen B k d1) (formula_weakening_gen B k d2)
  | FD_Arr _ _ _ d1 d2  => FD_Arr _ _ _ (formula_weakening_gen B k d1) (formula_weakening_gen B k d2)
  | FD_Atom _ p ts ad   => FD_Atom _ p _ (args_weakening_gen B k ad)
  
  (* KVANTOROK: Itt jön a mágia! Mivel belépünk az A' alá, a mélység Datatypes.S k lesz! *)
  | FD_All _ A' P d'    => FD_All _ A' _ (formula_weakening_gen B (Datatypes.S k) d')
  | FD_Ex _ A' P d'     => FD_Ex _ A' _ (formula_weakening_gen B (Datatypes.S k) d')
  end.

(* 3. A végső formula_weakening, amit a Soundness tétel (k=0) használ! *)
Definition formula_weakening {G Phi} B (d : formula_derivation G Phi) 
  : formula_derivation (B :: G) (h_lift 1 0 Phi) :=
  formula_weakening_gen B 0 d.

(* 1. Átkasztoljuk a derivációs fát a te h_shift-edre (Csak szintaxis) *)
Axiom shift_cast : forall {G A Psi},
  formula_derivation (A :: G) (h_lift 1 0 Psi) ->
  formula_derivation (A :: G) (Hyper_Substitution.h_shift 1 0 Psi).

(* 2. Kategóriaelméletileg ez egy izomorfizmus (Itt felvesszük a teljes kategória-környezetet!) *)
Axiom shift_cast_iso : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {CC : CartesianClosedCategory CatB} {BiCC : BiCartesianClosedCategory CC} 
  {GF : GoodFibration CatB} {M : SimpleModel CatB}
  {G A Psi} (d : formula_derivation (A :: G) (h_lift 1 0 Psi)),
  hom (interp_formula d) (interp_formula (shift_cast d)).

(* És az inverze (szintén a teljes környezettel) *)
Axiom shift_cast_iso_inv : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {CC : CartesianClosedCategory CatB} {BiCC : BiCartesianClosedCategory CC} 
  {GF : GoodFibration CatB} {M : SimpleModel CatB}
  {G A Psi} (d : formula_derivation (A :: G) (h_lift 1 0 Psi)),
  hom (interp_formula (shift_cast d)) (interp_formula d).

(* Az inverz Híd axióma: Pullback-ből a szintaktikai eltolásba *)
Axiom pullback_weakening_iso : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {CC : CartesianClosedCategory CatB} {BiCC : BiCartesianClosedCategory CC} 
  {GF : GoodFibration CatB} {M : SimpleModel CatB}
  {G : b_context} {Phi : h_ty} (A : b_ty) (d : formula_derivation G Phi),
  hom (@fobj _ _ (Pullback (ctx_proj G A)) (interp_formula d))
      (interp_formula (formula_weakening A d)).
      (* Az inverz Híd axióma: A szintaktikai eltolásból a Pullback-be *)
Axiom pullback_weakening_iso_inv : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {CC : CartesianClosedCategory CatB} {BiCC : BiCartesianClosedCategory CC} 
  {GF : GoodFibration CatB} {M : SimpleModel CatB}
  {G : b_context} {Phi : h_ty} (A : b_ty) (d : formula_derivation G Phi),
  hom (interp_formula (formula_weakening A d))
      (@fobj _ _ (Pullback (ctx_proj G A)) (interp_formula d)).

(* Keressük meg, mi a pontos neve a term-interpretációnak! 
   Feltételezem, hogy interp_tm vagy hasonló, de most M-en keresztül hívjuk. *)

(* A behelyettesítés kategóriaelméleti hídja *)
(* 1. Axióma a termek interpretációjára (Amíg meg nem írod a konkrét függvényt) *)

(* ================================================================= *)
(* A BEHELYETTESÍTÉS AXIÓMÁI (TÍPUSHELYES, VÉGLEGES VERZIÓ)          *)
(* ================================================================= *)

(* 1. Axióma a termek interpretációjára *)
Axiom interp_b_tm : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {GF : GoodFibration CatB} {M : SimpleModel CatB} 
  {G : b_context} {t : b_tm} {A : b_ty},
  base_typing G t A -> hom (interp_ctx G) (interp_base_ty A).

(* 1/B. A gráf morfizmus (G -> G x A), ami a behelyettesítés valódi alapja *)
Axiom subst_graph_mor : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {GF : GoodFibration CatB} {M : SimpleModel CatB} 
  {G : b_context} {t : b_tm} {A : b_ty},
  base_typing G t A -> hom (interp_ctx G) (interp_ctx (A :: G)).

(* 2. A behelyettesítés hídja (fd_subst -> t* fd_inner) *)
(* Itt már kötelező a CC és BiCC, mert az interp_formula használja őket! *)
Axiom subst_pullback_iso : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {CC : CartesianClosedCategory CatB} {BiCC : BiCartesianClosedCategory CC}
  {GF : GoodFibration CatB} {M : SimpleModel CatB}
  {G A Phi t} (bt : base_typing G t A) 
  (fd_inner : formula_derivation (A :: G) Phi)
  (fd_subst : formula_derivation G (Hyper_Substitution.h_subst 0 t Phi)), 
  hom (interp_formula fd_subst) 
      (@fobj _ _ (Pullback (subst_graph_mor bt)) (interp_formula fd_inner)).

(* 3. Az inverz behelyettesítés híd *)
Axiom subst_pullback_iso_inv : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {CC : CartesianClosedCategory CatB} {BiCC : BiCartesianClosedCategory CC}
  {GF : GoodFibration CatB} {M : SimpleModel CatB}
  {G A Phi t} (bt : base_typing G t A) 
  (fd_inner : formula_derivation (A :: G) Phi)
  (fd_subst : formula_derivation G (Hyper_Substitution.h_subst 0 t Phi)), 
  hom (@fobj _ _ (Pullback (subst_graph_mor bt)) (interp_formula fd_inner))
      (interp_formula fd_subst).

(* 4. ∀-elimináció egysége *)
Axiom all_elim_unit : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {CC : CartesianClosedCategory CatB} {BiCC : BiCartesianClosedCategory CC}
  {GF : GoodFibration CatB} {M : SimpleModel CatB} 
  {G A Phi t} (bt : base_typing G t A) (fd_inner : formula_derivation (A :: G) Phi),
  hom (@fobj _ _ (Pi_f (ctx_proj G A)) (interp_formula fd_inner)) 
      (@fobj _ _ (Pullback (subst_graph_mor bt)) (interp_formula fd_inner)).

(* 5. ∃-bevezetés egysége *)
Axiom ex_intro_unit : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {CC : CartesianClosedCategory CatB} {BiCC : BiCartesianClosedCategory CC}
  {GF : GoodFibration CatB} {M : SimpleModel CatB} 
  {G A Phi t} (bt : base_typing G t A) (fd_inner : formula_derivation (A :: G) Phi),
  hom (@fobj _ _ (Pullback (subst_graph_mor bt)) (interp_formula fd_inner)) 
      (@fobj _ _ (Sigma_f (ctx_proj G A)) (interp_formula fd_inner)).
Theorem soundness_hyper : forall {B : SetoidCategory} {CB : CartesianCategory B} 
  {CC : CartesianClosedCategory B} {BiCC : BiCartesianClosedCategory CC} (* Ezek kellenek! *)
  {GF : GoodFibration B} {M : SimpleModel B}
  {G : b_context} {Phi Psi : h_ty}
  (ed : entails_derivation G Phi Psi)
  (fd_phi : formula_derivation G Phi)
  (fd_psi : formula_derivation G Psi),
  inhabited (hom (interp_formula fd_phi) (interp_formula fd_psi)).
Proof.
  intros.
  generalize dependent fd_phi.
  generalize dependent fd_psi.
  induction ed; intros fd_psi fd_phi.

  - (* 1. LD_Id : Phi |- Phi *)
    apply inhabits. 
    (* A formula_cast-nak most már megvannak az implicit CC/BiCC példányai *)
    exact (formula_cast fd_phi fd_psi).

  - (* 2. LD_Comp : Phi |- Psi + Psi |- Chi => Phi |- Chi *)
    (* f a köztes deriváció (A_ent_B, B_ent_C) *)
    destruct (IHed1 f fd_phi) as [m1].
    destruct (IHed2 fd_psi f) as [m2].
    apply inhabits. 
    exact (compose m2 m1).

  - (* 3. LD_Top_Intro : G |- A -> Ty_Unit *)
    apply inhabits.
    (* Bármiből a terminálisba: terminal_map. Utána cast a cél fára. *)
    exact (compose (formula_cast (FD_Unit G) fd_psi) terminal_map).

  - (* 4. LD_Bot_Elim : G |- Ty_Void -> A *)
    apply inhabits.
    (* 1. Először cast-oljuk a kapott fd_phi-t a kanonikus (FD_Void G) fába. 
          Ez [[fd_phi]] -> [[FD_Void G]] irányú morfizmus. *)
    (* 2. Utána az initial_map-pel ugrunk az [[FD_Void G]]-ből (ami a kategória ⊥ objektuma) 
          közvetlenül az interp_formula fd_psi objektumba. *)
    exact (compose initial_map (formula_cast fd_phi (FD_Void G))).
  - (* 5. LD_And_Intro : G |- C -> A * B *)
    dependent destruction fd_psi.
    destruct (IHed1 fd_psi1 fd_phi) as [m1].
    destruct (IHed2 fd_psi2 fd_phi) as [m2].
    apply inhabits.
    exact (prod_map m1 m2).

  - (* 6. LD_And_E1 : G |- A * B -> A *)
    dependent destruction fd_phi.
    apply inhabits.
    exact (compose (formula_cast fd_phi1 fd_psi) prod_fst).

  - (* 7. LD_And_E2 : G |- A * B -> B *)
    dependent destruction fd_phi.
    apply inhabits.
    exact (compose (formula_cast fd_phi2 fd_psi) prod_snd).

  - (* 8. LD_Or_Intro1 : G |- A -> A + B *)
    dependent destruction fd_psi.
    apply inhabits.
    exact (compose coprod_inl (formula_cast fd_phi fd_psi1)).

  - (* 9. LD_Or_Intro2 : G |- B -> A + B *)
    dependent destruction fd_psi.
    apply inhabits.
    exact (compose coprod_inr (formula_cast fd_phi fd_psi2)).

  - (* 10. LD_Or_Elim : G |- A + B -> C *)
    dependent destruction fd_phi.
    destruct (IHed1 fd_psi fd_phi1) as [m1].
    destruct (IHed2 fd_psi fd_phi2) as [m2].
    apply inhabits.
    exact (coprod_map m1 m2).

  - (* 11. LD_Arr_Intro : G |- C -> (A -> B) *)
    dependent destruction fd_psi. 
    (* fd_prod definíciója a rekurzióhoz *)
    set (fd_prod := FD_Prod G C A fd_phi fd_psi1).
    destruct (IHed fd_psi2 fd_prod) as [m].
    apply inhabits.
    apply exp_map.
    exact m.

 - (* 12. LD_Arr_Elim : G |- (A -> B0) * A -> B0 *)
    dependent destruction fd_phi.  (* fd_phi1: A -> B0, fd_phi2: A *)
    dependent destruction fd_phi1. (* fd_phi1_1: A, fd_phi1_2: B0 *)
    apply inhabits.
    
    (* 1. Kibontjuk a kategóriaelméleti objektumokat *)
    simpl interp_formula.
    
    (* 2. A végső cast: B0_eredeti -> B0_cél *)
    apply (compose (formula_cast fd_phi1_2 fd_psi)).
    
    (* 3. Két alcélt hozunk létre az eapply compose-zal *)
    eapply compose.
    
    (* 4. A VARÁZSLAT: Először a MÁSODIK alcélt oldjuk meg! (A bemenetet) *)
    2: { 
      eapply prod_map.
      + (* Visszatérítjük az (A -> B0) részt *)
        apply prod_fst.
      + (* Kivesszük az 'A'-t, és cast-oljuk a megfelelőre *)
        exact (compose (formula_cast fd_phi2 fd_phi1_1) prod_snd).
    }
    
    (* 5. Most visszatérünk az ELSŐ alcélhoz. 
          A Coq már tudja a pontos típusokat a 2. lépésből, 
          így az eval mindenféle implicit hiba nélkül, tökéletesen illeszkedik! *)
    1: { 
      apply eval. 
    }
- (* 13. LD_All_Intro : G |- Psi -> ∀A.Phi *)
    dependent destruction fd_psi. 
    
    (* 1. Először előkészítjük a bemeneteket az IHed-hez *)
    pose (fd_phi_weak := formula_weakening A fd_phi).
    pose (fd_phi_weak_real := shift_cast fd_phi_weak).
    
    (* 2. DESTRUCT MIELŐTT CÉLT VÁLTUNK! 
          Mivel a célunk itt még 'inhabited' (Prop), a Coq boldogan engedi. *)
    destruct (IHed fd_psi fd_phi_weak_real) as [m_inner].
    
    (* 3. MOST váltjuk át a célt Type-ra az inhabits-szel! *)
    apply inhabits.
    
    (* 4. Kinyitjuk az interpretációt, hogy a Coq lássa a ∀ (Pi) funktort! *)
    simpl interp_formula.
    
    (* 5. A kategóriaelméleti adjunkció bevetése *)
    eapply right_adj_mor.
    
   (* 6. Összefűzzük a morfizmusokat: 
          A matematikai f ∘ g (compose) miatt HÁTULRÓL ELŐRE kell megadnunk a láncszemeket! *)
    eapply compose.
    { (* A lánc legutolsó lépése: h_shift(Psi) -> Phi *)
      exact m_inner. }
    eapply compose.
    { (* A lánc középső lépése: h_lift(Psi) -> h_shift(Psi) *)
      exact (shift_cast_iso fd_phi_weak). }
     (* A lánc legelső lépése: Pullback(Psi) -> h_lift(Psi) *)
      exact (pullback_weakening_iso A fd_phi). 
- (* 14. LD_All_Elim : G |- ∀A.Phi -> Phi[t/x] *)
    dependent destruction fd_phi. 
    apply inhabits.
    simpl interp_formula.
    
    (* Kompozíció: ∀ Phi -> Pullback(Phi) -> Phi[t/x] *)
    eapply compose.
    { (* A lánc vége: a Pullback-ből a behelyettesített formulába *)
      exact (subst_pullback_iso_inv b fd_phi fd_psi). }
    { (* A lánc eleje: a ∀ (Pi) funktor egysége a gráf morfizmus mentén *)
      exact (all_elim_unit b fd_phi). }

  - (* 15. LD_Ex_Intro : G |- Phi[t/x] -> ∃A.Phi *)
    dependent destruction fd_psi.
    apply inhabits.
    simpl interp_formula.
    
    (* Kompozíció: Phi[t/x] -> Pullback(Phi) -> ∃ Phi *)
    eapply compose.
    { (* A lánc vége: a Pullback-ből az ∃ (Sigma) funktorba *)
      exact (ex_intro_unit b fd_psi). }
    { (* A lánc eleje: a behelyettesített formulából a Pullback-be *)
      exact (subst_pullback_iso b fd_psi fd_phi). }

  - (* 16. LD_Ex_Elim : G |- ∃A.Phi -> Psi *)
    dependent destruction fd_phi.
    
    (* 1. Előkészítjük a cél (Psi) gyengítését és a konverziót *)
    pose (fd_psi_weak := formula_weakening A fd_psi).
    pose (fd_psi_weak_real := shift_cast fd_psi_weak).
    
    (* 2. Indukciós hipotézis a belső (A :: G) kontextusban *)
    destruct (IHed fd_psi_weak_real fd_phi) as [m_inner].
    
    apply inhabits.
    simpl interp_formula.
    
    (* 3. Bal adjunkció alkalmazása *)
    eapply left_adj_mor.
    
    (* 4. Kompozíció hátulról előre: Phi_inner -> h_shift(Psi) -> h_lift(Psi) -> Pullback(Psi) *)
    eapply compose.
    { exact (pullback_weakening_iso_inv A fd_psi). } (* <--- ITT A JAVÍTÁS (_inv) *)
    eapply compose.
    { exact (shift_cast_iso_inv fd_psi_weak). }
    { exact m_inner. }

  - (* 17. LD_Atom_Eq : strukturális egyenlőség ága *)
    (* 1. A környezetben lévő e : ts1 = ts2 alapján egységesítjük a formulákat *)
    subst ts2. 
    apply inhabits.
    
    (* 2. Mivel fd_phi és fd_psi két KÜLÖNBÖZŐ fa ugyanarra a (Ty_Atom p ts1) formulára,
          a korábban megírt formula_cast lemmádat használjuk az 'id' helyett! *)
    exact (formula_cast fd_phi fd_psi).
Qed.
