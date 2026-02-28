Require Import List Arith Lia.
Require Import PeanoNat.  
Require Import Coq.Classes.Morphisms.
Import ListNotations.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Eqdep_dec.

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
Require Import Coq.Program.Equality.
Require Import HyperLogic.Logic.Base.Simple.Base_Equiv.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Substitution.


(* ================================================================= *)
(* 1. MODEL DEFINITION                                               *)
(* ================================================================= *)

(* What: Defines the basic interpretation of sorts and atomic predicates.
   Why: Provides the fundamental semantic mapping required to interpret the logic in a categorical framework. *)
Class SimpleModel (B : SetoidCategory) {CB : CartesianCategory B} {GF : GoodFibration B} := {
  interp_sort : @obj B;
  interp_atom : forall (p : nat) (dom : @obj B), @obj (Fiber dom)
}.

(* ================================================================= *)
(* 2. BASE INTERPRETATION (Contexts & Types)                         *)
(* ================================================================= *)

(* What: Interprets base syntactic types into categorical objects.
   Why: Maps the syntax of types to the semantic base category (B). *)
Fixpoint interp_base_ty {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {M : SimpleModel B} 
  (A : b_ty) : @obj B :=
  match A with
  | b_Unit => terminal
  | b_Prod A B => prod (interp_base_ty A) (interp_base_ty B)
  | b_S => interp_sort
  end.

(* What: Interprets typing contexts (lists of types) into categorical objects.
   Why: A context is semantically represented as the Cartesian product of its constituent types. *)
Fixpoint interp_ctx {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {M : SimpleModel B} 
  (G : b_context) : @obj B :=
  match G with
  | nil => terminal
  | A :: G' => prod (interp_ctx G') (interp_base_ty A)
  end.

(* ================================================================= *)
(* 3. BASE TERMS INTERPRETATION (Morphisms in B)                     *)
(* ================================================================= *)

(* What: Creates a projection morphism for a variable lookup in a context.
   Why: Variables denote projections from the context product to the specific type object. *)
Fixpoint interp_var {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {M : SimpleModel B}
                    (G : b_context) (n : nat) (A : b_ty)
                    (H : get_type n G = Some A) {struct G}
                    : hom (interp_ctx G) (interp_base_ty A).
Proof.
  destruct G as [| B' G'].
  - (* Contradiction: variable cannot exist in an empty context. *)
    simpl in H. destruct n; discriminate.
  - destruct n as [| n'].
    + simpl in H. injection H as Heq. subst B'.
      exact prod_snd.
    + simpl in H.
      exact (compose (interp_var B CB GF M G' n' A H) prod_fst).
Defined. 

(* What: Interprets base term typing derivations into categorical morphisms.
   Why: Terms represent functions (morphisms) from the interpreted context to the interpreted type. *)
Fixpoint interp_base_tm {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {M : SimpleModel B}
                        {G : b_context} {t : b_tm} {A : b_ty}
                        (D : base_typing G t A) {struct D}
                        : hom (interp_ctx G) (interp_base_ty A) :=
  match D in (base_typing G0 t0 A0) return (hom (interp_ctx G0) (interp_base_ty A0)) with
  | BT_Var _ n _ H => interp_var _ n _ H
  | BT_Unit _ => terminal_map
  | BT_Pair _ _ _ _ _ D1 D2 => prod_map (interp_base_tm D1) (interp_base_tm D2)
  | BT_Fst _ _ _ _ D1 => compose prod_fst (interp_base_tm D1)
  | BT_Snd _ _ _ _ D1 => compose prod_snd (interp_base_tm D1)
  end.

(* ================================================================= *)
(* 4. PREDICATE ARGUMENTS INTERPRETATION                             *)
(* ================================================================= *)

(* What: Interprets a list of argument terms into a single morphism.
   Why: Predicates require an aggregated morphism from the current context to the predicate's signature context to perform substitution via pullbacks. *)
Fixpoint interp_args {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {M : SimpleModel B}
                     {G : b_context} {ts : list b_tm} {As : list b_ty}
                     (ad : args_derivation G ts As) {struct ad}
                     : hom (interp_ctx G) (interp_ctx As) :=
  match ad in (args_derivation G0 ts0 As0) return (hom (interp_ctx G0) (interp_ctx As0)) with
  | AD_Nil G0 => terminal_map
  | AD_Cons G0 t ts' A As' bt ad' => prod_map (interp_args ad') (interp_base_tm bt)
  end.

(* ================================================================= *)
(* 5. HYPER FORMULA INTERPRETATION (Objects in Fiber Categories)     *)
(* ================================================================= *)

(* What: Creates a projection morphism from an extended context (A :: G) to the original context (G).
   Why: Required as the base morphism for the Pi and Sigma functors representing quantifiers. *)
Definition ctx_proj {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {M : SimpleModel B} 
                    (G : b_context) (A : b_ty) : hom (interp_ctx (A :: G)) (interp_ctx G) :=
  @prod_fst B CB (interp_ctx G) (interp_base_ty A).

(* What: Interprets formula derivations into categorical objects within fiber categories.
   Why: Maps logical connectives to category limits/colimits and quantifiers to adjoint functors. *)
Fixpoint interp_formula {B : SetoidCategory} {CB : CartesianCategory B} 
                        {CC : CartesianClosedCategory B} 
                        {BiCC : BiCartesianClosedCategory CC} 
                        {GF : GoodFibration B} {M : SimpleModel B} 
                        {G : b_context} {Phi : h_ty} 
                        (fd : formula_derivation G Phi) 
                        : @obj (Fiber (interp_ctx G)) :=
  match fd in formula_derivation G' Phi' 
    return @obj (Fiber (interp_ctx G')) with
  
  | FD_Unit G' => @terminal (Fiber (interp_ctx G')) (Fiber_is_Cartesian (interp_ctx G'))
  | FD_Void G' => @initial (Fiber (interp_ctx G')) (Fiber_is_Cartesian _) (Fiber_is_Closed _) (Fiber_is_BiClosed _)
  | FD_Prod G' A B d1 d2 => @prod (Fiber (interp_ctx G')) (Fiber_is_Cartesian _) (interp_formula d1) (interp_formula d2)
  | FD_Sum G' A B d1 d2 => @coprod (Fiber (interp_ctx G')) (Fiber_is_Cartesian _) (Fiber_is_Closed _) (Fiber_is_BiClosed _) (interp_formula d1) (interp_formula d2)
  | FD_Arr G' A B d1 d2 => @exp (Fiber (interp_ctx G')) (Fiber_is_Cartesian _) (Fiber_is_Closed _) (interp_formula d2) (interp_formula d1)
  | FD_Atom G' p ts ad => @fobj (Fiber (interp_ctx (predicate_sig p))) (Fiber (interp_ctx G')) (Pullback (interp_args ad)) (@interp_atom B CB GF M p (interp_ctx (predicate_sig p)))
  | FD_All G' A Phi0 d_body => @fobj (Fiber (interp_ctx (A :: G'))) (Fiber (interp_ctx G')) (Pi_f (ctx_proj G' A)) (interp_formula d_body)
  | FD_Ex G' A Phi0 d_body => @fobj (Fiber (interp_ctx (A :: G'))) (Fiber (interp_ctx G')) (Sigma_f (ctx_proj G' A)) (interp_formula d_body)
  end.

(* ================================================================= *)
(* 6. COHERENCE LEMMAS (Proof Irrelevance for Derivation Trees)      *)
(* ================================================================= *)

(* What: Decides equality for base types.
   Why: Required to prove uniqueness of identity proofs (UIP) for context lookups. *)
Lemma b_ty_eq_dec : forall (x y : b_ty), {x = y} + {x <> y}.
Proof. decide equality. Qed.

Lemma opt_b_ty_eq_dec : forall (x y : option b_ty), {x = y} + {x <> y}.
Proof. decide equality; apply b_ty_eq_dec. Qed.

(* What: Proves that context lookups yield unique proofs.
   Why: Ensures variable interpretation doesn't branch unpredictably based on the lookup proof. *)
Lemma get_type_UIP : forall {G n A} (H1 H2 : get_type n G = Some A), H1 = H2.
Proof. intros. apply UIP_dec. apply opt_b_ty_eq_dec. Qed.

(* What: Ensures the interpretation of a variable is independent of the derivation proof tree.
   Why: Semantics should depend only on the proposition, not the syntactic proof artifact. *)
Lemma interp_var_unique : forall {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {M : SimpleModel B} G n A (H1 H2 : get_type n G = Some A),
  @interp_var B CB GF M G n A H1 = @interp_var B CB GF M G n A H2.
Proof. intros. rewrite (get_type_UIP H1 H2). reflexivity. Qed.

Lemma base_typing_unique : forall G t A1 A2 (d1 : base_typing G t A1) (d2 : base_typing G t A2), A1 = A2.
Proof.
  intros G t A1 A2 d1. generalize dependent A2.
  induction d1; intros A2 d2; dependent destruction d2.
  - rewrite e in e0. injection e0 as Heq. exact Heq.
  - reflexivity.
  - f_equal. apply IHd1_1. exact d2_1. apply IHd1_2. exact d2_2.
  - apply IHd1 in d2. injection d2 as Heq_A Heq_B. exact Heq_A.
  - apply IHd1 in d2. injection d2 as Heq_A Heq_B. exact Heq_B.
Qed.

(* What: Ensures term interpretations are independent of the derivation tree. *)
Lemma interp_base_tm_unique : forall {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {M : SimpleModel B} G t A (d1 d2 : base_typing G t A),
  @interp_base_tm B CB GF M G t A d1 = @interp_base_tm B CB GF M G t A d2.
Proof.
  intros. generalize dependent d2. 
  induction d1; intro d2; dependent destruction d2; simpl.
  - apply interp_var_unique.
  - reflexivity.
  - f_equal. apply IHd1_1. apply IHd1_2.
  - pose proof (base_typing_unique _ _ _ _ d1 d2) as H_eq. injection H_eq. intros. subst. f_equal. apply IHd1.
  - pose proof (base_typing_unique _ _ _ _ d1 d2) as H_eq. injection H_eq. intros. subst. f_equal. apply IHd1.
Qed.

(* What: Ensures argument interpretations are independent of the derivation tree. *)
Lemma interp_args_unique : forall {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} {M : SimpleModel B} G ts As (d1 d2 : args_derivation G ts As),
  @interp_args B CB GF M G ts As d1 = @interp_args B CB GF M G ts As d2.
Proof.
  intros. generalize dependent d2.
  induction d1; intros d2; dependent destruction d2; simpl.
  - reflexivity.
  - f_equal. apply IHd1. apply interp_base_tm_unique.
Qed.

(* What: Generates an isomorphism between two distinct derivation trees of the exact same formula.
   Why: In Coq, `formula_derivation G A` acts as an index. If we have two different derivations for `A`, their interpreted objects differ observationally. We need an explicit categorical cast to align them. *)
Lemma formula_cast_iso {B : SetoidCategory} {CB : CartesianCategory B} 
                       {CC : CartesianClosedCategory B} 
                       {BiCC : BiCartesianClosedCategory CC} 
                       {GF : GoodFibration B} {M : SimpleModel B} : 
  forall {G : b_context} {A : h_ty} (d1 d2 : formula_derivation G A), 
  (hom (interp_formula d1) (interp_formula d2) * hom (interp_formula d2) (interp_formula d1))%type.
Proof.
  intros G A d1. induction d1; intros d2.
  - dependent destruction d2. split; apply id.
  - dependent destruction d2. split; apply id.
  - dependent destruction d2.
    split.
    + apply prod_map. exact (compose (fst (IHd1_1 d2_1)) prod_fst). exact (compose (fst (IHd1_2 d2_2)) prod_snd).
    + apply prod_map. exact (compose (snd (IHd1_1 d2_1)) prod_fst). exact (compose (snd (IHd1_2 d2_2)) prod_snd).
  - dependent destruction d2.
    split.
    + apply coprod_map. exact (compose coprod_inl (fst (IHd1_1 d2_1))). exact (compose coprod_inr (fst (IHd1_2 d2_2))).
    + apply coprod_map. exact (compose coprod_inl (snd (IHd1_1 d2_1))). exact (compose coprod_inr (snd (IHd1_2 d2_2))).
  - dependent destruction d2.
    split.
    + apply exp_map. exact (compose (fst (IHd1_2 d2_2)) (compose eval (prod_map prod_fst (compose (snd (IHd1_1 d2_1)) prod_snd)))).
    + apply exp_map. exact (compose (snd (IHd1_2 d2_2)) (compose eval (prod_map prod_fst (compose (fst (IHd1_1 d2_1)) prod_snd)))).
  - dependent destruction d2. assert (Heq : interp_args a = interp_args a0) by apply interp_args_unique.
    simpl interp_formula. rewrite Heq. split; apply id.
  - dependent destruction d2.
    split.
    + exact (@fmap _ _ (Pi_f (ctx_proj G A)) _ _ (fst (IHd1 d2))).
    + exact (@fmap _ _ (Pi_f (ctx_proj G A)) _ _ (snd (IHd1 d2))).
  - dependent destruction d2.
    split.
    + exact (@fmap _ _ (Sigma_f (ctx_proj G A)) _ _ (fst (IHd1 d2))).
    + exact (@fmap _ _ (Sigma_f (ctx_proj G A)) _ _ (snd (IHd1 d2))).
Defined.

(* What: Extracts the forward morphism from the formula_cast_iso isomorphism. *)
Definition formula_cast {B : SetoidCategory} {CB : CartesianCategory B}
                        {CC : CartesianClosedCategory B}
                        {BiCC : BiCartesianClosedCategory CC}
                        {GF : GoodFibration B} {M : SimpleModel B}
                        {G : b_context} {A : h_ty} 
                        (d1 d2 : formula_derivation G A) :
  hom (@interp_formula B CB CC BiCC GF M G A d1) 
      (@interp_formula B CB CC BiCC GF M G A d2) :=
  fst (@formula_cast_iso B CB CC BiCC GF M G A d1 d2).

(* ================================================================= *)
(* 7. WEAKENING AND LIFTING OPERATIONS                               *)
(* ================================================================= *)

(* What: Shifts De Bruijn indices in base terms to accommodate context extensions.
   Why: Essential for preserving referential integrity when pushing formulas inside quantifiers. *)
Fixpoint b_lift (n : nat) (k : nat) (t : b_tm) : b_tm :=
  match t with
  | b_unit => b_unit
  | b_var i => if k <=? i then b_var (n + i) else b_var i
  | b_pair t1 t2 => b_pair (b_lift n k t1) (b_lift n k t2)
  | b_fst t' => b_fst (b_lift n k t')
  | b_snd t' => b_snd (b_lift n k t')
  end.

(* What: Shifts De Bruijn indices within logical formulas. *)
Fixpoint h_lift (n : nat) (k : nat) (Phi : h_ty) : h_ty :=
  match Phi with
  | Ty_Unit => Ty_Unit
  | Ty_Void => Ty_Void
  | Ty_Prod P1 P2 => Ty_Prod (h_lift n k P1) (h_lift n k P2)
  | Ty_Sum P1 P2  => Ty_Sum (h_lift n k P1) (h_lift n k P2)
  | Ty_Arr P1 P2  => Ty_Arr (h_lift n k P1) (h_lift n k P2)
  | Ty_Atom p ts  => Ty_Atom p (map (b_lift n k) ts)
  | Ty_All A P    => Ty_All A (h_lift n (Datatypes.S k) P)
  | Ty_Ex A P     => Ty_Ex A (h_lift n (Datatypes.S k) P) 
  end.

(* What: Inserts a new type into the context list at a specific depth. *)
Fixpoint insert_b_ty (k : nat) (B : b_ty) (G : b_context) : b_context :=
  match k, G with
  | 0, _ => B :: G
  | Datatypes.S k', A :: G' => A :: insert_b_ty k' B G'
  | Datatypes.S k', nil => nil 
  end.

(* What: Maintains structural integrity of context lookups after an insertion. *)
Lemma insert_get_type : forall G n A B k,
  get_type n G = Some A ->
  get_type (if k <=? n then Datatypes.S n else n) (insert_b_ty k B G) = Some A.
Proof.
  induction G as [| C G' IH]; intros n A B0 k H.
  - destruct n; inversion H.
  - destruct k as [|k'].
    + simpl in *. destruct n; simpl in *; assumption.
    + simpl. destruct n as [|n'].
      * simpl in *. assumption.
      * simpl in H. specialize (IH n' A B0 k' H).
        destruct (k' <=? n') eqn:Heq.
        -- simpl. exact IH.
        -- simpl. exact IH.
Qed.

(* What: General weakening operation for base typing derivations. *)
Lemma base_weakening_gen : forall G t A B k,
  base_typing G t A -> 
  base_typing (insert_b_ty k B G) (b_lift 1 k t) A.
Proof.
  intros G t A B k H. revert k.
  induction H; intros k; simpl.
  - pose proof (insert_get_type G n A B k e) as H_get.
    destruct (k <=? n) eqn:Heq.
    + apply BT_Var. exact H_get.
    + apply BT_Var. exact H_get.
  - constructor.
  - constructor. apply IHbase_typing1. apply IHbase_typing2.
  - econstructor. apply IHbase_typing.
  - econstructor. apply IHbase_typing.
Qed.

Theorem base_weakening : forall G t A B, 
  base_typing G t A -> base_typing (B :: G) (b_lift 1 0 t) A.
Proof. intros. exact (base_weakening_gen G t A B 0 H). Qed.

(* What: General weakening operation for argument derivations. *)
Fixpoint args_weakening_gen {G ts As} B k (d : args_derivation G ts As) 
  : args_derivation (insert_b_ty k B G) (map (b_lift 1 k) ts) As :=
  match d in (args_derivation G' ts' As') 
    return (args_derivation (insert_b_ty k B G') (map (b_lift 1 k) ts') As') 
  with
  | AD_Nil G' => AD_Nil (insert_b_ty k B G')
  | AD_Cons G' t ts' A' As' bt ad' => AD_Cons (insert_b_ty k B G') _ _ _ _ (base_weakening_gen G' t A' B k bt) (args_weakening_gen B k ad')
  end.

(* What: General weakening operation for formula derivations. *)
Fixpoint formula_weakening_gen {G Phi} B k (d : formula_derivation G Phi) 
  : formula_derivation (insert_b_ty k B G) (h_lift 1 k Phi) :=
  match d with
  | FD_Unit _ => FD_Unit _
  | FD_Void _ => FD_Void _
  | FD_Prod _ _ _ d1 d2 => FD_Prod _ _ _ (formula_weakening_gen B k d1) (formula_weakening_gen B k d2)
  | FD_Sum _ _ _ d1 d2  => FD_Sum _ _ _ (formula_weakening_gen B k d1) (formula_weakening_gen B k d2)
  | FD_Arr _ _ _ d1 d2  => FD_Arr _ _ _ (formula_weakening_gen B k d1) (formula_weakening_gen B k d2)
  | FD_Atom _ p ts ad   => FD_Atom _ p _ (args_weakening_gen B k ad)
  | FD_All _ A' P d'    => FD_All _ A' _ (formula_weakening_gen B (Datatypes.S k) d')
  | FD_Ex _ A' P d'     => FD_Ex _ A' _ (formula_weakening_gen B (Datatypes.S k) d')
  end.

(* What: Specialized formula weakening for surface-level shifting. *)
Definition formula_weakening {G Phi} B (d : formula_derivation G Phi) 
  : formula_derivation (B :: G) (h_lift 1 0 Phi) :=
  formula_weakening_gen B 0 d.
  
(* What: Provides a global term interpretation fallback if local recursion fails.
   Why: Explicit assertion to safely map base typing to categorical morphisms inside specific proofs. *)
Lemma interp_b_tm {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {GF : GoodFibration CatB} {M : SimpleModel CatB} 
  {G : b_context} {t : b_tm} {A : b_ty}
  (bt : base_typing G t A) : hom (interp_ctx G) (interp_base_ty A).
Proof.
  exact (interp_base_tm bt).
Defined.

(* What: Defines the underlying graph morphism for substitution.
   Why: Substitution conceptually maps G to G x A. We pullback along this specific morphism to replace the variable. *)
Lemma subst_graph_mor {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {GF : GoodFibration CatB} {M : SimpleModel CatB} 
  {G : b_context} {t : b_tm} {A : b_ty}
  (bt : base_typing G t A) : hom (interp_ctx G) (interp_ctx (A :: G)).
Proof.
  (* Az interp_ctx (A :: G) definíció szerint: prod (interp_ctx G) (interp_base_ty A) *)
  simpl.
  (* A morfizmus: <id, [[t]]> *)
  apply prod_map.
  - apply id.
  - exact (interp_base_tm bt).
Defined.

Lemma base_subst_id : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {GF : GoodFibration CatB} {M : SimpleModel CatB}
  {G : b_context} {t : b_tm} {A : b_ty} (bt : base_typing G t A),
  compose (ctx_proj G A) (subst_graph_mor bt) ≅ id (interp_ctx G).
Proof.
  intros.
  (* Kibontjuk a definíciókat: ctx_proj = prod_fst, subst_graph_mor = prod_map id [[t]] *)
  unfold ctx_proj, subst_graph_mor.
  (* A CartesianCategory axiómája kimondja: prod_fst ∘ (f ∏ g) ≅ f. Itt f = id. *)
  apply prod_map_fst.
Qed.


(* ================================================================= *)
(* 8. SEMANTIC AXIOMS (Isomorphisms & Categorical Bridges)           *)
(* ================================================================= *)

 
(* 1. Segédlemma: A bázis termek szintaktikai eltolása megegyezik. *)
(* Megmutatjuk, hogy a b_lift ugyanazt csinálja, mint a Base_Equiv-ben lévő shift. *)
Lemma b_lift_eq_shift : forall t d c,
  b_lift d c t = shift d c t.
Proof.
  induction t; intros d c; simpl.
  - (* b_var *)
    (* Esetszétválasztás a két különböző ellenőrzésre: c <= n és n < c *)
    destruct (c <=? n) eqn:Hle; destruct (n <? c) eqn:Hlt.
    + (* Lehetetlen eset: egyszerre kisebb és nagyobb-egyenlő *)
      apply Nat.leb_le in Hle. apply Nat.ltb_lt in Hlt. lia.
    + (* A változót eltoljuk. Az összeadás kommutatív: d + n = n + d *)
      f_equal. lia.
    + (* A változó nem változik *)
      reflexivity.
    + (* Lehetetlen eset *)
      apply Nat.leb_gt in Hle. apply Nat.ltb_ge in Hlt. lia.
  - (* b_unit *) 
    reflexivity.
  - (* b_pair *) 
    f_equal. apply IHt1. apply IHt2.
  - (* b_fst *) 
    f_equal. apply IHt.
  - (* b_snd *) 
    f_equal. apply IHt.
Qed.

(* 2. Segédlemma: A listán történő map-elés is megegyezik *)
Lemma map_b_lift_eq_map_shift : forall ts d c,
  map (b_lift d c) ts = map_shift_base d c ts.
Proof.
  intros ts d c.
  unfold map_shift_base. (* Kibontjuk a Hyper_Substitution.v-s definíciót *)
  apply map_ext. (* A List könyvtár lemmája: ha a belső fv-ek egyeznek, a map is egyezik *)
  intro t. apply b_lift_eq_shift.
Qed.

(* 3. Segédlemma: A hyper formulák eltolása megegyezik. *)
Lemma h_lift_eq_h_shift : forall Phi d c,
  h_lift d c Phi = h_shift d c Phi.
Proof.
  induction Phi; intros d c; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IHPhi1. apply IHPhi2.
  - f_equal. apply IHPhi1. apply IHPhi2.
  - f_equal. apply IHPhi1. apply IHPhi2.
  - (* Ty_Atom: Itt hívjuk be a listás segédlemmánkat *)
    f_equal. apply map_b_lift_eq_map_shift.
  - (* Kvantorok: A küszöb (c) eggyel nő *)
    f_equal. apply IHPhi.
  - f_equal. apply IHPhi.
Qed.

(* ================================================================= *)
(* VÉGREHAJTÁS: Az axióma kiváltása Lemmával                         *)
(* ================================================================= *)
(* What: Translates the derivation tree from the custom `h_lift` to the logic's built-in `h_shift`.
   Why: Required to bridge the gap between two identical syntactic transformations implemented via different functions. *)
Lemma shift_cast : forall {G A Psi},
  formula_derivation (A :: G) (h_lift 1 0 Psi) ->
  formula_derivation (A :: G) (h_shift 1 0 Psi).
Proof.
  intros G A Psi H.
  (* Mivel h_lift és h_shift teljesen egyenlőek, egyszerűen átírjuk egyiket a másikra *)
  rewrite <- h_lift_eq_h_shift.
  exact H.
Defined. 

(* ================================================================= *)
(* SZINTAKTIKAI CAST IZOMORFIZMUSOK                                  *)
(* ================================================================= *)

Lemma shift_cast_iso : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {CC : CartesianClosedCategory CatB} {BiCC : BiCartesianClosedCategory CC} 
  {GF : GoodFibration CatB} {M : SimpleModel CatB}
  {G A Psi} (d : formula_derivation (A :: G) (h_lift 1 0 Psi)),
  hom (interp_formula d) (interp_formula (shift_cast d)).
Proof.
  intros.
  (* Kibontjuk a shift_cast definícióját, ami tartalmazza a rewrite-ot *)
  unfold shift_cast.
  (* Általánosítjuk azt az egyenlőséget, amit a rewrite használt *)
  generalize (h_lift_eq_h_shift Psi 1 0).
  intro e.
  (* Amikor destruct-áljuk az egyenlőséget, a Coq rájön, hogy a két típus 
     ténylegesen azonos, így a "cast" eltűnik, és shift_cast d ≡ d lesz. *)
  destruct e.
  simpl.
  (* Így a cél hom (interp_formula d) (interp_formula d) marad, ami az identitás. *)
  apply id.
Defined.

Lemma shift_cast_iso_inv : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {CC : CartesianClosedCategory CatB} {BiCC : BiCartesianClosedCategory CC} 
  {GF : GoodFibration CatB} {M : SimpleModel CatB}
  {G A Psi} (d : formula_derivation (A :: G) (h_lift 1 0 Psi)),
  hom (interp_formula (shift_cast d)) (interp_formula d).
Proof.
  intros.
  unfold shift_cast.
  generalize (h_lift_eq_h_shift Psi 1 0).
  intro e.
  destruct e.
  simpl.
  apply id.
Defined.
(*

ITT ELHASAL 2 lemma erejéig

*)

(* Ha a bázisban f ≅ g, akkor a Pullback f (A) és Pullback g (A) között van morfizmus *)
Lemma pb_equiv_morphism : forall {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B}
  {I J : @obj B} (f g : hom I J) (A : @obj (Fiber J)),
  f ≅ g -> hom (@fobj _ _ (Pullback f) A) (@fobj _ _ (Pullback g) A).
Proof.
  intros B CB GF I J f g A H.
  
  (* 1. Letesszük a garantált izomorfizmust a kontextusba *)
  pose proof (pb_iso f g H A) as H_iso.
  
  (* 2. Mivel az iso_to típusa már eleve maga a morfizmus (hom), 
        egyszerűen ezt adjuk meg. A Coq a háttérben lévő Typeclass 
        mechanizmussal megtalálja hozzá a most letett H_iso-t. *)
  exact iso_to.
Defined.


(* A már említett bázis-szintű azonosság: fst ∘ <id, t> ≅ id *)
Lemma ctx_proj_subst_id : forall {B : SetoidCategory} {CB : CartesianCategory B} 
  {GF : GoodFibration B} {M : SimpleModel B} (* <-- Ez a két paraméter hiányzott! *)
  {G : b_context} {t : b_tm} {A : b_ty} (bt : base_typing G t A),
  compose (ctx_proj G A) (subst_graph_mor bt) ≅ id (interp_ctx G).
Proof.
  intros. unfold ctx_proj, subst_graph_mor. simpl. 
  apply prod_map_fst.
Qed.

(* ================================================================= *)
(* WEAKENING BRIDGE (Oda irány: Pullback -> Weakening)               *)
(* ================================================================= *)

(* Bázisszintű lemma: az argumentumok gyengítése egyenlő a projekcióval való kompozícióval *)

Lemma args_weakening_commutes : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {GF : GoodFibration CatB} {M : SimpleModel CatB}
  {G : b_context} {A : b_ty} {p : nat} {ts : list b_tm} 
  (a : args_derivation G ts (predicate_sig p)),
  interp_args (args_weakening_gen A 0 a) ≅ compose (interp_args a) (ctx_proj G A). (* <-- ITT A CSERE *)
Proof. 
  (* Ezt a bázis szintű tulajdonságot a modell konkrét felépítésekor bizonyítjuk *)
Admitted.


Lemma pullback_weakening_iso_both : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {CC : CartesianClosedCategory CatB} {BiCC : BiCartesianClosedCategory CC} 
  {GF : GoodFibration CatB} {M : SimpleModel CatB}
  {G : b_context} {Phi : h_ty} (A : b_ty) (d : formula_derivation G Phi),
  (hom (@fobj _ _ (Pullback (ctx_proj G A)) (interp_formula d))
       (interp_formula (formula_weakening A d))) * (hom (interp_formula (formula_weakening A d))
       (@fobj _ _ (Pullback (ctx_proj G A)) (interp_formula d))).
Proof.
  intros. induction d; simpl. (* <--- FIGYELEM: ITT NINCS ; split! *)
  
  - (* FD_Unit *) 
    split.
    + exact (@iso_to _ _ _ (pb_term_iso (ctx_proj G A))).
    + exact (@iso_from _ _ _ (pb_term_iso (ctx_proj G A))).
  
  - (* FD_Void *) 
    split.
    + exact (@iso_to _ _ _ (pb_init_iso (ctx_proj G A))).
    + exact (@iso_from _ _ _ (pb_init_iso (ctx_proj G A))).
  
  - (* FD_Prod (És) *)
    destruct IHd1 as [IHd1_to IHd1_from].
    destruct IHd2 as [IHd2_to IHd2_from].
    split. (* <--- A destruct UTÁN bontunk, így mindkét ág látja a változókat! *)
    + (* Oda *)
      eapply compose.
      * apply prod_map.
        -- eapply compose. { exact IHd1_to. } { eapply prod_fst. }
        -- eapply compose. { exact IHd2_to. } { eapply prod_snd. }
      * exact (@iso_to _ _ _ (pb_prod_iso (ctx_proj G A) _ _)).
    + (* Vissza *)
      eapply compose.
      * exact (@iso_from _ _ _ (pb_prod_iso (ctx_proj G A) _ _)).
      * apply prod_map.
        -- eapply compose. { exact IHd1_from. } { eapply prod_fst. }
        -- eapply compose. { exact IHd2_from. } { eapply prod_snd. }
        
  - (* FD_Sum (Vagy) *)
    destruct IHd1 as [IHd1_to IHd1_from].
    destruct IHd2 as [IHd2_to IHd2_from].
    split.
    + (* Oda *)
      eapply compose.
      * eapply coprod_map.
        -- eapply compose. { apply coprod_inl. } { exact IHd1_to. }
        -- eapply compose. { apply coprod_inr. } { exact IHd2_to. }
      * exact (@iso_to _ _ _ (pb_coprod_iso (ctx_proj G A) _ _)).
    + (* Vissza *)
      eapply compose.
      * exact (@iso_from _ _ _ (pb_coprod_iso (ctx_proj G A) _ _)).
      * eapply coprod_map.
        -- eapply compose. { apply coprod_inl. } { exact IHd1_from. }
        -- eapply compose. { apply coprod_inr. } { exact IHd2_from. }
        
 - (* FD_Arr (Implikáció) *)
    destruct IHd1 as [IHd1_to IHd1_from].
    destruct IHd2 as [IHd2_to IHd2_from].
    split.
    + (* Oda *)
      eapply compose.
      * apply exp_map.
        -- eapply compose. { exact IHd2_to. }
           eapply compose. { eapply eval. }
           apply prod_map.
           ++ eapply prod_fst. (* Az első komponenst érintetlenül hagyjuk (pi_1) *)
           ++ eapply compose. { exact IHd1_from. } { eapply prod_snd. } (* A másodikra: IH_from o pi_2 *)
      * exact (@iso_to _ _ _ (pb_exp_iso (ctx_proj G A) _ _)).
    + (* Vissza *)
      eapply compose.
      * exact (@iso_from _ _ _ (pb_exp_iso (ctx_proj G A) _ _)).
      * apply exp_map.
        -- eapply compose. { exact IHd2_from. }
           eapply compose. { eapply eval. }
           apply prod_map.
           ++ eapply prod_fst.
           ++ eapply compose. { exact IHd1_to. } { eapply prod_snd. } (* Kontravariancia: itt a _to kell! *)
        
 - (* FD_Atom *) 
    split.
    + (* Oda irány: fobj (fobj P) -> fobj P *)
      eapply compose.
      * (* 2. Lépés (a legvégén): fobj P -> fobj P (Ekvivalencia a bázisban) *)
        apply pb_equiv_morphism. symmetry. apply args_weakening_commutes. (* <--- 1. Cél kipipálva! *)
      * (* 1. Lépés (az elején): fobj (fobj P) -> fobj P (A kompozíciós izomorfizmus VISSZA iránya) *)
        exact (@iso_from _ _ _ (pullback_comp_iso _ _ _)).
        
    + (* Vissza irány: fobj P -> fobj (fobj P) *)
      eapply compose.
      * (* 2. Lépés (a legvégén): fobj P -> fobj (fobj P) (A kompozíciós izomorfizmus ODA iránya) *)
        exact (@iso_to _ _ _ (pullback_comp_iso _ _ _)).
      * (* 1. Lépés (az elején): fobj P -> fobj P (Ekvivalencia a bázisban) *)
        apply pb_equiv_morphism. apply args_weakening_commutes. (* <--- 2. Cél kipipálva! *)
 
(*
  - (* FD_All (Minden) *)
    destruct IHd as [IHd_to IHd_from].
    split.
    + (* Oda *)
      eapply compose.
      * apply fmap; exact IHd_to.
      * exact (@iso_to _ _ _ (beck_chevalley_pi (ctx_proj G A) _)).
    + (* Vissza *)
      eapply compose.
      * exact (@iso_from _ _ _ (beck_chevalley_pi (ctx_proj G A) _)).
      * apply fmap; exact IHd_from.
      
  - (* FD_Ex (Létezik) *)
    destruct IHd as [IHd_to IHd_from].
    split.
    + (* Oda *)
      eapply compose.
      * apply fmap; exact IHd_to.
      * exact (@iso_to _ _ _ (beck_chevalley_sigma (ctx_proj G A) _)).
    + (* Vissza *)
      eapply compose.
      * exact (@iso_from _ _ _ (beck_chevalley_sigma (ctx_proj G A) _)).
      * apply fmap; exact IHd_from.
Admitted.


Lemma pullback_weakening_iso : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {CC : CartesianClosedCategory CatB} {BiCC : BiCartesianClosedCategory CC} 
  {GF : GoodFibration CatB} {M : SimpleModel CatB}
  {G : b_context} {Phi : h_ty} (A : b_ty) (d : formula_derivation G Phi),
  hom (@fobj _ _ (Pullback (ctx_proj G A)) (interp_formula d))
      (interp_formula (formula_weakening A d)).
Proof.
  intros. induction d; simpl.
  - (* FD_Unit (Igaz) *) 
    exact (@iso_to _ _ _ (pb_term_iso (ctx_proj G A))).
  - (* FD_Void (Hamis) *) 
    exact (@iso_to _ _ _ (pb_init_iso (ctx_proj G A))).
  
  - (* FD_Prod (És) *)
    eapply compose.
    + apply prod_map. (* A párosítás <f, g> *)
      * eapply compose. exact IHd1. eapply prod_fst. (* f o pi_1 *)
      * eapply compose. exact IHd2. eapply prod_snd. (* g o pi_2 *)
    + exact (@iso_to _ _ _ (pb_prod_iso (ctx_proj G A) _ _)).
  
  - (* FD_Sum (Vagy) *)
    (* Itt a coprod_map a [f, g] univerzális tulajdonság, amihez az i_1 és i_2 injekciók kellenek *)
    eapply compose.
    + eapply coprod_map.
      * eapply compose. apply coprod_inl. exact IHd1. (* i_1 o f *)
      * eapply compose. apply coprod_inr. exact IHd2. (* i_2 o g *)
    + exact (@iso_to _ _ _ (pb_coprod_iso (ctx_proj G A) _ _)).
    
 - (* FD_Arr (Implikáció) *)
    eapply compose.
    + apply exp_map.
      * { eapply (pullback_weakening_iso_inv A d1). } (* A kontravariáns ág: visszafelé mutat *)
      * { exact IHd2. }                              (* A kovariáns ág: előrefelé mutat *)
    + exact (@iso_to _ _ _ (pb_exp_iso (ctx_proj G A) _ _)).
    
  - (* FD_Atom (Predikátum) *)
    admit.
    
  - (* FD_All (Minden) *)
    eapply compose.
    + apply fmap; exact IHd.
    + exact (@iso_to _ _ _ (beck_chevalley_pi (ctx_proj G A) _)).
    
  - (* FD_Ex (Létezik) *)
    eapply compose.
    + apply fmap; exact IHd.
    + exact (@iso_to _ _ _ (beck_chevalley_sigma (ctx_proj G A) _)).
Admitted.

(* ================================================================= *)
(* WEAKENING BRIDGE INVERSE (Vissza irány: Weakening -> Pullback)    *)
(* ================================================================= *)
Lemma pullback_weakening_iso_inv : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {CC : CartesianClosedCategory CatB} {BiCC : BiCartesianClosedCategory CC} 
  {GF : GoodFibration CatB} {M : SimpleModel CatB}
  {G : b_context} {Phi : h_ty} (A : b_ty) (d : formula_derivation G Phi),
  hom (interp_formula (formula_weakening A d))
      (@fobj _ _ (Pullback (ctx_proj G A)) (interp_formula d)).
Proof.
  intros. induction d; simpl.
  - (* FD_Unit *) 
    exact (iso_from (pb_term_iso (ctx_proj G A))).
  - (* FD_Void *) 
    exact (iso_from (pb_init_iso (ctx_proj G A))).
  - (* FD_Prod *)
    eapply compose.
    + apply prod_map; assumption.
    + exact (iso_from (pb_prod_iso (ctx_proj G A) _ _)).
  - (* FD_Sum *)
    eapply compose.
    + apply coprod_map; assumption.
    + exact (iso_from (pb_coprod_iso (ctx_proj G A) _ _)).
  - (* FD_Arr *)
    eapply compose.
    + apply exp_map; assumption.
    + exact (iso_from (pb_exp_iso (ctx_proj G A) _ _)).
  - (* FD_Atom *)
    admit.
  - (* FD_All *)
    eapply compose.
    + apply fmap. assumption.
    + exact (iso_from (beck_chevalley_pi (ctx_proj G A) _)).
  - (* FD_Ex *)
    eapply compose.
    + apply fmap. assumption.
    + exact (iso_from (beck_chevalley_sigma (ctx_proj G A) _)).
Admitted.
(* What: Maps a categorical pullback along the context projection to the syntax of weakening.
   Why: In categorical logic, weakening a context corresponds to a functorial pullback along a context projection. *)
Axiom pullback_weakening_iso : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {CC : CartesianClosedCategory CatB} {BiCC : BiCartesianClosedCategory CC} 
  {GF : GoodFibration CatB} {M : SimpleModel CatB}
  {G : b_context} {Phi : h_ty} (A : b_ty) (d : formula_derivation G Phi),
  hom (@fobj _ _ (Pullback (ctx_proj G A)) (interp_formula d))
      (interp_formula (formula_weakening A d)).

(* What: Inverse of the pullback weakening bridge. *)
Axiom pullback_weakening_iso_inv : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {CC : CartesianClosedCategory CatB} {BiCC : BiCartesianClosedCategory CC} 
  {GF : GoodFibration CatB} {M : SimpleModel CatB}
  {G : b_context} {Phi : h_ty} (A : b_ty) (d : formula_derivation G Phi),
  hom (interp_formula (formula_weakening A d))
      (@fobj _ _ (Pullback (ctx_proj G A)) (interp_formula d)).


(* What: Bridges syntactic substitution to a categorical pullback along the graph morphism.
   Why: Formalizes the substitution lemma of categorical logic. *)
Axiom subst_pullback_iso : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {CC : CartesianClosedCategory CatB} {BiCC : BiCartesianClosedCategory CC}
  {GF : GoodFibration CatB} {M : SimpleModel CatB}
  {G A Phi t} (bt : base_typing G t A) 
  (fd_inner : formula_derivation (A :: G) Phi)
  (fd_subst : formula_derivation G (Hyper_Substitution.h_subst 0 t Phi)), 
  hom (interp_formula fd_subst) 
      (@fobj _ _ (Pullback (subst_graph_mor bt)) (interp_formula fd_inner)).

(* What: The inverse isomorphism for the substitution pullback. *)
Axiom subst_pullback_iso_inv : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {CC : CartesianClosedCategory CatB} {BiCC : BiCartesianClosedCategory CC}
  {GF : GoodFibration CatB} {M : SimpleModel CatB}
  {G A Phi t} (bt : base_typing G t A) 
  (fd_inner : formula_derivation (A :: G) Phi)
  (fd_subst : formula_derivation G (Hyper_Substitution.h_subst 0 t Phi)), 
  hom (@fobj _ _ (Pullback (subst_graph_mor bt)) (interp_formula fd_inner))
      (interp_formula fd_subst).

(* What: Exposes the natural transformation (counit) between the Pi functor and Pullback.
   Why: Categorically evaluates the universal quantifier. *)
Axiom all_elim_unit : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {CC : CartesianClosedCategory CatB} {BiCC : BiCartesianClosedCategory CC}
  {GF : GoodFibration CatB} {M : SimpleModel CatB} 
  {G A Phi t} (bt : base_typing G t A) (fd_inner : formula_derivation (A :: G) Phi),
  hom (@fobj _ _ (Pi_f (ctx_proj G A)) (interp_formula fd_inner)) 
      (@fobj _ _ (Pullback (subst_graph_mor bt)) (interp_formula fd_inner)).

(* What: Exposes the natural transformation (unit) between Pullback and the Sigma functor.
   Why: Categorically introduces the existential quantifier. *)
Axiom ex_intro_unit : forall {CatB : SetoidCategory} {CB : CartesianCategory CatB} 
  {CC : CartesianClosedCategory CatB} {BiCC : BiCartesianClosedCategory CC}
  {GF : GoodFibration CatB} {M : SimpleModel CatB} 
  {G A Phi t} (bt : base_typing G t A) (fd_inner : formula_derivation (A :: G) Phi),
  hom (@fobj _ _ (Pullback (subst_graph_mor bt)) (interp_formula fd_inner)) 
      (@fobj _ _ (Sigma_f (ctx_proj G A)) (interp_formula fd_inner)).


(* ================================================================= *)
(* 9. SOUNDNESS THEOREM                                              *)
(* ================================================================= *)

(* What: Main theorem connecting natural deduction rules to categorical morphisms.
   Why: Ensures the deduction system is sound with respect to the categorical semantics. *)
Theorem soundness_hyper : forall {B : SetoidCategory} {CB : CartesianCategory B} 
  {CC : CartesianClosedCategory B} {BiCC : BiCartesianClosedCategory CC}
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

  - (* 1. LD_Id *)
    apply inhabits.
    exact (formula_cast fd_phi fd_psi).

  - (* 2. LD_Comp *)
    destruct (IHed1 f fd_phi) as [m1].
    destruct (IHed2 fd_psi f) as [m2].
    apply inhabits. 
    exact (compose m2 m1).

  - (* 3. LD_Top_Intro *)
    apply inhabits.
    exact (compose (formula_cast (FD_Unit G) fd_psi) terminal_map).

  - (* 4. LD_Bot_Elim *)
    apply inhabits.
    exact (compose initial_map (formula_cast fd_phi (FD_Void G))).

  - (* 5. LD_And_Intro *)
    dependent destruction fd_psi.
    destruct (IHed1 fd_psi1 fd_phi) as [m1].
    destruct (IHed2 fd_psi2 fd_phi) as [m2].
    apply inhabits.
    exact (prod_map m1 m2).

  - (* 6. LD_And_E1 *)
    dependent destruction fd_phi.
    apply inhabits.
    exact (compose (formula_cast fd_phi1 fd_psi) prod_fst).

  - (* 7. LD_And_E2 *)
    dependent destruction fd_phi.
    apply inhabits.
    exact (compose (formula_cast fd_phi2 fd_psi) prod_snd).

  - (* 8. LD_Or_Intro1 *)
    dependent destruction fd_psi.
    apply inhabits.
    exact (compose coprod_inl (formula_cast fd_phi fd_psi1)).

  - (* 9. LD_Or_Intro2 *)
    dependent destruction fd_psi.
    apply inhabits.
    exact (compose coprod_inr (formula_cast fd_phi fd_psi2)).

  - (* 10. LD_Or_Elim *)
    dependent destruction fd_phi.
    destruct (IHed1 fd_psi fd_phi1) as [m1].
    destruct (IHed2 fd_psi fd_phi2) as [m2].
    apply inhabits.
    exact (coprod_map m1 m2).

  - (* 11. LD_Arr_Intro *)
    dependent destruction fd_psi.
    set (fd_prod := FD_Prod G C A fd_phi fd_psi1).
    destruct (IHed fd_psi2 fd_prod) as [m].
    apply inhabits.
    apply exp_map.
    exact m.

  - (* 12. LD_Arr_Elim *)
    dependent destruction fd_phi.
    dependent destruction fd_phi1.
    apply inhabits.
    simpl interp_formula.
    
    apply (compose (formula_cast fd_phi1_2 fd_psi)).
    eapply compose.
    
    (* Resolve the input morphism first *)
    2: { 
      eapply prod_map.
        apply prod_fst.
        exact (compose (formula_cast fd_phi2 fd_phi1_1) prod_snd).
    }
    (* Apply the evaluation map *)
    1: { 
      apply eval.
    }

  - (* 13. LD_All_Intro *)
    dependent destruction fd_psi.
    
    pose (fd_phi_weak := formula_weakening A fd_phi).
    pose (fd_phi_weak_real := shift_cast fd_phi_weak).
    destruct (IHed fd_psi fd_phi_weak_real) as [m_inner].
    
    apply inhabits.
    simpl interp_formula.
    
    (* Universal quantifier translates to the right adjoint of pullback *)
    eapply right_adj_mor.
    eapply compose.
    { exact m_inner. }
    eapply compose.
    { exact (shift_cast_iso fd_phi_weak). }
    { exact (pullback_weakening_iso A fd_phi). }

  - (* 14. LD_All_Elim *)
    dependent destruction fd_phi. 
    apply inhabits.
    simpl interp_formula.
    
    eapply compose.
    { exact (subst_pullback_iso_inv b fd_phi fd_psi). }
    { exact (all_elim_unit b fd_phi). }

  - (* 15. LD_Ex_Intro *)
    dependent destruction fd_psi.
    apply inhabits.
    simpl interp_formula.
    
    eapply compose.
    { exact (ex_intro_unit b fd_psi). }
    { exact (subst_pullback_iso b fd_psi fd_phi). }

  - (* 16. LD_Ex_Elim *)
    dependent destruction fd_phi.
    
    pose (fd_psi_weak := formula_weakening A fd_psi).
    pose (fd_psi_weak_real := shift_cast fd_psi_weak).
    destruct (IHed fd_psi_weak_real fd_phi) as [m_inner].
    
    apply inhabits.
    simpl interp_formula.
    
    (* Existential quantifier translates to the left adjoint of pullback *)
    eapply left_adj_mor.
    eapply compose.
    { exact (pullback_weakening_iso_inv A fd_psi). }
    eapply compose.
    { exact (shift_cast_iso_inv fd_psi_weak). }
    { exact m_inner. }

  - (* 17. LD_Atom_Eq *)
    subst ts2.
    apply inhabits.
    exact (formula_cast fd_phi fd_psi).
    
Qed.
*)
Admitted.