Require Import HyperLogic.Cat.Core. 
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import Coq.Classes.Morphisms.

(** * 1. The Core Fibration (Hyperdoctrine) *)

(** WHAT IT IS:
  The [GoodFibration] class defines a categorical hyperdoctrine, serving as the 
  semantic foundation for our logic. It maps a Cartesian base category of individuals 
  to a family of BiCartesian Closed Categories (fibers) representing propositions.

  WHY WE CHOSE THIS SOLUTION:
  1. Local Proof Irrelevance: We explicitly require [fiber_is_thin]. This enforces 
     that the logic is Proof Irrelevant (at most one proof exists between any two 
     propositions), collapsing the logic into a preorder.
  2. Explicit Preservation Axioms: Even though right/left adjoints mathematically 
     preserve limits/colimits (and the fibers are Thin), we explicitly include 
     preservation isomorphisms (e.g., [pb_prod_iso]). In Coq, omitting these would 
     force us to manually reconstruct the isomorphisms from adjunctions every time 
     we rewrite, which severely hinders proof automation.
*)

Class GoodFibration (B : SetoidCategory) {CB : CartesianCategory B} := mk_GoodFibration {
  
  (** The indexed category mapping contexts to logical fibers *)
  Fiber : @obj B -> SetoidCategory;
  
  (** Fibers are locally Proof Irrelevant (Thin categories) *)
  fiber_is_thin : forall (I : @obj B), Thin (Fiber I);

  (** Logical structure of each fiber (Propositional logic / Heyting algebra) *)
  Fiber_is_Cartesian : forall (I : @obj B), CartesianCategory (Fiber I);
  Fiber_is_Closed    : forall (I : @obj B), @CartesianClosedCategory (Fiber I) (Fiber_is_Cartesian I);
  Fiber_is_BiClosed  : forall (I : @obj B), @BiCartesianClosedCategory (Fiber I) (Fiber_is_Cartesian I) (Fiber_is_Closed I);
  
  (** Substitution functor between fibers *)
  Pullback : forall {I J : @obj B}, (hom I J) -> Functor (Fiber J) (Fiber I);
  
  (** Structural isomorphisms for substitution *)
  pullback_id_iso : forall {I : @obj B} (A : @obj (Fiber I)),
      (@fobj _ _ (Pullback (id I)) A) ≅O A;
  pullback_comp_iso : forall {I J K : @obj B} (g : hom J K) (f : hom I J) (A : @obj (Fiber K)),
      (@fobj _ _ (Pullback (compose g f)) A) ≅O
      (@fobj _ _ (Pullback f) (@fobj _ _ (Pullback g) A));

  (** Logical preservation isomorphisms (convenience for rewriting) *)
  pb_term_iso : forall {I J : @obj B} (f : hom I J),
      (@fobj _ _ (Pullback f) (@terminal _ (Fiber_is_Cartesian J))) ≅O
      (@terminal _ (Fiber_is_Cartesian I));
  pb_prod_iso : forall {I J : @obj B} (f : hom I J) (A B : @obj (Fiber J)),
      (@fobj _ _ (Pullback f) (@prod _ (Fiber_is_Cartesian J) A B)) ≅O
      (@prod _ (Fiber_is_Cartesian I) (@fobj _ _ (Pullback f) A) (@fobj _ _ (Pullback f) B));
  pb_init_iso : forall {I J : @obj B} (f : hom I J),
      (@fobj _ _ (Pullback f) (@initial _ _ (Fiber_is_Closed J) (Fiber_is_BiClosed J))) ≅O
      (@initial _ _ (Fiber_is_Closed I) (Fiber_is_BiClosed I));
  pb_coprod_iso : forall {I J : @obj B} (f : hom I J) (A B : @obj (Fiber J)),
      (@fobj _ _ (Pullback f) (@coprod _ _ (Fiber_is_Closed J) (Fiber_is_BiClosed J) A B)) ≅O
      (@coprod _ _ (Fiber_is_Closed I) (Fiber_is_BiClosed I) (@fobj _ _ (Pullback f) A) (@fobj _ _ (Pullback f) B));
  pb_exp_iso : forall {I J : @obj B} (f : hom I J) (A B : @obj (Fiber J)),
      (@fobj _ _ (Pullback f) (@exp _ _ (Fiber_is_Closed J) A B)) ≅O
      (@exp _ _ (Fiber_is_Closed I) (@fobj _ _ (Pullback f) A) (@fobj _ _ (Pullback f) B));

 (** Quantifiers as Adjoints to substitution (Kizárólag a projekciók mentén!) *)
  pullback_has_left_adjoint : forall {I A : @obj B}, IsRightAdjoint (Pullback (@prod_fst B CB I A));
  pullback_has_right_adjoint : forall {I A : @obj B}, IsLeftAdjoint (Pullback (@prod_fst B CB I A));

  (** Beck-Chevalley conditions for quantifier commutation *)
  beck_chevalley_sigma : forall {I J K : @obj B} (f : hom K I) (A : @obj (Fiber (@prod B CB I J))),
      (@fobj _ _ (Pullback f) (@left_adj_obj _ _ _ pullback_has_left_adjoint A)) ≅O
      (@left_adj_obj _ _ _ pullback_has_left_adjoint
          (@fobj _ _ (Pullback (@prod_map B CB (prod K J) I J (compose f (@prod_fst B CB K J)) (@prod_snd B CB K J))) A));
          
  beck_chevalley_pi : forall {I J K : @obj B} (f : hom K I) (A : @obj (Fiber (@prod B CB I J))),
      (@fobj _ _ (Pullback f) (@right_adj_obj _ _ _ pullback_has_right_adjoint A)) ≅O
      (@right_adj_obj _ _ _ pullback_has_right_adjoint
          (@fobj _ _ (Pullback (@prod_map B CB (prod K J) I J (compose f (@prod_fst B CB K J)) (@prod_snd B CB K J))) A));

  (** Congruence of base morphisms over substitution *)
  pb_iso : forall {I J : @obj B} (f g : hom I J),
      f ≅ g -> forall (A : @obj (Fiber J)), (@fobj _ _ (Pullback f) A) ≅O (@fobj _ _ (Pullback g) A)
}.

(** ** Typeclass Registrations for Fibers *)

Global Instance GF_Fiber_CC
  {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} (I : @obj B)
  : CartesianCategory (Fiber I) := Fiber_is_Cartesian I.

Global Instance GF_Fiber_CCC
  {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} (I : @obj B)
  : CartesianClosedCategory (Fiber I) := Fiber_is_Closed I.

Global Instance GF_Fiber_BCCC
  {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} (I : @obj B)
  : BiCartesianClosedCategory (GF_Fiber_CCC I) := Fiber_is_BiClosed I.

Global Instance GF_Fiber_Thin
  {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} (I : @obj B)
  : Thin (Fiber I) := fiber_is_thin I.


(** * 2. The Total Category (Grothendieck Construction) *)

(** WHAT IT IS:
  The construction of the Total Space (often denoted as E), which mathematically 
  flattens the indexed category into a single large category containing both 
  base individuals and fiber propositions.

  WHY WE CHOSE THIS SOLUTION:
  Instead of using Coq's 'Record' keyword (which binds projections tightly), 
  we use 'Class' alongside 'Arguments' overriding. This allows us to manually 
  control Coq's implicit resolution mechanism, ensuring that dependent 
  typeclasses don't aggressively hide our target objects, preventing 
  "Non-functional construction" errors later.
*)

Class TotalObj {B : SetoidCategory} {CB : CartesianCategory B} (GF : GoodFibration B) := mk_TotalObj {
  t_base : @obj B;
  t_fib  : @obj (Fiber t_base)
}.
(** Force projection parameters to be explicit to avoid typeclass overreach. *)
Arguments t_base {_ _ _} _.
Arguments t_fib {_ _ _} _.

Class TotalHom {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} (X Y : TotalObj GF) := mk_TotalHom {
  h_base : hom (t_base X) (t_base Y);
  h_fib  : hom (t_fib X) (@fobj _ _ (Pullback h_base) (t_fib Y))
}.
Arguments h_base {_ _ _ _ _} _.
Arguments h_fib {_ _ _ _ _} _.

(** Equivalence in the Total Category relies on base equivalence and fiber isomorphism. *)
Definition TotalHom_equiv {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} 
                          {X Y : TotalObj GF} (M1 M2 : TotalHom X Y) : Prop :=
  exists (H_base : h_base M2 ≅ h_base M1),
    h_fib M1 ≅ 
    compose (@iso_to _ _ _ (pb_iso (h_base M2) (h_base M1) H_base (t_fib Y))) (h_fib M2).


(** * 3. Global Proof Irrelevance (Strictness) *)

(** WHAT IT IS:
  An extension class on top of [GoodFibration] that enforces Global Coherence.
  It states that if two morphisms in the Total Category cover the same base 
  path (Setoid equivalence in B), the entire morphisms must be equivalent.

  WHY WE CHOSE THIS SOLUTION:
  This is the cornerstone of our formalization. In dependent type theory and 
  fibrations, manipulating proofs across substitutions (fibers) is notoriously 
  difficult (coherence hell). By asserting [global_pi], we tell Coq that 
  fiber-level transports are strictly coherent. This reduces complex fiber 
  equivalences into simple base-level equivalences, acting as an ultra-powerful 
  rewrite rule.
*)

Class StrictGoodFibration (B : SetoidCategory) {CB : CartesianCategory B} (GF : GoodFibration B) := {
  global_pi : forall (X Y : TotalObj GF) (M1 M2 : TotalHom X Y),
    h_base M1 ≅ h_base M2 -> 
    TotalHom_equiv M1 M2
}.


(** * 4. Constructing the Total Setoid Category *)

(** WHAT IT IS:
  The formal instantiation of [SetoidCategory] for the Total Space.

  WHY WE CHOSE THIS SOLUTION:
  We construct identities and compositions with highly explicit annotations 
  (using the @ symbol). This prevents Coq's unification from guessing wrong 
  implicits for the fibered functors. We use the 'refine' tactic to construct 
  the category, allowing us to interactively prove the category laws (Assoc, 
  IdL, IdR). Thanks to our [global_pi] axiom, these proofs take exactly 
  two lines each.
*)

Definition total_id {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} 
                    (X : TotalObj GF) : TotalHom X X :=
  @mk_TotalHom B CB GF X X 
    (id (t_base X)) 
    (@iso_from _ _ _ (pullback_id_iso (t_fib X))).

Definition total_comp {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B} 
                      {X Y Z : TotalObj GF} 
                      (M2 : TotalHom Y Z) (M1 : TotalHom X Y) : TotalHom X Z :=
  @mk_TotalHom B CB GF X Z 
    (compose (h_base M2) (h_base M1))
    (compose 
       (@iso_from _ _ _ (pullback_comp_iso (h_base M2) (h_base M1) (t_fib Z)))
       (compose 
          (@fmap (Fiber (t_base Y)) (Fiber (t_base X)) (Pullback (h_base M1)) 
                 (t_fib Y) (@fobj _ _ (Pullback (h_base M2)) (t_fib Z)) (h_fib M2))
          (h_fib M1))).

Instance TotalHom_Equivalence {B : SetoidCategory} {CB : CartesianCategory B} 
  {GF : GoodFibration B} {SGF : StrictGoodFibration B GF} {X Y : TotalObj GF} 
  : Equivalence (@TotalHom_equiv B CB GF X Y).
Proof.
  split.
  - intros M. apply global_pi. reflexivity.
  - intros M1 M2 H. apply global_pi. destruct H as [Hb _]. exact Hb.
  - intros M1 M2 M3 H1 H2. apply global_pi. 
    destruct H1 as [Hb1 _]. destruct H2 as [Hb2 _]. 
    symmetry in Hb1. symmetry in Hb2. transitivity (h_base M2). all: assumption. 
Defined.

Instance TotalCategory {B : SetoidCategory} {CB : CartesianCategory B} 
  (GF : GoodFibration B) (SGF : StrictGoodFibration B GF) : SetoidCategory.
Proof.
  refine {|
    obj := TotalObj GF;
    hom := @TotalHom B CB GF;
    id := @total_id B CB GF;
    compose := @total_comp B CB GF;
    hom_equiv := @TotalHom_equiv B CB GF;
    hom_equiv_equivalence := @TotalHom_Equivalence B CB GF SGF;
    
    comp_assoc := _;
    id_right := _;
    id_left := _;
    comp_proper := _
  |}.
  
  - intros X Y Z W f g h. apply global_pi. apply comp_assoc.
  - intros X Y f. apply global_pi. apply id_right.
  - intros X Y f. apply global_pi. apply id_left.
  - intros X Y Z f g h i Hf Hh. apply global_pi.
    destruct Hf as [Hfb _]. destruct Hh as [Hhb _].
    apply comp_proper. symmetry in Hfb. exact Hfb.
    symmetry in Hhb. exact Hhb.
Defined.


(** * 5. Logical Quantifiers and the Base Individual Type *)

(** The Category representing two sorts: the standard terminal object and 
  the sort of individuals (S).
*)
Class TwoSortCategory (B : SetoidCategory) {CB : CartesianCategory B} := mk_TwoSortCategory {
  S : @obj B;
  S_is_not_Terminal : S <> terminal 
}.
Arguments S {B CB}.

(** The 'bang' morphism mapping the individual sort to the terminal object. *)
Definition bang (B : SetoidCategory) {CB : CartesianCategory B} {TSC : TwoSortCategory B} : hom (@S B CB TSC) terminal :=
  terminal_map.

Lemma pi_iso_cong :
  forall {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B}
         {I A : @obj B} (X Y : @obj (Fiber (@prod B CB I A))),
  X ≅O Y ->
  @right_adj_obj _ _ _ (@pullback_has_right_adjoint B CB GF I A) X ≅O
  @right_adj_obj _ _ _ (@pullback_has_right_adjoint B CB GF I A) Y.
Proof.
  intros B CB GF I A X Y H.
  refine {|
    iso_to := @right_adj_mor _ _ _ (@pullback_has_right_adjoint B CB GF I A) _ _
                (@compose (Fiber (@prod B CB I A)) _ _ _ (@iso_to _ _ _ H) (@epsilon _ _ _ (@pullback_has_right_adjoint B CB GF I A) X));
    iso_from := @right_adj_mor _ _ _ (@pullback_has_right_adjoint B CB GF I A) _ _
                  (@compose (Fiber (@prod B CB I A)) _ _ _ (@iso_from _ _ _ H) (@epsilon _ _ _ (@pullback_has_right_adjoint B CB GF I A) Y))
  |}.
  - apply (fiber_is_thin I).
  - apply (fiber_is_thin I).
Defined.

Lemma sigma_iso_cong :
  forall {B : SetoidCategory} {CB : CartesianCategory B} {GF : GoodFibration B}
         {I A : @obj B} (X Y : @obj (Fiber (@prod B CB I A))),
  X ≅O Y ->
  @left_adj_obj _ _ _ (@pullback_has_left_adjoint B CB GF I A) X ≅O
  @left_adj_obj _ _ _ (@pullback_has_left_adjoint B CB GF I A) Y.
Proof.
  intros B CB GF I A X Y H.
  refine {|
    iso_to := @left_adj_mor _ _ _ (@pullback_has_left_adjoint B CB GF I A) _ _
                (@compose (Fiber (@prod B CB I A)) _ _ _ (@unit _ _ _ (@pullback_has_left_adjoint B CB GF I A) Y) (@iso_to _ _ _ H));
    iso_from := @left_adj_mor _ _ _ (@pullback_has_left_adjoint B CB GF I A) _ _
                  (@compose (Fiber (@prod B CB I A)) _ _ _ (@unit _ _ _ (@pullback_has_left_adjoint B CB GF I A) X) (@iso_from _ _ _ H))
  |}.
  - apply (fiber_is_thin I).
  - apply (fiber_is_thin I).
Defined.