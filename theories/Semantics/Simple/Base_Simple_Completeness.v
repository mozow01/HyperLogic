Require Import Coq.Classes.Morphisms.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.Fibration.

Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Semantics.Simple.Base_Simple_Soundness.

(* ================================================================= *)
(* 1. A SZINTAKTIKUS KATEGÓRIA (TERM MODELL) MORFIZMUSAI             *)
(* ================================================================= *)

(* Egy morfizmus az A és B típusok között egyszerűen egy szintaktikai levezetés.
   A Record-ba becsomagoljuk magát a termet és a típusolási derivációt is. *)
Record hom_base (A B : b_ty) : Set := mk_hom_base {
  tm_of : b_tm;
  deriv_of : base_typing A tm_of B
}.

Arguments tm_of {A B} _.
Arguments deriv_of {A B} _.

(* ================================================================= *)
(* 2. A BÁZIS KATEGÓRIA PÉLDÁNYOSÍTÁSA                               *)
(* ================================================================= *)

Instance Base_SetoidCategory : SetoidCategory.
Proof.
  refine (mk_SetoidCategory 
    b_ty 
    hom_base 
    (fun X => mk_hom_base X X _ BT_Id)
    (fun X Y Z f g => mk_hom_base X Z _ (BT_Comp (deriv_of f) (deriv_of g)))
    (fun X Y f g => base_equiv X Y (tm_of f) (tm_of g))
    _ _ _ _ _).
  - intros X Y. constructor.
    + intros f. eapply BE_Refl. exact (deriv_of f).
    + intros f g. apply BE_Sym.
    + intros f g h. apply BE_Trans.
  - intros X Y Z W f g h. eapply BE_Assoc; apply deriv_of.
  - intros X Y f. apply BE_IdR. apply deriv_of.
  - intros X Y f. apply BE_IdL. apply deriv_of.
  - (* SetoidCategory groups morphisms first, then proofs! *)
    intros X Y Z f f' g g' Hf Hg.
    simpl.
    eapply BE_CongComp; eassumption.
Defined.

Instance Base_CartesianCategory : CartesianCategory Base_SetoidCategory.
Proof.
  refine (mk_CartesianCategory 
    Base_SetoidCategory
    b_Unit
    (fun X => mk_hom_base X b_Unit _ BT_Unit)
    _ (* terminal_map_unique *)
    b_Prod
    (fun X Y Z f g => mk_hom_base X (b_Prod Y Z) _ (BT_Pair (deriv_of f) (deriv_of g)))
    (fun X Y => mk_hom_base (b_Prod X Y) X _ BT_Fst)
    (fun X Y => mk_hom_base (b_Prod X Y) Y _ BT_Snd)
    _ _ _ _).
  - intros X f. eapply BE_Terminal. exact (deriv_of f). apply BT_Unit.
  - intros X Y Z f g. eapply BE_BetaFst; apply deriv_of.
  - intros X Y Z f g. eapply BE_BetaSnd; apply deriv_of.
  - intros X Y Z h. apply BE_EtaPair. apply deriv_of.
  - (* CartesianCategory interleaves morphisms and proofs! *)
    intros X Y Z f f' Hf g g' Hg.
    simpl.
    eapply BE_CongPair; eassumption.
Defined.

Instance Base_TwoSortCategory : TwoSortCategory Base_SetoidCategory.
Proof.
  refine (mk_TwoSortCategory Base_SetoidCategory Base_CartesianCategory b_S _).
  (* Bizonyítanunk kell, hogy S <> terminal. 
     Mivel b_S és b_Unit az Inductive b_ty két külön konstruktora, ez triviális. *)
  intro H. discriminate H.
Defined.

(* ================================================================= *)
(* 3. COMPLETENESS HELPER LEMMAS                                     *)
(* ================================================================= *)

(* Lemma 1: Interpretation of a type in our syntactic category is exactly itself. *)
Lemma interp_ty_id : forall A, 
  @interp_ty Base_SetoidCategory Base_CartesianCategory Base_TwoSortCategory A = A.
Proof.
  induction A; simpl; congruence.
Defined. 

(* Lemma 2: Term Identity. 
   Interpreting a derivation mathematically preserves its underlying syntactic term. *)
Lemma interp_tm_term : forall A B f (df : base_typing A f B),
  tm_of (@interp_tm Base_SetoidCategory Base_CartesianCategory Base_TwoSortCategory A B f df) = f.
Proof.
  intros A B f df.
  induction df; simpl.
  - reflexivity.
  - rewrite IHdf1, IHdf2. reflexivity.
  - reflexivity.
  - rewrite IHdf1, IHdf2. reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

(* Lemma 3: Safe Equivalence Casting. 
   Because base_equiv is no longer dependent on derivations, casting is trivial! *)
Lemma base_equiv_cast : forall A B A' B' f g f' g',
  A' = A -> B' = B -> f' = f -> g' = g ->
  base_equiv A' B' f' g' -> base_equiv A B f g.
Proof.
  intros; subst; assumption.
Qed.

(* Helper: Safely cast the types of a derivation if the types are provably equal. *)
Lemma base_typing_cast : forall A' B' A B t,
  A' = A -> B' = B -> base_typing A' t B' -> base_typing A t B.
Proof.
  intros A' B' A B t eqA eqB d.
  subst. exact d.
Qed.

(* ================================================================= *)
(* 4. COMPLETENESS (TELJESSÉG) TÉTEL                                 *)
(* ================================================================= *)

Theorem base_completeness_equational : forall {A B : b_ty} {f g : b_tm} 
  (df : base_typing A f B) (dg : base_typing A g B),
  (forall (C : SetoidCategory) (CC : CartesianCategory C) (TSC : TwoSortCategory C),
     @interp_tm C CC TSC A B f df ≅ @interp_tm C CC TSC A B g dg) ->
  base_equiv A B f g.
Proof.
  intros A B f g df dg H.
  
  (* 1. Instantiate the universal hypothesis with our Syntactic Category *)
  pose proof (H Base_SetoidCategory Base_CartesianCategory Base_TwoSortCategory) as Heq.
  
  (* 2. Apply our Trivial Casting Lemma *)
  eapply base_equiv_cast.
  
  (* Fill in the Type Proofs *)
  - apply interp_ty_id.
  - apply interp_ty_id.
  
  (* Fill in the Term Proofs *)
  - apply interp_tm_term.
  - apply interp_tm_term.
  
  (* Provide the actual Semantic Equivalence! *)
  - exact Heq.
Defined.

Theorem base_completeness_inhabitational : forall {A B : b_ty}, 
  (* PREMISE: The hom-set is inhabited in ALL valid models *)
  (forall (C : SetoidCategory) (CC : CartesianCategory C) (TSC : TwoSortCategory C),
     inhabited (hom (@interp_ty C CC TSC A) (@interp_ty C CC TSC B))) -> 
  
  (* CONCLUSION: There exists a syntactic term *)
  (exists (t : b_tm), inhabited (base_typing A t B)).
Proof.
  intros A B H.
  
  (* 1. Instantiate the universal hypothesis with our Syntactic Model *)
  pose proof (H Base_SetoidCategory Base_CartesianCategory Base_TwoSortCategory) as [f_hom].
  
  (* 2. Destruct the categorical morphism into its term and derivation. *)
  destruct f_hom as [t_syn d_syn].
  
  (* 3. Provide the extracted term as the witness for our existential quantifier *)
  exists t_syn.
  constructor. (* This proves the 'inhabited' wrapper *)
  
  (* 4. Bridge the semantic types (interp_ty A) to syntactic types (A) *)
  eapply base_typing_cast.
  - apply interp_ty_id.
  - apply interp_ty_id.
  - exact d_syn.
Qed.
  