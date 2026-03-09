
Require Import Coq.Classes.Morphisms.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.Fibration.

Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Semantics.Simple.Base_Simple_Soundness.
Require Import Coq.Program.Equality.

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
    (fun X Y f g => base_equiv (deriv_of f) (deriv_of g))
    _ _ _ _ _).
  - intros X Y. constructor.
    + intros f. apply BE_Refl.
    + intros f g. apply BE_Sym.
    + intros f g h. apply BE_Trans.
  - intros X Y Z W f g h. apply BE_Assoc.
  - intros X Y f. apply BE_IdR.
  - intros X Y f. apply BE_IdL.
  - unfold Proper, respectful. intros X Y Z f g Hfg h i Hhi.
    apply BE_CongComp; assumption.
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
    
  - (* terminal_map_unique *)
    intros X f. apply BE_EtaUnit.
  - (* prod_map_fst *)
    intros X Y Z f g. apply BE_BetaFst.
  - (* prod_map_snd *)
    intros X Y Z f g. apply BE_BetaSnd.
  - (* prod_eta *)
    intros X Y Z h. apply BE_EtaPair.
  - (* prod_map_proper_ax *)
    unfold Proper, respectful. intros X Y Z f f' Hf g g' Hg.
    apply BE_CongPair; assumption.
Defined.

Instance Base_TwoSortCategory : TwoSortCategory Base_SetoidCategory.
Proof.
  refine (mk_TwoSortCategory Base_SetoidCategory Base_CartesianCategory b_S _).
  (* Bizonyítanunk kell, hogy S <> terminal. 
     Mivel b_S és b_Unit az Inductive b_ty két külön konstruktora, ez triviális. *)
  intro H. discriminate H.
Defined.

Require Import Coq.Program.Equality. (* Needed for dependent destruction *)

Require Import Coq.Program.Equality.

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

(* Lemma 3: Type Determinism (Uniqueness of Types). *)
Lemma base_typing_unique : forall A f B1 (d1 : base_typing A f B1) B2 (d2 : base_typing A f B2),
  B1 = B2.
Proof.
  intros A f B1 d1.
  induction d1; intros B2 d2; dependent destruction d2.
  - reflexivity.
  - assert (H_B : B = B0). { eapply IHd1_2. exact d2_2. }
    subst B0. eapply IHd1_1. exact d2_1.
  - reflexivity.
  - assert (H_B : B = B0). { eapply IHd1_1. exact d2_1. }
    assert (H_C : C = C0). { eapply IHd1_2. exact d2_2. }
    subst. reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

(* Lemma 4: Proof Irrelevance. *)
Lemma base_typing_pi : forall A B f (d1 d2 : base_typing A f B), base_equiv d1 d2.
Proof.
  intros A B f d1.
  induction d1; intros d2; dependent destruction d2.
  - apply BE_Refl.
  - assert (H_B : B = B0). { eapply base_typing_unique. exact d1_2. exact d2_2. }
    subst B0.
    apply BE_CongComp.
    + apply IHd1_2.
    + apply IHd1_1.
  - apply BE_Refl.
  - apply BE_CongPair.
    + apply IHd1_1.
    + apply IHd1_2.
  - apply BE_Refl.
  - apply BE_Refl.
Defined.

(* Lemma 5: Safe Equivalence Casting (Now handles Types AND Terms!) *)
Lemma base_equiv_cast : forall A B A' B' f g f' g'
  (eqA : A' = A) (eqB : B' = B) 
  (eqF : f' = f) (eqG : g' = g)
  (df' : base_typing A' f' B') (dg' : base_typing A' g' B')
  (df : base_typing A f B) (dg : base_typing A g B),
  base_equiv df' dg' -> base_equiv df dg.
Proof.
  intros A B A' B' f g f' g' eqA eqB eqF eqG df' dg' df dg Heq.
  
  (* 1. Unify all types and terms globally! *)
  subst. 
  
  (* 2. Chain the equivalences via Proof Irrelevance *)
  eapply BE_Trans.
  - apply base_typing_pi.
  - eapply BE_Trans.
    + exact Heq.
    + apply base_typing_pi.
Defined.

(* ================================================================= *)
(* 4. COMPLETENESS (TELJESSÉG) TÉTEL                                 *)
(* ================================================================= *)

Theorem base_completeness_equational : forall {A B : b_ty} {f g : b_tm} 
  (df : base_typing A f B) (dg : base_typing A g B),
  (forall (C : SetoidCategory) (CC : CartesianCategory C) (TSC : TwoSortCategory C),
     @interp_tm C CC TSC A B f df ≅ @interp_tm C CC TSC A B g dg) ->
  base_equiv df dg.
Proof.
  intros A B f g df dg H.
  
  (* 1. Instantiate the universal hypothesis with our Syntactic Category *)
  pose proof (H Base_SetoidCategory Base_CartesianCategory Base_TwoSortCategory) as Heq.
  
  (* 2. Apply our Ultimate Casting Lemma *)
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

Theorem base_completeness_inhabitational : forall {C : SetoidCategory} {CC : CartesianCategory C} 
  {TSC : TwoSortCategory C} {A B : b_ty}, inhabited (hom (interp_ty A) (interp_ty B)) -> 
  (exists (t : b_tm), inhabited (base_typing A t B)).
Proof.
Admitted.