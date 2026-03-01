
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

(*
(* ================================================================= *)
(* 2. A BÁZIS KATEGÓRIA PÉLDÁNYOSÍTÁSA                               *)
(* ================================================================= *)

Instance Base_SetoidCategory : SetoidCategory.
Proof.
  refine (mk_SetoidCategory 
    b_ty 
    hom_base 
    (* id *)
    (fun X => mk_hom_base X X _ BT_Id)
    (* compose: A _ helyére a Coq kitalálja a b_comp-ot a BT_Comp típusa alapján! *)
    (fun X Y Z f g => mk_hom_base X Z _ (BT_Comp (deriv_of f) (deriv_of g)))
    (* hom_equiv *)
    (fun X Y f g => base_equiv (deriv_of f) (deriv_of g))
    _ _ _ _ _).
  
  - (* Equivalence *)
    intros X Y. constructor.
    + intros f. apply BE_Refl.
    + intros f g. apply BE_Sym.
    + intros f g h. apply BE_Trans.
  - (* comp_assoc *)
    intros X Y Z W f g h. apply BE_Assoc.
  - (* id_right *)
    intros X Y f. apply BE_IdR.
  - (* id_left *)
    intros X Y f. apply BE_IdL.
  - (* comp_proper *)
    unfold Proper, respectful. intros X Y Z f g Hfg h i Hhi. 
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

(* ================================================================= *)
(* 3. COMPLETENESS (TELJESSÉG) TÉTEL                                 *)
(* ================================================================= *)
(* A tétel kimondja, hogy ha az interpretáció bármely modellben egyenlő, 
   akkor a nyers szintaxisban is egyenlőnek kell lenniük. *)

Theorem base_completeness : forall {A B : b_ty} {f g : b_tm} 
  (df : base_typing A f B) (dg : base_typing A g B),
  (forall (C : SetoidCategory) (CC : CartesianCategory C) (TSC : TwoSortCategory C),
     @interp_tm C CC TSC A B f df ≅ @interp_tm C CC TSC A B g dg) ->
  base_equiv df dg.
Proof.
  intros A B f g df dg H.
  (* Alkalmazzuk az univerzális hipotézist a saját Szintaktikus Kategóriánkra! *)
  pose proof (H Base_SetoidCategory Base_CartesianCategory Base_TwoSortCategory) as Heq.
  
  (* Mivel a Szintaktikus Kategóriában az egyenlőség (≅) definíció szerint maga 
     a 'base_equiv', és az 'interp_tm df' pontosan visszaadja a 'df'-et,
     a Heq pontosan a bizonyítandó célunkká konvertálódik. *)
  exact Heq.
Qed.

*)