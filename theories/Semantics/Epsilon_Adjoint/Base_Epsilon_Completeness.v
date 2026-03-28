(* theories/Semantics/Epsilon_Adjoint/Base_Epsilon_Completeness.v *)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Equality.

Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.Fibration.

Require Import HyperLogic.Logic.Base.Epsilon_Adjoint.Base_Syntax.
Require Import HyperLogic.Semantics.Epsilon_Adjoint.Epsilon_Adjoint_Fibration.

(* ================================================================= *)
(* 1. A SZINTAKTIKUS KATEGÓRIA (TERM MODELL) MORFIZMUSAI             *)
(* ================================================================= *)

Class hom_base {Sign : Type} (A B : b_ty) : Type := mk_hom_base {
  tm_of : @b_tm Sign;
  deriv_of : @base_typing Sign A tm_of B
}.

Arguments tm_of {Sign A B} _.
Arguments deriv_of {Sign A B} _.

(* ================================================================= *)
(* 2. A BÁZIS KATEGÓRIA PÉLDÁNYOSÍTÁSA                               *)
(* ================================================================= *)

Instance Base_SetoidCategory {Sign : Type} : SetoidCategory.
Proof.
  refine (mk_SetoidCategory 
    b_ty 
    (@hom_base Sign) 
    (fun X => @mk_hom_base Sign X X b_id BT_Id)
    (fun X Y Z f g => @mk_hom_base Sign X Z (b_comp (tm_of f) (tm_of g)) (BT_Comp (deriv_of f) (deriv_of g)))
    (fun X Y f g => base_equiv (deriv_of f) (deriv_of g))
    _ _ _ _ _).
  - intros X Y. constructor.
    + intros f. apply BE_Refl.
    + intros f g. apply BE_Sym.
    + intros f g h. apply BE_Trans.
  - intros X Y Z W f g h. apply BE_Assoc.
  - intros X Y f. apply BE_IdR.
  - intros X Y f. apply BE_IdL.
  - unfold Proper, respectful.
    intros X Y Z f g Hfg h i Hhi.
    apply BE_CongComp; assumption.
Defined.

Instance Base_CartesianCategory {Sign : Type} : CartesianCategory (@Base_SetoidCategory Sign).
Proof.
  refine (mk_CartesianCategory 
    (@Base_SetoidCategory Sign)
    b_Unit
    (fun X => @mk_hom_base Sign X b_Unit b_unit BT_Unit)
    _ (* terminal_map_unique *)
    b_Prod
    (fun X Y Z f g => @mk_hom_base Sign X (b_Prod Y Z) (b_pair (tm_of f) (tm_of g)) (BT_Pair (deriv_of f) (deriv_of g)))
    (fun X Y => @mk_hom_base Sign (b_Prod X Y) X b_fst BT_Fst)
    (fun X Y => @mk_hom_base Sign (b_Prod X Y) Y b_snd BT_Snd)
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

Instance Base_TwoSortCategory {Sign : Type} : TwoSortCategory (@Base_SetoidCategory Sign).
Proof.
  refine (mk_TwoSortCategory (@Base_SetoidCategory Sign) (@Base_CartesianCategory Sign) b_S _).
  intro H. discriminate H.
Defined.

(* ================================================================= *)
(* 3. EPSILON BASE MODEL                                             *)
(* ================================================================= *)

(* Segédlemma: A típus interpretációja a szintaktikus modellben önmaga *)
Lemma interp_ty_id {Sign : Type} : forall A, 
  @interp_ty (@Base_SetoidCategory Sign) (@Base_CartesianCategory Sign) (@Base_TwoSortCategory Sign) A = A.
Proof.
  induction A; simpl; congruence.
Defined.

Instance Base_Epsilon_Model {Sign : Type} : @BaseEpsilonModel Sign (@Base_SetoidCategory Sign) (@Base_CartesianCategory Sign) (@Base_TwoSortCategory Sign).
Proof.
  constructor.
  (* i_const : forall I A s, hom I A *)
  intros I A s.
  (* Kicseréljük az interp_ty I és interp_ty A hívásokat tisztán I-re és A-ra *)
  rewrite (interp_ty_id I).
  rewrite (interp_ty_id A).
  (* Most már a cél pontosan hom_base I A, így az apply tökéletesen illeszkedik! *)
  apply (@mk_hom_base Sign I A (b_const A s) BT_Const).
Defined.