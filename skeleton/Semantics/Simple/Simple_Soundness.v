Require Import Coq.Classes.Morphisms.
Require Import List Arith PeanoNat Lia.
Import ListNotations.

(* Kategóriaelméleti alapok *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import HyperLogic.Cat.Fibration.

(* Szintaxis és Bázis Szemantika *)
Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Semantics.Simple.Base_Simple_Soundness.
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum.
(*Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.*)
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax_Conv.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Lemmas_Conv.

(* ================================================================= *)
(* 1. HYPER MODEL ÉS INTERPRETÁCIÓ                                   *)
(* ================================================================= *)

Class HyperModel {C : SetoidCategory} {CC : CartesianCategory C}
                 {TSC : TwoSortCategory C} {GF : GoodFibration C}
                 (SGF : StrictGoodFibration C GF) := {

  i_atom : forall (p : nat) (t : b_tm) (I : b_ty), @obj (Fiber (interp_ty I)) ;

  i_atom_pb : forall (p : nat) (t : b_tm) (I A : b_ty) (f : b_tm) (df : base_typing I f A),
      @fobj _ _ (Pullback (interp_tm df)) (i_atom p t A) ≅O i_atom p (b_comp t f) I ;

  (* NEW 1: The Base Category Model MUST respect the Base Syntax Equations (Proof. Admitted. (* Ne feledd, ide Defined kell! *)

Lemma form_pullback_general_iso :
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF}
         (Phi : h_ty) (I J : b_ty) (g : b_tm) (dg : base_typing I g J),
  interp_h_ty I (form_pullback g Phi) ≅O
  @fobj _ _ (Pullback (interp_tm dg)) (interp_h_ty J Phi).
Proof. Admitted.

(** * Syntactic Substitution = Semantic Pullback *)
Lemma form_pullback_iso :
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF}
         (I A : b_ty) (f : b_tm) (df : base_typing I f A) (Phi : h_ty),
  interp_h_ty I (form_pullback (b_pair b_id f) Phi) ≅O
  @fobj _ _ (Pullback (interp_tm (BT_Pair BT_Id df))) (interp_h_ty (b_Prod I A) Phi).
Proof. Admitted.

Lemma form_pullback_fst_iso :
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF}
         (I A : b_ty) (Phi : h_ty),
  interp_h_ty (b_Prod I A) (form_pullback b_fst Phi) ≅O
  @fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I Phi).
Proof. Admitted.

Lemma ctx_pullback_iso :
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF}
         (I A : b_ty) (G : h_context),
  interp_h_ctx (b_Prod I A) (ctx_pullback b_fst G) ≅O
  @fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ctx I G).
Proof. Admitted.
(* Kvantor struktúrális trükkök (Identitás-visszahúzás és Frobenius Reciprocitás) *)
Lemma pb_eval_iso :
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF}
         (I A : b_ty) (f : b_tm) (df : base_typing I f A) (Phi : h_ty),
  hom (interp_h_ty I (Ty_All A Phi))
      (@fobj _ _ (Pullback (interp_tm (BT_Pair BT_Id df)))
        (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I (Ty_All A Phi)))).
Proof. Admitted.

Lemma pb_unit_iso :
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF}
         (I A : b_ty) (f : b_tm) (df : base_typing I f A) (Phi : h_ty),
  hom (@fobj _ _ (Pullback (interp_tm (BT_Pair BT_Id df)))
        (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I (Ty_Ex A Phi))))
      (interp_h_ty I (Ty_Ex A Phi)).
Proof. Admitted.

Lemma ex_elim_frobenius :
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF}
         (I A : b_ty) (G : h_context) (Phi Chi : h_ty),
  hom (prod (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ctx I G))
            (interp_h_ty (b_Prod I A) Phi))
      (@fobj _ _ (Pullback (interp_tm (BT_Fst (A:=I) (B:=A)))) (interp_h_ty I Chi)) ->
  hom (prod (interp_h_ctx I G) (interp_h_ty I (Ty_Ex A Phi))) (interp_h_ty I Chi).
Proof. Admitted.

Lemma pullback_fmap_iso :
  forall {C : SetoidCategory} {CC : CartesianCategory C} {GF : GoodFibration C} {X Y : obj} (f : hom X Y)
         (A B : @obj (Fiber Y)),
  A ≅O B -> @fobj _ _ (Pullback f) A ≅O @fobj _ _ (Pullback f) B.
Proof. Admitted.

(* ================================================================= *)
(* 2.5 SOUNDNESS OF STRUCTURAL EQUIVALENCE                           *)
(* ================================================================= *)

Lemma interp_form_equiv :
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF}
         (I : b_ty) (Phi Psi : h_ty),
  form_equiv I Phi Psi -> interp_h_ty I Phi ≅O interp_h_ty I Psi.
Proof. Admitted.

Lemma interp_ctx_equiv :
  forall {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C}
         {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF}
         (I : b_ty) (G1 G2 : h_context),
  ctx_equiv I G1 G2 -> interp_h_ctx I G1 ≅O interp_h_ctx I G2.
Proof. Admitted.

(* ================================================================= *)
(* 3. INHABITED SOUNDNESS TÉTEL                                      *)
(* ================================================================= *)

Theorem hyper_soundness_inhabited
  {C : SetoidCategory} {CC : CartesianCategory C} {BCCC : CartesianClosedCategory C} {BiCCC : BiCartesianClosedCategory BCCC}
  {TSC : TwoSortCategory C} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} {HM : HyperModel SGF}
  {I : b_ty} {G : h_context} {p : h_tm} {Phi : h_ty}
  (D : h_derivation I G p Phi) : hom (interp_h_ctx I G) (interp_h_ty I Phi).
Proof. Admitted.

