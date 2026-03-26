(* theories/Semantics/Epsilon_Adjoint/Epsilon_Adjoint_Soundness.v *)

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

(* Szintaxis és Adjungált Szemantika *)
Require Import HyperLogic.Logic.Base.Epsilon_Adjoint.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon_Adjoint.Hyper_Syntax.
Require Import HyperLogic.Semantics.Epsilon_Adjoint.Epsilon_Adjoint_Fibration.

(* ================================================================= *)
(* 1. STRUKTURÁLIS KOMPATIBILITÁSI LEMMÁK                            *)
(* ================================================================= *)

Lemma typing_subst_ext :
  forall {Sign : Type} {I J b : b_ty} {g : @b_tm Sign} (dg : base_typing I g J),
  base_typing (b_Prod I b) (b_subst_ext g) (b_Prod J b).
Proof.
  intros Sign I J b g dg.
  unfold b_subst_ext.
  apply BT_Pair.
  - eapply BT_Comp. exact dg. apply BT_Fst.
  - apply BT_Snd.
Defined.

(* ================================================================= *)
(* 2. KONVERZIÓS LEMMÁK (ADMITTED)                                   *)
(* ================================================================= *)

Lemma interp_form_equiv : 
  forall {Sign : Type} {SM : SkolemMapping Sign} 
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} 
  {EHM : EpsilonHyperModel SGF}
  {AdEHM : @AdjointEpsilonFibration Sign SM C CC TSC BEM GF SGF EHM},
  forall (I : b_ty) (Phi Psi : @h_ty Sign),
  form_equiv I Phi Psi -> 
  interp_h_ty I Phi ≅O interp_h_ty I Psi.
Proof.
Admitted.

Lemma interp_ctx_equiv : 
  forall {Sign : Type} {SM : SkolemMapping Sign} 
  {C : SetoidCategory} {CC : CartesianCategory C} {TSC : TwoSortCategory C} 
  {BEM : BaseEpsilonModel} {GF : GoodFibration C} {SGF : StrictGoodFibration C GF} 
  {EHM : EpsilonHyperModel SGF}
  {AdEHM : @AdjointEpsilonFibration Sign SM C CC TSC BEM GF SGF EHM},
  forall (I : b_ty) (G1 G2 : @h_context Sign),
  ctx_equiv I G1 G2 -> 
  interp_h_ctx I G1 ≅O interp_h_ctx I G2.
Proof.
Admitted.

(* ================================================================= *)
(* 3. SOUNDNESS TÉTEL                                                *)
(* ================================================================= *)

Theorem soundness : 
  forall {Sign : Type} {SM : SkolemMapping Sign} 
  {C : SetoidCategory} {CC : CartesianCategory C} 
  {BCCC : CartesianClosedCategory C} {BiCCC : BiCartesianClosedCategory BCCC}
  {TSC : TwoSortCategory C} {BEM : BaseEpsilonModel} {GF : GoodFibration C} 
  {SGF : StrictGoodFibration C GF} {EHM : EpsilonHyperModel SGF}
  {AdEHM : @AdjointEpsilonFibration Sign SM C CC TSC BEM GF SGF EHM},
  forall (I : b_ty) (G : @h_context Sign) (p : @h_tm Sign) (Phi : @h_ty Sign),
  h_derivation I G p Phi -> 
  hom (interp_h_ctx I G) (interp_h_ty I Phi).
Proof.
  intros Sign SM C CC BCCC BiCCC TSC BEM GF SGF EHM AdEHM I G p Phi H_der.
  induction H_der.
  
  (* --------------------------------------------------------------- *)
  (* VÁLTOZÓK ÉS STRUKTURÁLIS SZABÁLYOK                              *)
  (* --------------------------------------------------------------- *)
  
  - (* HD_Var0 *)
    apply prod_snd.
    
  - (* HD_VarS *)
    eapply compose.
    + exact IHH_der.
    + apply prod_fst.
    
  - (* HD_Conv (Cél formula konverziója) *)
    eapply compose.
    + apply (@iso_to _ _ _ (interp_form_equiv I _ _ f)).
    + exact IHH_der.
      
  - (* HD_Ctx_Conv (Kontextus konverziója) *)
    eapply compose.
    + exact IHH_der.
    + apply (@iso_from _ _ _ (interp_ctx_equiv I _ _ c)).

  (* --------------------------------------------------------------- *)
  (* PROPOZICIONÁLIS MAG (STLC + Sum + Void)                         *)
  (* --------------------------------------------------------------- *)
  
  - (* HD_Unit *)
    apply terminal_map.
    
  - (* HD_Lam *)
    apply exp_map. 
    exact IHH_der.
    
  - (* HD_App *)
    eapply compose. 
    + eapply eval. 
    + apply (prod_map IHH_der1 IHH_der2).
    
  - (* HD_Pair *)
    apply (prod_map IHH_der1 IHH_der2).
    
  - (* HD_Fst *)
    eapply compose. 
    + eapply prod_fst. 
    + exact IHH_der.
    
  - (* HD_Snd *)
    eapply compose. 
    + eapply prod_snd. 
    + exact IHH_der.
    
  - (* HD_Inl *)
    eapply compose. 
    + eapply coprod_inl. 
    + exact IHH_der.
    
  - (* HD_Inr *)
    eapply compose. 
    + eapply coprod_inr. 
    + exact IHH_der.
    
  - (* HD_Case *)
    eapply compose.
    + eapply compose.
      * apply (coprod_map IHH_der2 IHH_der3).
      * eapply compose.
        -- eapply eval.
        -- eapply compose.
           ++ eapply prod_map.
              ** eapply compose.
                 --- apply (coprod_map 
                       (exp_map (compose coprod_inl (prod_map prod_snd prod_fst))) 
                       (exp_map (compose coprod_inr (prod_map prod_snd prod_fst)))
                     ).
                 --- eapply prod_fst.
              ** eapply prod_snd.
           ++ eapply (prod_map prod_snd prod_fst).
    + eapply (prod_map (id _) IHH_der1).

  - (* HD_Absurd *)
    eapply compose.
    + apply initial_map.
    + exact IHH_der.

  (* --------------------------------------------------------------- *)
  (* KVANTOROK (Későbbi lépésekben fejezzük be)                      *)
  (* --------------------------------------------------------------- *)
  
  - (* HD_All_Intro *) admit.
  - (* HD_All_Elim *) admit.
  - (* HD_Ex_Intro *) admit.
  - (* HD_Ex_Elim *) admit.

Admitted.