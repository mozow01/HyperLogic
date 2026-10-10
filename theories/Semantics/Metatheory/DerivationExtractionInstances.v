(** Structural extraction applied without changing completeness hypotheses. *)
Require Import List.
Import ListNotations.
Require Import HyperLogic.Logic.Metatheory.DerivationExtraction.
Require Import HyperLogic.Logic.Base.EpsilonFull.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.
Require Import HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax_Lemmas.
Require Import HyperLogic.Semantics.EpsilonFull.EpsilonFull_Completeness.

Module F := HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax.
Module FL := HyperLogic.Logic.Hyper.EpsilonFull.Hyper_Syntax_Lemmas.
Module FC := HyperLogic.Semantics.EpsilonFull.EpsilonFull_Completeness.

Definition epsilonfull_extract_concrete
  {Sign Func Pred : Type} `{HFunc : FunctionSignature Func}
  `{HPred : PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
  (I : b_ty) (G : @F.h_context Sign Func Pred)
  (Phi : @F.h_ty Sign Func Pred)
  (wfc : F.All_WellFormed I G)
  (q : @F.h_tm Sign Func Pred)
  (dq : F.h_derivation I [] q (F.Ty_Arrow (FC.h_make_ctx_ty G) Phi)) :
  {p : @F.h_tm Sign Func Pred & F.h_derivation I G p Phi} :=
  @extract_concrete
    (@F.h_context Sign Func Pred) (@F.h_ty Sign Func Pred)
    (@F.h_tm Sign Func Pred)
    (fun G0 p Psi => @F.h_derivation Sign Func Pred HFunc HPred SM I G0 p Psi)
    [] G (FC.h_make_ctx_ty G) Phi F.Ty_Arrow F.tm_app
    (fun q0 d => @FL.h_derivation_append Sign Func Pred HFunc HPred SM
      I [] G q0 (F.Ty_Arrow (FC.h_make_ctx_ty G) Phi) d wfc)
    (existT _ (FC.h_reify_ctx G) (FC.h_reify_ctx_typing I G wfc))
    (fun q0 r d1 d2 => @F.HD_App Sign Func Pred HFunc HPred SM
      I G q0 r (FC.h_make_ctx_ty G) Phi d1 d2) q dq.

Require HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Require HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.
Require HyperLogic.Logic.Hyper.Epsilon.Epsilon_Syntax_Lemmas.
Require HyperLogic.Semantics.Epsilon.Epsilon_Completeness.
Module EB := HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Module E := HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.
Module EL := HyperLogic.Logic.Hyper.Epsilon.Epsilon_Syntax_Lemmas.
Module EC := HyperLogic.Semantics.Epsilon.Epsilon_Completeness.

Definition epsilon_extract_concrete
  {Sign Func Pred : Type} `{HFunc : EB.FunctionSignature Func}
  `{HPred : E.PredicateSignature Pred} {SM : E.SkolemMapping Sign Func Pred}
  (I : EB.b_ty) (G : @E.h_context Sign Func Pred)
  (Phi : @E.h_ty Sign Func Pred)
  (wfc : E.All_WellFormed I G)
  (q : @E.h_tm Sign Func Pred)
  (dq : E.h_derivation I [] q (E.Ty_Arrow (EC.h_make_ctx_ty G) Phi)) :
  {p : @E.h_tm Sign Func Pred & E.h_derivation I G p Phi} :=
  @extract_concrete
    (@E.h_context Sign Func Pred) (@E.h_ty Sign Func Pred)
    (@E.h_tm Sign Func Pred)
    (fun G0 p Psi => @E.h_derivation Sign Func Pred HFunc HPred SM I G0 p Psi)
    [] G (EC.h_make_ctx_ty G) Phi E.Ty_Arrow E.tm_app
    (fun q0 d => @EL.h_derivation_append Sign Func Pred HFunc HPred SM
      I [] G q0 (E.Ty_Arrow (EC.h_make_ctx_ty G) Phi) d wfc)
    (existT _ (EC.h_reify_ctx G) (EC.h_reify_ctx_typing I G wfc))
    (fun q0 r d1 d2 => @E.HD_App Sign Func Pred HFunc HPred SM
      I G q0 r (EC.h_make_ctx_ty G) Phi d1 d2) q dq.

Require HyperLogic.Logic.Base.IFOL.Base_Syntax.
Require HyperLogic.Logic.Hyper.IFOL.Hyper_Syntax.
Require HyperLogic.Logic.Hyper.IFOL.Hyper_Syntax_Lemmas.
Require HyperLogic.Semantics.IFOL.IFOL_Completeness.
Module IB := HyperLogic.Logic.Base.IFOL.Base_Syntax.
Module IF := HyperLogic.Logic.Hyper.IFOL.Hyper_Syntax.
Module IL := HyperLogic.Logic.Hyper.IFOL.Hyper_Syntax_Lemmas.
Module IC := HyperLogic.Semantics.IFOL.IFOL_Completeness.

Definition ifol_extract_concrete
  {Func Pred : Type} `{HFunc : IB.FunctionSignature Func}
  `{HPred : IF.PredicateSignature Pred}
  (I : IB.b_ty) (G : @IF.h_context Func Pred)
  (Phi : @IF.h_ty Func Pred)
  (wfc : IF.All_WellFormed I G)
  (q : @IF.h_tm Func Pred)
  (dq : IF.h_derivation I [] q (IF.Ty_Arrow (IC.h_make_ctx_ty G) Phi)) :
  {p : @IF.h_tm Func Pred & IF.h_derivation I G p Phi} :=
  @extract_concrete
    (@IF.h_context Func Pred) (@IF.h_ty Func Pred)
    (@IF.h_tm Func Pred)
    (fun G0 p Psi => @IF.h_derivation Func Pred HFunc HPred I G0 p Psi)
    [] G (IC.h_make_ctx_ty G) Phi IF.Ty_Arrow IF.tm_app
    (fun q0 d => @IL.h_derivation_append Func Pred HFunc HPred
      I [] G q0 (IF.Ty_Arrow (IC.h_make_ctx_ty G) Phi) d wfc)
    (existT _ (IC.h_reify_ctx G) (IC.h_reify_ctx_typing I G wfc))
    (fun q0 r d1 d2 => @IF.HD_App Func Pred HFunc HPred
      I G q0 r (IC.h_make_ctx_ty G) Phi d1 d2) q dq.

Definition epsilonfull_extract_inhabited
  {Sign Func Pred : Type} `{HFunc : FunctionSignature Func}
  `{HPred : PredicateSignature Pred} {SM : SkolemMapping Sign Func Pred}
  (I : b_ty) (G : @F.h_context Sign Func Pred)
  (Phi : @F.h_ty Sign Func Pred) (wfc : F.All_WellFormed I G) :
  (exists q : @F.h_tm Sign Func Pred,
    inhabited (F.h_derivation I [] q
      (F.Ty_Arrow (FC.h_make_ctx_ty G) Phi))) ->
  exists p : @F.h_tm Sign Func Pred,
    inhabited (F.h_derivation I G p Phi).
Proof.
  intros [q [dq]].
  destruct (epsilonfull_extract_concrete I G Phi wfc q dq) as [p dp].
  exists p. constructor. exact dp.
Defined.

Definition epsilon_extract_inhabited
  {Sign Func Pred : Type} `{HFunc : EB.FunctionSignature Func}
  `{HPred : E.PredicateSignature Pred} {SM : E.SkolemMapping Sign Func Pred}
  (I : EB.b_ty) (G : @E.h_context Sign Func Pred)
  (Phi : @E.h_ty Sign Func Pred) (wfc : E.All_WellFormed I G) :
  (exists q : @E.h_tm Sign Func Pred,
    inhabited (E.h_derivation I [] q
      (E.Ty_Arrow (EC.h_make_ctx_ty G) Phi))) ->
  exists p : @E.h_tm Sign Func Pred,
    inhabited (E.h_derivation I G p Phi).
Proof.
  intros [q [dq]].
  destruct (epsilon_extract_concrete I G Phi wfc q dq) as [p dp].
  exists p. constructor. exact dp.
Defined.

Definition ifol_extract_inhabited
  {Func Pred : Type} `{HFunc : IB.FunctionSignature Func}
  `{HPred : IF.PredicateSignature Pred}
  (I : IB.b_ty) (G : @IF.h_context Func Pred)
  (Phi : @IF.h_ty Func Pred) (wfc : IF.All_WellFormed I G) :
  (exists q : @IF.h_tm Func Pred,
    inhabited (IF.h_derivation I [] q
      (IF.Ty_Arrow (IC.h_make_ctx_ty G) Phi))) ->
  exists p : @IF.h_tm Func Pred,
    inhabited (IF.h_derivation I G p Phi).
Proof.
  intros [q [dq]].
  destruct (ifol_extract_concrete I G Phi wfc q dq) as [p dp].
  exists p. constructor. exact dp.
Defined.
