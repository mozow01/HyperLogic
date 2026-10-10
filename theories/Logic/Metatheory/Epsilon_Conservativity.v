
Require Import HyperLogic.Logic.Metatheory.EpsilonFull_Translation.
Require Import HyperLogic.Logic.Metatheory.EpsilonFull_Erasure.
Require Export HyperLogic.Logic.Metatheory.Canonical_Epsilon_Comparison.

Section EpsilonConservativity.

Context {Sign Func Pred : Type}.

Context `{HFuncEps : EpsBase.FunctionSignature Func}.
Context `{HFuncFull : FullBase.FunctionSignature Func}.
Context {HFuncCompat : @FunctionSignatureCompat Func HFuncEps HFuncFull}.
Context `{HPredEps : EpsHyper.PredicateSignature Pred}.
Context `{HPredFull : FullHyper.PredicateSignature Pred}.
Context {HPredCompat : @PredicateSignatureCompat Pred HPredEps HPredFull}.
Context `{HSkolemEps : EpsHyper.SkolemMapping Sign Func Pred}.
Context `{HSkolemFull : FullHyper.SkolemMapping Sign Func Pred}.
Context {HSkolemCompat : @SkolemMappingCompat Sign Func Pred HSkolemEps HSkolemFull}.

Definition in_epsilon_image_ty
  (Phi : @FullHyper.h_ty Sign Func Pred) : Prop :=
  exists Psi, embed_h_ty Psi = Phi.

Definition in_epsilon_image_ctx
  (G : @FullHyper.h_context Sign Func Pred) : Prop :=
  exists D, embed_h_context D = G.

Definition in_epsilon_image_tm
  (p : @FullHyper.h_tm Sign Func Pred) : Prop :=
  exists q, embed_h_tm q = p.

Definition epsilonfull_conservative_over_epsilon : Type :=
  forall (I : EpsBase.b_ty)
         (G : @EpsHyper.h_context Sign Func Pred)
         (Phi : @EpsHyper.h_ty Sign Func Pred),
    { p_full : @FullHyper.h_tm Sign Func Pred &
        @FullHyper.h_derivation Sign Func Pred
          HFuncFull HPredFull HSkolemFull
          (embed_b_ty I) (embed_h_context G) p_full (embed_h_ty Phi) } ->
    { p_eps : @EpsHyper.h_tm Sign Func Pred &
        @EpsHyper.h_derivation Sign Func Pred
          HFuncEps HPredEps HSkolemEps
          I G p_eps Phi }.

Theorem epsilonfull_extends_epsilon :
  forall (I : EpsBase.b_ty)
         (G : @EpsHyper.h_context Sign Func Pred)
         (p : @EpsHyper.h_tm Sign Func Pred)
         (Phi : @EpsHyper.h_ty Sign Func Pred),
    @EpsHyper.h_derivation Sign Func Pred
      HFuncEps HPredEps HSkolemEps
      I G p Phi ->
    @FullHyper.h_derivation Sign Func Pred
      HFuncFull HPredFull HSkolemFull
      (embed_b_ty I) (embed_h_context G) (embed_h_tm p) (embed_h_ty Phi).
Proof.
  apply epsilon_derivation_to_epsilonfull.
Qed.

End EpsilonConservativity.

Section EpsilonFullErasureConservativity.

Context {SignFull SignEps Func Pred : Type}.

Context `{HFuncEps : EpsBase.FunctionSignature Func}.
Context `{HFuncFull : FullBase.FunctionSignature Func}.
Context {HFuncCompat : @FunctionSignatureCompat Func HFuncEps HFuncFull}.
Context `{HPredEps : EpsHyper.PredicateSignature Pred}.
Context `{HPredFull : FullHyper.PredicateSignature Pred}.
Context {HPredCompat : @PredicateSignatureCompat Pred HPredEps HPredFull}.
Context `{HSkolemEps : EpsHyper.SkolemMapping SignEps Func Pred}.
Context `{HSkolemFull : FullHyper.SkolemMapping SignFull Func Pred}.
Context `{HSkolemErasure : @SkolemErasure SignFull SignEps Func Pred HSkolemEps HSkolemFull}.

(** Every full derivation erases to an epsilon-only derivation using the
    signature coherence packaged by [SkolemErasure]. *)
Definition epsilonfull_erasure_conservative_over_epsilon : Type :=
  forall (I : FullBase.b_ty)
         (G : @FullHyper.h_context SignFull Func Pred)
         (Phi : @FullHyper.h_ty SignFull Func Pred),
    { p_full : @FullHyper.h_tm SignFull Func Pred &
        @FullHyper.h_derivation SignFull Func Pred
          HFuncFull HPredFull HSkolemFull I G p_full Phi } ->
    { p_eps : @EpsHyper.h_tm SignEps Func Pred &
        @EpsHyper.h_derivation SignEps Func Pred
          HFuncEps HPredEps HSkolemEps
          (erase_b_ty I)
          (erase_h_context G)
          p_eps
          (erase_h_ty Phi) }.

Theorem epsilonfull_erasure_conservativity :
  epsilonfull_erasure_conservative_over_epsilon.
Proof.
  intros I G Phi [p_full Hfull].
  exists (erase_h_tm p_full).
  exact (erase_h_derivation Hfull).
Qed.

End EpsilonFullErasureConservativity.
