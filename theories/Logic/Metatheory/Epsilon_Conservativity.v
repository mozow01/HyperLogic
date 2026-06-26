(* theories/Logic/Metatheory/Epsilon_Conservativity.v *)

Require Import HyperLogic.Logic.Metatheory.EpsilonFull_Translation.

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
