(* theories/Logic/Hyper/Epsilon_Adjoint/Hyper_Syntax_Lemmas.v *)

Require Import List.
Import ListNotations.
Require Import HyperLogic.Logic.Base.Epsilon_Adjoint.Base_Syntax.
Require Import HyperLogic.Logic.STLC_PI_Sum.STLC_PI_Sum.
Require Import HyperLogic.Logic.Hyper.Epsilon_Adjoint.Hyper_Syntax.

Lemma phi_iso_phi_id_snd : forall {Sign : Type} `{SkolemMapping Sign} (I A : b_ty) (Phi : @h_ty Sign)
  (wf : WellFormed (b_Prod I A) Phi),
  form_equiv (b_Prod I A) Phi (form_subst (b_pair b_id b_snd) (form_subst b_fst Phi)).
Proof. Admitted. (* A Qed-hez már csak a bázis egyenlőség admit-ját kell feloldani *)

Lemma eps_implies_ex : forall {Sign : Type} `{SkolemMapping Sign} (I A : b_ty) (Phi : @h_ty Sign),
  h_derivation I [ Phi .[ ε A, Phi ] ]
    (tm_ex_intro (b_const A (skolem_index A Phi)) (tm_var 0))
    (Ty_Ex A Phi).
Proof. Admitted.

Lemma ex_implies_eps : forall {Sign : Type} `{SkolemMapping Sign} (I A : b_ty) (Phi : @h_ty Sign),
  h_derivation I [ Ty_Ex A Phi ]
    (tm_ex_elim (tm_var 0) (tm_eps_intro b_snd (tm_var 0)))
    (Phi .[ ε A, Phi ]).
Proof. Admitted.

