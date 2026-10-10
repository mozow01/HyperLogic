(** A small structural extraction principle shared by the three term models. *)

Section StructuralExtraction.
Context {Context Formula Term : Type}.
Variable derives : Context -> Term -> Formula -> Type.
Variable empty_context G : Context.
Variable context_formula Phi : Formula.
Variable implication : Formula -> Formula -> Formula.
Variable application : Term -> Term -> Term.
Variable weaken : forall q,
  derives empty_context q (implication context_formula Phi) ->
  derives G q (implication context_formula Phi).
Variable reify : {r : Term & derives G r context_formula}.
Variable apply_rule : forall q r,
  derives G q (implication context_formula Phi) ->
  derives G r context_formula ->
  derives G (application q r) Phi.

Definition extract_concrete (q : Term)
  (dq : derives empty_context q (implication context_formula Phi)) :
  {p : Term & derives G p Phi}.
Proof.
  destruct reify as [r dr].
  exists (application q r).
  apply apply_rule.
  - apply weaken. exact dq.
  - exact dr.
Defined.

Definition extract_inhabited :
  (exists q : Term,
      inhabited (derives empty_context q (implication context_formula Phi))) ->
  exists p : Term, inhabited (derives G p Phi).
Proof.
  intros [q [dq]].
  destruct (extract_concrete q dq) as [p dp].
  exists p. constructor. exact dp.
Defined.
End StructuralExtraction.
