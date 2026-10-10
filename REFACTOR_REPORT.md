# Refactor record

This record distinguishes this pass from the preexisting worktree edits. Before this pass, HyperLogic had 109 modified tracked files and the paper repository was clean. The baseline status and diff were recorded in `/tmp/hyperlogic-baseline-status.txt` and `/tmp/hyperlogic-baseline.diff`. No preexisting changes were reset.

## Name changes

The following 15 declarations were renamed in the counterexample module. Every reference in that Rocq module and the manuscript was updated. No other Rocq module imported these old declaration names, so no external Rocq import changed for this group. The two witness names distinguish substituting the formula before choosing from substituting a chosen witness.

| Old full name | New full name | Reason |
| --- | --- | --- |
| `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.test_func_dom` | `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.counterexample_func_dom` | the counterexample signature domain |
| `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.test_func_cod` | `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.counterexample_func_cod` | the counterexample signature codomain |
| `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.test_g` | `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.counterexample_substitution` | the base substitution used in the counterexample |
| `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.test_g_typing` | `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.counterexample_substitution_typing` | typing of that substitution |
| `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.test_Phi` | `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.substitution_counterexample_formula` | the formula before substitution |
| `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.test_Phi_wellformed` | `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.substitution_counterexample_formula_wellformed` | well-formedness of that formula |
| `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.test_Phi_sub` | `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.substituted_counterexample_formula` | the formula after substitution |
| `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.test_Phi_sub_wellformed` | `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.substituted_counterexample_formula_wellformed` | well-formedness after substitution |
| `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.test_eps_sub` | `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.witness_of_substituted_formula` | selection for the substituted formula |
| `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.test_eps_comp` | `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.substituted_witness` | substitution of the originally selected witness |
| `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.test_eps_sub_typing` | `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.witness_of_substituted_formula_typing` | typing of selection after formula substitution |
| `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.test_eps_comp_typing` | `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.substituted_witness_typing` | typing of the substituted selected witness |
| `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.test_substitutivity_judgement` | `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.counterexample_substitutivity_equation` | the one equation tested by the models |
| `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.test_substitutivity_not_derivable` | `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.counterexample_equation_not_derivable` | nonderivability of that one equation |
| `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.test_substitutivity_valid_in` | `HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity.EpsilonFullSubstitutivity.counterexample_equation_valid_in` | validity of that one equation in a specified model |

The local notation `test_skolem` became `counterexample_skolem` in the same module. A Rocq notation is lexical syntax, so it has no kernel-level fully qualified constant name. The old notation had no use outside the module.

`HyperLogic.Semantics.EpsilonFull.EpsilonFull_ModelCategory.TermModel_initial_unique` is now the primary proof. `HyperLogic.Semantics.EpsilonFull.EpsilonFull_ModelCategory.TermModel_strict_initial_unique` remains as a compatibility alias to it. The conclusion is `EpsilonFullModelHom_equiv`, not equality of model-hom records.

`separating_model_refutes_substitutivity` and `uniform_model_validates_substitutivity` are the primary manuscript references. The older `finite_hyperdoctrine_countermodel` and `uniform_hyperdoctrine_validates_substitutivity` remain available. Each states validity or refutation of the specified counterexample equation, not the entire substitution scheme.

## Module dependencies

- `Cat/EpsilonSelection` contains the category-level unit, selection, and adjunction correspondence. `EpsilonFull_SelectionModels` and `Epsilon_SelectionModels` separately turn chosen units into their respective model interfaces and provide reverse constructions. The soundness modules are not imported by the fibration interfaces.
- `Logic/Hyper/EpsilonFull/DualDrinker_Syntax` now owns the pure syntax and diagonal calculation. `Semantics/Metatheory/DualDrinker` imports and includes it for old qualified uses, then proves semantic claims.
- `H3_Algebra` and `H5_Algebra` now own the algebraic carriers and operations. The original refutation modules include them for old qualified uses. `FiniteHeytingExamples` imports the algebra modules directly.
- `Logic/Metatheory/DerivationExtraction` is calculus independent. `Semantics/Metatheory/DerivationExtractionInstances` supplies separate EpsilonFull, Epsilon, and IFOL instances.
- `IndexedHeytingPredicates` constructs the arbitrary-index hyperdoctrine from explicit `ChosenIndexedHeytingBounds`; `FiniteHeytingAlgebra` alone does not provide the required Type-valued bounds for arbitrary index types.

## Checks

An isolated copy of the current worktree compiled all 93 sources in `_CoqProject` under Coq 8.18.0. `coqchk` checked the principal result modules. All 137 unique active manuscript `\coqterm` labels resolved. `Print Assumptions` found no new declared axiom: Full soundness and the new chosen-unit and indexed-Heyting constructors are closed, while Full completeness and initiality retain the existing `Eqdep.Eq_rect_eq.eq_rect_eq` dependency. Some new concrete counterexample consequences inherit that existing dependency through the finite base model. Both repositories passed `git diff --check`. No LaTeX compiler was available.
