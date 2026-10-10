# HyperLogic

HyperLogic formalizes typed intuitionistic hyperdoctrine calculi in Coq 8.18.0.
The main development is **EpsilonFull** (intuitionistic first-order logic with
existentials and intensional epsilon). **IFOL** is the comparison calculus;
**Epsilon** is the distinct epsilon-only calculus used in the paper's appendix.
**Epsilon_Adjoint** has its own syntax and model interface. The Individual
modules are supported compatibility paths. Legacy Simple and Simple_Ext
sources are kept in the repository but are excluded from the supported build.

The `theories/Logic/Base` and `theories/Logic/Hyper` trees contain raw and
typed syntax. `theories/Semantics` contains model interfaces, soundness,
completeness, the syntactic term models, and countermodels. `theories/Cat`
contains the shared thin setoid-fibration infrastructure. In particular:

- `Cat/EpsilonSelection.v` proves the chosen unit, selection-isomorphism,
  and inhabited hom comparison results.
- `Semantics/EpsilonFull/EpsilonFull_SelectionModels.v` constructs the Full
  model structure from chosen units; `EpsilonFull_ModelCategory.v` states
  term-model initiality up to hom equivalence.
- `Semantics/Epsilon/Epsilon_SelectionModels.v` constructs all five laws of
  the epsilon-only model from chosen units.
- `Semantics/Metatheory/EpsilonFull_Substitutivity.v` contains the concrete
  separating and uniform models and the extensionality counterexample.
- `Logic/Hyper/EpsilonFull/Examples.v` contains the detailed typed examples
  used in the paper.
- `Semantics/EpsilonFull/IndexedHeytingPredicates.v` constructs an H-valued
  hyperdoctrine over arbitrary `S` when chosen indexed suprema and infima
  are supplied as Type-level data.

`_CoqProject` is the source list for the supported build. Generate its Makefile
and compile with the `coq-8.18.0` opam switch:

```sh
opam exec --switch=coq-8.18.0 -- coq_makefile -f _CoqProject -o Makefile.coq
opam exec --switch=coq-8.18.0 -- make -f Makefile.coq -j2
```
