# HyperLogic

HyperLogic formalizes typed intuitionistic hyperdoctrine calculi in Coq 8.18.0.
The main development is **EpsilonFull** (intuitionistic first-order logic with
existentials and intensional epsilon). **IFOL** is the comparison calculus;
**Epsilon** is the distinct epsilon-only calculus used in the paper's appendix.
**Epsilon_Adjoint** has its own syntax and model interface. The Individual
modules are supported compatibility paths. Legacy Simple and Simple_Ext
sources are kept in the repository but are excluded from the supported build.
`Logic/Hyper/Epsilon/Critical_Epsilon_Provable.v` and
`Semantics/Conservativity/Model_Expansion.v` are also outside this build.

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

## Build and verification

`_CoqProject` lists the 93 supported `.v` files and sets `-R theories HyperLogic`.
Every listed source is tracked in Git. Simple/Simple_Ext and the two additional
files named above remain outside the supported build; reviving them is a
separate task.

Prerequisites: `opam`, a C compiler and standard build tools, and GNU `make`.
The sources use Coq's standard library. Initialize opam if needed, then
create the documented compiler and Coq environment once:

```sh
opam init -y
opam switch create coq-8.18.0 ocaml-base-compiler.4.14.1 -y
opam install --switch=coq-8.18.0 -y coq.8.18.0
```

From the repository root, generate the local Makefile from `_CoqProject`, then
build. `Makefile.coq` and its configuration are generated, ignored files; no
machine-specific Makefile is part of the release.

```sh
opam exec --switch=coq-8.18.0 -- coq_makefile -f _CoqProject -o Makefile.coq
opam exec --switch=coq-8.18.0 -- make -f Makefile.coq -j2
```

Check the main result modules with Coq's kernel after the build:

```sh
opam exec --switch=coq-8.18.0 -- coqchk -R theories HyperLogic \
  HyperLogic.Semantics.EpsilonFull.EpsilonFull_Soundness \
  HyperLogic.Semantics.EpsilonFull.EpsilonFull_Completeness \
  HyperLogic.Semantics.EpsilonFull.EpsilonFull_ModelCategory \
  HyperLogic.Semantics.EpsilonFull.EpsilonFull_SelectionModels \
  HyperLogic.Semantics.Epsilon.Epsilon_SelectionModels \
  HyperLogic.Semantics.Epsilon.Epsilon_Completeness \
  HyperLogic.Semantics.IFOL.IFOL_Completeness \
  HyperLogic.Semantics.Metatheory.EpsilonFull_Substitutivity \
  HyperLogic.Semantics.Metatheory.DerivationExtractionInstances \
  HyperLogic.Semantics.EpsilonFull.IndexedHeytingPredicates
```

`Print Assumptions` shows that Full completeness and term-model initiality
retain the existing `Eqdep.Eq_rect_eq.eq_rect_eq` dependency. Some concrete
counterexample consequences inherit it through the finite base model. The
new chosen-unit and indexed-Heyting constructors introduce no axiom. See
[the refactor record](REFACTOR_REPORT.md) for the formalization inventory.

The [CI workflow](.github/workflows/coq.yml) runs the same clean build and
kernel check on pushes and pull requests.

The [documentation index](docs/index.html) and older research reports are
historical working notes. Use the tracked Rocq sources and `_CoqProject` for
the current formal statements and build scope.
