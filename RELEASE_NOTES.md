# HyperLogic v0.1.0

Initial versioned source release of the supported HyperLogic Rocq/Coq library.
The release is intended for Coq 8.18.0 with OCaml 4.14.1.

## Included

- All 93 `.v` sources listed in `_CoqProject`, including the EpsilonFull
  development, the distinct Epsilon and IFOL calculi, Epsilon_Adjoint, and the
  Individual compatibility paths.
- Chosen-unit characterizations and model constructors for EpsilonFull and
  epsilon-only semantics; term-model initiality up to hom equivalence.
- Formal counterexamples for definitional witness substitutivity and
  extensionality, structural derivation extraction for three calculi, and
  concrete EpsilonFull examples used by the manuscript.
- A conditional H-valued hyperdoctrine over arbitrary `S`, with explicitly
  chosen Type-valued indexed bounds.
- A portable `_CoqProject` build path, kernel-check instructions, and a CI
  workflow for the documented Coq version.

## Build and verification

Follow [README.md](https://github.com/mozow01/HyperLogic/blob/v0.1.0/README.md) to create the opam environment, generate the
ignored `Makefile.coq`, compile the full supported library, and run `coqchk`.
The release commit was checked from a fresh clone: 93 of 93 supported sources
compiled, and the main result modules passed `coqchk`.

## Scope and known dependencies

- Full completeness and term-model initiality retain the existing
  `Eqdep.Eq_rect_eq.eq_rect_eq` dependency. Some concrete counterexample
  consequences inherit it through the finite base model. No new axiom or
  `Admitted` was introduced for this release.
- The arbitrary-`S` H-valued construction assumes chosen indexed suprema and
  infima; these are not obtained constructively from a finite Heyting algebra
  alone.
- Legacy Simple and Simple_Ext sources, plus
  `Logic/Hyper/Epsilon/Critical_Epsilon_Provable.v` and
  `Semantics/Conservativity/Model_Expansion.v`, remain outside the supported
  build. The old `docs/` reports are historical working notes.

See [REFACTOR_REPORT.md](https://github.com/mozow01/HyperLogic/blob/v0.1.0/REFACTOR_REPORT.md) for the detailed name and module
changes. This release contains source code; GitHub can produce source archives
from its tag when the release is published.
