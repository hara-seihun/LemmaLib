# LemmaLib

LemmaLib is a curated Lean library for reusable results that are not yet in Mathlib. It depends on Mathlib and follows its naming, documentation, and style conventions.

The library contains curated general-purpose lemmas. Problem-specific formalizations and one-off proofs are deliberately excluded.

## Build

```sh
lake update
lake build
```

Import the whole library with:

```lean
import LemmaLib
```

Individual modules can be imported separately.

## Scope

The initial library covers finite differences, additive idempotents, polynomial reflection, weighted Cesàro estimates, calculus of even functions and isolated zeros, two-closures of permutation groups, semidirect products, small matrix identities, exponential Vandermonde systems, coordinatewise determinant integration, and separated subsequences in pseudometric spaces.

## Contributing

The Mathlib contributor documentation used by this project is vendored under [`docs/mathlib-guidelines`](docs/mathlib-guidelines). New declarations should use their natural Mathlib namespaces and should be written as if they were candidates for eventual upstream inclusion.

LemmaLib is licensed under Apache 2.0; see [`LICENSE`](LICENSE).
