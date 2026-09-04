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

The initial library covers finite differences, additive idempotents, polynomial reflection, weighted Cesàro estimates, calculus of even functions and isolated zeros, the Euler–Maclaurin formula with a third-order remainder and Stirling's formula for the complex Gamma function with an explicit remainder, two-closures of permutation groups, semidirect products, small matrix identities, exponential Vandermonde systems, coordinatewise determinant integration, separated subsequences in pseudometric spaces, and the de Bruijn–Newman heat flow `H t` (`LemmaLib.NumberTheory.DeBruijnNewman`): Riemann's representation `H 0 z = ξ((1 + i z)/2) / 8` proved from Mathlib's completed zeta function, the heat-kernel formula `H t z = ∫ H 0 (z - 2i√t v) e^{-v²}/√π dv`, the contour shift of a Gaussian-decaying holomorphic integrand between horizontal lines, and Polymath15's effective Riemann–Siegel model with its approximation theorem reduced to the Riemann–Siegel expansion `TailEstimate` (the heat-flow estimate `RtnEstimate` for the main terms, Polymath Proposition 6.1, is proved).

## Contributing

The Mathlib contributor documentation used by this project is vendored under [`docs/mathlib-guidelines`](docs/mathlib-guidelines). New declarations should use their natural Mathlib namespaces and should be written as if they were candidates for eventual upstream inclusion.

LemmaLib is licensed under Apache 2.0; see [`LICENSE`](LICENSE).
