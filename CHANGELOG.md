# Changelog

## Unreleased

## [v1.2.0] — 2026-08-31

- Added `meanZeroPoissonInvertible_of_irreducible`, deriving the centered
  Poisson inverse from normalized stationarity and mathlib's finite matrix
  irreducibility through a maximum principle and finite-dimensional
  injective-implies-surjective argument.
- Added an end-to-end two-state regression example that invokes the public
  probabilistic crown theorem and proves actual limits `3/2 <= 6`.
- Added a compile-time `#print axioms` audit for the crown theorem.
- Added an MIT license, repository metadata, a compact README claim boundary,
  a theorem-ownership study guide, and a documentation index.
- Moved development plans, research notes, and detailed release notes under
  `docs/`.

Detailed notes: [docs/releases/RELEASE_NOTES_V1.2.md](docs/releases/RELEASE_NOTES_V1.2.md)

## [v1.1.0] — 2026-08-31

- Constructed actual finite-horizon stationary path PMFs and probability
  measures.
- Proved the exact identity
  `(n + 1) * Var(chainSampleMean n) = stationaryScaledVariance n`.
- Added the probabilistic crown theorem
  `metropolisHastings_minimizes_sampleMeanAsymptoticVariance`.
- Verified three-state actual asymptotic-variance limits `2/3` and `2`.

Detailed notes: [docs/releases/RELEASE_NOTES_V1.1.md](docs/releases/RELEASE_NOTES_V1.1.md)

## [v1.0.0] — 2026-08-31

- Completed the algebraic Peskun chain from MH acceptance maximality through
  Dirichlet and inverse-quadratic-form ordering.
- Added the conditional covariance/Cesàro variance-limit bridge.
- Added two-state and three-state exact examples.

Detailed notes: [docs/releases/RELEASE_NOTES.md](docs/releases/RELEASE_NOTES.md)

## Initial finite-state MH correctness — 2026-08-27

- Proved symmetric and zero-safe asymmetric MH stochasticity, detailed
  balance, and stationarity.

[v1.2.0]: https://github.com/brianyu43/lean-metro/releases/tag/v1.2.0
[v1.1.0]: https://github.com/brianyu43/lean-metro/releases/tag/v1.1.0
[v1.0.0]: https://github.com/brianyu43/lean-metro/releases/tag/v1.0.0
