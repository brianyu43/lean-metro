# Lean Metro v1.2.0

## Why this release exists

v1.2.0 closes the highest-value findings from an external evaluation. It
tests the final public theorem end to end, records its axiom dependencies,
connects one formerly abstract assumption to a standard finite-state Markov
condition, and makes the repository easier to audit as a portfolio artifact.

## New machine-checked mathematics

- `FiniteKernel.Irreducible P` reuses mathlib's `Matrix.IsIrreducible P.prob`.
- `fixedPointsAreConstants_of_irreducible` proves a finite maximum principle:
  a fixed function reaches its maximum everywhere along positive-probability
  paths, so irreducibility makes it constant.
- `meanZeroSubmodule` and `meanZeroLaplacianLinearMap` bundle centered
  functions and `I-P` as finite-dimensional linear algebra.
- `meanZeroPoissonInvertible_of_irreducible` turns injectivity of `I-P` on the
  centered subspace into surjectivity and produces the full centered Poisson
  inverse.

This closes the Poisson-invertibility input from finite irreducibility together
with normalized stationarity. It does not yet derive covariance decay from
general aperiodicity or a spectral gap.

## Crown-theorem integration example

`LeanMetro/CrownExample.lean` uses the same two-state target and proposal for:

- the Metropolis--Hastings acceptance rule; and
- an admissible competitor accepting one half as often.

The example proves irreducibility for both generated kernels, obtains both
Poisson inverses through the new adapter, proves their covariance decay, and
directly invokes
`metropolisHastings_minimizes_sampleMeanAsymptoticVariance`. The returned
actual scaled sample-mean variance limits are `3/2` and `6`, with `3/2 <= 6`.

## Trust and presentation

- `LeanMetro/AxiomAudit.lean` fixes the crown theorem's `#print axioms` output
  at `[propext, Classical.choice, Quot.sound]` using `#guard_msgs`.
- CI compiles that audit explicitly, so a new `sorryAx` or project-specific
  axiom changes the expected output and fails the check.
- Added an MIT license, GitHub description, homepage, and focused topics.
- Added a compact claim boundary to both READMEs and a proof-ownership guide
  for the five questions an external reviewer is most likely to ask.
- Moved development records and detailed release notes under `docs/`.

## Verification gate

The release is made only after:

```text
new proof modules compile individually
the axiom-audit module compiles with its guarded expected output
lake build succeeds
no sorry/admit/user-declared axiom appears in project sources
git diff --check succeeds
GitHub Actions succeeds on the release commit
```

## Exact scope after v1.2.0

The project now automatically obtains centered Poisson invertibility from
finite irreducibility. The probabilistic crown theorem still receives
covariance decay explicitly for both kernels. Therefore the exact result is a
finite-state Peskun theorem for actual stationary sample-mean variance limits
under explicit decay, not yet the fully automatic irreducible-aperiodic
theorem and not a Markov-chain CLT.
