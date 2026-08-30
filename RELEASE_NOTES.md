# Lean Metro v1.0.0

## Included

- symmetric and zero-safe asymmetric finite-state MH correctness
- generic admissible accept/reject kernels
- MH accepted-move maximality and off-diagonal Peskun domination
- finite reversible kernels and weighted self-adjoint Markov operators
- Dirichlet-form identity and ordering
- mean-zero Poisson existence/uniqueness interface
- inverse quadratic-form ordering
- final algebraic Peskun variance theorem
- two-state and three-state exact numerical examples
- conditional covariance/Cesàro variance-limit bridge
- GitHub Actions build and proof-placeholder rejection

## Primary theorem

```text
metropolisHastings_minimizes_algebraicAsymptoticVariance
```

## Verification gate

The release is made only after:

```text
all key modules compile individually
lake build succeeds
no sorry/admit/axiom appears in LeanMetro sources
git diff --check succeeds
GitHub Actions succeeds on the release commit
```

## Scope boundary

The v1.0 result is finite-dimensional and algebraic. A literal probability
space construction of a stationary Markov process and its sample-mean
variance identity remains a separate Phase 6b milestone.
