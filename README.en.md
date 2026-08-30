# Lean Metro

[![Lean CI](https://github.com/brianyu43/lean-metro/actions/workflows/lean.yml/badge.svg)](https://github.com/brianyu43/lean-metro/actions/workflows/lean.yml)

Lean Metro is a Lean 4 formalization of finite-state Metropolis--Hastings
correctness and Peskun ordering for the asymptotic variance of an actual
stationary sample mean.

## Main result

For a finite nonempty state space, positive target weights, a stochastic
proposal, and any admissible accept/reject rule with the same target and
proposal, the project proves:

```text
MH acceptance maximality
  => off-diagonal Peskun domination
  => Dirichlet-form ordering
  => inverse-quadratic-form ordering
  => algebraic asymptotic-variance ordering
```

The algebraic theorem is:

```text
metropolisHastings_minimizes_algebraicAsymptoticVariance
```

The project then constructs a probability mass function and probability
measure for every finite stationary Markov path. For a path of `N = n + 1`
states, it proves with mathlib's literal `ProbabilityTheory.variance` that

```text
N * Var(sample mean) = stationaryScaledVariance.
```

Under an explicit Poisson-covariance decay assumption, the left-hand side
converges to the algebraic asymptotic variance. The final probabilistic theorem
is:

```text
metropolisHastings_minimizes_sampleMeanAsymptoticVariance
```

It returns both actual sample-mean variance limits and their Peskun ordering.
Unique centered Poisson solutions and covariance decay are explicit theorem
parameters; they are not silently inferred from unformalized irreducibility.

## Machine-checked examples

- Two states: the MH and lazy-kernel algebraic variances are `3/2` and `6`.
- Three states: the fast uniform and lazy-kernel variances are `2/3` and `2`.
- For the three-state example, those last two values are also proved to be the
  limits of the actual scaled sample-mean variances. The lazy decay is the
  nontrivial geometric sequence `(1/2)^n`.
- The identity kernel is rejected as a singular Poisson example because its
  fixed functions are not only constants.

`VarianceLimit.lean` proves the exact finite-time covariance remainder identity.
`FinitePath.lean`, `StationaryMoments.lean`, and `SampleMeanVariance.lean`
connect it to actual finite-path measures and random variables.

## Claim boundary

The project uses a separate probability space for each finite horizon; it
does not construct one infinite path space through a Kolmogorov extension.
It also does not derive covariance decay automatically from general
irreducibility and aperiodicity, prove a Markov-chain CLT, or analyze mixing
rates. See [THEOREM_AUDIT.md](THEOREM_AUDIT.md) for all assumptions and
exclusions.

## Build

The project pins Lean `v4.33.1` and a mathlib revision.

```bash
lake update
lake exe cache get
lake build
```

CI also rejects `sorry`, `admit`, and user-defined `axiom` declarations.
