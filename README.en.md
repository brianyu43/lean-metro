# Lean Metro

[![Lean CI](https://github.com/brianyu43/lean-metro/actions/workflows/lean.yml/badge.svg)](https://github.com/brianyu43/lean-metro/actions/workflows/lean.yml)

Lean Metro is a Lean 4 formalization of finite-state Metropolis--Hastings
correctness and Peskun ordering for the asymptotic variance of an actual
stationary sample mean.

The crown theorem,
`metropolisHastings_minimizes_sampleMeanAsymptoticVariance_of_irreducible`,
proves that MH and an admissible competitor with the same positive target and
stochastic proposal have actual scaled-variance limits, with the MH limit no
larger, when both generated kernels are finite irreducible. A maximum principle
and finite-dimensional linear algebra construct the Poisson inverses;
reversibility telescopes the exact remainder, so covariance decay and
aperiodicity are not assumptions. The project does not claim an infinite path
space, a CLT, or mixing rates.
[Theorem audit](THEOREM_AUDIT.md) · [Proof ownership guide](docs/PROOF_OWNERSHIP_GUIDE.md) · [Changelog](CHANGELOG.md) · [MIT license](LICENSE)

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

For a reversible kernel with a centered Poisson solution, the remainder
telescopes exactly:

```text
sum k=0..n, <f, P^(k+1)g>_pi
  = <g, Pg>_pi - <g, P^(n+2)g>_pi.
```

Finite stochastic iterates are uniformly bounded, so division by `n + 1`
sends this endpoint difference to zero without pointwise covariance decay.
The standard-assumption probabilistic theorem is:

```text
metropolisHastings_minimizes_sampleMeanAsymptoticVariance_of_irreducible
```

It returns both actual sample-mean variance limits and their Peskun ordering.
The caller supplies irreducibility for the MH and competitor kernels, but no
Poisson inverse, covariance decay, aperiodicity, or spectral gap.

## Machine-checked examples

- Two states: the MH and lazy-kernel algebraic variances are `3/2` and `6`.
- Three states: the fast uniform and lazy-kernel variances are `2/3` and `2`.
- For the three-state example, those last two values are also proved to be the
  limits of the actual scaled sample-mean variances. The lazy decay is the
  nontrivial geometric sequence `(1/2)^n`.
- `CrownExample.lean` directly invokes the irreducibility-facing crown theorem
  for MH and a half-MH-acceptance competitor built from the same target and
  proposal, obtaining actual limits `3/2 <= 6` without inverse or decay inputs.
- `PeriodicVarianceExample.lean` proves that a deterministic two-cycle has
  Poisson covariance `(-1)^n / 2`, which does not tend to zero, while its actual
  scaled sample-mean variance still tends to `0` by telescoping.
- The identity kernel is rejected as a singular Poisson example because its
  fixed functions are not only constants.

`VarianceLimit.lean` proves the exact finite-time covariance remainder identity.
`ReversibleVarianceLimit.lean` proves the endpoint telescope and its uniform
bound. `FinitePath.lean` through `ReversibleSampleMeanVariance.lean` connect it
to actual finite-path measures and random variables.

`Irreducibility.lean` reuses `Matrix.IsIrreducible`, proves the finite maximum
principle for fixed functions, bundles mean-zero functions as a finite-dimensional
subspace, and applies injective-implies-surjective to `I-P`. Its theorem
`meanZeroPoissonInvertible_of_irreducible` automatically supplies the centered
Poisson inverse. `IrreduciblePeskun.lean` composes that adapter with the
decay-free variance theorem into the public crown theorem.

## General-state extension (unreleased)

The finite development remains unchanged. A separate `LeanMetroGeneral`
namespace now contains the first measure-theoretic layer:

```text
joint proposal flow pi(dx) Q(x,dy)
  => swap-based reversibility
  => stationarity
  => reference-target densities h(x) and h(y)
  => MH accepted-flow maximality with density min(h(x),h(y)).
```

`referenceMH_largest_reversibleAcceptedFlow` proves that an admissible
competitor flow and the MH accepted flow are both swap-symmetric and that the
competitor is dominated by MH as a measure. Its proof is the finite
`Aa <= A`, `Aa = Ba^T <= B` argument lifted to almost-everywhere densities and
`Measure.withDensity_mono`. `FiniteAdapter.lean` recovers the existing
accepted-move inequality for positive symmetric finite proposals.

This unreleased layer does not yet construct the general accept/reject kernel,
Dirichlet or L2 operators, trajectory variance, a spectral-gap adapter, or the
infinite-dimensional Gaussian pCN application. Those gates are fixed in the
[general-state roadmap](docs/development/GENERAL_STATE_ROADMAP.md).

## Claim boundary

The project uses a separate probability space for each finite horizon; it
does not construct one infinite path space through a Kolmogorov extension.
The completed finite theorem does not prove pointwise or norm convergence of
`P^n g`, derive spectral
mixing rates, prove a Markov-chain CLT, or analyze convergence from arbitrary
initial distributions. See [THEOREM_AUDIT.md](THEOREM_AUDIT.md) for all
assumptions and exclusions.

## Build

The project pins Lean `v4.33.1` and a mathlib revision.

```bash
lake update
lake exe cache get
lake build
```

CI also rejects `sorry`, `admit`, and user-defined `axiom` declarations in both
namespaces and audits the finite and general-state crown theorem dependencies.
