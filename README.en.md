# Lean Metro

[![Lean CI](https://github.com/brianyu43/lean-metro/actions/workflows/lean.yml/badge.svg)](https://github.com/brianyu43/lean-metro/actions/workflows/lean.yml)

Lean Metro is a Lean 4 formalization of finite-state Metropolis--Hastings
correctness and the algebraic core of Peskun ordering.

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

The final theorem is:

```text
metropolisHastings_minimizes_algebraicAsymptoticVariance
```

It assumes that the centered Poisson problems for both kernels have unique
solutions. This requirement is explicit through `MeanZeroPoissonInvertible`;
the development does not silently infer it from unformalized irreducibility.

## Machine-checked examples

- Two states: the MH and lazy-kernel algebraic variances are `3/2` and `6`.
- Three states: the fast uniform and lazy-kernel variances are `2/3` and `2`.
- The identity kernel is rejected as a singular Poisson example because its
  fixed functions are not only constants.

`VarianceLimit.lean` also proves an exact finite-time covariance remainder
identity. If the Poisson remainder covariance tends to zero, the covariance
formula converges to the algebraic asymptotic variance. The three-state fast
kernel instantiates this theorem with limit `2/3`.

## Claim boundary

The project does not yet construct a stationary random-variable Markov
process and identify its literal `N * Var(sample mean)` with the finite-time
covariance expression. It therefore calls the core result *algebraic*
asymptotic variance. See [THEOREM_AUDIT.md](THEOREM_AUDIT.md) for all
assumptions and exclusions.

## Build

The project pins Lean `v4.33.1` and a mathlib revision.

```bash
lake update
lake exe cache get
lake build
```

CI also rejects `sorry`, `admit`, and user-defined `axiom` declarations.
