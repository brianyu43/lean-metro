# Lean Metro v1.3.0

## Why this release exists

v1.3.0 removes the strongest remaining analytic input from the actual
sample-mean variance theorem. v1.2 constructed centered Poisson inverses from
finite irreducibility, but the public probabilistic theorem still received a
pointwise Poisson-covariance-decay proof for each kernel. This release proves
that reversibility makes the exact finite-horizon remainder telescope, so
boundedness—not pointwise decay—is sufficient.

## New machine-checked mathematics

For a reversible finite kernel and a centered Poisson solution
`(I - P)g = f`, `LeanMetro/ReversibleVarianceLimit.lean` proves

```text
<f, P^k g>_pi
  = <g, P^k g>_pi - <g, P^(k+1) g>_pi
```

and hence the exact finite sum

```text
sum k in range (n + 1), <f, P^(k+1) g>_pi
  = <g, P g>_pi - <g, P^(n+2) g>_pi.
```

A finite Markov operator preserves a uniform absolute bound. Therefore the two
endpoint quadratic forms are bounded independently of `n`, and division by
`n + 1` sends the remainder to zero. The resulting theorem is

```text
stationaryScaledVariance_tendsto_algebraicAsymptoticVariance_of_reversible
```

It requires reversibility and a centered Poisson inverse, but no covariance
decay, aperiodicity, irreducibility, or spectral gap. Nonnegativity and
normalization of `pi` are needed only at the next layer, where actual path
probability measures are constructed.

`LeanMetro/ReversibleSampleMeanVariance.lean` transfers the result through the
previously proved exact finite-path identity for mathlib's literal
`ProbabilityTheory.variance`.

## Standard-assumption public theorem

`LeanMetro/IrreduciblePeskun.lean` adds

```text
metropolisHastings_minimizes_sampleMeanAsymptoticVariance_of_irreducible
```

for a positive target, stochastic proposal, and admissible competitor. The
caller supplies finite irreducibility for the generated MH and competitor
kernels and a centered observable. The theorem internally constructs both
Poisson inverses, proves both actual stationary sample-mean variance limits,
and returns their Peskun ordering. Its signature contains no supplied inverse,
pointwise decay, aperiodicity, or spectral-gap hypothesis.

Both irreducibility assumptions are explicit: an admissible competitor may
reject every proposed move, so competitor irreducibility cannot in general be
inferred from MH irreducibility.

## End-to-end and periodic regressions

- `two_state_crown_actual_limits_and_order_of_irreducible` directly invokes the
  new public theorem for a two-state MH kernel and a half-MH-acceptance
  competitor. It obtains actual scaled-variance limits `3/2` and `6`, together
  with `3/2 <= 6`, without manually supplying Poisson inverses or decay.
- `PeriodicVarianceExample.lean` formalizes the deterministic two-state swap.
  The chain is finite, irreducible, and reversible but periodic. Its Poisson
  covariance is `(-1)^n / 2`, so pointwise convergence to zero is false, while
  its actual scaled sample-mean variance still converges to `0` through the new
  telescoping theorem.

The periodic example is both a regression test and a claim-boundary witness:
aperiodicity is unnecessary for this variance-limit conclusion, although it
can still matter for pointwise convergence, mixing, and rates.

## Trust and compatibility

- The older decay-based theorems remain available as lower-level APIs.
- `AxiomAudit.lean` now guards the legacy crown theorem, the decay-free core,
  the irreducibility-facing crown theorem, the concrete two-state crown
  theorem, and the periodic actual-limit theorem.
- Every audited result depends only on Lean's standard
  `[propext, Classical.choice, Quot.sound]` set.
- CI still rejects `sorry`, `admit`, and user-declared `axiom` tokens and
  compiles the guarded axiom audit separately.

## Verification gate

The release is made only after:

```text
all new modules compile individually
all five guarded axiom audits compile
lake build succeeds
no sorry/admit/user-declared axiom appears in project sources
git diff --check and documentation-link checks succeed
GitHub Actions succeeds on the exact release commit
the v1.3.0 tag resolves to that verified commit
```

## Exact scope after v1.3.0

The project now proves actual stationary sample-mean asymptotic-variance
Peskun ordering for finite irreducible MH and irreducible admissible competitor
kernels without a pointwise covariance-decay assumption. It does not prove
pointwise or norm convergence of `P^n g`, a spectral gap, quantitative mixing
rates, an infinite path-space construction, a Markov-chain CLT, or a
general-state-space theorem.
