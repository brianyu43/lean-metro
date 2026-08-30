# Lean Metro v1.1.0

## Included

- finite-horizon stationary Markov path type, PMF, and probability measure
- current-state marginal and path-sum moment identities
- exact identity using mathlib's actual variance:

  ```text
  (n + 1) * Var(chainSampleMean n) = stationaryScaledVariance n
  ```

- conditional convergence of the actual scaled sample-mean variance to the
  Poisson-form algebraic asymptotic variance
- final probabilistic Peskun theorem for MH versus every admissible
  accept/reject competitor
- three-state regression limits: fast `2/3`, lazy `2`, including geometric
  lazy covariance decay
- Korean and English documentation and an updated theorem audit

## Primary theorem

```text
metropolisHastings_minimizes_sampleMeanAsymptoticVariance
```

## Verification gate

The release is made only after:

```text
all new modules compile individually
lake build succeeds
no sorry/admit/axiom appears in LeanMetro sources
git diff --check succeeds
GitHub Actions succeeds on the release commit
```

## Scope boundary

The theorem uses a separate probability space for every finite horizon and
assumes centered Poisson invertibility and covariance decay explicitly. It does
not construct one infinite path space, prove a Markov-chain CLT, or derive the
decay assumption from general irreducibility and aperiodicity.
