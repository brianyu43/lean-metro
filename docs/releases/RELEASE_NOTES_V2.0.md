# Lean Metro v2.0.0

v2.0.0 begins the general measurable-state-space development without changing
the completed finite-state theory.  The release stops deliberately at
reference-reversible accepted-flow maximality; it does not yet claim a general
accept/reject transition kernel or a general-state variance theorem.

## Main theorem

```text
LeanMetroGeneral.referenceMH_largest_reversibleAcceptedFlow
```

For a measurable state space, reference measure `μ`, proposal kernel `Q`,
target density `h : X → ℝ≥0∞`, and admissible acceptance rule `a`, assume:

- `μ(dx)Q(x,dy)` is invariant under swapping `x` and `y`;
- `h` and `a` are measurable;
- `a(x,y) ≤ 1` pointwise;
- `h(x)a(x,y)=h(y)a(y,x)` almost everywhere under the joint proposal flow.

The theorem proves that the competitor and reference-MH accepted flows are
both swap-symmetric and that

```text
acceptedFlow μ Q h a ≤ referenceMHAcceptedFlow μ Q h.
```

The proof is the measure-theoretic form of the finite scalar argument:

```text
h(x)a(x,y) ≤ h(x)
h(x)a(x,y) = h(y)a(y,x) ≤ h(y)
therefore h(x)a(x,y) ≤ min(h(x),h(y)).
```

## New modules

- `JointFlow.lean`: joint proposal flow, coordinate reversal, involution,
  monotonicity, and density change of variables.
- `Reversibility.lean`: measure-level reversibility and
  reversibility-implies-stationarity.
- `ReferenceProposal.lean`: reference reversibility and target-flow density
  reversal.
- `AcceptedFlow.lean`: admissibility, accepted flows, symmetry, and maximality.
- `FiniteAdapter.lean`: a finite kernel backed by counting measure, atom
  formulas, symmetric proposal-flow reversibility, and regression to the
  existing finite accepted-move theorem.
- `AxiomAudit.lean`: compile-time audits for the public general theorem and its
  finite end-to-end adapter.

## Finite regression

```text
finite_referenceMH_largest_reversibleAcceptedFlow
general_reference_maximality_recovers_finite_mhAcceptedMove_maximal
```

The first theorem instantiates the public measure theorem on a finite discrete
space. The second recovers the existing pointwise accepted-move inequality for
positive symmetric proposals. Zero proposal entries will be handled by an
almost-everywhere atom adapter; fully asymmetric proposals belong to the later
common-part construction `ν ⊓ reverseFlow ν`.

## Verification

The release gate requires:

```text
lake build
lake env lean LeanMetro/AxiomAudit.lean
lake env lean LeanMetroGeneral/AxiomAudit.lean
no sorry/admit/user axiom
git diff --check
```

The public general theorem and the finite end-to-end adapter depend only on
Lean's standard `[propext, Classical.choice, Quot.sound]` axioms.

## Next release

v2.1 will construct the accepted proposal subkernel, add the rejection mass as
a Dirac stay-put kernel, and prove stochasticity, reversibility, and
stationarity of the resulting general accept/reject transition kernel.
