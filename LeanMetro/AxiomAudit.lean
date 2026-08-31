import LeanMetro.CrownExample
import LeanMetro.PeriodicVarianceExample

namespace LeanMetro

/-!
# Axiom audit

These are compile-time regression tests for the legacy conditional crown
theorem, the decay-free reversible core, the irreducibility-facing crown
theorem, and its concrete end-to-end examples. The three listed dependencies
are Lean's standard extensionality, classical-choice, and quotient soundness
axioms. `#guard_msgs` makes compilation fail if any reported set changes,
including if `sorryAx` or a project-specific assumption appears.
-/

/--
info: 'LeanMetro.metropolisHastings_minimizes_sampleMeanAsymptoticVariance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms metropolisHastings_minimizes_sampleMeanAsymptoticVariance

/--
info: 'LeanMetro.stationaryScaledVariance_tendsto_algebraicAsymptoticVariance_of_reversible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms stationaryScaledVariance_tendsto_algebraicAsymptoticVariance_of_reversible

/--
info: 'LeanMetro.metropolisHastings_minimizes_sampleMeanAsymptoticVariance_of_irreducible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms metropolisHastings_minimizes_sampleMeanAsymptoticVariance_of_irreducible

/--
info: 'LeanMetro.two_state_crown_actual_limits_and_order_of_irreducible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms two_state_crown_actual_limits_and_order_of_irreducible

/--
info: 'LeanMetro.periodic_sampleMean_scaledVariance_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms periodic_sampleMean_scaledVariance_tendsto_zero

end LeanMetro
