import LeanMetroGeneral.FiniteAdapter

namespace LeanMetroGeneral

/-!
# Axiom audit

Compile-time dependency audit for the first general-state crown theorem.
The three listed dependencies are Lean's standard extensionality,
classical-choice, and quotient-soundness axioms.
-/

/--
info: 'LeanMetroGeneral.referenceMH_largest_reversibleAcceptedFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms referenceMH_largest_reversibleAcceptedFlow

/--
info: 'LeanMetroGeneral.finite_referenceMH_largest_reversibleAcceptedFlow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms finite_referenceMH_largest_reversibleAcceptedFlow

end LeanMetroGeneral
