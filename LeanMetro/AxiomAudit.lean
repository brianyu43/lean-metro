import LeanMetro.ProbabilisticPeskun

namespace LeanMetro

/-!
# Axiom audit

This is a compile-time regression test for the public crown theorem.  The three
listed dependencies are Lean's standard extensionality, classical-choice, and
quotient soundness axioms.  `#guard_msgs` makes compilation fail if the reported
set changes, including if `sorryAx` or a project-specific assumption appears.
-/

/--
info: 'LeanMetro.metropolisHastings_minimizes_sampleMeanAsymptoticVariance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms metropolisHastings_minimizes_sampleMeanAsymptoticVariance

end LeanMetro
