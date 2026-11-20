import BakerProportionalCubicReleaseAudit_v1

/-!
# Baker generalized cubic-law release definition and axiom audit

This audit imports the previously compiled release theorems, prints the
actual definitions used by Lean, and reports their transitive axioms.
The exact residual definition should read
`proportionalChord a b theta - theta / b`.
-/

#print BakerTrisection.proportionalChord
#print BakerTrisection.proportionalChordResidual
#print BakerTrisection.normalizedChordResidual
#print BakerTrisection.proportionalChordCubicCoefficient

#check BakerTrisection.proportionalChord_cubic_limit_explicit
#check BakerTrisection.proportionalChord_cubic_limit_four_three_release
#check BakerTrisection.proportionalChord_cubic_limit_equal_release

#print axioms BakerTrisection.proportionalChord_cubic_limit_explicit
#print axioms BakerTrisection.proportionalChord_cubic_limit_four_three_release
#print axioms BakerTrisection.proportionalChord_cubic_limit_equal_release
