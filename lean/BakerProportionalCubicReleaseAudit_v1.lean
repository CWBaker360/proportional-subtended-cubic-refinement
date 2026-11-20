import Mathlib
import BakerProportionalCubicLimit_v3

namespace BakerTrisection

/-!
# Release audit: generalized proportional-chord cubic limit

This module restates the already-verified theorem with its coefficient expanded,
and records the 4:3 and equal-parameter specializations. It introduces no
additional axioms or unproved mathematical hypotheses.
-/

/-- Explicit coefficient statement for all nonzero real parameters. -/
theorem proportionalChord_cubic_limit_explicit
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Filter.Tendsto
      (fun theta : ℝ => proportionalChordResidual a b theta / theta ^ 3)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds ((a ^ 2 - b ^ 2) / (24 * a ^ 2 * b ^ 3))) := by
  simpa only [proportionalChordCubicCoefficient] using
    proportionalChord_cubic_limit_general a b ha hb

/-- The original Baker 4:3 seed has cubic coefficient 7/10368. -/
theorem proportionalChord_cubic_limit_four_three_release :
    Filter.Tendsto
      (fun theta : ℝ => proportionalChordResidual 4 3 theta / theta ^ 3)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (7 / 10368 : ℝ)) := by
  simpa only [proportionalChordCubicCoefficient_four_three] using
    proportionalChord_cubic_limit_general 4 3 (by norm_num) (by norm_num)

/-- Equal nonzero parameters eliminate the cubic coefficient. -/
theorem proportionalChord_cubic_limit_equal_release
    (a : ℝ) (ha : a ≠ 0) :
    Filter.Tendsto
      (fun theta : ℝ => proportionalChordResidual a a theta / theta ^ 3)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (0 : ℝ)) := by
  simpa only [proportionalChordCubicCoefficient_equal] using
    proportionalChord_cubic_limit_general a a ha ha

end BakerTrisection

#check BakerTrisection.proportionalChord_cubic_limit_explicit
#check BakerTrisection.proportionalChord_cubic_limit_four_three_release
#check BakerTrisection.proportionalChord_cubic_limit_equal_release

#print axioms BakerTrisection.proportionalChord_cubic_limit_explicit
#print axioms BakerTrisection.proportionalChord_cubic_limit_four_three_release
#print axioms BakerTrisection.proportionalChord_cubic_limit_equal_release
