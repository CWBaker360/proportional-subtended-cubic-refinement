import Mathlib
import BakerProportionalScaling_v3

namespace BakerTrisection

/-!
Basic exact identities for the normalized proportional-chord residual.
These facts prepare the one-parameter cubic-limit analysis; they do not
assert the as-yet-unproved general cubic limit.
-/

/-- The normalized chord residual is odd in its angle input. -/
theorem normalizedChordResidual_neg (r t : ℝ) :
    normalizedChordResidual r (-t) = -normalizedChordResidual r t := by
  simp [normalizedChordResidual, Real.sin_neg, Real.arcsin_neg] <;> ring

/-- With zero scale ratio, the normalized chord residual vanishes. -/
theorem normalizedChordResidual_zero_ratio (t : ℝ) :
    normalizedChordResidual 0 t = 0 := by
  simp [normalizedChordResidual]

/-- The normalized cubic coefficient vanishes at zero scale ratio. -/
theorem normalizedChordCubicCoefficient_zero :
    normalizedChordCubicCoefficient 0 = 0 := by
  simp [normalizedChordCubicCoefficient]

/-- Factorization of the proposed normalized cubic coefficient. -/
theorem normalizedChordCubicCoefficient_factored (r : ℝ) :
    normalizedChordCubicCoefficient r = r * (r - 1) * (r + 1) / 6 := by
  unfold normalizedChordCubicCoefficient
  ring

end BakerTrisection

#check BakerTrisection.normalizedChordResidual_neg
#check BakerTrisection.normalizedChordResidual_zero_ratio
#check BakerTrisection.normalizedChordCubicCoefficient_zero
#check BakerTrisection.normalizedChordCubicCoefficient_factored

#print axioms BakerTrisection.normalizedChordResidual_neg
#print axioms BakerTrisection.normalizedChordResidual_zero_ratio
#print axioms BakerTrisection.normalizedChordCubicCoefficient_zero
#print axioms BakerTrisection.normalizedChordCubicCoefficient_factored
