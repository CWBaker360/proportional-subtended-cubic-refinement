import Mathlib
import BakerNormalizedCubicLimitDenominator_v3

namespace BakerTrisection

/-!
# Cubic-limit preparation: certified punctured derivative slopes

The derivatives at zero already exist and their values are known. Mathlib's
`HasDerivAt.tendsto_slope_zero` converts each into a genuine punctured limit.
This is the final (third-derivative) limit that appears at the bottom of a
three-stage L'Hopital calculation. The quotient limit H_r(t)/t^3 is NOT
claimed by this module; that requires further transfer steps.
-/

/-- The first derivative has zero slope at zero. -/
theorem normalizedChord_first_slope_limit (r : ℝ) :
    Filter.Tendsto
      (fun h : ℝ => h⁻¹ • (normalizedChordResidual r (0 + h) - normalizedChordResidual r 0))
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (0 : ℝ)) := by
  exact (normalizedChordResidual_hasDerivAt_zero r).tendsto_slope_zero

/-- The second derivative has zero slope at zero. -/
theorem normalizedChord_second_slope_limit (r : ℝ) :
    Filter.Tendsto
      (fun h : ℝ => h⁻¹ •
        ((deriv (normalizedChordResidual r)) (0 + h) -
          (deriv (normalizedChordResidual r)) 0))
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (0 : ℝ)) := by
  exact (normalizedChord_deriv_hasDerivAt_zero r).tendsto_slope_zero

/-- The third derivative determines the punctured slope of the second derivative. -/
theorem normalizedChord_third_slope_limit (r : ℝ) :
    Filter.Tendsto
      (fun h : ℝ => h⁻¹ •
        ((deriv (fun x : ℝ => deriv (normalizedChordResidual r) x)) (0 + h) -
          (deriv (fun x : ℝ => deriv (normalizedChordResidual r) x)) 0))
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (6 * normalizedChordCubicCoefficient r)) := by
  exact (normalizedChord_second_deriv_hasDerivAt_coefficient r).tendsto_slope_zero

end BakerTrisection

#check BakerTrisection.normalizedChord_first_slope_limit
#check BakerTrisection.normalizedChord_second_slope_limit
#check BakerTrisection.normalizedChord_third_slope_limit
#print axioms BakerTrisection.normalizedChord_first_slope_limit
#print axioms BakerTrisection.normalizedChord_second_slope_limit
#print axioms BakerTrisection.normalizedChord_third_slope_limit
