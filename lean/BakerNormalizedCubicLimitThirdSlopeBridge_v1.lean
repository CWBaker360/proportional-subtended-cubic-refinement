import Mathlib
import BakerNormalizedCubicLimitSlope_v1

namespace BakerTrisection

/-!
# Cubic limit: third-slope quotient bridge

This module converts the certified punctured derivative slope of H_r''
into the ordinary scalar quotient needed at the bottom of a repeated
L'Hopital argument.  It does not yet prove the cubic quotient limit.
-/

/-- Since H_r''(0)=0, its punctured slope is H_r''(t)/t. -/
theorem normalizedChord_second_deriv_over_t_limit (r : ℝ) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ *
        deriv (fun x : ℝ => deriv (normalizedChordResidual r) x) t)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (6 * normalizedChordCubicCoefficient r)) := by
  simpa only [zero_add, normalizedChord_second_deriv_zero,
    sub_zero, smul_eq_mul] using normalizedChord_third_slope_limit r

/-- The final derivative quotient already converges to the cubic coefficient. -/
theorem normalizedChord_second_deriv_over_six_t_limit (r : ℝ) :
    Filter.Tendsto
      (fun t : ℝ =>
        (t⁻¹ * deriv (fun x : ℝ => deriv (normalizedChordResidual r) x) t) / 6)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (normalizedChordCubicCoefficient r)) := by
  have h := (normalizedChord_second_deriv_over_t_limit r).div_const (6 : ℝ)
  have hc : (6 * normalizedChordCubicCoefficient r) / 6 =
      normalizedChordCubicCoefficient r := by ring
  rw [hc] at h
  exact h

end BakerTrisection

#check BakerTrisection.normalizedChord_second_deriv_over_t_limit
#check BakerTrisection.normalizedChord_second_deriv_over_six_t_limit
#print axioms BakerTrisection.normalizedChord_second_deriv_over_t_limit
#print axioms BakerTrisection.normalizedChord_second_deriv_over_six_t_limit
