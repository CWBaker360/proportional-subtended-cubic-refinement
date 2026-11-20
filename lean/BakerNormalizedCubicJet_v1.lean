import Mathlib
import BakerNormalizedThirdDerivativeCertificate_v1
import BakerNormalizedSecondDerivativeBridge_v2
import BakerNormalizedFirstDerivative_v3

namespace BakerTrisection

/-!
# General normalized chord: certified cubic Taylor jet at the origin

This module packages the verified ordinary first, second, and third
 derivatives of H_r(t) = arcsin (r sin t) - r t, without claiming a
 Taylor remainder or the cubic quotient limit. The latter remains a
 separate analytic theorem to be proved.
-/

/-- The third derivative equals six times the proposed cubic coefficient. -/
theorem normalizedChord_third_deriv_eq_six_cubicCoefficient (r : ℝ) :
    deriv (fun t : ℝ =>
      deriv (fun x : ℝ => deriv (normalizedChordResidual r) x) t) 0 =
      6 * normalizedChordCubicCoefficient r := by
  rw [normalizedChord_third_deriv_zero]
  unfold normalizedChordCubicCoefficient
  ring

/-- The complete ordinary derivative data through degree three at the origin. -/
theorem normalizedChord_cubic_jet_zero (r : ℝ) :
    normalizedChordResidual r 0 = 0 ∧
    deriv (normalizedChordResidual r) 0 = 0 ∧
    deriv (fun t : ℝ => deriv (normalizedChordResidual r) t) 0 = 0 ∧
    deriv (fun t : ℝ =>
      deriv (fun x : ℝ => deriv (normalizedChordResidual r) x) t) 0 =
        6 * normalizedChordCubicCoefficient r := by
  exact ⟨normalizedChordResidual_zero r,
    normalizedChordResidual_deriv_zero r,
    normalizedChord_second_deriv_zero r,
    normalizedChord_third_deriv_eq_six_cubicCoefficient r⟩

/-- The third-derivative calculation as a genuine `HasDerivAt` theorem. -/
theorem normalizedChord_second_deriv_hasDerivAt_coefficient (r : ℝ) :
    HasDerivAt
      (fun t : ℝ => deriv (fun x : ℝ => deriv (normalizedChordResidual r) x) t)
      (6 * normalizedChordCubicCoefficient r) 0 := by
  have hc : 6 * normalizedChordCubicCoefficient r = r * (r ^ 2 - 1) := by
    unfold normalizedChordCubicCoefficient
    ring
  rw [hc]
  exact normalizedChord_second_deriv_hasDerivAt_zero r

end BakerTrisection

#check BakerTrisection.normalizedChord_third_deriv_eq_six_cubicCoefficient
#check BakerTrisection.normalizedChord_cubic_jet_zero
#check BakerTrisection.normalizedChord_second_deriv_hasDerivAt_coefficient
#print axioms BakerTrisection.normalizedChord_third_deriv_eq_six_cubicCoefficient
#print axioms BakerTrisection.normalizedChord_cubic_jet_zero
#print axioms BakerTrisection.normalizedChord_second_deriv_hasDerivAt_coefficient
