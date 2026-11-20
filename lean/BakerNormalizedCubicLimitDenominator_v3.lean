import Mathlib
import BakerNormalizedCubicJet_v1

namespace BakerTrisection

/-!
# Cubic-limit preparation: denominator derivative ladder

These are ordinary derivative statements used by a three-stage
L'Hopital argument for H_r(t)/t^3.  They do not assert the limit.
The numerator's derivative data are already certified in
`BakerNormalizedCubicJet_v1`.
-/

/-- First derivative of the cubic denominator. -/
theorem normalizedCubicDenominator_hasDerivAt (t : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ 3) (3 * t ^ 2) t := by
  convert (hasDerivAt_id t).pow 3 using 1
  all_goals first
    | (funext x; rfl)
    | norm_num

/-- First derivative of the quadratic denominator occurring after one step. -/
theorem normalizedQuadraticDenominator_hasDerivAt (t : ℝ) :
    HasDerivAt (fun x : ℝ => 3 * x ^ 2) (6 * t) t := by
  convert ((hasDerivAt_id t).pow 2).const_mul 3 using 1 <;> simp only [Pi.pow_apply, id_eq] <;> ring

/-- First derivative of the linear denominator occurring after two steps. -/
theorem normalizedLinearDenominator_hasDerivAt (t : ℝ) :
    HasDerivAt (fun x : ℝ => 6 * x) 6 t := by
  convert (hasDerivAt_id t).const_mul 6 using 1 <;> simp only [id_eq, mul_one]

/-- The cubic denominator and its first two derived denominators vanish
at the origin. -/
theorem normalizedCubicDenominator_vanish_at_zero :
    (0 : ℝ) ^ 3 = 0 ∧ 3 * (0 : ℝ) ^ 2 = 0 ∧ 6 * (0 : ℝ) = 0 := by
  norm_num

/-- The three nonzero conditions needed away from zero. -/
theorem normalizedCubicDenominator_nonzero_of_ne_zero
    (t : ℝ) (ht : t ≠ 0) :
    t ^ 3 ≠ 0 ∧ 3 * t ^ 2 ≠ 0 ∧ 6 * t ≠ 0 := by
  constructor
  · exact pow_ne_zero 3 ht
  constructor
  · exact mul_ne_zero (by norm_num) (pow_ne_zero 2 ht)
  · exact mul_ne_zero (by norm_num) ht

/-- The scalar obtained by dividing the certified third derivative by 6. -/
theorem normalizedChord_third_deriv_div_six (r : ℝ) :
    (deriv (fun t : ℝ =>
      deriv (fun x : ℝ => deriv (normalizedChordResidual r) x) t) 0) / 6 =
      normalizedChordCubicCoefficient r := by
  rw [normalizedChord_third_deriv_eq_six_cubicCoefficient]
  ring

end BakerTrisection

#check BakerTrisection.normalizedCubicDenominator_hasDerivAt
#check BakerTrisection.normalizedQuadraticDenominator_hasDerivAt
#check BakerTrisection.normalizedLinearDenominator_hasDerivAt
#check BakerTrisection.normalizedCubicDenominator_vanish_at_zero
#check BakerTrisection.normalizedCubicDenominator_nonzero_of_ne_zero
#check BakerTrisection.normalizedChord_third_deriv_div_six
#print axioms BakerTrisection.normalizedCubicDenominator_hasDerivAt
#print axioms BakerTrisection.normalizedQuadraticDenominator_hasDerivAt
#print axioms BakerTrisection.normalizedLinearDenominator_hasDerivAt
#print axioms BakerTrisection.normalizedCubicDenominator_vanish_at_zero
#print axioms BakerTrisection.normalizedCubicDenominator_nonzero_of_ne_zero
#print axioms BakerTrisection.normalizedChord_third_deriv_div_six
