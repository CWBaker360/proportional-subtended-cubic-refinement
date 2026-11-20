import Mathlib
import BakerNormalizedThirdDerivativePrep_v2

namespace BakerTrisection

/-!
# Generalized normalized chord: denominator derivatives

This module proves positivity of the radicand and the pointwise derivative
of its square root on the explicit neighborhood around zero. These are the
remaining analytic prerequisites for differentiating the expression for H_r'.

Compilation candidate: it is not a proof of H_r'''(0).
-/

/-- The radicand is strictly positive throughout the certified neighborhood. -/
theorem normalizedChordRadicand_pos_of_small (r t : ℝ)
    (ht : |t| < 1 / (|r| + 1)) :
    0 < normalizedChordRadicand r t := by
  have ha := normalizedChord_abs_argument_lt_one_of_small r t ht
  have hu : -1 < r * Real.sin t ∧ r * Real.sin t < 1 := abs_lt.mp ha
  have hp : 0 < (1 - r * Real.sin t) * (1 + r * Real.sin t) := by
    apply mul_pos
    · linarith [hu.2]
    · linarith [hu.1]
  unfold normalizedChordRadicand normalizedChordInner
  nlinarith

/-- The square-root denominator is nonzero on the certified neighborhood. -/
theorem normalizedChordSqrtRadicand_ne_zero_of_small (r t : ℝ)
    (ht : |t| < 1 / (|r| + 1)) :
    Real.sqrt (normalizedChordRadicand r t) ≠ 0 := by
  have hp := normalizedChordRadicand_pos_of_small r t ht
  exact ne_of_gt (Real.sqrt_pos.2 hp)

/-- Derivative of the square-root denominator at any point in the neighborhood. -/
theorem normalizedChordSqrtRadicand_hasDerivAt_of_small (r t : ℝ)
    (ht : |t| < 1 / (|r| + 1)) :
    HasDerivAt (fun x : ℝ => Real.sqrt (normalizedChordRadicand r x))
      ((0 - 2 * normalizedChordInner r t ^ (2 - 1) * (r * Real.cos t)) /
        (2 * Real.sqrt (normalizedChordRadicand r t))) t := by
  have hr := normalizedChordRadicand_hasDerivAt r t
  have hne : normalizedChordRadicand r t ≠ 0 :=
    ne_of_gt (normalizedChordRadicand_pos_of_small r t ht)
  exact hr.sqrt hne

end BakerTrisection

#check BakerTrisection.normalizedChordRadicand_pos_of_small
#check BakerTrisection.normalizedChordSqrtRadicand_ne_zero_of_small
#check BakerTrisection.normalizedChordSqrtRadicand_hasDerivAt_of_small
#print axioms BakerTrisection.normalizedChordRadicand_pos_of_small
#print axioms BakerTrisection.normalizedChordSqrtRadicand_ne_zero_of_small
#print axioms BakerTrisection.normalizedChordSqrtRadicand_hasDerivAt_of_small
