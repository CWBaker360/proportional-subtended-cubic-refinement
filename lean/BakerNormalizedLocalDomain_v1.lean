import Mathlib
import BakerNormalizedDerivativeGeneral_v1

namespace BakerTrisection

/-!
# An explicit neighborhood for the general normalized residual

For each real ratio r, the positive radius 1 / (|r| + 1) keeps
|r * sin t| strictly below 1. Thus the previously verified
arcsine chain-rule derivative is valid throughout that neighborhood.

Compilation candidate for Lean 4.36.0-rc2 / Mathlib.
-/

/-- The open interval of radius `1 / (|r| + 1)` is inside the
strict real-arcsine derivative domain, for *every* real `r`. -/
theorem normalizedChord_abs_argument_lt_one_of_small
    (r t : ℝ) (ht : |t| < 1 / (|r| + 1)) :
    |r * Real.sin t| < 1 := by
  have hp : 0 < |r| + 1 := by positivity
  have hmul : (|r| + 1) * |t| < 1 := by
    have h := mul_lt_mul_of_pos_left ht hp
    have hc : (|r| + 1) * (1 / (|r| + 1)) = 1 := by
      field_simp
    rw [hc] at h
    exact h
  have hle : |r| * |t| ≤ (|r| + 1) * |t| := by
    nlinarith [abs_nonneg t]
  calc
    |r * Real.sin t| = |r| * |Real.sin t| := abs_mul r (Real.sin t)
    _ ≤ |r| * |t| :=
      mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (abs_nonneg r)
    _ ≤ (|r| + 1) * |t| := hle
    _ < 1 := hmul

/-- The normalized residual has its explicit derivative on this
positive, ratio-dependent neighborhood of zero. -/
theorem normalizedChord_hasDerivAt_on_explicit_neighborhood
    (r t : ℝ) (ht : |t| < 1 / (|r| + 1)) :
    HasDerivAt (normalizedChordResidual r)
      ((1 / Real.sqrt (1 - (r * Real.sin t) ^ 2)) *
        (r * Real.cos t) - r) t := by
  exact normalizedChordResidual_hasDerivAt_of_abs_lt_one r t
    (normalizedChord_abs_argument_lt_one_of_small r t ht)

end BakerTrisection

#check BakerTrisection.normalizedChord_abs_argument_lt_one_of_small
#check BakerTrisection.normalizedChord_hasDerivAt_on_explicit_neighborhood
#print axioms BakerTrisection.normalizedChord_abs_argument_lt_one_of_small
#print axioms BakerTrisection.normalizedChord_hasDerivAt_on_explicit_neighborhood
