import Mathlib
import BakerNormalizedThirdDerivativeBridge_v1

namespace BakerTrisection

/-!
# Normalized chord: reduced second-derivative model at the origin

The anticipated reduced expression for the ordinary second derivative is

  r * (r^2 - 1) * sin t / (sqrt (1 - (r sin t)^2))^3.

This module proves its derivative at zero equals r * (r^2 - 1).
A separate algebraic bridge must still identify this expression with the
ordinary second derivative proved in the imported module. No claim of the
ordinary third derivative of H_r is made here.
-/

noncomputable def normalizedChordReducedSecond (r t : ℝ) : ℝ :=
  (r * (r ^ 2 - 1) * Real.sin t) /
    (Real.sqrt (normalizedChordRadicand r t)) ^ 3

/-- The numerator of the reduced second-derivative expression has the
expected derivative at zero. -/
theorem normalizedChordReducedNumerator_hasDerivAt_zero (r : ℝ) :
    HasDerivAt (fun t : ℝ => r * (r ^ 2 - 1) * Real.sin t)
      (r * (r ^ 2 - 1)) 0 := by
  convert (Real.hasDerivAt_sin 0).const_mul (r * (r ^ 2 - 1)) using 1 <;>
    simp

/-- The denominator of the reduced second derivative equals one at zero. -/
theorem normalizedChordReducedDenominator_zero (r : ℝ) :
    (Real.sqrt (normalizedChordRadicand r 0)) ^ 3 = 1 := by
  simp [normalizedChordRadicand, normalizedChordInner]

/-- The reduced second-derivative model has the predicted derivative at zero. -/
theorem normalizedChordReducedSecond_hasDerivAt_zero (r : ℝ) :
    HasDerivAt (normalizedChordReducedSecond r) (r * (r ^ 2 - 1)) 0 := by
  have hn := normalizedChordReducedNumerator_hasDerivAt_zero r
  have hd0 := normalizedChordSqrtRadicand_hasDerivAt_zero r
  have hd := hd0.pow 3
  have hne : (Real.sqrt (normalizedChordRadicand r 0)) ^ 3 ≠ 0 := by
    rw [normalizedChordReducedDenominator_zero]
    norm_num
  have hq := hn.div hd hne
  have hnum : r * (r ^ 2 - 1) * Real.sin 0 = 0 := by simp
  have hden : (Real.sqrt (normalizedChordRadicand r 0)) ^ 3 = 1 :=
    normalizedChordReducedDenominator_zero r
  have hfun :
      normalizedChordReducedSecond r =
        (fun t : ℝ => r * (r ^ 2 - 1) * Real.sin t) /
          ((fun t : ℝ => Real.sqrt (normalizedChordRadicand r t)) ^ 3) := by
    funext t
    rfl
  rw [hfun]
  convert hq using 1 <;>
    simp [hden, hnum, normalizedChordRadicand, normalizedChordInner]

/-- The ordinary derivative of the reduced expression has the same value. -/
theorem normalizedChordReducedSecond_deriv_zero (r : ℝ) :
    deriv (normalizedChordReducedSecond r) 0 = r * (r ^ 2 - 1) := by
  exact (normalizedChordReducedSecond_hasDerivAt_zero r).deriv

end BakerTrisection

#check BakerTrisection.normalizedChordReducedNumerator_hasDerivAt_zero
#check BakerTrisection.normalizedChordReducedDenominator_zero
#check BakerTrisection.normalizedChordReducedSecond_hasDerivAt_zero
#check BakerTrisection.normalizedChordReducedSecond_deriv_zero
#print axioms BakerTrisection.normalizedChordReducedSecond_hasDerivAt_zero
#print axioms BakerTrisection.normalizedChordReducedSecond_deriv_zero
