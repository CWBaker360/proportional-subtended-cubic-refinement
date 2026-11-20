import Mathlib
import BakerNormalizedSecondDerivativePrep_v2

namespace BakerTrisection

/-!
# Normalized chord: derivative of its first-derivative expression at zero

The previous module proved that the cosine numerator and the arcsine
radicand have derivative zero at zero. Here we show the quotient appearing
in the derivative of H_r is stationary at zero as well.

This is a derivative theorem for an explicit expression. The subsequent
module will identify it with the ordinary second derivative of H_r.
-/

/-- The explicit first-derivative expression for the normalized residual. -/
noncomputable def normalizedChordDerivativeExpression (r t : ℝ) : ℝ :=
  normalizedChordNumerator r t / Real.sqrt (normalizedChordRadicand r t) - r

/-- The square-root denominator has zero first derivative at zero. -/
theorem normalizedChordSqrtRadicand_hasDerivAt_zero (r : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sqrt (normalizedChordRadicand r t)) 0 0 := by
  have hr := normalizedChordRadicand_hasDerivAt_zero r
  have hne : normalizedChordRadicand r 0 ≠ 0 := by
    simp [normalizedChordRadicand, normalizedChordInner]
  have hs := hr.sqrt hne
  simpa only [zero_div] using hs

/-- The quotient in the first-derivative expression is stationary at zero. -/
theorem normalizedChordQuotient_hasDerivAt_zero (r : ℝ) :
    HasDerivAt
      (fun t : ℝ => normalizedChordNumerator r t /
        Real.sqrt (normalizedChordRadicand r t)) 0 0 := by
  have hn := normalizedChordNumerator_hasDerivAt_zero r
  have hs := normalizedChordSqrtRadicand_hasDerivAt_zero r
  have hne : Real.sqrt (normalizedChordRadicand r 0) ≠ 0 := by
    simp [normalizedChordRadicand, normalizedChordInner]
  have hq := hn.div hs hne
  convert hq using 1 <;> simp only [Pi.div_apply, zero_mul, mul_zero, sub_zero, zero_div]

/-- The full first-derivative expression has derivative zero at zero. -/
theorem normalizedChordDerivativeExpression_hasDerivAt_zero (r : ℝ) :
    HasDerivAt (normalizedChordDerivativeExpression r) 0 0 := by
  have hq := normalizedChordQuotient_hasDerivAt_zero r
  have hc := hq.sub_const r
  convert hc using 1 <;> rfl

end BakerTrisection

#check BakerTrisection.normalizedChordSqrtRadicand_hasDerivAt_zero
#check BakerTrisection.normalizedChordQuotient_hasDerivAt_zero
#check BakerTrisection.normalizedChordDerivativeExpression_hasDerivAt_zero
#print axioms BakerTrisection.normalizedChordSqrtRadicand_hasDerivAt_zero
#print axioms BakerTrisection.normalizedChordQuotient_hasDerivAt_zero
#print axioms BakerTrisection.normalizedChordDerivativeExpression_hasDerivAt_zero
