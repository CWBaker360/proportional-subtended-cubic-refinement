import Mathlib
import BakerNormalizedThirdDerivativeDenominator_v1
import BakerNormalizedSecondDerivativeCore_v4

namespace BakerTrisection

/-!
# Generalized normalized chord: quotient-rule derivatives

Differentiates the explicit first-derivative expression of H_r at every
point in the certified neighborhood. The resulting expression is kept
in quotient-rule form for robust formal verification.

This is not yet the proof of the third derivative at zero.
-/

/-- The quotient of the cosine numerator by the positive square-root
radicand is differentiable on the certified neighborhood. -/
theorem normalizedChordQuotient_hasDerivAt_of_small (r t : ℝ)
    (ht : |t| < 1 / (|r| + 1)) :
    HasDerivAt
      (fun x : ℝ => normalizedChordNumerator r x /
        Real.sqrt (normalizedChordRadicand r x))
      (((r * -Real.sin t) * Real.sqrt (normalizedChordRadicand r t) -
         normalizedChordNumerator r t *
           ((0 - 2 * normalizedChordInner r t ^ (2 - 1) *
              (r * Real.cos t)) /
            (2 * Real.sqrt (normalizedChordRadicand r t)))) /
        (Real.sqrt (normalizedChordRadicand r t)) ^ 2) t := by
  have hn := normalizedChordNumerator_hasDerivAt r t
  have hs := normalizedChordSqrtRadicand_hasDerivAt_of_small r t ht
  have hne := normalizedChordSqrtRadicand_ne_zero_of_small r t ht
  have hq := hn.div hs hne
  convert hq using 1 <;> rfl

/-- The explicit expression G_r for H_r' has a pointwise derivative
throughout the certified neighborhood. -/
theorem normalizedChordDerivativeExpression_hasDerivAt_of_small (r t : ℝ)
    (ht : |t| < 1 / (|r| + 1)) :
    HasDerivAt (normalizedChordDerivativeExpression r)
      (((r * -Real.sin t) * Real.sqrt (normalizedChordRadicand r t) -
         normalizedChordNumerator r t *
           ((0 - 2 * normalizedChordInner r t ^ (2 - 1) *
              (r * Real.cos t)) /
            (2 * Real.sqrt (normalizedChordRadicand r t)))) /
        (Real.sqrt (normalizedChordRadicand r t)) ^ 2) t := by
  have hq := normalizedChordQuotient_hasDerivAt_of_small r t ht
  have hc := hq.sub_const r
  convert hc using 1 <;> rfl

end BakerTrisection

#check BakerTrisection.normalizedChordQuotient_hasDerivAt_of_small
#check BakerTrisection.normalizedChordDerivativeExpression_hasDerivAt_of_small
#print axioms BakerTrisection.normalizedChordQuotient_hasDerivAt_of_small
#print axioms BakerTrisection.normalizedChordDerivativeExpression_hasDerivAt_of_small
