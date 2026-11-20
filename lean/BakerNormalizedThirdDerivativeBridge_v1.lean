import Mathlib
import BakerNormalizedSecondDerivativeBridge_v2
import BakerNormalizedThirdDerivativeQuotient_v1

namespace BakerTrisection

/-!
# Generalized normalized chord: ordinary second derivative on a neighborhood

Transfers the verified derivative of the explicit first-derivative expression
G_r to the ordinary derivative of the first derivative of H_r, at each point
in the certified open neighborhood.

The formula below is deliberately kept in quotient-rule form. This module
does not yet establish the ordinary third derivative at zero.
-/

/-- Near any `t` satisfying the explicit local-domain restriction, the
ordinary derivative of `H_r` agrees with its explicit expression. -/
theorem normalizedChord_deriv_eventuallyEq_expression_at (r t : ℝ)
    (ht : |t| < 1 / (|r| + 1)) :
    (fun x : ℝ => deriv (normalizedChordResidual r) x)
      =ᶠ[nhds t] normalizedChordDerivativeExpression r := by
  have hinterval :
      Set.Ioo (-(1 / (|r| + 1))) (1 / (|r| + 1)) ∈ nhds t := by
    exact Ioo_mem_nhds (abs_lt.mp ht).1 (abs_lt.mp ht).2
  filter_upwards [hinterval] with x hx
  exact normalizedChord_deriv_eq_expression_of_small r x (abs_lt.mpr hx)

/-- The ordinary first-derivative function of `H_r` has the derivative
provided by the quotient rule, throughout the explicit neighborhood. -/
theorem normalizedChord_second_hasDerivAt_of_small (r t : ℝ)
    (ht : |t| < 1 / (|r| + 1)) :
    HasDerivAt (fun x : ℝ => deriv (normalizedChordResidual r) x)
      (((r * -Real.sin t) * Real.sqrt (normalizedChordRadicand r t) -
         normalizedChordNumerator r t *
           ((0 - 2 * normalizedChordInner r t ^ (2 - 1) *
              (r * Real.cos t)) /
            (2 * Real.sqrt (normalizedChordRadicand r t)))) /
        (Real.sqrt (normalizedChordRadicand r t)) ^ 2) t := by
  have hG := normalizedChordDerivativeExpression_hasDerivAt_of_small r t ht
  have heq := normalizedChord_deriv_eventuallyEq_expression_at r t ht
  exact hG.congr_of_eventuallyEq heq

/-- A pointwise explicit formula for the ordinary second derivative of H_r
on the same neighborhood. -/
theorem normalizedChord_second_deriv_eq_of_small (r t : ℝ)
    (ht : |t| < 1 / (|r| + 1)) :
    deriv (fun x : ℝ => deriv (normalizedChordResidual r) x) t =
      (((r * -Real.sin t) * Real.sqrt (normalizedChordRadicand r t) -
         normalizedChordNumerator r t *
           ((0 - 2 * normalizedChordInner r t ^ (2 - 1) *
              (r * Real.cos t)) /
            (2 * Real.sqrt (normalizedChordRadicand r t)))) /
        (Real.sqrt (normalizedChordRadicand r t)) ^ 2) := by
  exact (normalizedChord_second_hasDerivAt_of_small r t ht).deriv

end BakerTrisection

#check BakerTrisection.normalizedChord_deriv_eventuallyEq_expression_at
#check BakerTrisection.normalizedChord_second_hasDerivAt_of_small
#check BakerTrisection.normalizedChord_second_deriv_eq_of_small
#print axioms BakerTrisection.normalizedChord_deriv_eventuallyEq_expression_at
#print axioms BakerTrisection.normalizedChord_second_hasDerivAt_of_small
#print axioms BakerTrisection.normalizedChord_second_deriv_eq_of_small
