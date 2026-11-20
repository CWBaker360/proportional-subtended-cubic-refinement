import Mathlib
import BakerNormalizedLocalDomain_v1
import BakerNormalizedSecondDerivativeCore_v4

namespace BakerTrisection

/-!
# General normalized chord: ordinary second derivative at zero

For each real r, the normalized residual H_r has its first derivative
represented by `normalizedChordDerivativeExpression r` on an explicit
neighborhood of zero. The previously verified derivative of that expression
at zero is then transferred to the ordinary derivative of H_r.

This module is a revised compilation candidate for Lean 4.36.0-rc2 / Mathlib.
-/

/-- Pointwise identification of the derivative and the explicit expression
on the already-certified neighborhood. -/
theorem normalizedChord_deriv_eq_expression_of_small
    (r t : ℝ) (ht : |t| < 1 / (|r| + 1)) :
    deriv (normalizedChordResidual r) t =
      normalizedChordDerivativeExpression r t := by
  have hd := (normalizedChord_hasDerivAt_on_explicit_neighborhood r t ht).deriv
  rw [hd]
  simp only [normalizedChordDerivativeExpression,
    normalizedChordNumerator, normalizedChordRadicand,
    normalizedChordInner]
  simp only [one_mul, div_eq_mul_inv]
  ring

/-- The first derivative agrees with its explicit analytic expression
throughout a neighborhood of zero. -/
theorem normalizedChord_deriv_eventuallyEq_expression (r : ℝ) :
    (fun t : ℝ => deriv (normalizedChordResidual r) t)
      =ᶠ[nhds (0 : ℝ)] normalizedChordDerivativeExpression r := by
  have hr : 0 < (1 : ℝ) / (|r| + 1) := by positivity
  have hnear : Set.Ioo (-(1 / (|r| + 1))) (1 / (|r| + 1)) ∈ nhds (0 : ℝ) := by
    exact Ioo_mem_nhds (by linarith) hr
  filter_upwards [hnear] with t ht
  exact normalizedChord_deriv_eq_expression_of_small r t (abs_lt.mpr ht)

/-- The ordinary first derivative of H_r itself has derivative zero
at the origin. This is the true second-derivative statement. -/
theorem normalizedChord_deriv_hasDerivAt_zero (r : ℝ) :
    HasDerivAt (fun t : ℝ => deriv (normalizedChordResidual r) t) 0 0 := by
  have hG := normalizedChordDerivativeExpression_hasDerivAt_zero r
  have heq := normalizedChord_deriv_eventuallyEq_expression r
  exact hG.congr_of_eventuallyEq heq

/-- The ordinary second derivative of the normalized residual vanishes. -/
theorem normalizedChord_second_deriv_zero (r : ℝ) :
    deriv (fun t : ℝ => deriv (normalizedChordResidual r) t) 0 = 0 := by
  exact (normalizedChord_deriv_hasDerivAt_zero r).deriv

end BakerTrisection

#check BakerTrisection.normalizedChord_deriv_eq_expression_of_small
#check BakerTrisection.normalizedChord_deriv_eventuallyEq_expression
#check BakerTrisection.normalizedChord_deriv_hasDerivAt_zero
#check BakerTrisection.normalizedChord_second_deriv_zero
#print axioms BakerTrisection.normalizedChord_deriv_hasDerivAt_zero
#print axioms BakerTrisection.normalizedChord_second_deriv_zero
