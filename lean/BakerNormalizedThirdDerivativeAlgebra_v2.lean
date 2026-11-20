import Mathlib
import BakerNormalizedThirdDerivativeReducedCore_v2

namespace BakerTrisection

/-!
# Algebraic bridge for the normalized chord third derivative

The existing verified theorem `normalizedChord_second_deriv_eq_of_small`
provides H_r'' in unsimplified quotient-rule form.  The reduced expression
`normalizedChordReducedSecond` has its own verified derivative at zero.
This module connects them by algebra on the positive-radicand neighborhood.

Compilation candidate: the axiom audit must be checked on the user's Lean
installation before treating this as a completed proof.
-/

/-- An algebraic quotient identity. `z` will be the positive square root of
`1 - (r * x)^2`, while `x` and `y` will be sine and cosine. -/
private theorem reduced_quotient_algebra (r x y z : ℝ)
    (hz : z ≠ 0)
    (hsq : z ^ 2 = 1 - (r * x) ^ 2)
    (hcircle : x ^ 2 + y ^ 2 = 1) :
    ((r * -x * z - (r * y) *
        ((0 - 2 * (r * x) ^ (2 - 1) * (r * y)) / (2 * z))) / z ^ 2)
      = (r * (r ^ 2 - 1) * x) / z ^ 3 := by
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hsq_scaled := congrArg (fun u : ℝ => (2 * r * x) * u) hsq
  have hcircle_scaled := congrArg (fun u : ℝ => (2 * r ^ 3 * x) * u) hcircle
  field_simp
  ring_nf at hsq_scaled hcircle_scaled ⊢
  linarith

/-- On the certified neighborhood, the ordinary second derivative of H_r
agrees with the reduced, differentiable expression. -/
theorem normalizedChord_second_deriv_eq_reduced_of_small (r t : ℝ)
    (ht : |t| < 1 / (|r| + 1)) :
    deriv (fun x : ℝ => deriv (normalizedChordResidual r) x) t =
      normalizedChordReducedSecond r t := by
  rw [normalizedChord_second_deriv_eq_of_small r t ht]
  have hp := normalizedChordRadicand_pos_of_small r t ht
  have hz := normalizedChordSqrtRadicand_ne_zero_of_small r t ht
  have hsq : (Real.sqrt (normalizedChordRadicand r t)) ^ 2 =
      1 - (r * Real.sin t) ^ 2 := by
    rw [Real.sq_sqrt (le_of_lt hp)]
    rfl
  have hcircle : (Real.sin t) ^ 2 + (Real.cos t) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  change
    ((r * -Real.sin t * Real.sqrt (normalizedChordRadicand r t) -
        (r * Real.cos t) *
          ((0 - 2 * (r * Real.sin t) ^ (2 - 1) *
              (r * Real.cos t)) /
            (2 * Real.sqrt (normalizedChordRadicand r t)))) /
        (Real.sqrt (normalizedChordRadicand r t)) ^ 2) =
      (r * (r ^ 2 - 1) * Real.sin t) /
        (Real.sqrt (normalizedChordRadicand r t)) ^ 3
  exact reduced_quotient_algebra r (Real.sin t) (Real.cos t)
    (Real.sqrt (normalizedChordRadicand r t)) hz hsq hcircle

end BakerTrisection

#check BakerTrisection.normalizedChord_second_deriv_eq_reduced_of_small
#print axioms BakerTrisection.normalizedChord_second_deriv_eq_reduced_of_small
