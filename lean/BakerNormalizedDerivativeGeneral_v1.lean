import Mathlib
import BakerNormalizedFirstDerivative_v3

namespace BakerTrisection

/-!
# General derivative of the normalized proportional-chord residual

This is an intermediate analytic module for the arbitrary-r cubic-limit proof.
It establishes the exact first derivative wherever the arcsine input lies in
(-1, 1). In particular, it does not assume `r` itself lies in (-1, 1).

Compilation candidate for Lean 4.36.0-rc2 / Mathlib; not yet locally checked.
-/

/-- The normalized residual is differentiable at every point where the
arcsine input lies strictly between -1 and 1. -/
theorem normalizedChordResidual_hasDerivAt_of_abs_lt_one
    (r t : ℝ) (ht : |r * Real.sin t| < 1) :
    HasDerivAt (normalizedChordResidual r)
      ((1 / Real.sqrt (1 - (r * Real.sin t) ^ 2)) *
        (r * Real.cos t) - r) t := by
  have hbounds := abs_lt.mp ht
  have hne_neg : r * Real.sin t ≠ -1 := by
    intro he
    rw [he] at hbounds
    norm_num at hbounds
  have hne_pos : r * Real.sin t ≠ 1 := by
    intro he
    rw [he] at hbounds
    norm_num at hbounds
  have hsin :
      HasDerivAt (fun x : ℝ => r * Real.sin x)
        (r * Real.cos t) t := by
    simpa using (Real.hasDerivAt_sin t).const_mul r
  have harcsin :=
    (Real.hasDerivAt_arcsin hne_neg hne_pos).comp t hsin
  have hlinear :
      HasDerivAt (fun x : ℝ => r * x) r t := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id t).const_mul r
  have hsub := harcsin.sub hlinear
  convert hsub using 1
  · funext x
    simp only [normalizedChordResidual, Function.comp_apply, Pi.sub_apply, id_eq]

/-- Ordinary derivative formula, under the same strict-domain condition. -/
theorem normalizedChordResidual_deriv_of_abs_lt_one
    (r t : ℝ) (ht : |r * Real.sin t| < 1) :
    deriv (normalizedChordResidual r) t =
      (1 / Real.sqrt (1 - (r * Real.sin t) ^ 2)) *
        (r * Real.cos t) - r := by
  exact (normalizedChordResidual_hasDerivAt_of_abs_lt_one r t ht).deriv

end BakerTrisection

#check BakerTrisection.normalizedChordResidual_hasDerivAt_of_abs_lt_one
#check BakerTrisection.normalizedChordResidual_deriv_of_abs_lt_one
#print axioms BakerTrisection.normalizedChordResidual_hasDerivAt_of_abs_lt_one
#print axioms BakerTrisection.normalizedChordResidual_deriv_of_abs_lt_one
