import Mathlib
import BakerNormalizedThirdDerivativeAlgebra_v2

namespace BakerTrisection

/-!
# General normalized chord: ordinary third derivative at zero

The algebraic bridge identifies the ordinary second derivative of
  H_r(t) = arcsin (r sin t) - r t
with the reduced expression S_r throughout an explicit open neighborhood.
The reduced expression has a verified derivative at zero. This module
transfers that derivative to the ordinary second-derivative function.

Compilation candidate: check the user's Lean 4 / Mathlib compile and axiom audit.
-/

/-- The ordinary second derivative agrees locally with the reduced expression. -/
theorem normalizedChord_second_deriv_eventuallyEq_reduced (r : ℝ) :
    (fun t : ℝ => deriv (fun x : ℝ => deriv (normalizedChordResidual r) x) t)
      =ᶠ[nhds (0 : ℝ)] normalizedChordReducedSecond r := by
  have hr : 0 < (1 : ℝ) / (|r| + 1) := by positivity
  have hnear :
      Set.Ioo (-(1 / (|r| + 1))) (1 / (|r| + 1)) ∈ nhds (0 : ℝ) := by
    exact Ioo_mem_nhds (by linarith) hr
  filter_upwards [hnear] with t ht
  exact normalizedChord_second_deriv_eq_reduced_of_small r t (abs_lt.mpr ht)

/-- The ordinary second-derivative function has the predicted derivative
at zero for any real ratio r. -/
theorem normalizedChord_second_deriv_hasDerivAt_zero (r : ℝ) :
    HasDerivAt
      (fun t : ℝ => deriv (fun x : ℝ => deriv (normalizedChordResidual r) x) t)
      (r * (r ^ 2 - 1)) 0 := by
  have hS := normalizedChordReducedSecond_hasDerivAt_zero r
  have heq := normalizedChord_second_deriv_eventuallyEq_reduced r
  exact hS.congr_of_eventuallyEq heq

/-- The genuine ordinary third derivative at the origin. -/
theorem normalizedChord_third_deriv_zero (r : ℝ) :
    deriv (fun t : ℝ =>
      deriv (fun x : ℝ => deriv (normalizedChordResidual r) x) t) 0 =
      r * (r ^ 2 - 1) := by
  exact (normalizedChord_second_deriv_hasDerivAt_zero r).deriv

end BakerTrisection

#check BakerTrisection.normalizedChord_second_deriv_eventuallyEq_reduced
#check BakerTrisection.normalizedChord_second_deriv_hasDerivAt_zero
#check BakerTrisection.normalizedChord_third_deriv_zero
#print axioms BakerTrisection.normalizedChord_second_deriv_eventuallyEq_reduced
#print axioms BakerTrisection.normalizedChord_second_deriv_hasDerivAt_zero
#print axioms BakerTrisection.normalizedChord_third_deriv_zero
