import Mathlib
import BakerNormalizedSecondDerivativeBridge_v2

namespace BakerTrisection

/-!
# Normalized chord: preparation for the third derivative

Establish pointwise first-derivative formulas for the inner sine,
cosine numerator and radicand. The earlier second-order module
certified only their derivatives at zero; these general-point identities
are needed for a derivative formula for H_r'' near zero.

This is a revised compilation candidate, not a verified third-derivative theorem.
-/

/-- The normalized inner sine is differentiable at every real point. -/
theorem normalizedChordInner_hasDerivAt (r t : ℝ) :
    HasDerivAt (normalizedChordInner r) (r * Real.cos t) t := by
  change HasDerivAt (fun x : ℝ => r * Real.sin x) (r * Real.cos t) t
  exact (Real.hasDerivAt_sin t).const_mul r

/-- The cosine numerator is differentiable at every real point. -/
theorem normalizedChordNumerator_hasDerivAt (r t : ℝ) :
    HasDerivAt (normalizedChordNumerator r) (r * -Real.sin t) t := by
  change HasDerivAt (fun x : ℝ => r * Real.cos x) (r * -Real.sin t) t
  exact (Real.hasDerivAt_cos t).const_mul r

/-- The radicand is differentiable at every real point, with a
chain-rule expression retaining the inner sine notation. -/
theorem normalizedChordRadicand_hasDerivAt (r t : ℝ) :
    HasDerivAt (normalizedChordRadicand r)
      (0 - (2 * normalizedChordInner r t ^ (2 - 1) * (r * Real.cos t))) t := by
  have hi := normalizedChordInner_hasDerivAt r t
  have hs := hi.pow 2
  have hr := (hasDerivAt_const t (1 : ℝ)).sub hs
  change HasDerivAt
    (fun x : ℝ => (1 : ℝ) - (normalizedChordInner r x) ^ 2)
    (0 - (2 * normalizedChordInner r t ^ (2 - 1) * (r * Real.cos t))) t
  convert hr using 1 <;> rfl

end BakerTrisection

#check BakerTrisection.normalizedChordInner_hasDerivAt
#check BakerTrisection.normalizedChordNumerator_hasDerivAt
#check BakerTrisection.normalizedChordRadicand_hasDerivAt
#print axioms BakerTrisection.normalizedChordInner_hasDerivAt
#print axioms BakerTrisection.normalizedChordNumerator_hasDerivAt
#print axioms BakerTrisection.normalizedChordRadicand_hasDerivAt
