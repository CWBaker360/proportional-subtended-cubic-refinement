import Mathlib

namespace BakerTrisection

/-!
# General proportional-chord seed: first structural lemmas

This is a new, standalone generalization module. It does not yet establish
Taylor coefficients, a valid inverse-sine domain, or convergence.
-/

/-- The real-valued proportional-chord seed for parameters `a` and `b`. -/
noncomputable def proportionalChord (a b θ : ℝ) : ℝ :=
  2 * Real.arcsin ((a / b) * Real.sin (θ / (2 * a)))

/-- Every proportional-chord seed takes zero to zero. -/
theorem proportionalChord_zero (a b : ℝ) :
    proportionalChord a b 0 = 0 := by
  simp [proportionalChord]

/-- The proportional-chord seed is odd in the angle. -/
theorem proportionalChord_neg (a b θ : ℝ) :
    proportionalChord a b (-θ) = -proportionalChord a b θ := by
  simp only [proportionalChord, neg_div, Real.sin_neg, mul_neg, Real.arcsin_neg]

/-- The Baker 4:3 seed is the `(a,b) = (4,3)` specialization. -/
theorem proportionalChord_four_three (θ : ℝ) :
    proportionalChord 4 3 θ =
      2 * Real.arcsin ((4 / 3) * Real.sin (θ / 8)) := by
  norm_num [proportionalChord]

#check BakerTrisection.proportionalChord_zero
#check BakerTrisection.proportionalChord_neg
#check BakerTrisection.proportionalChord_four_three

#print axioms BakerTrisection.proportionalChord_zero
#print axioms BakerTrisection.proportionalChord_neg
#print axioms BakerTrisection.proportionalChord_four_three

end BakerTrisection
