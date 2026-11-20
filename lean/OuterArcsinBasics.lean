import Mathlib
import SecondDerivative

namespace BakerTrisection

/-- Arcsine is three-times continuously differentiable at zero. -/
theorem outer_arcsin_smooth_three :
    ContDiffAt ℝ 3 Real.arcsin 0 := by
  exact Real.contDiffAt_arcsin
    (by norm_num) (by norm_num)

/-- The first derivative of arcsine at zero is one. -/
theorem outer_arcsin_first_zero :
    deriv Real.arcsin 0 = 1 := by
  have h :=
    Real.hasDerivAt_arcsin
      (x := (0 : ℝ))
      (by norm_num) (by norm_num)
  simpa using h.deriv

/-- The second iterated derivative of arcsine vanishes at zero. -/
theorem outer_arcsin_second_zero :
    iteratedDeriv 2 Real.arcsin 0 = 0 := by
  apply odd_second_derivative_zero
  intro x
  exact Real.arcsin_neg x

end BakerTrisection

#check BakerTrisection.outer_arcsin_smooth_three
#check BakerTrisection.outer_arcsin_first_zero
#check BakerTrisection.outer_arcsin_second_zero

#print axioms BakerTrisection.outer_arcsin_smooth_three
#print axioms BakerTrisection.outer_arcsin_first_zero
#print axioms BakerTrisection.outer_arcsin_second_zero