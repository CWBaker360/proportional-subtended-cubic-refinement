import Mathlib
import BakerResidual

namespace BakerTrisection

/-- The second iterated derivative of an odd real function
    vanishes at the origin. -/
theorem odd_second_derivative_zero
    (f : ℝ → ℝ)
    (hodd : ∀ x, f (-x) = -f x) :
    iteratedDeriv 2 f 0 = 0 := by

  have hfun :
      (fun x : ℝ => f (-x)) =
      (fun x : ℝ => -f x) := by
    funext x
    exact hodd x

  have hderiv := congrArg
    (fun g : ℝ → ℝ => iteratedDeriv 2 g 0) hfun

  rw [iteratedDeriv_comp_neg,
      iteratedDeriv_fun_neg] at hderiv

  norm_num at hderiv
  linarith

/-- The second derivative of the Baker 4:3 residual
    vanishes at the origin. -/
theorem bakerResidual_second_derivative_zero :
    iteratedDeriv 2
      (fun x : ℝ => bakerResidual (4 / 3) x)
      0 = 0 := by

  apply odd_second_derivative_zero
  intro x
  unfold bakerResidual
  rw [neg_div, Real.sin_neg, mul_neg, Real.arcsin_neg]
  ring


end BakerTrisection

#check BakerTrisection.odd_second_derivative_zero
#check BakerTrisection.bakerResidual_second_derivative_zero

#print axioms BakerTrisection.bakerResidual_second_derivative_zero