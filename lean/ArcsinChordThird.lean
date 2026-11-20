import Mathlib
import SecondDerivative
import InnerDerivativeChain
import InnerIteratedDerivatives
import OuterArcsinBasics
import OuterArcsinThird
import ThirdOrderComposition

namespace BakerTrisection

/--
The third iterated derivative of the Baker
4:3 arcsine chord composition at zero.
-/
theorem arcsin_chord_third_zero :
    iteratedDeriv 3
      (fun x : ℝ =>
        Real.arcsin
          ((4 / 3) * Real.sin ((3 / 8) * x)))
      0 = 7 / 128 := by

  let u : ℝ → ℝ :=
    fun x => (4 / 3) * Real.sin ((3 / 8) * x)

  have hu : ContDiffAt ℝ 3 u 0 := by
    dsimp [u]
    fun_prop

  have hu0 : u 0 = 0 := by
    simp [u]

  have hu1 : deriv u 0 = 1 / 2 := by
    dsimp [u]
    simpa using chord_inner_deriv 0

  have hu2 : iteratedDeriv 2 u 0 = 0 := by
    apply odd_second_derivative_zero
    intro x
    change
      (4 / 3 : ℝ) * Real.sin ((3 / 8) * (-x)) =
        -((4 / 3 : ℝ) * Real.sin ((3 / 8) * x))
    rw [mul_neg, Real.sin_neg, mul_neg]
  have hu3 : iteratedDeriv 3 u 0 = -(9 / 128) := by
    change
      iteratedDeriv 3
        (fun x : ℝ =>
          (4 / 3) * Real.sin ((3 / 8) * x))
        0 = -(9 / 128)
    exact inner_third_iterated_zero

  have hc :=
    third_order_composition_at_zero
      u Real.arcsin
      hu outer_arcsin_smooth_three
      hu0 hu1 hu2 hu3
      outer_arcsin_first_zero
      outer_arcsin_second_zero
      outer_arcsin_third_zero

  simpa only [Function.comp_def, u] using hc

end BakerTrisection

#check BakerTrisection.arcsin_chord_third_zero
#print axioms BakerTrisection.arcsin_chord_third_zero