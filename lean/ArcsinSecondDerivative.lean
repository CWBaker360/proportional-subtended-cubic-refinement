import Mathlib
import SecondDerivative

namespace BakerTrisection

/-- The arcsine chord composition is an odd function. -/
theorem arcsin_chord_odd (x : ℝ) :
    Real.arcsin
      ((4 / 3) * Real.sin ((3 / 8) * (-x))) =
    -Real.arcsin
      ((4 / 3) * Real.sin ((3 / 8) * x)) := by
  rw [mul_neg, Real.sin_neg, mul_neg, Real.arcsin_neg]

/-- The second iterated derivative vanishes at zero. -/
theorem arcsin_chord_second_derivative_zero :
    iteratedDeriv 2
      (fun x : ℝ =>
        Real.arcsin
          ((4 / 3) * Real.sin ((3 / 8) * x)))
      0 = 0 := by
  apply odd_second_derivative_zero
  intro x
  exact arcsin_chord_odd x

end BakerTrisection

#check BakerTrisection.arcsin_chord_odd
#check BakerTrisection.arcsin_chord_second_derivative_zero

#print axioms BakerTrisection.arcsin_chord_second_derivative_zero