import Mathlib
import ArcsinComposition
import ArcsinSecondDerivative
import SecondDerivative
import ResidualThirdDerivative

namespace BakerTrisection

/-- Explicit Baker 4:3 residual. -/
noncomputable def cubicResidual (x : ℝ) : ℝ :=
  x - 2 * Real.arcsin
    ((4 / 3) * Real.sin ((3 / 8) * x))

theorem cubicResidual_zero :
    cubicResidual 0 = 0 := by
  simp [cubicResidual]

theorem cubicResidual_first_zero :
    deriv cubicResidual 0 = 0 := by
  have ha := arcsin_chord_hasDerivAt_zero
  have h :=
    (hasDerivAt_id (0 : ℝ)).sub
      (ha.const_mul (2 : ℝ))
  have hfun :
      cubicResidual =
        (id : ℝ → ℝ) -
          (fun y : ℝ =>
            2 * Real.arcsin
              ((4 / 3) * Real.sin ((3 / 8) * y))) := by
    funext x
    rfl

  have hh : HasDerivAt cubicResidual 0 0 := by
    rw [hfun]
    convert h using 1 <;> norm_num

  exact hh.deriv

theorem cubicResidual_second_zero :
    iteratedDeriv 2 cubicResidual 0 = 0 := by
  apply odd_second_derivative_zero
  intro x
  dsimp [cubicResidual]
  rw [mul_neg, Real.sin_neg, mul_neg, Real.arcsin_neg]
  ring

theorem cubicResidual_third_zero :
    iteratedDeriv 3 cubicResidual 0 = -(7 / 64) := by
  change
    iteratedDeriv 3
      (fun x : ℝ =>
        x - 2 * Real.arcsin
          ((4 / 3) * Real.sin ((3 / 8) * x)))
      0 = -(7 / 64)
  exact residual_third_explicit

end BakerTrisection

#check BakerTrisection.cubicResidual_zero
#check BakerTrisection.cubicResidual_first_zero
#check BakerTrisection.cubicResidual_second_zero
#check BakerTrisection.cubicResidual_third_zero

#print axioms BakerTrisection.cubicResidual_first_zero
#print axioms BakerTrisection.cubicResidual_second_zero
#print axioms BakerTrisection.cubicResidual_third_zero