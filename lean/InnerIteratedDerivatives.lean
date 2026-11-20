import Mathlib
import InnerDerivativeChain
import InnerThirdDerivative

namespace BakerTrisection

private noncomputable def inner (x : ℝ) : ℝ :=
  (4 / 3) * Real.sin ((3 / 8) * x)

/-- The second iterated derivative at every real x. -/
theorem inner_second_iterated (x : ℝ) :
    iteratedDeriv 2 inner x =
      -(3 / 16) * Real.sin ((3 / 8) * x) := by

  have hfirst :
      deriv inner =
        (fun y : ℝ =>
          (1 / 2) * Real.cos ((3 / 8) * y)) := by
    funext y
    exact chord_inner_deriv y

  have hstep :
      iteratedDeriv 2 inner = deriv (deriv inner) := by
    simpa only [iteratedDeriv_one] using
      (iteratedDeriv_succ (n := 1) (f := inner))

  rw [hstep, hfirst]
  exact (chord_inner_first_expression_hasDerivAt x).deriv

/-- The third iterated derivative at zero. -/
theorem inner_third_iterated_zero :
    iteratedDeriv 3 inner 0 = -(9 / 128) := by

  have hsecond :
      iteratedDeriv 2 inner =
        (fun x : ℝ =>
          -(3 / 16) * Real.sin ((3 / 8) * x)) := by
    funext x
    exact inner_second_iterated x

  have hstep :
      iteratedDeriv 3 inner =
        deriv (iteratedDeriv 2 inner) := by
    simpa using
      (iteratedDeriv_succ (n := 2) (f := inner))

  rw [hstep, hsecond]
  simpa only [neg_div] using
    chord_inner_second_expression_derivative.deriv

end BakerTrisection

#check BakerTrisection.inner_second_iterated
#check BakerTrisection.inner_third_iterated_zero

#print axioms BakerTrisection.inner_second_iterated
#print axioms BakerTrisection.inner_third_iterated_zero