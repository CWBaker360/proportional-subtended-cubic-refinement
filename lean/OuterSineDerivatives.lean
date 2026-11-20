import Mathlib

namespace BakerTrisection

private theorem sine_derivative :
    deriv Real.sin = Real.cos := by
  funext x
  exact (Real.hasDerivAt_sin x).deriv

private theorem cosine_derivative :
    deriv Real.cos = (fun x : ℝ => -Real.sin x) := by
  funext x
  exact (Real.hasDerivAt_cos x).deriv

private theorem negative_sine_derivative :
    deriv (fun x : ℝ => -Real.sin x) =
      (fun x : ℝ => -Real.cos x) := by
  funext x
  exact (Real.hasDerivAt_sin x).neg.deriv

theorem outer_sine_second :
    iteratedDeriv 2 Real.sin =
      (fun x : ℝ => -Real.sin x) := by
  calc
    iteratedDeriv 2 Real.sin =
        deriv (iteratedDeriv 1 Real.sin) := by
          simpa using
            (iteratedDeriv_succ (n := 1) (f := Real.sin))
    _ = deriv Real.cos := by
          rw [iteratedDeriv_one, sine_derivative]
    _ = (fun x : ℝ => -Real.sin x) :=
          cosine_derivative

theorem outer_sine_third :
    iteratedDeriv 3 Real.sin =
      (fun x : ℝ => -Real.cos x) := by
  calc
    iteratedDeriv 3 Real.sin =
        deriv (iteratedDeriv 2 Real.sin) := by
          simpa using
            (iteratedDeriv_succ (n := 2) (f := Real.sin))
    _ = deriv (fun x : ℝ => -Real.sin x) := by
          rw [outer_sine_second]
    _ = (fun x : ℝ => -Real.cos x) :=
          negative_sine_derivative

theorem outer_sine_third_zero :
    iteratedDeriv 3 Real.sin 0 = -1 := by
  rw [outer_sine_third]
  norm_num

end BakerTrisection

#check BakerTrisection.outer_sine_second
#check BakerTrisection.outer_sine_third_zero

#print axioms BakerTrisection.outer_sine_second
#print axioms BakerTrisection.outer_sine_third_zero