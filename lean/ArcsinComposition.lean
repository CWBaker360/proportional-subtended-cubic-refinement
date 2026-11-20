import Mathlib
import InnerDerivativeChain

namespace BakerTrisection

/-- First derivative of the arcsine chord composition at zero. -/
theorem arcsin_chord_hasDerivAt_zero :
    HasDerivAt
      (fun x : ℝ =>
        Real.arcsin
          ((4 / 3) * Real.sin ((3 / 8) * x)))
      (1 / 2) 0 := by

  have hi :
      HasDerivAt
        (fun x : ℝ =>
          (4 / 3) * Real.sin ((3 / 8) * x))
        (1 / 2) 0 := by
    simpa using chord_inner_hasDerivAt 0

  have ha :
      HasDerivAt Real.arcsin 1
        ((4 / 3 : ℝ) * Real.sin ((3 / 8 : ℝ) * 0)) := by
    simpa using
      (Real.hasDerivAt_arcsin
        (x := (0 : ℝ))
        (by norm_num) (by norm_num))

  have hc := ha.comp 0 hi
  simpa only [Function.comp_def, one_mul] using hc

/-- The ordinary first derivative of the composition. -/
theorem arcsin_chord_deriv_zero :
    deriv
      (fun x : ℝ =>
        Real.arcsin
          ((4 / 3) * Real.sin ((3 / 8) * x)))
      0 = 1 / 2 := by
  exact arcsin_chord_hasDerivAt_zero.deriv

end BakerTrisection

#check BakerTrisection.arcsin_chord_hasDerivAt_zero
#check BakerTrisection.arcsin_chord_deriv_zero

#print axioms BakerTrisection.arcsin_chord_deriv_zero