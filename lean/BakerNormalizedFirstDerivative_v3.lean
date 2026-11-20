import Mathlib
import BakerNormalizedChordBasics_v1

namespace BakerTrisection

/-!
# First derivative of the normalized chord residual

The linear term in `arcsin (r * sin t) - r * t` vanishes for every real `r`.
This does not assert the generalized cubic limit.
-/

/-- The normalized chord residual has derivative zero at the origin. -/
theorem normalizedChordResidual_hasDerivAt_zero (r : ℝ) :
    HasDerivAt (normalizedChordResidual r) 0 0 := by
  have hsin : HasDerivAt (fun t : ℝ => r * Real.sin t) r 0 := by
    simpa using (Real.hasDerivAt_sin (0 : ℝ)).const_mul r
  have hne_neg : (0 : ℝ) ≠ -1 := by norm_num
  have hne_pos : (0 : ℝ) ≠ 1 := by norm_num
  have harcsinAt :
      HasDerivAt Real.arcsin 1 (r * Real.sin (0 : ℝ)) := by
    simpa using (Real.hasDerivAt_arcsin hne_neg hne_pos)
  have harcsin := harcsinAt.comp 0 hsin
  have hlinear : HasDerivAt (fun t : ℝ => r * t) r 0 := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id (0 : ℝ)).const_mul r
  have hsub := harcsin.sub hlinear
  convert hsub using 1
  · funext t
    simp only [normalizedChordResidual, Function.comp_apply, Pi.sub_apply, id_eq]
  · norm_num <;> ring

/-- The ordinary derivative also vanishes at the origin. -/
theorem normalizedChordResidual_deriv_zero (r : ℝ) :
    deriv (normalizedChordResidual r) 0 = 0 :=
  (normalizedChordResidual_hasDerivAt_zero r).deriv

end BakerTrisection

#check BakerTrisection.normalizedChordResidual_hasDerivAt_zero
#check BakerTrisection.normalizedChordResidual_deriv_zero
#print axioms BakerTrisection.normalizedChordResidual_hasDerivAt_zero
#print axioms BakerTrisection.normalizedChordResidual_deriv_zero
