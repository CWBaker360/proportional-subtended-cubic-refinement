import Mathlib
import BakerNormalizedLocalDomain_v1

namespace BakerTrisection

/-!
# General normalized chord: second-derivative preparation

The numerator and radicand in the explicit formula for H_r' both
have zero derivative at the origin. These are actual ordinary
first-derivative statements, not just symmetric-difference identities.

No new second-derivative or cubic-limit theorem is claimed here.
-/

/-- The linear-sine inner expression of the normalized chord. -/
noncomputable def normalizedChordInner (r t : ℝ) : ℝ := r * Real.sin t

/-- Radicand in the derivative of the normalized chord. -/
noncomputable def normalizedChordRadicand (r t : ℝ) : ℝ :=
  1 - (normalizedChordInner r t) ^ 2

/-- Cosine numerator in the derivative of the normalized chord. -/
noncomputable def normalizedChordNumerator (r t : ℝ) : ℝ :=
  r * Real.cos t

/-- The inner sine has derivative `r` at zero. -/
theorem normalizedChordInner_hasDerivAt_zero (r : ℝ) :
    HasDerivAt (normalizedChordInner r) r 0 := by
  change HasDerivAt (fun t : ℝ => r * Real.sin t) r 0
  simpa using (Real.hasDerivAt_sin (0 : ℝ)).const_mul r

/-- The radicand is stationary at the origin. -/
theorem normalizedChordRadicand_hasDerivAt_zero (r : ℝ) :
    HasDerivAt (normalizedChordRadicand r) 0 0 := by
  have hi := normalizedChordInner_hasDerivAt_zero r
  have hs := hi.pow 2
  have hr := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hs
  convert hr using 1
  · funext t
    rfl
  · simp [normalizedChordInner] 

/-- The cosine numerator is stationary at the origin. -/
theorem normalizedChordNumerator_hasDerivAt_zero (r : ℝ) :
    HasDerivAt (normalizedChordNumerator r) 0 0 := by
  have hc := (Real.hasDerivAt_cos (0 : ℝ)).const_mul r
  convert hc using 1
  · funext t
    simp only [normalizedChordNumerator]
  · simp

end BakerTrisection

#check BakerTrisection.normalizedChordInner_hasDerivAt_zero
#check BakerTrisection.normalizedChordRadicand_hasDerivAt_zero
#check BakerTrisection.normalizedChordNumerator_hasDerivAt_zero
#print axioms BakerTrisection.normalizedChordInner_hasDerivAt_zero
#print axioms BakerTrisection.normalizedChordRadicand_hasDerivAt_zero
#print axioms BakerTrisection.normalizedChordNumerator_hasDerivAt_zero
