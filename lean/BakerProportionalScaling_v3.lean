import BakerProportionalResidual_v1

namespace BakerTrisection

/-- The one-parameter normalized arcsine-sine residual. -/
noncomputable def normalizedChordResidual (r t : ℝ) : ℝ :=
  Real.arcsin (r * Real.sin t) - r * t

/-- The normalized residual is zero at the origin. -/
theorem normalizedChordResidual_zero (r : ℝ) :
    normalizedChordResidual r 0 = 0 := by
  simp [normalizedChordResidual]

/-- Normalization eliminates the scale parameter `a` from the
transcendental part of the proportional-chord residual. -/
theorem proportionalChordResidual_normalized
    (a b theta : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    proportionalChordResidual a b theta =
      2 * normalizedChordResidual (a / b) (theta / (2 * a)) := by
  have hlin : 2 * ((a / b) * (theta / (2 * a))) = theta / b := by
    field_simp [ha, hb]
  unfold proportionalChordResidual proportionalChord normalizedChordResidual
  rw [← hlin]
  ring

/-- The predicted cubic coefficient of the normalized residual. -/
noncomputable def normalizedChordCubicCoefficient (r : ℝ) : ℝ :=
  r * (r ^ 2 - 1) / 6

/-- Algebraic compatibility of the normalized cubic coefficient
with the two-parameter coefficient. This does not yet prove the
normalized cubic limit; that is the next analytic obligation. -/
theorem proportionalChordCubicCoefficient_normalized
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    proportionalChordCubicCoefficient a b =
      normalizedChordCubicCoefficient (a / b) / (4 * a ^ 3) := by
  unfold proportionalChordCubicCoefficient normalizedChordCubicCoefficient
  field_simp [ha, hb]
  ring

end BakerTrisection

#check BakerTrisection.normalizedChordResidual_zero
#check BakerTrisection.proportionalChordResidual_normalized
#check BakerTrisection.proportionalChordCubicCoefficient_normalized
#print axioms BakerTrisection.normalizedChordResidual_zero
#print axioms BakerTrisection.proportionalChordResidual_normalized
#print axioms BakerTrisection.proportionalChordCubicCoefficient_normalized
