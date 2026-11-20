import BakerProportionalCubicAnchor_v2

namespace BakerTrisection

/-- Error of the proportional-chord approximation relative to `theta / b`. -/
noncomputable def proportionalChordResidual (a b theta : ℝ) : ℝ :=
  proportionalChord a b theta - theta / b

/-- The generalized residual vanishes at the origin. -/
theorem proportionalChordResidual_zero (a b : ℝ) :
    proportionalChordResidual a b 0 = 0 := by
  simp [proportionalChordResidual, proportionalChord_zero]

/-- The generalized residual is odd in the input angle. -/
theorem proportionalChordResidual_neg (a b theta : ℝ) :
    proportionalChordResidual a b (-theta) =
      -proportionalChordResidual a b theta := by
  simp only [proportionalChordResidual, proportionalChord_neg, neg_div]
  ring

/-- The proposed cubic coefficient has the expected factored numerator. -/
theorem proportionalChordCubicCoefficient_factored (a b : ℝ) :
    proportionalChordCubicCoefficient a b =
      ((a - b) * (a + b)) / (24 * a ^ 2 * b ^ 3) := by
  unfold proportionalChordCubicCoefficient
  congr 1
  ring

/-- The original 4:3 residual is an instance of the generalized residual. -/
theorem proportionalChordResidual_four_three (theta : ℝ) :
    proportionalChordResidual 4 3 theta =
      2 * Real.arcsin ((4 / 3) * Real.sin (theta / 8)) - theta / 3 := by
  simp only [proportionalChordResidual, proportionalChord_four_three]

/-- Certified cubic limit for the 4:3 member in generalized residual notation. -/
theorem proportionalChordResidual_four_three_cubic_limit :
    Filter.Tendsto
      (fun theta : ℝ => proportionalChordResidual 4 3 theta / theta ^ 3)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (proportionalChordCubicCoefficient 4 3)) := by
  simpa only [proportionalChordResidual] using
    proportionalChord_four_three_cubic_limit

end BakerTrisection

#check BakerTrisection.proportionalChordResidual_zero
#check BakerTrisection.proportionalChordResidual_neg
#check BakerTrisection.proportionalChordCubicCoefficient_factored
#check BakerTrisection.proportionalChordResidual_four_three_cubic_limit
#print axioms BakerTrisection.proportionalChordResidual_zero
#print axioms BakerTrisection.proportionalChordResidual_neg
#print axioms BakerTrisection.proportionalChordCubicCoefficient_factored
#print axioms BakerTrisection.proportionalChordResidual_four_three_cubic_limit
