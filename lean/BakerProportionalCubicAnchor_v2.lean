import Mathlib
import BakerProportionalChord_v2
import TrisectionSeedLimit

namespace BakerTrisection

/-- Candidate cubic coefficient for the proportional-chord family.
This is a definition, not yet a proof of the general asymptotic expansion. -/
noncomputable def proportionalChordCubicCoefficient (a b : ℝ) : ℝ :=
  (a ^ 2 - b ^ 2) / (24 * a ^ 2 * b ^ 3)

/-- The proposed coefficient agrees with the certified 4:3 seed. -/
theorem proportionalChordCubicCoefficient_four_three :
    proportionalChordCubicCoefficient 4 3 = (7 / 10368 : ℝ) := by
  norm_num [proportionalChordCubicCoefficient]

/-- Equal chord parameters give zero cubic coefficient. -/
theorem proportionalChordCubicCoefficient_equal (a : ℝ) :
    proportionalChordCubicCoefficient a a = 0 := by
  simp [proportionalChordCubicCoefficient]

/-- Transfer the already-certified 4:3 cubic seed limit into
   the new proportional-chord notation. -/
theorem proportionalChord_four_three_cubic_limit :
    Filter.Tendsto
      (fun θ : ℝ => (proportionalChord 4 3 θ - θ / 3) / θ ^ 3)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (proportionalChordCubicCoefficient 4 3)) := by
  rw [proportionalChordCubicCoefficient_four_three]
  simpa only [proportionalChord_four_three] using
    direct_seed_cubic_limit

end BakerTrisection

#check BakerTrisection.proportionalChordCubicCoefficient_four_three
#check BakerTrisection.proportionalChordCubicCoefficient_equal
#check BakerTrisection.proportionalChord_four_three_cubic_limit

#print axioms BakerTrisection.proportionalChordCubicCoefficient_four_three
#print axioms BakerTrisection.proportionalChordCubicCoefficient_equal
#print axioms BakerTrisection.proportionalChord_four_three_cubic_limit
