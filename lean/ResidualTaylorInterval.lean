import Mathlib
import ResidualLocalSmooth

namespace BakerTrisection

/--
There exists a positive radius on which the
Baker 4:3 residual is C³.
-/
theorem cubicResidual_smooth_interval :
    ∃ ε : ℝ, 0 < ε ∧
      ContDiffOn ℝ 3 cubicResidual (Set.Ioo (-ε) ε) := by

  have heventually :
      ∀ᶠ x : ℝ in nhds (0 : ℝ),
        ContDiffAt ℝ 3 cubicResidual x :=
    cubicResidual_smooth_three.eventually (by norm_num)

  obtain ⟨ε, hε, hnear⟩ :=
    (Metric.eventually_nhds_iff).mp heventually

  refine ⟨ε, hε, ?_⟩

  intro x hx

  apply ContDiffAt.contDiffWithinAt

  apply hnear

  have habs : |x| < ε := by
    exact abs_lt.mpr hx

  simpa [Real.dist_eq] using habs

end BakerTrisection

#check BakerTrisection.cubicResidual_smooth_interval
#print axioms BakerTrisection.cubicResidual_smooth_interval