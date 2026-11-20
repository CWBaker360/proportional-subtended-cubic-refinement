import Mathlib
import ResidualTaylorInterval

namespace BakerTrisection

/--
The normalized third-order Taylor remainder tends
to zero on a neighborhood of the origin.
-/
theorem cubicResidual_taylor_remainder :
    ∃ ε : ℝ, 0 < ε ∧
      Filter.Tendsto
        (fun x : ℝ =>
          (cubicResidual x -
            taylorWithinEval cubicResidual 3
              (Set.Ioo (-ε) ε) 0 x) / x ^ 3)
        (nhdsWithin (0 : ℝ) (Set.Ioo (-ε) ε))
        (nhds (0 : ℝ)) := by

  obtain ⟨ε, hε, hsmooth⟩ :=
    cubicResidual_smooth_interval

  have hzero :
      (0 : ℝ) ∈ Set.Ioo (-ε) ε := by
    constructor <;> linarith

  have hconvex :
      Convex ℝ (Set.Ioo (-ε) ε) :=
    convex_Ioo (-ε) ε

  refine ⟨ε, hε, ?_⟩

  simpa only [sub_zero] using
    (Real.taylor_tendsto hconvex hzero hsmooth)

end BakerTrisection

#check BakerTrisection.cubicResidual_taylor_remainder
#print axioms BakerTrisection.cubicResidual_taylor_remainder