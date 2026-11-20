import Mathlib
import ResidualTaylorRemainder
import ResidualTaylorPolynomial

namespace BakerTrisection

/--
The Baker 4:3 residual has cubic coefficient -7/384.
The limit is taken through nonzero real inputs.
-/
theorem cubicResidual_cubic_limit :
    Filter.Tendsto
      (fun x : ℝ => cubicResidual x / x ^ 3)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (-(7 / 384 : ℝ))) := by

  obtain ⟨ε, hε, hbase⟩ :=
    cubicResidual_taylor_remainder

  have hnear :
      Set.Ioo (-ε) ε ∈ nhds (0 : ℝ) := by
    apply Ioo_mem_nhds
    all_goals linarith

  rw [(nhdsWithin_eq_nhds).2 hnear] at hbase

  have hrem :
      Filter.Tendsto
        (fun x : ℝ =>
          (cubicResidual x -
            (-(7 / 384 : ℝ)) * x ^ 3) / x ^ 3)
        (nhds (0 : ℝ))
        (nhds (0 : ℝ)) := by
    simpa only
      [cubicResidual_taylor_polynomial ε hε]
      using hbase

  have hremP :
      Filter.Tendsto
        (fun x : ℝ =>
          (cubicResidual x -
            (-(7 / 384 : ℝ)) * x ^ 3) / x ^ 3)
        (nhdsWithin (0 : ℝ) ({0}ᶜ))
        (nhds (0 : ℝ)) :=
    hrem.mono_left nhdsWithin_le_nhds

  have hconst :
      Filter.Tendsto
        (fun _ : ℝ => (-(7 / 384 : ℝ)))
        (nhdsWithin (0 : ℝ) ({0}ᶜ))
        (nhds (-(7 / 384 : ℝ))) :=
    tendsto_const_nhds

  have hsum :
      Filter.Tendsto
        (fun x : ℝ =>
          (cubicResidual x -
            (-(7 / 384 : ℝ)) * x ^ 3) / x ^ 3
            + (-(7 / 384 : ℝ)))
        (nhdsWithin (0 : ℝ) ({0}ᶜ))
        (nhds (-(7 / 384 : ℝ))) := by
    simpa using hremP.add hconst

  have heq :
      (fun x : ℝ =>
        (cubicResidual x -
          (-(7 / 384 : ℝ)) * x ^ 3) / x ^ 3
          + (-(7 / 384 : ℝ)))
        =ᶠ[nhdsWithin (0 : ℝ) ({0}ᶜ)]
      (fun x : ℝ => cubicResidual x / x ^ 3) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff,
        Set.mem_singleton_iff] using hx
    field_simp [hx0]
    ring

  exact hsum.congr' heq

/-- Explicit public form of the cubic residual limit. -/
theorem baker_four_thirds_cubic_limit :
    Filter.Tendsto
      (fun x : ℝ =>
        (x - 2 * Real.arcsin
          ((4 / 3) * Real.sin ((3 / 8) * x))) / x ^ 3)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (-(7 / 384 : ℝ))) := by
  simpa only [cubicResidual] using
    cubicResidual_cubic_limit

end BakerTrisection

#check BakerTrisection.cubicResidual_cubic_limit
#check BakerTrisection.baker_four_thirds_cubic_limit

#print axioms BakerTrisection.cubicResidual_cubic_limit
#print axioms BakerTrisection.baker_four_thirds_cubic_limit