import Mathlib
import BakerCubicLimit

namespace BakerTrisection

/-- Scaling by 1/3 preserves the punctured neighborhood of zero. -/
private theorem tendsto_third_punctured :
    Filter.Tendsto (fun x : ℝ => x / 3)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : Filter.Tendsto (fun x : ℝ => x / 3)
        (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
      convert (continuousAt_id.div_const (3 : ℝ)).tendsto using 1 <;> norm_num
    exact hc.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact div_ne_zero hx0 (by norm_num)

/-- The direct Baker 4:3 seed overshoots the exact third by
    the positive leading coefficient 7/10368. -/
theorem direct_seed_cubic_limit :
    Filter.Tendsto
      (fun θ : ℝ =>
        (2 * Real.arcsin ((4 / 3) * Real.sin (θ / 8)) - θ / 3) / θ ^ 3)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (7 / 10368 : ℝ)) := by
  have hscaled := baker_four_thirds_cubic_limit.comp tendsto_third_punctured
  have hmul :
      Filter.Tendsto
        (fun θ : ℝ =>
          (-(1 / 27 : ℝ)) *
            (((θ / 3) - 2 * Real.arcsin
              ((4 / 3) * Real.sin ((3 / 8) * (θ / 3)))) / (θ / 3) ^ 3))
        (nhdsWithin (0 : ℝ) ({0}ᶜ))
        (nhds ((-(1 / 27 : ℝ)) * (-(7 / 384 : ℝ)))) := by
    simpa only [Function.comp_def] using hscaled.const_mul (-(1 / 27 : ℝ))
  have heq :
      (fun θ : ℝ =>
        (-(1 / 27 : ℝ)) *
          (((θ / 3) - 2 * Real.arcsin
            ((4 / 3) * Real.sin ((3 / 8) * (θ / 3)))) / (θ / 3) ^ 3))
        =ᶠ[nhdsWithin (0 : ℝ) ({0}ᶜ)]
      (fun θ : ℝ =>
        (2 * Real.arcsin ((4 / 3) * Real.sin (θ / 8)) - θ / 3) / θ ^ 3) := by
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    have hθ0 : θ ≠ 0 := by simpa using hθ
    have harg : (3 / 8 : ℝ) * (θ / 3) = θ / 8 := by ring
    rw [harg]
    field_simp [hθ0]
    ring
  have hresult := hmul.congr' heq
  convert hresult using 1 <;> norm_num

end BakerTrisection

#check BakerTrisection.direct_seed_cubic_limit
#print axioms BakerTrisection.direct_seed_cubic_limit
