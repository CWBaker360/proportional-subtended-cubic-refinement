import Mathlib

namespace BakerTrisection

/--
Third-order composition theorem with exact
derivative data for the Baker 4:3 construction.
-/
theorem third_order_composition_at_zero
    (u g : ℝ → ℝ)
    (hu : ContDiffAt ℝ 3 u 0)
    (hg : ContDiffAt ℝ 3 g 0)
    (hu0 : u 0 = 0)
    (hu1 : deriv u 0 = 1 / 2)
    (hu2 : iteratedDeriv 2 u 0 = 0)
    (hu3 : iteratedDeriv 3 u 0 = -(9 / 128))
    (hg1 : deriv g 0 = 1)
    (hg2 : iteratedDeriv 2 g 0 = 0)
    (hg3 : iteratedDeriv 3 g 0 = 1) :
    iteratedDeriv 3 (g ∘ u) 0 = 7 / 128 := by

  have hc :
      iteratedDeriv 3 (g ∘ u) 0 =
        iteratedDeriv 3 g (u 0) * (deriv u 0) ^ 3
        + 3 * iteratedDeriv 2 g (u 0) *
            iteratedDeriv 2 u 0 * deriv u 0
        + deriv g (u 0) * iteratedDeriv 3 u 0 := by
    exact iteratedDeriv_comp_three
      (by simpa [hu0] using hg) hu

  rw [hc, hu0, hu1, hu2, hu3, hg1, hg2, hg3]
  norm_num

end BakerTrisection

#check BakerTrisection.third_order_composition_at_zero
#print axioms BakerTrisection.third_order_composition_at_zero