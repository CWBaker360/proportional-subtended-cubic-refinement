import Mathlib
import OuterArcsinBasics
import OuterSineDerivatives

namespace BakerTrisection

/-- The third iterated derivative of arcsine at zero is one. -/
theorem outer_arcsin_third_zero :
    iteratedDeriv 3 Real.arcsin 0 = 1 := by

  have hpi : (0 : ℝ) < Real.pi / 2 := by
    have hp := Real.pi_pos
    linarith

  have hleft : -(Real.pi / 2) < (0 : ℝ) := by
    linarith

  have hlocal :
      (Real.arcsin ∘ Real.sin) =ᶠ[nhds (0 : ℝ)]
        (id : ℝ → ℝ) := by
    filter_upwards [Ioo_mem_nhds hleft hpi] with x hx
    exact Real.arcsin_sin (le_of_lt hx.1) (le_of_lt hx.2)

  have hid :
      iteratedDeriv 3 (Real.arcsin ∘ Real.sin) 0 = 0 := by
    rw [hlocal.iteratedDeriv_eq 3]
    simp [iteratedDeriv_id]

  have hsmooth : ContDiffAt ℝ 3 Real.sin 0 :=
    Real.contDiff_sin.contDiffAt

  have houter :
      ContDiffAt ℝ 3 Real.arcsin (Real.sin 0) := by
    simpa only [Real.sin_zero] using outer_arcsin_smooth_three

  have hs1 : deriv Real.sin 0 = 1 := by
    simpa using (Real.hasDerivAt_sin 0).deriv

  have hs2 : iteratedDeriv 2 Real.sin 0 = 0 := by
    rw [outer_sine_second]
    simp

  have hc :=
    iteratedDeriv_comp_three houter hsmooth

  rw [hid, Real.sin_zero, hs1, hs2,
      outer_arcsin_second_zero, outer_arcsin_first_zero,
      outer_sine_third_zero] at hc

  norm_num at hc
  linarith

end BakerTrisection

#check BakerTrisection.outer_arcsin_third_zero
#print axioms BakerTrisection.outer_arcsin_third_zero