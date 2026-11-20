import Mathlib
import ResidualTaylorPrereqs
import OuterArcsinBasics

namespace BakerTrisection

/-- The explicit Baker residual is C³ at zero. -/
theorem cubicResidual_smooth_three :
    ContDiffAt ℝ 3 cubicResidual 0 := by

  have hinner :
      ContDiffAt ℝ 3
        (fun x : ℝ =>
          (4 / 3) * Real.sin ((3 / 8) * x)) 0 := by
    fun_prop

  have houter :
      ContDiffAt ℝ 3 Real.arcsin
        ((4 / 3 : ℝ) * Real.sin ((3 / 8 : ℝ) * 0)) := by
    simpa only [Real.sin_zero, mul_zero] using
      outer_arcsin_smooth_three

  have hcomposition :
      ContDiffAt ℝ 3
        (fun x : ℝ =>
          Real.arcsin
            ((4 / 3) * Real.sin ((3 / 8) * x))) 0 := by
    simpa only [Function.comp_def] using
      houter.comp 0 hinner

  have hscaled :
      ContDiffAt ℝ 3
        (fun x : ℝ =>
          (2 : ℝ) • Real.arcsin
            ((4 / 3) * Real.sin ((3 / 8) * x))) 0 :=
    hcomposition.const_smul (2 : ℝ)

  have hscaled' :
      ContDiffAt ℝ 3
        (fun x : ℝ =>
          2 * Real.arcsin
            ((4 / 3) * Real.sin ((3 / 8) * x))) 0 := by
    simpa only [smul_eq_mul] using hscaled

  have hid :
      ContDiffAt ℝ 3 (id : ℝ → ℝ) 0 := by
    fun_prop

  have hsub := hid.sub hscaled'

  have heq :
      cubicResidual =
        (id : ℝ → ℝ) -
          (fun x : ℝ =>
            2 * Real.arcsin
              ((4 / 3) * Real.sin ((3 / 8) * x))) := by
    funext x
    rfl

  rw [heq]
  exact hsub

end BakerTrisection

#check BakerTrisection.cubicResidual_smooth_three
#print axioms BakerTrisection.cubicResidual_smooth_three