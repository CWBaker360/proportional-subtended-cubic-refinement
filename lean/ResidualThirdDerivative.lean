import Mathlib
import ArcsinChordThird
import OuterArcsinBasics

namespace BakerTrisection

private noncomputable def chordA (x : ℝ) : ℝ :=
  Real.arcsin ((4 / 3) * Real.sin ((3 / 8) * x))

private noncomputable def residualF (x : ℝ) : ℝ :=
  x - 2 * chordA x

theorem residual_third_derivative_zero :
    iteratedDeriv 3 residualF 0 = -(7 / 64) := by

  have hA :
      iteratedDeriv 3 chordA 0 = 7 / 128 := by
    exact arcsin_chord_third_zero

  have hId :
      iteratedDeriv 3 (id : ℝ → ℝ) 0 = 0 := by
    simp [iteratedDeriv_id]

  have hInnerSmooth :
      ContDiffAt ℝ 3
        (fun x : ℝ =>
          (4 / 3) * Real.sin ((3 / 8) * x)) 0 := by
    fun_prop

  have hOuterSmooth :
      ContDiffAt ℝ 3 Real.arcsin
        ((4 / 3 : ℝ) * Real.sin ((3 / 8 : ℝ) * 0)) := by
    simpa only [Real.sin_zero, mul_zero] using
      outer_arcsin_smooth_three

  have hASmooth : ContDiffAt ℝ 3 chordA 0 := by
    have hcomp := hOuterSmooth.comp 0 hInnerSmooth
    have heq :
        chordA =
          (fun x : ℝ =>
            Real.arcsin ((4 / 3) * Real.sin ((3 / 8) * x))) := by
      funext x
      rfl
    rw [heq]
    simpa only [Function.comp_def] using hcomp
  have hIdSmooth :
      ContDiffAt ℝ 3 (id : ℝ → ℝ) 0 := by
    fun_prop

  have hScaledSmooth :
      ContDiffAt ℝ 3 ((2 : ℝ) • chordA) 0 := by
    have hpoint :
        ContDiffAt ℝ 3
          (fun y : ℝ => (2 : ℝ) • chordA y) 0 :=
      hASmooth.const_smul (2 : ℝ)
    have heq :
        ((2 : ℝ) • chordA : ℝ → ℝ) =
          (fun y : ℝ => (2 : ℝ) • chordA y) := by
      funext y
      simp only [Pi.smul_apply]
    rw [heq]
    exact hpoint
  have hlinear :
      residualF = (id : ℝ → ℝ) - (2 : ℝ) • chordA := by
    funext x
    simp [residualF, chordA, Pi.sub_apply]

  rw [hlinear]
  rw [iteratedDeriv_sub, iteratedDeriv_const_smul]
  · simp [hId, hA]
    norm_num
  · exact hASmooth
  · exact hIdSmooth
  · exact hScaledSmooth

/-- Public statement of the Baker 4:3 residual third derivative. -/
theorem residual_third_explicit :
    iteratedDeriv 3
      (fun x : ℝ =>
        x - 2 * Real.arcsin
          ((4 / 3) * Real.sin ((3 / 8) * x)))
      0 = -(7 / 64) := by
  have hfun :
      (fun x : ℝ =>
        x - 2 * Real.arcsin
          ((4 / 3) * Real.sin ((3 / 8) * x))) =
        residualF := by
    funext x
    rfl
  rw [hfun]
  exact residual_third_derivative_zero
end BakerTrisection

#check BakerTrisection.residual_third_derivative_zero
#print axioms BakerTrisection.residual_third_derivative_zero
#check BakerTrisection.residual_third_explicit
#print axioms BakerTrisection.residual_third_explicit