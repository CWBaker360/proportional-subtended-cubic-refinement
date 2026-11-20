import Mathlib

namespace BakerTrisection

/-- The geometric residual operator. -/
noncomputable def bakerResidual (r x : ℝ) : ℝ :=
  x - 2 * Real.arcsin (r * Real.sin (x / (2 * r)))

/-- Every residual operator fixes zero. -/
theorem bakerResidual_zero (r : ℝ) :
    bakerResidual r 0 = 0 := by
  simp [bakerResidual]

/-- Exact arithmetic of the proposed 4:3 cubic coefficient. -/
theorem cubic_coefficient_four_thirds :
    -(((((4 : ℝ) / 3) ^ 2) - 1) /
      (24 * (((4 : ℝ) / 3) ^ 2))) =
      -(7 : ℝ) / 384 := by
  norm_num

/-- The 4:3 residual fixes zero. -/

theorem bakerResidual_four_thirds_hasDerivAt_zero :
    HasDerivAt
      (fun x : ℝ => bakerResidual (4 / 3) x) 0 0 := by

  have hlin :
      HasDerivAt (fun x : ℝ => (3 / 8) * x)
        (3 / 8) 0 := by
    convert (hasDerivAt_id (0 : ℝ)).const_mul (3 / 8 : ℝ)
      using 1 <;> norm_num

  have hsin :
      HasDerivAt
        (fun x : ℝ => Real.sin ((3 / 8) * x))
        (3 / 8) 0 := by
    have hs :=
      (Real.hasDerivAt_sin ((3 / 8 : ℝ) * 0)).comp 0 hlin
    simpa [Function.comp_def] using hs

  have harg :
      HasDerivAt
        (fun x : ℝ =>
          (4 / 3) * Real.sin ((3 / 8) * x))
        (1 / 2) 0 := by
    convert hsin.const_mul (4 / 3 : ℝ)
      using 1 <;> norm_num

  have ha :
      HasDerivAt Real.arcsin 1 0 := by
    convert Real.hasDerivAt_arcsin
      (x := (0 : ℝ)) (by norm_num) (by norm_num)
      using 1 <;> norm_num

  have harc :
      HasDerivAt
        (fun x : ℝ =>
          Real.arcsin
            ((4 / 3) * Real.sin ((3 / 8) * x)))
        (1 / 2) 0 := by
    have ha' :
        HasDerivAt Real.arcsin 1
          ((4 / 3 : ℝ) * Real.sin ((3 / 8) * 0)) := by
      simpa using ha
    have hc := ha'.comp 0 harg
    simpa [Function.comp_def] using hc

  have hmain :
      HasDerivAt
        (fun x : ℝ =>
          x - 2 * Real.arcsin
            ((4 / 3) * Real.sin ((3 / 8) * x)))
        0 0 := by
    have hd :=
      (hasDerivAt_id (0 : ℝ)).sub
        (harc.const_mul 2)
    convert hd using 1
    · funext x
      rfl
    · norm_num

  have hform :
      (fun x : ℝ => bakerResidual (4 / 3) x) =
      (fun x : ℝ =>
        x - 2 * Real.arcsin
          ((4 / 3) * Real.sin ((3 / 8) * x))) := by
    funext x
    have hdiv :
        x / (2 * ((4 : ℝ) / 3)) =
          ((3 : ℝ) / 8) * x := by
      ring
    simp only [bakerResidual, hdiv]

  rw [hform]
  exact hmain

#check BakerTrisection.bakerResidual_four_thirds_hasDerivAt_zero
#print axioms BakerTrisection.bakerResidual_four_thirds_hasDerivAt_zero
