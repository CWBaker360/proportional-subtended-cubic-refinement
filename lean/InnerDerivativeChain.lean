import Mathlib

namespace BakerTrisection

/-- First derivative of the inner chord function at every x. -/
theorem chord_inner_hasDerivAt (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => (4 / 3) * Real.sin ((3 / 8) * y))
      ((1 / 2) * Real.cos ((3 / 8) * x)) x := by

  have hlin :
      HasDerivAt (fun y : ℝ => (3 / 8) * y)
        (3 / 8) x := by
    simpa using
      (hasDerivAt_id x).const_mul (3 / 8 : ℝ)

  have hs :=
    (Real.hasDerivAt_sin ((3 / 8 : ℝ) * x)).comp x hlin

  have h := hs.const_mul (4 / 3 : ℝ)

  have h' :
      HasDerivAt
        (fun y : ℝ => (4 / 3) * Real.sin ((3 / 8) * y))
        ((4 / 3) *
          (Real.cos ((3 / 8) * x) * (3 / 8))) x := by
    simpa only [Function.comp_def] using h

  convert h' using 1
  ring

/-- Explicit formula for the first derivative. -/
theorem chord_inner_deriv (x : ℝ) :
    deriv
      (fun y : ℝ => (4 / 3) * Real.sin ((3 / 8) * y))
      x =
      (1 / 2) * Real.cos ((3 / 8) * x) := by
  exact (chord_inner_hasDerivAt x).deriv

/-- Derivative of the explicit first-derivative expression. -/
theorem chord_inner_first_expression_hasDerivAt (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => (1 / 2) * Real.cos ((3 / 8) * y))
      (-(3 / 16) * Real.sin ((3 / 8) * x)) x := by

  have hlin :
      HasDerivAt (fun y : ℝ => (3 / 8) * y)
        (3 / 8) x := by
    simpa using
      (hasDerivAt_id x).const_mul (3 / 8 : ℝ)

  have hc :=
    (Real.hasDerivAt_cos ((3 / 8 : ℝ) * x)).comp x hlin

  have h := hc.const_mul (1 / 2 : ℝ)

  have h' :
      HasDerivAt
        (fun y : ℝ => (1 / 2) * Real.cos ((3 / 8) * y))
        ((1 / 2) *
          (-Real.sin ((3 / 8) * x) * (3 / 8))) x := by
    simpa only [Function.comp_def] using h

  convert h' using 1
  ring

end BakerTrisection

#check BakerTrisection.chord_inner_hasDerivAt
#check BakerTrisection.chord_inner_deriv
#check BakerTrisection.chord_inner_first_expression_hasDerivAt

#print axioms BakerTrisection.chord_inner_hasDerivAt
#print axioms BakerTrisection.chord_inner_first_expression_hasDerivAt