import Mathlib

namespace BakerTrisection

/--
Derivative at zero of the explicit second-derivative
expression for the inner 4:3 sine function.
-/
theorem chord_inner_second_expression_derivative :
    HasDerivAt
      (fun x : ℝ =>
        -((3 : ℝ) / 16) *
          Real.sin ((3 / 8) * x))
      (-(9 : ℝ) / 128) 0 := by

  have hlin :
      HasDerivAt
        (fun x : ℝ => (3 / 8) * x)
        (3 / 8) 0 := by
    convert
      (hasDerivAt_id (0 : ℝ)).const_mul (3 / 8 : ℝ)
      using 1 <;> norm_num

  have hsin :
      HasDerivAt
        (fun x : ℝ => Real.sin ((3 / 8) * x))
        (3 / 8) 0 := by
    convert
      (Real.hasDerivAt_sin ((3 / 8 : ℝ) * 0)).comp
        0 hlin
      using 1 <;> norm_num [Function.comp_def]

  have hscaled := hsin.const_mul (-(3 / 16 : ℝ))

  convert hscaled using 1 <;> norm_num

end BakerTrisection

#check BakerTrisection.chord_inner_second_expression_derivative

#print axioms BakerTrisection.chord_inner_second_expression_derivative