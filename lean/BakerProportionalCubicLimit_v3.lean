import Mathlib
import BakerNormalizedCubicLimitFinalLHopital_v1
import BakerProportionalScaling_v3

namespace BakerTrisection

/-!
# Generalized proportional-chord cubic limit (v3)

Transfer the verified normalized cubic limit through the nonzero linear
rescaling theta ↦ theta/(2*a). No extra axioms are introduced.
-/

/-- Nonzero real scaling preserves convergence to zero through the punctured
neighborhood of zero. -/
theorem proportionalChord_scale_tendsto_punctured
    (a : ℝ) (ha : a ≠ 0) :
    Filter.Tendsto (fun theta : ℝ => theta / (2 * a))
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) := by
  have ha2 : (2 : ℝ) * a ≠ 0 := mul_ne_zero (by norm_num) ha
  have hzero : Filter.Tendsto (fun theta : ℝ => theta / (2 * a))
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (0 : ℝ)) := by
    have hc : ContinuousAt (fun theta : ℝ => theta / (2 * a)) (0 : ℝ) := by
      fun_prop
    have hfull : Filter.Tendsto (fun theta : ℝ => theta / (2 * a))
        (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
      simpa only [zero_div] using hc.tendsto
    exact hfull.mono_left nhdsWithin_le_nhds
  have hnonzero : Filter.Tendsto (fun theta : ℝ => theta / (2 * a))
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (Filter.principal ({0}ᶜ)) := by
    apply Filter.tendsto_principal.2
    filter_upwards [self_mem_nhdsWithin] with theta ht
    have htheta : theta ≠ 0 := by simpa using ht
    have hquot : theta / (2 * a) ≠ 0 := div_ne_zero htheta ha2
    simpa using hquot
  change Filter.Tendsto (fun theta : ℝ => theta / (2 * a))
    (nhdsWithin (0 : ℝ) ({0}ᶜ))
    (nhds (0 : ℝ) ⊓ Filter.principal ({0}ᶜ))
  exact Filter.tendsto_inf.mpr ⟨hzero, hnonzero⟩

/-- Algebraic transfer of the normalized cubic quotient. The formula is
valid at zero as well because both residuals vanish there. -/
theorem proportionalChord_cubic_quotient_identity
    (a b theta : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    proportionalChordResidual a b theta / theta ^ 3 =
      (normalizedChordResidual (a / b) (theta / (2 * a)) /
        (theta / (2 * a)) ^ 3) * (1 / (4 * a ^ 3)) := by
  rw [proportionalChordResidual_normalized a b theta ha hb]
  by_cases htheta : theta = 0
  · subst theta
    simp [normalizedChordResidual_zero]
  · field_simp [ha, htheta]
    <;> ring

/-- The fully generalized cubic coefficient of the proportional-chord
residual, for arbitrary nonzero real parameters a and b. -/
theorem proportionalChord_cubic_limit_general
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Filter.Tendsto
      (fun theta : ℝ => proportionalChordResidual a b theta / theta ^ 3)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (proportionalChordCubicCoefficient a b)) := by
  have hscaled := (normalizedChord_cubic_limit (a / b)).comp
    (proportionalChord_scale_tendsto_punctured a ha)
  have hmul : Filter.Tendsto
      (fun theta : ℝ =>
        (normalizedChordResidual (a / b) (theta / (2 * a)) /
          (theta / (2 * a)) ^ 3) * (1 / (4 * a ^ 3)))
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (normalizedChordCubicCoefficient (a / b) * (1 / (4 * a ^ 3)))) := by
    exact hscaled.mul tendsto_const_nhds
  have hcoeff :
      normalizedChordCubicCoefficient (a / b) * (1 / (4 * a ^ 3)) =
        proportionalChordCubicCoefficient a b := by
    rw [proportionalChordCubicCoefficient_normalized a b ha hb]
    ring
  have hfun :
      (fun theta : ℝ =>
        (normalizedChordResidual (a / b) (theta / (2 * a)) /
          (theta / (2 * a)) ^ 3) * (1 / (4 * a ^ 3))) =
      (fun theta : ℝ => proportionalChordResidual a b theta / theta ^ 3) := by
    funext theta
    exact (proportionalChord_cubic_quotient_identity a b theta ha hb).symm
  rw [hfun, hcoeff] at hmul
  exact hmul

end BakerTrisection

#check BakerTrisection.proportionalChord_scale_tendsto_punctured
#check BakerTrisection.proportionalChord_cubic_quotient_identity
#check BakerTrisection.proportionalChord_cubic_limit_general
#print axioms BakerTrisection.proportionalChord_scale_tendsto_punctured
#print axioms BakerTrisection.proportionalChord_cubic_quotient_identity
#print axioms BakerTrisection.proportionalChord_cubic_limit_general
