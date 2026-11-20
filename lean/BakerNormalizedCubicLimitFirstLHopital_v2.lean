import Mathlib
import BakerNormalizedCubicLimitThirdSlopeBridge_v1
import BakerNormalizedThirdDerivativeBridge_v1

namespace BakerTrisection

/-!
# First backward L'Hopital transfer for the generalized cubic limit

From H_r''(t)/(6t) -> c(r), prove H_r'(t)/(3t^2) -> c(r).
The transfer uses Mathlib's actual punctured-neighborhood 0/0 L'Hopital
rule. The final H_r(t)/t^3 limit is not yet claimed.
-/

private theorem localRadiusPos (r : ℝ) :
    0 < (1 : ℝ) / (|r| + 1) := by positivity

/-- The first-derivative numerator has the required local derivative. -/
theorem normalizedChord_first_deriv_eventually_hasDerivAt (r : ℝ) :
    ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) ({0}ᶜ),
      HasDerivAt (fun x : ℝ => deriv (normalizedChordResidual r) x)
        (deriv (fun x : ℝ => deriv (normalizedChordResidual r) x) t) t := by
  have hnear : Set.Ioo (-(1 / (|r| + 1))) (1 / (|r| + 1)) ∈ nhds (0 : ℝ) := by
    exact Ioo_mem_nhds (by linarith [localRadiusPos r]) (localRadiusPos r)
  have hnearWithin : Set.Ioo (-(1 / (|r| + 1))) (1 / (|r| + 1)) ∈
      nhdsWithin (0 : ℝ) ({0}ᶜ) := nhdsWithin_le_nhds hnear
  filter_upwards [hnearWithin] with t ht
  have hs := normalizedChord_second_hasDerivAt_of_small r t (abs_lt.mpr ht)
  rw [normalizedChord_second_deriv_eq_of_small r t (abs_lt.mpr ht)]
  exact hs

/-- First genuine L'Hopital transfer, from the second derivative to the first. -/
theorem normalizedChord_first_deriv_over_three_t_sq_limit (r : ℝ) :
    Filter.Tendsto
      (fun t : ℝ => deriv (normalizedChordResidual r) t / (3 * t ^ 2))
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (normalizedChordCubicCoefficient r)) := by
  have hf : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) ({0}ᶜ),
      HasDerivAt (fun x : ℝ => deriv (normalizedChordResidual r) x)
        (deriv (fun x : ℝ => deriv (normalizedChordResidual r) x) t) t :=
    normalizedChord_first_deriv_eventually_hasDerivAt r
  have hg : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) ({0}ᶜ),
      HasDerivAt (fun x : ℝ => 3 * x ^ 2) (6 * t) t :=
    Filter.Eventually.of_forall (normalizedQuadraticDenominator_hasDerivAt)
  have hnonzero : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) ({0}ᶜ), (6 : ℝ) * t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ (0 : ℝ) := by simpa using ht
    exact mul_ne_zero (by norm_num) ht0
  have hf0 : Filter.Tendsto
      (fun t : ℝ => deriv (normalizedChordResidual r) t)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (0 : ℝ)) := by
    have hc := (normalizedChord_deriv_hasDerivAt_zero r).continuousAt
    simpa [normalizedChordResidual_deriv_zero r] using
      (hc.tendsto.mono_left nhdsWithin_le_nhds)
  have hg0 : Filter.Tendsto (fun t : ℝ => 3 * t ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (0 : ℝ)) := by
    have hc : Continuous (fun t : ℝ => 3 * t ^ 2) := by fun_prop
    have hc0 : ContinuousAt (fun t : ℝ => 3 * t ^ 2) 0 := hc.continuousAt
    have hlim : Filter.Tendsto (fun t : ℝ => 3 * t ^ 2)
        (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (3 * (0 : ℝ) ^ 2)) :=
      hc0.tendsto.mono_left nhdsWithin_le_nhds
    simpa using hlim
  have hratio : Filter.Tendsto
      (fun t : ℝ =>
        deriv (fun x : ℝ => deriv (normalizedChordResidual r) x) t / (6 * t))
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (normalizedChordCubicCoefficient r)) := by
    have heq :
        (fun t : ℝ =>
          deriv (fun x : ℝ => deriv (normalizedChordResidual r) x) t / (6 * t)) =
        (fun t : ℝ =>
          (t⁻¹ * deriv (fun x : ℝ => deriv (normalizedChordResidual r) x) t) / 6) := by
      funext t
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [heq]
    exact normalizedChord_second_deriv_over_six_t_limit r
  exact HasDerivAt.lhopital_zero_nhdsNE hf hg hnonzero hf0 hg0 hratio

end BakerTrisection

#check BakerTrisection.normalizedChord_first_deriv_eventually_hasDerivAt
#check BakerTrisection.normalizedChord_first_deriv_over_three_t_sq_limit
#print axioms BakerTrisection.normalizedChord_first_deriv_eventually_hasDerivAt
#print axioms BakerTrisection.normalizedChord_first_deriv_over_three_t_sq_limit
