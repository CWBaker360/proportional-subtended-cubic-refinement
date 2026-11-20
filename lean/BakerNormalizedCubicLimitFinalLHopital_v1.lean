import Mathlib
import BakerNormalizedCubicLimitFirstLHopital_v2
import BakerNormalizedLocalDomain_v1

namespace BakerTrisection

/-!
# Final L'Hopital transfer: general normalized cubic limit

Uses the verified limit of H_r'(t)/(3t^2) and the actual Mathlib
punctured-neighborhood L'Hopital theorem to prove H_r(t)/t^3 -> c(r).
No new axioms or assumptions on the real ratio r.
-/

/-- The normalized residual is differentiable eventually on the punctured
neighborhood of zero, for any real ratio. -/
theorem normalizedChord_eventually_hasDerivAt (r : ℝ) :
    ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) ({0}ᶜ),
      HasDerivAt (normalizedChordResidual r)
        (deriv (normalizedChordResidual r) t) t := by
  have hradius : 0 < (1 : ℝ) / (|r| + 1) := by positivity
  have hnear : Set.Ioo (-(1 / (|r| + 1))) (1 / (|r| + 1)) ∈ nhds (0 : ℝ) := by
    exact Ioo_mem_nhds (by linarith) hradius
  have hnearWithin : Set.Ioo (-(1 / (|r| + 1))) (1 / (|r| + 1)) ∈
      nhdsWithin (0 : ℝ) ({0}ᶜ) := nhdsWithin_le_nhds hnear
  filter_upwards [hnearWithin] with t ht
  have hd := normalizedChord_hasDerivAt_on_explicit_neighborhood r t (abs_lt.mpr ht)
  rw [hd.deriv]
  exact hd

/-- The central normalized cubic asymptotic law, for arbitrary real r. -/
theorem normalizedChord_cubic_limit (r : ℝ) :
    Filter.Tendsto
      (fun t : ℝ => normalizedChordResidual r t / t ^ 3)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (normalizedChordCubicCoefficient r)) := by
  have hf : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) ({0}ᶜ),
      HasDerivAt (normalizedChordResidual r)
        (deriv (normalizedChordResidual r) t) t :=
    normalizedChord_eventually_hasDerivAt r
  have hg : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) ({0}ᶜ),
      HasDerivAt (fun x : ℝ => x ^ 3) (3 * t ^ 2) t :=
    Filter.Eventually.of_forall normalizedCubicDenominator_hasDerivAt
  have hnonzero : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) ({0}ᶜ),
      (3 : ℝ) * t ^ 2 ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ (0 : ℝ) := by simpa using ht
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 ht0)
  have hf0 : Filter.Tendsto
      (normalizedChordResidual r)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (0 : ℝ)) := by
    have hc := (normalizedChordResidual_hasDerivAt_zero r).continuousAt
    simpa [normalizedChordResidual_zero r] using
      (hc.tendsto.mono_left nhdsWithin_le_nhds)
  have hg0 : Filter.Tendsto (fun t : ℝ => t ^ 3)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (0 : ℝ)) := by
    have hc : Continuous (fun t : ℝ => t ^ 3) := by fun_prop
    have hlim : Filter.Tendsto (fun t : ℝ => t ^ 3)
        (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds ((0 : ℝ) ^ 3)) :=
      hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa using hlim
  exact HasDerivAt.lhopital_zero_nhdsNE hf hg hnonzero hf0 hg0
    (normalizedChord_first_deriv_over_three_t_sq_limit r)

end BakerTrisection

#check BakerTrisection.normalizedChord_eventually_hasDerivAt
#check BakerTrisection.normalizedChord_cubic_limit
#print axioms BakerTrisection.normalizedChord_eventually_hasDerivAt
#print axioms BakerTrisection.normalizedChord_cubic_limit
