import Mathlib
import Cvs.Upstream.L2TranslationContinuity
import Cvs.WeilForm.Mollify.MollifyShiftedEnergy
import Cvs.WeilForm.Mollify.MollifyTranslationModulus

/-!
# The mollification error vanishes with the kernel's radius

    ∫ ((f⋆ρₙ)(s) − f s)² ds → 0    as the radii of the `ρₙ` tend to zero

`Cvs.WeilForm.Mollify.MollifyTranslationModulus` bounds the error by the translation modulus over the kernel's support, and the
modulus tends to zero because translation is continuous in `L²`.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter

namespace Cvs.WeilForm.Mollify.MollifyErrorVanishes

/-- **The mollification error vanishes.** -/
theorem tendsto_integral_conv_sub {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hfm : Measurable f) {ρ : ℕ → ℝ → ℝ} {δ : ℕ → ℝ}
    (hρc : ∀ n, Continuous (ρ n)) (hρs : ∀ n, HasCompactSupport (ρ n))
    (hρm : ∀ n, Measurable (ρ n)) (hρi : ∀ n, Integrable (ρ n) (volume : Measure ℝ))
    (hρnn : ∀ n, ∀ t : ℝ, 0 ≤ ρ n t) (hρ1 : ∀ n, (∫ t : ℝ, ρ n t) = 1)
    (hrad : ∀ n, ∀ t : ℝ, δ n < |t| → ρ n t = 0)
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n : ℕ => ∫ s : ℝ, (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f (ρ n) s - f s) ^ 2)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- the translation modulus is small on a neighbourhood of the origin
  have htr := Cvs.Upstream.L2TranslationContinuity.tendsto_integral_sub_translate_sq hf
  rw [Metric.tendsto_nhds] at htr
  obtain ⟨η, hηpos, hη⟩ := Metric.eventually_nhds_iff.mp (htr (ε / 2) (by linarith))
  -- the radii eventually fit inside it
  have hev : ∀ᶠ n : ℕ in Filter.atTop, |δ n| < η / 2 := by
    have := Metric.tendsto_atTop.mp hδ (η / 2) (by linarith)
    obtain ⟨N, hN⟩ := this
    exact Filter.eventually_atTop.mpr ⟨N, fun n hn => by simpa [Real.dist_eq] using hN n hn⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  have hδn : |δ n| < η / 2 := hN n hn
  have hsmall : ∀ t : ℝ, |t| ≤ δ n → (∫ s : ℝ, (f (s - t) - f s) ^ 2) ≤ ε / 2 := by
    intro t ht
    have htη : dist (-t) 0 < η := by
      rw [Real.dist_eq, sub_zero, abs_neg]
      calc |t| ≤ δ n := ht
        _ ≤ |δ n| := le_abs_self _
        _ < η / 2 := hδn
        _ < η := by linarith
    have h := hη htη
    rw [Real.dist_eq, sub_zero] at h
    have heq : (∫ x : ℝ, (f x - f (x + -t)) ^ 2) = ∫ s : ℝ, (f (s - t) - f s) ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [← sub_eq_add_neg]
      ring
    rw [heq] at h
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) h)
  have hbound := Cvs.WeilForm.Mollify.MollifyTranslationModulus.integral_conv_sub_le (δ := δ n) (ε := ε / 2)
    (by linarith) hf hfm (hρc n) (hρs n) (hρm n) (hρi n) (hρnn n) (hρ1 n)
    (fun t htne => by
      by_contra hc
      push_neg at hc
      exact htne (hrad n t hc))
    hsmall
  have hnn : 0 ≤ ∫ s : ℝ, (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f (ρ n) s - f s) ^ 2 :=
    integral_nonneg fun s => sq_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith

end Cvs.WeilForm.Mollify.MollifyErrorVanishes
