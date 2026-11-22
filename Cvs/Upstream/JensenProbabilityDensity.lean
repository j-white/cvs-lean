import Mathlib
import Cvs.Upstream.CauchySchwarzLine

/-!
# Jensen against a probability density

    (∫ k·ρ)² ≤ ∫ k²·ρ      for `ρ ≥ 0` of unit mass

Cauchy–Schwarz with the density split as `√ρ·√ρ`; the mollification bound is this applied at
each point.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real

namespace Cvs.Upstream.JensenProbabilityDensity

/-- The square root of a probability density is in `L²`. -/
theorem memLp_sqrt {ρ : ℝ → ℝ} (hρnn : ∀ t, 0 ≤ ρ t) (hρ : Integrable ρ (volume : Measure ℝ)) :
    MemLp (fun t : ℝ => Real.sqrt (ρ t)) 2 (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Real.sqrt (ρ t)) (volume : Measure ℝ) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hρ.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine hρ.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hρnn t)]

/-- **Jensen against a probability density.** -/
theorem sq_integral_weighted_le {ρ k : ℝ → ℝ} (hρnn : ∀ t, 0 ≤ ρ t)
    (hρ : Integrable ρ (volume : Measure ℝ)) (hρ1 : (∫ t : ℝ, ρ t) = 1)
    (hk : MemLp (fun t : ℝ => k t * Real.sqrt (ρ t)) 2 (volume : Measure ℝ)) :
    (∫ t : ℝ, k t * ρ t) ^ 2 ≤ ∫ t : ℝ, k t ^ 2 * ρ t := by
  have hs := memLp_sqrt hρnn hρ
  have hcs := Cvs.Upstream.CauchySchwarzLine.abs_integral_mul_le hk hs
  -- the product recombines the density
  have hprod : (∫ t : ℝ, (k t * Real.sqrt (ρ t)) * Real.sqrt (ρ t))
      = ∫ t : ℝ, k t * ρ t :=
    integral_congr_ae (Filter.Eventually.of_forall fun t => by
      simp only
      rw [mul_assoc, Real.mul_self_sqrt (hρnn t)])
  have hsqf : (∫ t : ℝ, (k t * Real.sqrt (ρ t)) ^ 2) = ∫ t : ℝ, k t ^ 2 * ρ t :=
    integral_congr_ae (Filter.Eventually.of_forall fun t => by
      simp only
      rw [mul_pow, Real.sq_sqrt (hρnn t)])
  have hsqg : (∫ t : ℝ, (Real.sqrt (ρ t)) ^ 2) = 1 := by
    rw [← hρ1]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by
      simp only
      rw [Real.sq_sqrt (hρnn t)])
  rw [hprod, hsqf, hsqg, Real.sqrt_one, mul_one] at hcs
  have hnn : 0 ≤ ∫ t : ℝ, k t ^ 2 * ρ t := by
    refine integral_nonneg fun t => ?_
    exact mul_nonneg (sq_nonneg _) (hρnn t)
  nlinarith [hcs, abs_nonneg (∫ t : ℝ, k t * ρ t), sq_abs (∫ t : ℝ, k t * ρ t),
    Real.sq_sqrt hnn, Real.sqrt_nonneg (∫ t : ℝ, k t ^ 2 * ρ t)]

end Cvs.Upstream.JensenProbabilityDensity
