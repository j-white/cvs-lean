import Mathlib
import Cvs.WeilForm.Archimedean.ElementaryLevyIntegral
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyTermsSum
import Cvs.Zeta.Digamma

/-!
# The archimedean symbol's Lévy representation, in one integral

    Re ψ(¼ + it/2) − Re ψ(¼) = ∫₀^∞ (1 − cos(tu/2)) · densityU u  du

the series of `ArchLevy` summed under the integral sign, against a strictly positive density.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real MeasureTheory Set Filter Topology Cvs.Zeta

namespace Cvs.WeilForm.Archimedean.LevyRepresentation

variable {t : ℝ}

/-- The `k`-th Lévy integrand. -/
def term (t : ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  (1 - Real.cos (t / 2 * u)) * Real.exp (-((1 / 4 + (k : ℝ)) * u))

theorem term_nonneg (t : ℝ) (k : ℕ) (u : ℝ) : 0 ≤ term t k u := by
  unfold term
  have h1 : 0 ≤ 1 - Real.cos (t / 2 * u) := by
    have := Real.cos_le_one (t / 2 * u); linarith
  positivity

theorem coeff_pos (k : ℕ) : (0:ℝ) < 1 / 4 + (k : ℝ) := by
  have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

theorem integrable_term (t : ℝ) (k : ℕ) : IntegrableOn (term t k) (Ioi 0) :=
  Cvs.WeilForm.Archimedean.ElementaryLevyIntegral.integrableOn (coeff_pos k) (t / 2)

/-- The `k`-th integral is the `k`-th deficit. -/
theorem integral_term (t : ℝ) (k : ℕ) :
    (∫ u in Ioi (0:ℝ), term t k u) = digammaDeficit t k :=
  (Cvs.WeilForm.Archimedean.LevyTermsSum.digammaDeficit_eq_integral t k).symm

/-- Norms may be dropped: the integrand is nonnegative. -/
theorem integral_norm_term (t : ℝ) (k : ℕ) :
    (∫ u in Ioi (0:ℝ), ‖term t k u‖) = digammaDeficit t k := by
  rw [← integral_term t k]
  exact integral_congr_ae (Filter.Eventually.of_forall fun u =>
    Real.norm_of_nonneg (term_nonneg t k u))

/-- **The terms sum pointwise to the density**, off the origin. -/
theorem hasSum_term {u : ℝ} (hu : 0 < u) (t : ℝ) :
    HasSum (fun k => term t k u) ((1 - Real.cos (t / 2 * u)) * Cvs.WeilForm.Archimedean.LevyDensity.densityU u) := by
  have h := (Cvs.WeilForm.Archimedean.LevyDensity.hasSum_exp u hu).mul_left (1 - Real.cos (t / 2 * u))
  exact h

/-- **The Lévy representation.**  The digamma series, summed under the integral. -/
theorem integral_rep (t : ℝ) [DigammaEulerLimitRe t] [DigammaEulerLimitRe 0] :
    (∫ u in Ioi (0:ℝ), (1 - Real.cos (t / 2 * u)) * Cvs.WeilForm.Archimedean.LevyDensity.densityU u)
      = (Complex.digamma (digammaArg t 0)).re - (Complex.digamma (digammaArg 0 0)).re := by
  have hsummable : Summable fun k : ℕ => ∫ u in Ioi (0:ℝ), ‖term t k u‖ := by
    simp only [integral_norm_term t]
    exact (Cvs.WeilForm.Archimedean.LevyTermsSum.hasSum_digammaDeficit t).summable
  have hHS := hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (Ioi (0:ℝ))) (F := term t)
    (fun k => integrable_term t k) hsummable
  -- the pointwise sum agrees a.e. on `Ioi 0` with the density form
  have hae : (∫ u in Ioi (0:ℝ), ∑' k, term t k u)
      = ∫ u in Ioi (0:ℝ), (1 - Real.cos (t / 2 * u)) * Cvs.WeilForm.Archimedean.LevyDensity.densityU u := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    exact (hasSum_term hu t).tsum_eq
  have hdef : (fun k => ∫ u in Ioi (0:ℝ), term t k u) = digammaDeficit t :=
    funext (integral_term t)
  rw [hdef] at hHS
  rw [← hae]
  exact tendsto_nhds_unique hHS.tendsto_sum_nat
    (Cvs.WeilForm.Archimedean.LevyTermsSum.hasSum_digammaDeficit t).tendsto_sum_nat

end Cvs.WeilForm.Archimedean.LevyRepresentation
