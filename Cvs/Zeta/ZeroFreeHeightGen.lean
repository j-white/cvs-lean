import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Finset.Card
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Cvs.Zeta.HeightGap
import Cvs.Zeta.ZeroFreeHeight
import Cvs.Zeta.ZetaZeroCount
import Cvs.Zeta.ZetaZeroCountGen

/-!
# The zero-avoiding height, at an arbitrary radius

`Cvs.Zeta.ZeroFreeHeight` fixes the radius at `9/4`, the second of the two constants flagged as
too small for the Landau disc.
-/

open Complex Real Set Metric Finset

namespace Cvs.Zeta

/-- The zero ordinates near height `T`, as a `Finset`, at an arbitrary radius. -/
theorem exists_ordinates_card_le' (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) (hk : 1 ≤ k)
    (hkr : 2 * ρ ≤ (k : ℝ) + 3 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 2 * ρ + 1 ≤ |T| →
      ∃ A : Finset ℝ, (A.card : ℝ) ≤ K * (1 + Real.log |T|) ∧
        ∀ z : ℂ, z ∈ closedBall (2 + T * I) ρ → riemannZeta z = 0 → z.im ∈ A := by
  obtain ⟨K, hK0, hK⟩ := exists_zero_count_riemannZeta_ball' ρ hρ k hk hkr
  refine ⟨K, hK0, fun T hT => ?_⟩
  have hTρ : ρ + 1 ≤ |T| := by linarith
  have hcpt : IsCompact (closedBall (2 + T * I) ρ) := isCompact_closedBall _ _
  have hana : AnalyticOnNhd ℂ riemannZeta (closedBall (2 + T * I) ρ) :=
    fun w hw => analyticAt_riemannZeta (ne_one_of_mem_ball' hTρ hw)
  refine ⟨(zeroFinset riemannZeta _ hcpt).image Complex.im, ?_, ?_⟩
  · have h1 : ((zeroFinset riemannZeta _ hcpt).image Complex.im).card
        ≤ (zeroFinset riemannZeta _ hcpt).card := Finset.card_image_le
    have h2 := card_zeroFinset_le hcpt hana
    have h3 := hK T hT
    have h1' : (((zeroFinset riemannZeta _ hcpt).image Complex.im).card : ℝ)
        ≤ ((zeroFinset riemannZeta _ hcpt).card : ℝ) := by exact_mod_cast h1
    have h2' : ((zeroFinset riemannZeta _ hcpt).card : ℝ)
        ≤ ((∑ᶠ u, MeromorphicOn.divisor riemannZeta (closedBall (2 + T * I) ρ) u : ℤ) : ℝ) := by
      exact_mod_cast h2
    linarith
  · intro z hz hz0
    refine Finset.mem_image.mpr ⟨z, ?_, rfl⟩
    have hz1 : z ≠ 1 := ne_one_of_mem_ball' hTρ hz
    have hordne : analyticOrderAt riemannZeta z ≠ ⊤ := analyticOrderAt_riemannZeta_ne_top hz1
    have hpos : analyticOrderAt riemannZeta z ≠ 0 := by
      intro hc
      rcases analyticOrderAt_eq_zero.mp hc with h | h
      · exact h (analyticAt_riemannZeta hz1)
      · exact h hz0
    have hdiv : MeromorphicOn.divisor riemannZeta (closedBall (2 + T * I) ρ) z ≠ 0 := by
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hana hz]
      lift analyticOrderAt riemannZeta z to ℕ using hordne with M hM
      simp only [ENat.map_natCast, WithTop.untop₀_coe, ne_eq, Nat.cast_eq_zero]
      simpa using hpos
    simpa [zeroFinset] using hdiv

/-- **A zero-avoiding height, at an arbitrary radius.** -/
theorem exists_zero_free_height' (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) (hk : 1 ≤ k)
    (hkr : 2 * ρ ≤ (k : ℝ) + 3 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 2 * ρ + 1 ≤ |T| →
      ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧
        ∀ z : ℂ, z ∈ closedBall (2 + T * I) ρ → riemannZeta z = 0 →
          1 / (2 * (K * (1 + Real.log |T|) + 2)) ≤ |T' - z.im| := by
  obtain ⟨K, hK0, hK⟩ := exists_ordinates_card_le' ρ hρ k hk hkr
  refine ⟨K, hK0, fun T hT => ?_⟩
  obtain ⟨A, hAcard, hAmem⟩ := hK T hT
  have hlog : 0 ≤ Real.log |T| := Real.log_nonneg (by linarith)
  have hpos : 0 ≤ K * (1 + Real.log |T|) := by positivity
  set N : ℕ := ⌈K * (1 + Real.log |T|)⌉₊ with hN
  have hAN : A.card ≤ N := by
    have : (A.card : ℝ) ≤ (N : ℝ) := le_trans hAcard (Nat.le_ceil _)
    exact_mod_cast this
  obtain ⟨T', h1, h2, h3⟩ := exists_far_from_finset_of_card_le A T hAN
  refine ⟨T', h1, h2, fun z hz hz0 => ?_⟩
  refine le_trans ?_ (h3 z.im (hAmem z hz hz0))
  have hNle : (N : ℝ) ≤ K * (1 + Real.log |T|) + 1 := by
    rw [hN]; linarith [Nat.ceil_lt_add_one hpos]
  refine one_div_le_one_div_of_le (by positivity) ?_
  linarith

end Cvs.Zeta
