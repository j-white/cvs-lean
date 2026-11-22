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
import Cvs.Zeta.DivisorMatch
import Cvs.Zeta.ZetaLogDeriv
import Cvs.Zeta.ZetaZeroCount

/-!
# Joining the Landau count to the ζ zero count

`exists_logDeriv_sub_sum_le_center` reports its multiplicity sum as a divisor sum for `ζ₁(c +
·)` on the disc about the **origin**; `exists_zero_count_riemannZeta_ball'` bounds a divisor
sum for `ζ` on the disc about **`c`**.
-/

open Complex Real Set Metric Finset

namespace Cvs.Zeta

/-- The divisor of a translated function, at the translated point. -/
theorem divisor_comp_add_apply {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (c : ℂ) (r : ℝ) (σ : ℂ) :
    MeromorphicOn.divisor (fun w : ℂ => f (c + w)) (closedBall (0 : ℂ) r) σ
      = MeromorphicOn.divisor f (closedBall c r) (c + σ) := by
  have hFa : AnalyticOnNhd ℂ (fun w : ℂ => f (c + w)) (closedBall (0 : ℂ) r) := by
    intro w _
    have hg : AnalyticAt ℂ (fun w : ℂ => c + w) w := analyticAt_const.add analyticAt_id
    exact (hf (c + w) (Set.mem_univ _)).comp hg
  have hfa : AnalyticOnNhd ℂ f (closedBall c r) := fun w _ => hf w (Set.mem_univ w)
  have hmem : σ ∈ closedBall (0 : ℂ) r ↔ c + σ ∈ closedBall c r := by
    simp [mem_closedBall, dist_eq_norm]
  by_cases hσ : σ ∈ closedBall (0 : ℂ) r
  · rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hFa hσ,
      MeromorphicOn.AnalyticOnNhd.divisor_apply hfa (hmem.mp hσ),
      analyticOrderAt_comp_add f c σ]
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hσ,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ (fun hc => hσ (hmem.mpr hc))]

/-- **The translated divisor sum equals the original.** -/
theorem finsum_divisor_comp_add {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (c : ℂ) (r : ℝ) :
    (∑ᶠ σ, (MeromorphicOn.divisor (fun w : ℂ => f (c + w)) (closedBall (0 : ℂ) r) σ : ℤ))
      = ∑ᶠ u, (MeromorphicOn.divisor f (closedBall c r) u : ℤ) := by
  have hpt : ∀ σ : ℂ,
      (MeromorphicOn.divisor (fun w : ℂ => f (c + w)) (closedBall (0 : ℂ) r) σ : ℤ)
        = (MeromorphicOn.divisor f (closedBall c r) ((Equiv.addLeft c) σ) : ℤ) := by
    intro σ
    simpa using divisor_comp_add_apply hf c r σ
  rw [finsum_congr hpt]
  exact finsum_comp_equiv (Equiv.addLeft c)

/-- `ζ₁` and `ζ` have the same divisor on a ball avoiding the pole. -/
theorem divisor_riemannZeta₁_apply_eq {c : ℂ} {r : ℝ}
    (h1 : (1 : ℂ) ∉ closedBall c r) (u : ℂ) :
    MeromorphicOn.divisor riemannZeta₁ (closedBall c r) u
      = MeromorphicOn.divisor riemannZeta (closedBall c r) u := by
  have hz1 : AnalyticOnNhd ℂ riemannZeta₁ (closedBall c r) :=
    fun w _ => differentiable_riemannZeta₁.analyticAt w
  have hz : AnalyticOnNhd ℂ riemannZeta (closedBall c r) :=
    fun w hw => analyticAt_riemannZeta (fun hc => h1 (hc ▸ hw))
  by_cases hu : u ∈ closedBall c r
  · rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hz1 hu,
      MeromorphicOn.AnalyticOnNhd.divisor_apply hz hu,
      analyticOrderAt_riemannZeta₁_eq (fun hc => h1 (hc ▸ hu))]
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]

/-- **The chain, joined.**  The multiplicity sum of the Landau factorisation for
`ζ₁(c + ·)` on the disc of radius `r` about the origin equals the `ζ` divisor sum on the
disc of radius `r` about `c` — which is what the zero count bounds. -/
theorem finsum_divisor_zeta₁_comp_add_eq {c : ℂ} {r : ℝ}
    (h1 : (1 : ℂ) ∉ closedBall c r) :
    (∑ᶠ σ, (MeromorphicOn.divisor (fun w : ℂ => riemannZeta₁ (c + w))
        (closedBall (0 : ℂ) r) σ : ℤ))
      = ∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall c r) u : ℤ) := by
  rw [finsum_divisor_comp_add analyticOnNhd_riemannZeta₁ c r]
  exact finsum_congr fun u => by rw [divisor_riemannZeta₁_apply_eq h1 u]

/-- **The count, transferred.** -/
theorem count_transfer {c : ℂ} {r : ℝ} (h1 : (1 : ℂ) ∉ closedBall c r)
    {S : Finset ℂ} {m : ℂ → ℕ}
    (h : (∑ σ ∈ S, (m σ : ℤ))
      = ∑ᶠ u, (MeromorphicOn.divisor (fun w : ℂ => riemannZeta₁ (c + w))
          (closedBall (0 : ℂ) r) u : ℤ)) :
    (∑ σ ∈ S, (m σ : ℤ))
      = ∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall c r) u : ℤ) :=
  h.trans (finsum_divisor_zeta₁_comp_add_eq h1)

end Cvs.Zeta
