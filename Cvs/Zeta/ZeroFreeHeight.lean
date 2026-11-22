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
import Cvs.Zeta.ZetaLogDeriv
import Cvs.Zeta.ZetaPolyGrowth
import Cvs.Zeta.ZetaZeroCount

/-!
# A horizontal line avoiding the zeros

`Cvs.Zeta.ZetaZeroCount` bounds the zeros near height `T` by `O(log T)`, and
`Cvs.Zeta.HeightGap` turns a bound on a *`Finset` of ordinates* into a height far from all of
them.
-/

open Complex Set Metric Finset

namespace Cvs.Zeta

/-- The zeros of an analytic function in a compact set, as a `Finset`. -/
noncomputable def zeroFinset (f : ℂ → ℂ) (U : Set ℂ) (hU : IsCompact U) : Finset ℂ :=
  ((MeromorphicOn.divisor f U).finiteSupport hU).toFinset

/-- **The divisor sum dominates the number of distinct zeros.** Each zero contributes at least `1`
to the divisor, so the `O(log T)` bound on the divisor sum is also a bound on the
*cardinality* — which is the shape the pigeonhole needs. -/
theorem card_zeroFinset_le {f : ℂ → ℂ} {U : Set ℂ} (hU : IsCompact U)
    (hf : AnalyticOnNhd ℂ f U) :
    ((zeroFinset f U hU).card : ℤ) ≤ ∑ᶠ u, MeromorphicOn.divisor f U u := by
  classical
  set D : ℂ → ℤ := fun u => MeromorphicOn.divisor f U u with hD
  have hsub : Function.support D ⊆ (zeroFinset f U hU : Set ℂ) := by
    intro u hu
    simpa [zeroFinset] using hu
  have hsum : ∑ᶠ u, D u = ∑ u ∈ zeroFinset f U hU, D u :=
    finsum_eq_finsetSum_of_support_subset D hsub
  rw [hD] at hsum
  rw [hsum]
  have hone : ∀ u ∈ zeroFinset f U hU, (1 : ℤ) ≤ MeromorphicOn.divisor f U u := by
    intro u hu
    have hmem : u ∈ U := by
      have := (MeromorphicOn.divisor f U).supportWithinDomain
      apply this
      simpa [zeroFinset] using hu
    have hne : MeromorphicOn.divisor f U u ≠ 0 := by simpa [zeroFinset] using hu
    have hnn : (0 : ℤ) ≤ MeromorphicOn.divisor f U u := by
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hmem]
      cases h : analyticOrderAt f u <;> simp [h]
    omega
  calc ((zeroFinset f U hU).card : ℤ) = ∑ _u ∈ zeroFinset f U hU, (1 : ℤ) := by simp
    _ ≤ ∑ u ∈ zeroFinset f U hU, MeromorphicOn.divisor f U u :=
        Finset.sum_le_sum hone

/-- `ζ` is nowhere locally zero away from its pole.  Needed because a zero with *infinite*
order would have divisor `0` and so escape `zeroFinset` entirely. -/
theorem analyticOrderAt_riemannZeta_ne_top {u : ℂ} (hu : u ≠ 1) :
    analyticOrderAt riemannZeta u ≠ ⊤ := by
  have hlin : AnalyticAt ℂ (fun w : ℂ => w - 1) u := (differentiable_id.sub_const 1).analyticAt u
  have hz : AnalyticAt ℂ riemannZeta u := analyticAt_riemannZeta hu
  have hev : riemannZeta₁ =ᶠ[nhds u] fun w : ℂ => (w - 1) * riemannZeta w := by
    filter_upwards [(isOpen_compl_singleton (x := (1 : ℂ))).mem_nhds hu] with w hw
    exact riemannZeta₁_eq_mul hw
  have hord : analyticOrderAt riemannZeta₁ u
      = analyticOrderAt (fun w : ℂ => w - 1) u + analyticOrderAt riemannZeta u := by
    rw [analyticOrderAt_congr hev]
    exact analyticOrderAt_mul hlin hz
  have hlin0 : analyticOrderAt (fun w : ℂ => w - 1) u = 0 := by
    rw [analyticOrderAt_eq_zero]
    exact Or.inr (sub_ne_zero.mpr hu)
  rw [hlin0, zero_add] at hord
  rw [← hord]
  exact analyticOrderAt_riemannZeta₁_ne_top u

end Cvs.Zeta
