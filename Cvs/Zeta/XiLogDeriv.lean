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
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.InnerFactor
import Cvs.Zeta.LandauCancel
import Cvs.Zeta.LandauLemma

/-!
# `ξ'/ξ` minus its nearby poles

The end of route B.
-/

open Complex Set Metric Finset

namespace Cvs.Zeta

@[simp] theorem normProd_zero (S : Finset ℂ) (m : ℂ → ℕ) : normProd S m 0 = 1 := by
  rw [normProd]
  refine Finset.prod_eq_one fun ρ _ => ?_
  simp

/-! ### Recentring -/

/-- **`f'/f` minus its nearby poles, at an arbitrary centre, for any entire `f`.** -/
theorem exists_logDeriv_sub_sum_le_center {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hford : ∀ z : ℂ, analyticOrderAt f z ≠ ⊤)
    {c : ℂ} {r M : ℝ} (hr : 0 < r) (hc : f c ≠ 0)
    (hMbd : ∀ z : ℂ, ‖z - c‖ = 2 * r → ‖f z‖ ≤ M) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ), (∀ σ ∈ S, ‖σ‖ ≤ r) ∧
      ((∑ σ ∈ S, (m σ : ℤ))
        = ∑ᶠ u, MeromorphicOn.divisor (fun w : ℂ => f (c + w))
            (Metric.closedBall (0 : ℂ) r) u) ∧
      (∀ σ ∈ S, f (c + σ) = 0) ∧
      ∀ z : ℂ, ‖z - c‖ ≤ r / 4 → (z - c) ∉ S →
        ‖logDeriv f z - ∑ σ ∈ S, (m σ : ℂ) / (z - (c + σ))‖
          ≤ 8 * (Real.log M - Real.log ‖f c‖ + 1) / r := by
  set F : ℂ → ℂ := fun w => f (c + w) with hF
  have hfD : Differentiable ℂ f := fun w => (hf w (Set.mem_univ w)).differentiableAt
  have hFd : Differentiable ℂ F :=
    hfD.comp ((differentiable_const c).add differentiable_id)
  have hFa : AnalyticOnNhd ℂ F Set.univ := fun w _ => hFd.analyticAt w
  have hFord : ∀ w : ℂ, analyticOrderAt F w ≠ ⊤ := by
    intro w htop
    rw [analyticOrderAt_eq_top] at htop
    refine hford (c + w) ?_
    rw [analyticOrderAt_eq_top]
    have hmap : Filter.Tendsto (fun v : ℂ => v - c) (nhds (c + w)) (nhds w) := by
      have := (continuous_sub_right c).tendsto (c + w)
      simpa using this
    filter_upwards [hmap.eventually htop] with v hv
    simpa [hF] using hv
  have hF0 : F 0 ≠ 0 := by simpa [hF] using hc
  obtain ⟨S, m, g, hS0, hSr, hga, hfg, hgne, hcount, hSzero, -⟩ :=
    exists_inner_factorization hFa hFord hF0 r
  refine ⟨S, m, hSr, hcount, hSzero, fun z hz hzS => ?_⟩
  have hg0 : g 0 = f c := by
    have := hfg 0
    rw [normProd_zero, mul_one] at this
    simpa [hF] using this.symm
  have hgD : Differentiable ℂ g := fun w => (hga w (Set.mem_univ w)).differentiableAt
  have hMF : ∀ w : ℂ, ‖w‖ = 2 * r → ‖F w‖ ≤ M := by
    intro w hw
    refine hMbd (c + w) ?_
    simpa using hw
  have hgM := norm_le_of_divide_out_inner_zeros hr hfg
    (fun ρ hρ => ⟨hS0 ρ hρ, hSr ρ hρ⟩) hgD.diffContOnCl hMF
  have hgball : ∀ w ∈ ball (0 : ℂ) r, ‖g w‖ ≤ M := by
    intro w hw
    refine hgM w ?_
    rw [mem_closedBall_zero_iff]
    rw [mem_ball_zero_iff] at hw
    linarith
  have hgz : ∀ w ∈ ball (0 : ℂ) r, g w ≠ 0 := by
    intro w hw
    rw [mem_ball_zero_iff] at hw
    exact hgne w hw.le
  have hmain := norm_logDeriv_sub_sum_le (f := F) (g := g) (S := S) (m := m)
    hr hfg hS0 hgD.differentiableOn hgz hgball hz hzS
  rw [hg0] at hmain
  -- transport the logarithmic derivative and the poles back
  have hld : logDeriv F (z - c) = logDeriv f z := by
    rw [logDeriv_apply, logDeriv_apply, hF]
    simp only [deriv_comp_const_add]
    congr 1 <;> ring_nf
  rw [hld] at hmain
  refine le_trans (le_of_eq ?_) hmain
  congr 2
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  ring

end Cvs.Zeta
