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
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiLogDeriv

/-!
# Landau's lemma for `ξ`, with the divisor data kept

`Cvs.Zeta.exists_logDeriv_riemannXi_sub_sum_le` states Landau's bound and existentially
quantifies the near set `S` and its multiplicities `m`, exposing only `‖ρ‖ ≤ r` about them.
-/

noncomputable section

open Complex Set Metric Finset Cvs.Zeta

namespace Cvs.ZeroFree

/-- **Landau's lemma for `ξ`, with the divisor identified and the near set complete.** -/
theorem exists_landau_riemannXi {r M : ℝ} (hr : 0 < r)
    (hMbd : ∀ z : ℂ, ‖z‖ = 2 * r → ‖riemannXi z‖ ≤ M) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ ∈ S, ‖ρ‖ ≤ r) ∧ (∀ ρ ∈ S, ρ ≠ 0) ∧ (∀ ρ ∈ S, riemannXi ρ = 0) ∧
      (∀ u : ℂ, (m u : ℤ) = MeromorphicOn.divisor riemannXi Set.univ u) ∧
      (∀ u : ℂ, ‖u‖ ≤ r → m u ≠ 0 → u ∈ S) ∧
      ∀ z : ℂ, ‖z‖ ≤ r / 4 → z ∉ S →
        ‖logDeriv riemannXi z - ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ)‖
          ≤ 8 * (Real.log M + Real.log 2 + 1) / r := by
  obtain ⟨S, m, g, hS0, hSr, hga, hfg, hgne, hcount, hzeroS, hmdiv⟩ :=
    exists_inner_factorization analyticOnNhd_riemannXi analyticOrderAt_riemannXi_ne_top
      (by rw [riemannXi_zero]; norm_num) r
  -- completeness of `S`
  have hcomplete : ∀ u : ℂ, ‖u‖ ≤ r → m u ≠ 0 → u ∈ S := by
    intro u hu hm
    by_contra hus
    have hnp : normProd S m u ≠ 0 := normProd_ne_zero_of_notMem hS0 hus
    have hgu : g u ≠ 0 := hgne u hu
    have hxi : riemannXi u ≠ 0 := by
      rw [hfg u]; exact mul_ne_zero hgu hnp
    have hord : analyticOrderAt riemannXi u = 0 := by
      rw [analyticOrderAt_eq_zero]; exact Or.inr hxi
    have hd := hmdiv u
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply analyticOnNhd_riemannXi (Set.mem_univ u),
      hord] at hd
    simp at hd
    exact hm hd
  refine ⟨S, m, hSr, hS0, hzeroS, hmdiv, hcomplete, fun z hz hzS => ?_⟩
  -- the bound: `Cvs.Zeta`'s assembly, verbatim
  have hg0 : g 0 = 1 / 2 := by
    have := hfg 0
    rw [normProd_zero, mul_one, riemannXi_zero] at this
    exact this.symm
  have hgD : Differentiable ℂ g := fun w => (hga w (Set.mem_univ w)).differentiableAt
  have hgd : DiffContOnCl ℂ g (ball (0 : ℂ) (2 * r)) := hgD.diffContOnCl
  have hgM : ∀ w ∈ closedBall (0 : ℂ) (2 * r), ‖g w‖ ≤ M :=
    norm_le_of_divide_out_inner_zeros hr hfg (fun ρ hρ => ⟨hS0 ρ hρ, hSr ρ hρ⟩) hgd hMbd
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
  have hgdiff : DifferentiableOn ℂ g (ball (0 : ℂ) r) := hgD.differentiableOn
  have hb := norm_logDeriv_sub_sum_le (f := riemannXi) (g := g) (S := S) (m := m)
    hr hfg hS0 hgdiff hgz hgball hz hzS
  rw [hg0] at hb
  refine le_trans hb (le_of_eq ?_)
  congr 2
  rw [show ‖(1 : ℂ) / 2‖ = 1 / 2 by norm_num, show (1 : ℝ) / 2 = 2⁻¹ by norm_num,
    Real.log_inv]
  ring

end Cvs.ZeroFree
