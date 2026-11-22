import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.Hadamard
import Cvs.Zeta.HadamardProduct.CriterionMechanicalHyps
import Cvs.Zeta.HadamardProduct.LandauCriterion
import Cvs.Zeta.HadamardProduct.LandauLemmaXi
import Cvs.Zeta.HadamardProduct.LandauNearSumIndex
import Cvs.Zeta.HadamardProduct.LandauNearSumXi
import Cvs.Zeta.HadamardProduct.OrderOneGrowth
import Cvs.Zeta.HadamardProduct.XiExceptionalSet
import Cvs.Zeta.HadamardProduct.XiZerosCountable
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.Weierstrass

/-!
# Rung 3

ξ(z) = ∏_{‖u‖<1}(z−u)^{m_u} · ∏_ρ E₁(z/ρ) · e^{az+b}
-/

noncomputable section

open Complex Filter Topology Finset Cvs.Zeta

namespace Cvs.ZeroFree

/-- **Rung 3.**  The exponential factor in Hadamard's product for `ξ` is affine — stated both
as the product and as the constancy of its logarithmic derivative. -/
theorem exists_affine_exponent_riemannXi :
    ∃ c b : ℂ,
      (∀ z : ℂ, riemannXi z
          = finiteFactor Cvs.ZeroFree.smallS Cvs.ZeroFree.mult z
            * (∏' n : zeroIndex riemannXi, weierstrassE1 (z / zeroSeq riemannXi n))
            * Complex.exp (c * z + b))
      ∧ (∀ z : ℂ, z ∉ Cvs.ZeroFree.xiExceptional →
          logDeriv riemannXi z
            = Cvs.ZeroFree.smallSum z
              + ((∑' n : zeroIndex riemannXi,
                  (1 / (z - zeroSeq riemannXi n) + 1 / zeroSeq riemannXi n)) + c)) := by
  classical
  -- the growth bound, and the resulting `M`
  obtain ⟨C, A, hC, hA, hgrow⟩ := exists_growth_bound_riemannXi
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  set M : ℝ → ℝ := fun r => C * Real.exp (A * (2 * r * (1 + Real.log (2 * r)))) with hMdef
  have hMbd : ∀ r : ℝ, ∀ z : ℂ, ‖z‖ = 2 * r → ‖riemannXi z‖ ≤ M r := by
    intro r z hz
    have h := hgrow z
    rw [hz] at h
    exact h
  -- Landau's data, chosen for every radius
  have hex : ∀ r : ℝ, ∃ (S : Finset ℂ) (m : ℂ → ℕ), 0 < r →
      (∀ ρ ∈ S, ‖ρ‖ ≤ r) ∧ (∀ ρ ∈ S, ρ ≠ 0) ∧ (∀ ρ ∈ S, riemannXi ρ = 0) ∧
      (∀ u : ℂ, (m u : ℤ) = MeromorphicOn.divisor riemannXi Set.univ u) ∧
      (∀ u : ℂ, ‖u‖ ≤ r → m u ≠ 0 → u ∈ S) ∧
      (∀ z : ℂ, ‖z‖ ≤ r / 4 → z ∉ S →
        ‖logDeriv riemannXi z - ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ)‖
          ≤ 8 * (Real.log (M r) + Real.log 2 + 1) / r) := by
    intro r
    rcases le_or_gt r 0 with h | h
    · exact ⟨∅, fun _ => 0, fun hc => absurd hc (not_lt.mpr h)⟩
    · obtain ⟨S, m, h1, h2, h3, h4, h5, h6⟩ := Cvs.ZeroFree.exists_landau_riemannXi h (hMbd r)
      exact ⟨S, m, fun _ => ⟨h1, h2, h3, h4, h5, h6⟩⟩
  choose Sl ml hSl using hex
  -- Hadamard
  obtain ⟨h, hhdiff, hprod, hHad⟩ := Cvs.ZeroFree.exists_hadamard_xiD
  -- the near index sets, and that they omit nothing of small modulus
  have hN : ∀ᶠ r : ℝ in atTop,
      ∀ n, n ∉ Cvs.ZeroFree.nearIdx (Sl r) → r < ‖zeroSeq riemannXi n‖ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr n hn
    by_contra hc
    push Not at hc
    obtain ⟨-, -, -, hmdiv, hcomplete, -⟩ := hSl r hr
    refine hn ?_
    rw [Cvs.ZeroFree.nearIdx, Cvs.ZeroFree.mem_sigmaFinset]
    refine hcomplete _ hc ?_
    intro h0
    refine Cvs.ZeroFree.divisor_zeroSeq_ne_zero n ?_
    show ((MeromorphicOn.divisor riemannXi Set.univ ((n.1 : ℂ)) : ℤ)) = 0
    rw [← hmdiv, h0]
    simp
  -- Landau's bound, in the criterion's shape
  have hL : ∀ᶠ r : ℝ in atTop, ∀ z ∈ Metric.ball (0 : ℂ) (r / 4),
      z ∉ Cvs.ZeroFree.xiExceptional →
      ‖Cvs.ZeroFree.xiD z - ∑ n ∈ Cvs.ZeroFree.nearIdx (Sl r), 1 / (z - zeroSeq riemannXi n)‖
        ≤ 8 * (Real.log (M r) + Real.log 2 + 1) / r := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr z hz hzE
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
    obtain ⟨-, -, hzeroS, hmdiv, hcomplete, hbound⟩ := hSl r hr0
    have hzS : z ∉ Sl r := by
      intro hc
      exact Cvs.ZeroFree.riemannXi_ne_zero_of_notMem hzE (hzeroS z hc)
    have hznorm : ‖z‖ ≤ r / 4 := by
      rw [Metric.mem_ball, dist_zero_right] at hz
      exact hz.le
    have hb := hbound z hznorm hzS
    rw [Cvs.ZeroFree.landau_sum_split hr hmdiv hcomplete z] at hb
    have hrw : logDeriv riemannXi z
        - (Cvs.ZeroFree.smallSum z + ∑ n ∈ Cvs.ZeroFree.nearIdx (Sl r), 1 / (z - zeroSeq riemannXi n))
        = Cvs.ZeroFree.xiD z - ∑ n ∈ Cvs.ZeroFree.nearIdx (Sl r), 1 / (z - zeroSeq riemannXi n) := by
      rw [Cvs.ZeroFree.xiD]; ring
    rwa [hrw] at hb
  -- the two limits
  have hB : Tendsto (fun r : ℝ => 8 * (8 * (Real.log (M r) + Real.log 2 + 1) / r) / r)
      atTop (nhds 0) := by
    refine (Cvs.ZeroFree.tendsto_landau_over_sq (A := A) hCpos).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    rw [hMdef]
    field_simp
    ring
  have hε := Cvs.ZeroFree.tendsto_tsum_compl summable_inv_norm_sq_riemannXi hN
  -- the criterion
  obtain ⟨c, b, hcb⟩ := Cvs.ZeroFree.landau_criterion hhdiff summable_inv_norm_sq_riemannXi
    (fun n => one_le_norm_zeroSeq n) Cvs.ZeroFree.countable_xiExceptional
    Cvs.ZeroFree.range_subset_xiExceptional hN hHad hL hB hε
  have hfun : h = fun w : ℂ => c * w + b := funext hcb
  have hderiv : ∀ w : ℂ, deriv h w = c := by
    intro w
    rw [hfun]
    simp
  refine ⟨c, b, fun z => ?_, fun z hz => ?_⟩
  · rw [hprod z, hcb z]
  · have hd := hHad z hz
    rw [Cvs.ZeroFree.xiD, hderiv z] at hd
    linear_combination hd

/-- **Rung 3, as `Cvs.Zeta` states its gap.**  `ξ'/ξ` is the pole sum plus a constant. -/
theorem exists_const_logDeriv_riemannXi :
    ∃ B : ℂ, ∀ z : ℂ, z ∉ Cvs.ZeroFree.xiExceptional →
      logDeriv riemannXi z
        = Cvs.ZeroFree.smallSum z
          + ((∑' n : zeroIndex riemannXi,
              (1 / (z - zeroSeq riemannXi n) + 1 / zeroSeq riemannXi n)) + B) := by
  obtain ⟨c, -, -, hlog⟩ := exists_affine_exponent_riemannXi
  exact ⟨c, hlog⟩

end Cvs.ZeroFree
