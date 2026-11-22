import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Cvs.Zeta.HadamardProduct.AffineFromBoundedApprox
import Cvs.Zeta.HadamardProduct.LandauRearrangement

/-!
# Across the zeros, and the assembled criterion

Two things finish the abstract half of rung 3.
-/

noncomputable section

open Complex Filter Topology Metric

namespace Cvs.ZeroFree

/-- **A holomorphic function bounded off a countable set is bounded.**  The exceptional set
here is the zero set, where `LandauRearrangement`'s rearrangement is silent. -/
theorem norm_le_of_countable_exceptional {H : ℂ → ℂ} {U E : Set ℂ} {B : ℝ}
    (hU : IsOpen U) (hH : ∀ z ∈ U, ContinuousAt H z) (hE : E.Countable)
    (hb : ∀ z ∈ U, z ∉ E → ‖H z‖ ≤ B) :
    ∀ z ∈ U, ‖H z‖ ≤ B := by
  intro z hz
  have hdense : Dense Eᶜ := Set.Countable.dense_compl ℂ hE
  have hsub : U ⊆ closure (U ∩ Eᶜ) := hdense.open_subset_closure_inter hU
  have hnb : (nhdsWithin z (U ∩ Eᶜ)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hsub hz)
  have hcont : Tendsto (fun w => ‖H w‖) (nhdsWithin z (U ∩ Eᶜ)) (nhds ‖H z‖) :=
    ((hH z hz).norm).continuousWithinAt
  refine le_of_tendsto hcont ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact hb w hw.1 hw.2

variable {ι : Type*} {a : ι → ℂ}

/-- **Rung 3's criterion, with the zeros as a single family.** An entire `h` is affine as soon
as Landau's bound and Hadamard's identity hold at the two limits. -/
theorem landau_criterion {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (ha : Summable fun n => ‖a n‖⁻¹ ^ 2) (h1 : ∀ n, 1 ≤ ‖a n‖)
    {E : Set ℂ} (hcount : E.Countable) (haE : Set.range a ⊆ E)
    {D : ℂ → ℂ} {N : ℝ → Finset ι} {B : ℝ → ℝ}
    (hN : ∀ᶠ r : ℝ in atTop, ∀ n, n ∉ N r → r < ‖a n‖)
    (hHad : ∀ z : ℂ, z ∉ E →
      D z = (∑' n, (1 / (z - a n) + 1 / a n)) + deriv h z)
    (hL : ∀ᶠ r : ℝ in atTop, ∀ z ∈ ball (0 : ℂ) (r / 4), z ∉ E →
      ‖D z - ∑ n ∈ N r, 1 / (z - a n)‖ ≤ B r)
    (hB : Tendsto (fun r => 8 * B r / r) atTop (nhds 0))
    (hε : Tendsto (fun r => ∑' n : {x : ι // x ∉ N r}, 4 * ‖a (n : ι)‖⁻¹ ^ 2)
      atTop (nhds 0)) :
    ∃ c b : ℂ, ∀ z, h z = c * z + b := by
  classical
  set G : ℝ → ℂ → ℂ :=
    fun r w => Cvs.ZeroFree.farSum a (N r) w + Cvs.ZeroFree.nearConst a (N r) with hGdef
  have hderivDiff : Differentiable ℂ (deriv h) := by
    have hana : AnalyticOnNhd ℂ h Set.univ := hh.differentiableOn.analyticOnNhd isOpen_univ
    intro z
    exact ((hana.deriv_of_isOpen isOpen_univ) z (Set.mem_univ z)).differentiableAt
  have hbase : ∀ᶠ r : ℝ in atTop, 0 < r ∧ ∀ n, n ∉ N r → r < ‖a n‖ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hN] with r hr hn
    exact ⟨hr, hn⟩
  -- `G r` is holomorphic on the ball
  have hG : ∀ᶠ r : ℝ in atTop, DifferentiableOn ℂ (G r) (ball (0 : ℂ) (r / 4)) := by
    filter_upwards [hbase] with r hr
    exact Cvs.ZeroFree.differentiableOn_farSum ha hr.1 hr.2
  -- the Landau bound, extended across the zeros
  have hbd : ∀ᶠ r : ℝ in atTop, ∀ z ∈ ball (0 : ℂ) (r / 4),
      ‖deriv h z + G r z‖ ≤ B r := by
    filter_upwards [hG, hL] with r hGr hLr
    refine norm_le_of_countable_exceptional isOpen_ball (fun z hz => ?_) hcount ?_
    · exact ((hderivDiff z).add
        (hGr.differentiableAt (isOpen_ball.mem_nhds hz))).continuousAt
    · intro z hz hzE
      have hzn : ∀ n, z ≠ a n := by
        intro n hc
        exact hzE (haE ⟨n, hc.symm⟩)
      exact Cvs.ZeroFree.norm_le_of_landau ha h1 hzn (hHad z hzE) (hLr z hz hzE)
  -- the derivative of `G r` is the far tail
  have hGd : ∀ᶠ r : ℝ in atTop, ∀ z ∈ ball (0 : ℂ) (r / 8),
      ‖deriv (G r) z‖ ≤ ∑' n : {x : ι // x ∉ N r}, 4 * ‖a (n : ι)‖⁻¹ ^ 2 := by
    filter_upwards [hbase] with r hr z hz
    rw [mem_ball, dist_zero_right] at hz
    exact Cvs.ZeroFree.norm_deriv_farSum_le ha hr.1 hr.2 (by linarith [hr.1])
  exact Cvs.ZeroFree.affine_of_bounded_approx hh hG hbd hGd hB hε

end Cvs.ZeroFree
