import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Cvs.Zeta.HadamardProduct.GenusOneFactorLogDeriv
import Cvs.Zeta.HadamardProduct.ShiftedSquareZeroSum

/-!
# Differentiating the genus-1 logarithmic derivative term by term

`CanonicalProductLogDeriv` gives, for a genus-1 canonical product `P(w) = ∏ₙ E₁(w/aₙ)`,
-/

noncomputable section

open Complex Metric

namespace Cvs.ZeroFree

variable {ι : Type*} {a : ι → ℂ}

/-- **The genus-1 term vanishes at the origin.**  No hypothesis on `a`: when `a = 0` both
halves are `1/0 = 0`. -/
theorem genus_one_at_zero (w : ℂ) : 1 / ((0 : ℂ) - w) + 1 / w = 0 := by
  rw [zero_sub, div_neg, neg_add_cancel]

/-- **Term-by-term differentiation of the genus-1 series** on a ball the zeros stay away from:
d/dz Σₙ [1/(z − aₙ) + 1/aₙ] = Σₙ −(z − aₙ)⁻² for `‖z‖ < R`, `4R ≤ ‖aₙ‖`. -/
theorem hasDerivAt_tsum_genus_one (ha : Summable fun n => ‖a n‖⁻¹ ^ 2)
    {R : ℝ} (hR : 0 < R) (hfar : ∀ n, 4 * R ≤ ‖a n‖) {z : ℂ} (hz : ‖z‖ < R) :
    HasDerivAt (fun w : ℂ => ∑' n, (1 / (w - a n) + 1 / a n))
      (∑' n, -(1 / (z - a n) ^ 2)) z := by
  have hane : ∀ n, a n ≠ 0 := by
    intro n
    have : (0 : ℝ) < ‖a n‖ := lt_of_lt_of_le (by linarith) (hfar n)
    exact norm_pos_iff.mp this
  have hball : ∀ w : ℂ, w ∈ ball (0 : ℂ) R → ∀ n, 2 * ‖w‖ ≤ ‖a n‖ := by
    intro w hw n
    rw [mem_ball, dist_zero_right] at hw
    linarith [hfar n]
  have hne : ∀ w : ℂ, w ∈ ball (0 : ℂ) R → ∀ n, w ≠ a n := by
    intro w hw n hc
    have h2 := hball w hw n
    rw [← hc] at h2
    rw [mem_ball, dist_zero_right] at hw
    have : (0 : ℝ) < ‖w‖ := by
      rcases eq_or_lt_of_le (norm_nonneg w) with h | h
      · exfalso
        have hw0 : w = 0 := by rw [← norm_eq_zero]; exact h.symm
        rw [hw0] at hc
        exact hane n hc.symm
      · exact h
    linarith
  refine hasDerivAt_tsum_of_isPreconnected (u := fun n => 4 * ‖a n‖⁻¹ ^ 2)
    (g := fun n (w : ℂ) => 1 / (w - a n) + 1 / a n)
    (g' := fun n (w : ℂ) => -(1 / (w - a n) ^ 2)) (y₀ := (0 : ℂ))
    (ha.mul_left 4) isOpen_ball (convex_ball (0 : ℂ) R).isPreconnected
    (fun n w hw => ?_) (fun n w hw => ?_) (mem_ball_self hR) ?_ (by
      rw [mem_ball, dist_zero_right]; exact hz)
  · exact Cvs.ZeroFree.hasDerivAt_logDeriv_term (hne w hw n)
  · have h2 := hball w hw n
    have han : (0 : ℝ) < ‖a n‖ := lt_of_lt_of_le (by linarith) (hfar n)
    have hb := Cvs.ZeroFree.norm_inv_sub_le han h2
    have h0 : (0 : ℝ) ≤ ‖(w - a n)⁻¹‖ := norm_nonneg _
    have hnn : (0 : ℝ) ≤ 2 * ‖a n‖⁻¹ := by positivity
    rw [norm_neg, one_div, norm_inv, ← norm_inv]
    rw [show ((w - a n) ^ 2)⁻¹ = ((w - a n)⁻¹) ^ 2 by rw [inv_pow], norm_pow]
    nlinarith
  · simpa only [genus_one_at_zero] using summable_zero

end Cvs.ZeroFree
