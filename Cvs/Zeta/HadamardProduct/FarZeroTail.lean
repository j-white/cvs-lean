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
import Cvs.Zeta.HadamardProduct.ShiftedSquareZeroSum

/-!
# The far-zero tail, and why it is the easy half of `ε r → 0`
-/

noncomputable section

open Complex Filter Topology Metric

namespace Cvs.ZeroFree

variable {ι : Type*} {a : ι → ℂ}

/-- The termwise comparison, squared: `‖(z − aₙ)⁻²‖ ≤ 4‖aₙ‖⁻²` when `2‖z‖ ≤ ‖aₙ‖`. -/
theorem norm_inv_sub_sq_le {z w : ℂ} (hw : 0 < ‖w‖) (h : 2 * ‖z‖ ≤ ‖w‖) :
    ‖-(1 / (z - w) ^ 2)‖ ≤ 4 * ‖w‖⁻¹ ^ 2 := by
  have hb := Cvs.ZeroFree.norm_inv_sub_le hw h
  have h0 : (0 : ℝ) ≤ ‖(z - w)⁻¹‖ := norm_nonneg _
  have hnn : (0 : ℝ) ≤ 2 * ‖w‖⁻¹ := by positivity
  rw [norm_neg, one_div, norm_inv, ← norm_inv]
  rw [show ((z - w) ^ 2)⁻¹ = ((z - w)⁻¹) ^ 2 by rw [inv_pow], norm_pow]
  nlinarith

/-- The squared series converges on a ball the zeros keep away from. -/
theorem summable_norm_far (ha : Summable fun n => ‖a n‖⁻¹ ^ 2)
    {R : ℝ} (hR : 0 < R) (hfar : ∀ n, 4 * R ≤ ‖a n‖) {z : ℂ} (hz : ‖z‖ < R) :
    Summable fun n => ‖-(1 / (z - a n) ^ 2)‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (ha.mul_left 4)
  have han : (0 : ℝ) < ‖a n‖ := lt_of_lt_of_le (by linarith) (hfar n)
  exact norm_inv_sub_sq_le han (by linarith [hfar n])

/-- **The far-zero contribution to `h''`, bounded by a tail of `Σ ‖aₙ‖⁻²`.** -/
theorem norm_tsum_far_le (ha : Summable fun n => ‖a n‖⁻¹ ^ 2)
    {R : ℝ} (hR : 0 < R) (hfar : ∀ n, 4 * R ≤ ‖a n‖) {z : ℂ} (hz : ‖z‖ < R) :
    ‖∑' n, -(1 / (z - a n) ^ 2)‖ ≤ ∑' n, 4 * ‖a n‖⁻¹ ^ 2 := by
  refine le_trans (norm_tsum_le_tsum_norm (summable_norm_far ha hR hfar hz)) ?_
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_norm_far ha hR hfar hz)
    (ha.mul_left 4)
  have han : (0 : ℝ) < ‖a n‖ := lt_of_lt_of_le (by linarith) (hfar n)
  exact norm_inv_sub_sq_le han (by linarith [hfar n])

/-! ### The tail tends to zero -/

/-- The part of `Σ 4‖aₙ‖⁻²` carried by the zeros outside the disc of radius `r`. -/
def farTail (a : ι → ℂ) (r : ℝ) : ℝ :=
  ∑' n, if r < ‖a n‖ then 4 * ‖a n‖⁻¹ ^ 2 else 0

theorem summable_farTail (ha : Summable fun n => ‖a n‖⁻¹ ^ 2) (r : ℝ) :
    Summable fun n => if r < ‖a n‖ then 4 * ‖a n‖⁻¹ ^ 2 else 0 := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (ha.mul_left 4)
  · split
    · positivity
    · exact le_refl 0
  · split
    · exact le_refl _
    · positivity

theorem farTail_nonneg (a : ι → ℂ) (r : ℝ) : 0 ≤ farTail a r :=
  tsum_nonneg fun n => by split <;> positivity

/-- **`Σ_{‖aₙ‖ > r} 4‖aₙ‖⁻² → 0`.**  A tail of a convergent sum, nothing more. -/
theorem tendsto_farTail (ha : Summable fun n => ‖a n‖⁻¹ ^ 2) :
    Tendsto (farTail a) atTop (nhds 0) := by
  classical
  refine Metric.tendsto_atTop.mpr fun δ hδ => ?_
  obtain ⟨F, hF⟩ :=
    ((tendsto_tsum_compl_atTop_zero (fun n => 4 * ‖a n‖⁻¹ ^ 2)).eventually
      (gt_mem_nhds hδ)).exists
  refine ⟨∑ n ∈ F, ‖a n‖, fun r hr => ?_⟩
  set g : ι → ℝ := fun n => if r < ‖a n‖ then 4 * ‖a n‖⁻¹ ^ 2 else 0 with hg
  have hgs : Summable g := summable_farTail ha r
  have hFzero : ∑ n ∈ F, g n = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    have hle : ‖a n‖ ≤ ∑ m ∈ F, ‖a m‖ :=
      Finset.single_le_sum (fun m _ => norm_nonneg (a m)) hn
    simp only [hg, if_neg (not_lt.mpr (le_trans hle hr))]
  have hsplit : ∑ n ∈ F, g n + ∑' n : {x // x ∉ F}, g n = farTail a r :=
    hgs.sum_add_tsum_subtype_compl F
  have hcmp : ∑' n : {x // x ∉ F}, g n ≤ ∑' n : {x // x ∉ F}, 4 * ‖a (n : ι)‖⁻¹ ^ 2 := by
    refine Summable.tsum_le_tsum (fun n => ?_) (hgs.subtype _) ((ha.mul_left 4).subtype _)
    simp only [hg]
    split
    · exact le_refl _
    · positivity
  have hlt : ∑' n : {x // x ∉ F}, 4 * ‖a (n : ι)‖⁻¹ ^ 2 < δ := hF
  have : farTail a r < δ := by
    rw [← hsplit, hFzero, zero_add]
    exact lt_of_le_of_lt hcmp hlt
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (farTail_nonneg a r)]
  exact this

end Cvs.ZeroFree
