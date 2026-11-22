import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# The shifted square sum over the zeros
-/

open Complex Filter Topology

namespace Cvs.ZeroFree

variable {ι : Type*} {a : ι → ℂ}

/-- Far from `z`, the shifted inverse is comparable to the unshifted one. -/
theorem norm_inv_sub_le {z w : ℂ} (hw : 0 < ‖w‖) (h : 2 * ‖z‖ ≤ ‖w‖) :
    ‖(z - w)⁻¹‖ ≤ 2 * ‖w‖⁻¹ := by
  have hzw : ‖w‖ / 2 ≤ ‖z - w‖ := by
    have h1 := norm_sub_norm_le w z
    rw [norm_sub_rev] at h1
    linarith [norm_nonneg z]
  have hpos : (0 : ℝ) < ‖z - w‖ := lt_of_lt_of_le (by linarith) hzw
  rw [norm_inv, inv_le_iff_one_le_mul₀ hpos]
  have hwinv : ‖w‖ * ‖w‖⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hw)
  have hinvpos : (0 : ℝ) < ‖w‖⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hzw hinvpos.le, hwinv.le, hwinv.ge]

/-- Summability of `‖aₙ‖⁻²` with `‖aₙ‖ ≥ 1` pushes `‖aₙ‖` past any bound, off a finite set. -/
theorem eventually_two_norm_le (ha : Summable fun n => ‖a n‖⁻¹ ^ 2)
    (h1 : ∀ n, 1 ≤ ‖a n‖) (z : ℂ) :
    ∀ᶠ n in cofinite, 2 * ‖z‖ ≤ ‖a n‖ := by
  set M : ℝ := 2 * ‖z‖ + 1 with hM
  have hM0 : (0 : ℝ) < M := by
    have := norm_nonneg z; rw [hM]; linarith
  have hz0 : Tendsto (fun n => ‖a n‖⁻¹ ^ 2) cofinite (nhds 0) := ha.tendsto_cofinite_zero
  have ht : (0 : ℝ) < (M⁻¹) ^ 2 := by positivity
  filter_upwards [hz0.eventually (gt_mem_nhds ht)] with n hn
  have han : (0 : ℝ) < ‖a n‖ := lt_of_lt_of_le zero_lt_one (h1 n)
  have h0 : (0 : ℝ) ≤ ‖a n‖⁻¹ := by positivity
  have hlt : ‖a n‖⁻¹ < M⁻¹ :=
    lt_of_pow_lt_pow_left₀ 2 (le_of_lt (inv_pos.mpr hM0)) hn
  have : M < ‖a n‖ := by
    have := (inv_lt_inv₀ han hM0).mp hlt
    linarith
  rw [hM] at this
  linarith

end Cvs.ZeroFree
