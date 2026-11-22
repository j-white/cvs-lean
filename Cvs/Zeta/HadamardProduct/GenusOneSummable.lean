import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Cvs.Zeta.HadamardProduct.ShiftedSquareZeroSum

/-!
# The genus-1 series is summable
-/

open Complex Filter Topology

namespace Cvs.ZeroFree

variable {ι : Type*} {a : ι → ℂ}

/-- **The genus-1 term, combined.**  `1/(z-a) + 1/a = z/(a(z-a))` — the cancellation that makes
the series converge like `Σ‖a‖⁻²` instead of `Σ‖a‖⁻¹`. -/
theorem genus_one_term_eq {z w : ℂ} (hw : w ≠ 0) (hzw : z ≠ w) :
    1 / (z - w) + 1 / w = z / (w * (z - w)) := by
  have hzw' : z - w ≠ 0 := sub_ne_zero_of_ne hzw
  field_simp
  ring

/-- And so it is `O(‖z‖·‖a‖⁻²)` far from `z`. -/
theorem norm_genus_one_term_le {z w : ℂ} (hw : 0 < ‖w‖) (h : 2 * ‖z‖ ≤ ‖w‖) (hzw : z ≠ w) :
    ‖1 / (z - w) + 1 / w‖ ≤ 2 * ‖z‖ * ‖w‖⁻¹ ^ 2 := by
  have hw0 : w ≠ 0 := norm_pos_iff.mp hw
  rw [genus_one_term_eq hw0 hzw, norm_div, norm_mul]
  have hzw' : ‖w‖ / 2 ≤ ‖z - w‖ := by
    have h1 := norm_sub_norm_le w z
    rw [norm_sub_rev] at h1
    linarith [norm_nonneg z]
  have hpos : (0 : ℝ) < ‖z - w‖ := lt_of_lt_of_le (by linarith) hzw'
  rw [div_le_iff₀ (by positivity)]
  have hwne : ‖w‖ ≠ 0 := ne_of_gt hw
  have hsimp : 2 * ‖z‖ * ‖w‖⁻¹ ^ 2 * (‖w‖ * ‖z - w‖) = 2 * ‖z‖ * ‖w‖⁻¹ * ‖z - w‖ := by
    field_simp
  rw [hsimp]
  have hstep : 2 * ‖z‖ * ‖w‖⁻¹ * (‖w‖ / 2) ≤ 2 * ‖z‖ * ‖w‖⁻¹ * ‖z - w‖ :=
    mul_le_mul_of_nonneg_left hzw' (by positivity)
  have hval : 2 * ‖z‖ * ‖w‖⁻¹ * (‖w‖ / 2) = ‖z‖ := by field_simp
  linarith

/-- **The genus-1 series converges.** This is `φ'/φ` as a sum over the zeros: produced it as a
`HasSum` at each point, and this says the family is summable outright, which is what
term-by-term differentiation needs as its starting hypothesis. -/
theorem summable_genus_one (ha : Summable fun n => ‖a n‖⁻¹ ^ 2)
    (h1 : ∀ n, 1 ≤ ‖a n‖) {z : ℂ} (hz : ∀ n, z ≠ a n) :
    Summable fun n => 1 / (z - a n) + 1 / a n := by
  refine Summable.of_norm_bounded_eventually (g := fun n => 2 * ‖z‖ * ‖a n‖⁻¹ ^ 2)
    (ha.mul_left _) ?_
  filter_upwards [Cvs.ZeroFree.eventually_two_norm_le ha h1 z] with n hn
  have han : (0 : ℝ) < ‖a n‖ := lt_of_lt_of_le zero_lt_one (h1 n)
  exact norm_genus_one_term_le han hn (hz n)

end Cvs.ZeroFree
