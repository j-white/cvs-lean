import Mathlib
import Cvs.WeilForm.GaussianRegulariser

/-!
# The Gaussian kernel is an approximate identity

    ∫ h x · gaussHat c x dx → h 0     as `c → 0`

for bounded `h` continuous at the origin.  Rescaling by `√c` turns the kernel into a fixed
Gaussian and the argument into one dominated convergence.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter

namespace Cvs.Upstream.GaussianApproximateIdentity

/-- The unit Gaussian. -/
def unitGauss (y : ℝ) : ℝ := Real.exp (-π * y ^ 2)

theorem integrable_unitGauss : Integrable unitGauss (volume : Measure ℝ) := by
  have := integrable_exp_neg_mul_sq (b := π) pi_pos
  exact this

theorem integral_unitGauss : (∫ y : ℝ, unitGauss y) = 1 := by
  unfold unitGauss
  have h : (∫ y : ℝ, Real.exp (-π * y ^ 2)) = Real.sqrt (π / π) := integral_gaussian π
  rw [h, div_self (ne_of_gt pi_pos), Real.sqrt_one]

/-- **The kernel, rescaled, is a fixed Gaussian.** -/
theorem integral_gaussHat_rescale {c : ℝ} (hc : 0 < c) (h : ℝ → ℝ)
    (hint : Integrable (fun x : ℝ => h x * Cvs.WeilForm.GaussianRegulariser.gaussHat c x)
      (volume : Measure ℝ)) :
    (∫ x : ℝ, h x * Cvs.WeilForm.GaussianRegulariser.gaussHat c x)
      = ∫ y : ℝ, h (Real.sqrt c * y) * unitGauss y := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hcv := MeasureTheory.Measure.integral_comp_mul_left
    (fun x : ℝ => h x * Cvs.WeilForm.GaussianRegulariser.gaussHat c x) (Real.sqrt c)
  rw [abs_of_pos (inv_pos.mpr hsc), smul_eq_mul] at hcv
  have hker : ∀ y : ℝ, Cvs.WeilForm.GaussianRegulariser.gaussHat c (Real.sqrt c * y)
      = (Real.sqrt c)⁻¹ * unitGauss y := by
    intro y
    rw [Cvs.WeilForm.GaussianRegulariser.gaussHat, unitGauss]
    congr 1
    congr 1
    have hsq : (Real.sqrt c * y) ^ 2 = c * y ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc.le]
    rw [hsq]
    field_simp
  have hleft : (∫ y : ℝ, h (Real.sqrt c * y) * Cvs.WeilForm.GaussianRegulariser.gaussHat c
      (Real.sqrt c * y)) = (Real.sqrt c)⁻¹ * ∫ y : ℝ, h (Real.sqrt c * y) * unitGauss y := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [hker y]
    ring
  rw [hleft] at hcv
  have : (Real.sqrt c)⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hsc)
  field_simp at hcv
  linarith [hcv]

/-- **The kernel is an approximate identity.** -/
theorem tendsto_integral_gaussHat {h : ℝ → ℝ} {M : ℝ}
    (hmeas : Measurable h) (hbd : ∀ x, |h x| ≤ M) (hcont : ContinuousAt h 0)
    (hint : ∀ c : ℝ, 0 < c → Integrable (fun x : ℝ => h x * Cvs.WeilForm.GaussianRegulariser.gaussHat c x)
      (volume : Measure ℝ)) :
    Tendsto (fun n : ℕ =>
        ∫ x : ℝ, h x * Cvs.WeilForm.GaussianRegulariser.gaussHat (1 / ((n : ℝ) + 1)) x)
      atTop (nhds (h 0)) := by
  set c : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hc
  have hcpos : ∀ n, 0 < c n := fun n => by rw [hc]; positivity
  -- rescale each integral
  have hrw : ∀ n, (∫ x : ℝ, h x * Cvs.WeilForm.GaussianRegulariser.gaussHat (c n) x)
      = ∫ y : ℝ, h (Real.sqrt (c n) * y) * unitGauss y := fun n =>
    integral_gaussHat_rescale (hcpos n) h (hint _ (hcpos n))
  -- the rescaled arguments go to zero
  have hczero : Tendsto (fun n : ℕ => Real.sqrt (c n)) atTop (nhds 0) := by
    have h1 : Tendsto c atTop (nhds 0) := by
      rw [hc]; exact tendsto_one_div_add_atTop_nhds_zero_nat
    have := (Real.continuous_sqrt.tendsto 0).comp h1
    simpa [Function.comp_def] using this
  -- dominated convergence
  have hlim : Tendsto (fun n : ℕ => ∫ y : ℝ, h (Real.sqrt (c n) * y) * unitGauss y) atTop
      (nhds (∫ y : ℝ, h 0 * unitGauss y)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => M * unitGauss y) ?_ ?_ (integrable_unitGauss.const_mul M) ?_
    · filter_upwards with n
      exact ((hmeas.comp (measurable_const.mul measurable_id)).mul
        (by unfold unitGauss; fun_prop)).aestronglyMeasurable
    · filter_upwards with n
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_mul]
      have hu : |unitGauss y| = unitGauss y := abs_of_nonneg (Real.exp_pos _).le
      rw [hu]
      exact mul_le_mul_of_nonneg_right (hbd _) (Real.exp_pos _).le
    · filter_upwards with y
      have harg : Tendsto (fun n : ℕ => Real.sqrt (c n) * y) atTop (nhds 0) := by
        have := hczero.mul_const y
        simpa using this
      have := (hcont.tendsto.comp harg)
      exact (this.mul_const (unitGauss y))
  rw [integral_const_mul, integral_unitGauss, mul_one] at hlim
  exact Tendsto.congr (fun n => (hrw n).symm) hlim

end Cvs.Upstream.GaussianApproximateIdentity
