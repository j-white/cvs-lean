import Mathlib

/-!
# A mollifier of every radius

    `kernel hδ` is continuous, nonnegative, of unit mass, and supported in `[−δ, δ]`

Mathlib's normalised bump function, with the seven properties the mollification blocks ask
for, read off in one place.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter

namespace Cvs.WeilForm.Mollify.MollifierKernel

/-- The bump of radius `δ`. -/
def bump {δ : ℝ} (hδ : 0 < δ) : ContDiffBump (0:ℝ) :=
  { rIn := δ / 2
    rOut := δ
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith }

/-- **The mollifier of radius `δ`.** -/
def kernel {δ : ℝ} (hδ : 0 < δ) : ℝ → ℝ := (bump hδ).normed (volume : Measure ℝ)

theorem continuous_kernel {δ : ℝ} (hδ : 0 < δ) : Continuous (kernel hδ) :=
  ContDiffBump.continuous_normed _

theorem measurable_kernel {δ : ℝ} (hδ : 0 < δ) : Measurable (kernel hδ) :=
  (continuous_kernel hδ).measurable

theorem hasCompactSupport_kernel {δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (kernel hδ) :=
  ContDiffBump.hasCompactSupport_normed _

theorem integrable_kernel {δ : ℝ} (hδ : 0 < δ) : Integrable (kernel hδ) (volume : Measure ℝ) :=
  (continuous_kernel hδ).integrable_of_hasCompactSupport (hasCompactSupport_kernel hδ)

theorem kernel_nonneg {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : 0 ≤ kernel hδ t :=
  ContDiffBump.nonneg_normed _ _

theorem integral_kernel {δ : ℝ} (hδ : 0 < δ) : (∫ t : ℝ, kernel hδ t) = 1 :=
  ContDiffBump.integral_normed _

/-- **The mollifier's radius.** -/
theorem kernel_eq_zero {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : δ < |t|) : kernel hδ t = 0 := by
  have hsupp : Function.support (kernel hδ) = Metric.ball (0:ℝ) δ := by
    rw [kernel]
    exact ContDiffBump.support_normed_eq _
  by_contra hne
  have hmem : t ∈ Metric.ball (0:ℝ) δ := by
    rw [← hsupp]
    exact Function.mem_support.mpr hne
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hmem
  exact absurd hmem (not_lt.mpr ht.le)

end Cvs.WeilForm.Mollify.MollifierKernel
