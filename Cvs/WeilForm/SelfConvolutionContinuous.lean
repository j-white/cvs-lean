import Mathlib
import Cvs.Upstream.CauchySchwarzLine
import Cvs.Upstream.L2TranslationContinuity
import Cvs.Zeta.WeilPositivityStatement

/-!
# The self-convolution of an L² function is continuous

    |g v − g u| ≤ ‖f‖₂ · √(∫ (f t − f (t + (v−u)))²)

so continuity of the self-convolution is translation continuity in `L²`, evaluated at the
shift between the two points.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.SelfConvolutionContinuous

/-- The shifted difference, re-centred. -/
theorem integral_shift_diff_sq {f : ℝ → ℝ} (u v : ℝ) :
    (∫ s : ℝ, (f (s + v) - f (s + u)) ^ 2)
      = ∫ t : ℝ, (f t - f (t + (v - u))) ^ 2 := by
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun t : ℝ => (f t - f (t + (v - u))) ^ 2) u
  refine Eq.trans ?_ h
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only
  rw [show s + u + (v - u) = s + v by ring]
  ring

/-- **The self-convolution is continuous.** -/
theorem continuous_selfConvolution {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ)) :
    Continuous (selfConvolution f) := by
  set E : ℝ := Real.sqrt (∫ x : ℝ, f x ^ 2) with hE
  have hEnn : 0 ≤ E := Real.sqrt_nonneg _
  refine Metric.continuous_iff.mpr fun u ε hε => ?_
  -- the translation modulus we may spend
  set ε' : ℝ := (ε / (E + 1)) ^ 2 with hε'
  have hε'pos : 0 < ε' := by rw [hε']; positivity
  have htr := Cvs.Upstream.L2TranslationContinuity.tendsto_integral_sub_translate_sq hf
  rw [Metric.tendsto_nhds] at htr
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp (htr ε' hε'pos)
  refine ⟨δ, hδpos, fun v hv => ?_⟩
  -- Cauchy-Schwarz against the shifted difference
  have hfv : MemLp (fun s => f (s + v)) 2 (volume : Measure ℝ) :=
    hf.comp_measurePreserving (measurePreserving_add_right (volume : Measure ℝ) v)
  have hfu : MemLp (fun s => f (s + u)) 2 (volume : Measure ℝ) :=
    hf.comp_measurePreserving (measurePreserving_add_right (volume : Measure ℝ) u)
  have hdiff : MemLp (fun s => f (s + v) - f (s + u)) 2 (volume : Measure ℝ) := hfv.sub hfu
  have hIv : Integrable (fun s => f s * f (s + v)) (volume : Measure ℝ) := hf.integrable_mul hfv
  have hIu : Integrable (fun s => f s * f (s + u)) (volume : Measure ℝ) := hf.integrable_mul hfu
  have hsplit : selfConvolution f v - selfConvolution f u
      = ∫ s : ℝ, f s * (f (s + v) - f (s + u)) := by
    have h1 : selfConvolution f v = ∫ s : ℝ, f s * f (s + v) := rfl
    have h2 : selfConvolution f u = ∫ s : ℝ, f s * f (s + u) := rfl
    rw [h1, h2, ← integral_sub hIv hIu]
    exact integral_congr_ae (Filter.Eventually.of_forall fun s => by ring)
  have hcs := Cvs.Upstream.CauchySchwarzLine.abs_integral_mul_le hf hdiff
  -- the shifted difference is small
  have hshift : (∫ s : ℝ, (f (s + v) - f (s + u)) ^ 2) < ε' := by
    have hdv : dist v u < δ := hv
    have := hδ (y := v - u) (by
      rw [Real.dist_eq, sub_zero]
      rw [Real.dist_eq] at hdv
      exact hdv)
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (integral_nonneg fun t => sq_nonneg _)] at this
    rw [integral_shift_diff_sq]
    exact this
  have hbound : Real.sqrt (∫ s : ℝ, (f (s + v) - f (s + u)) ^ 2) ≤ ε / (E + 1) := by
    have h1 : Real.sqrt (∫ s : ℝ, (f (s + v) - f (s + u)) ^ 2) ≤ Real.sqrt ε' :=
      Real.sqrt_le_sqrt hshift.le
    rwa [hε', Real.sqrt_sq (by positivity)] at h1
  rw [Real.dist_eq, hsplit]
  calc |∫ s : ℝ, f s * (f (s + v) - f (s + u))|
      ≤ E * Real.sqrt (∫ s : ℝ, (f (s + v) - f (s + u)) ^ 2) := hcs
    _ ≤ E * (ε / (E + 1)) := mul_le_mul_of_nonneg_left hbound hEnn
    _ < ε := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [hEnn, hε]

end Cvs.WeilForm.SelfConvolutionContinuous
