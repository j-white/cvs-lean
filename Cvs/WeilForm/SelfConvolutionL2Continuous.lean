import Mathlib
import Cvs.Upstream.CauchySchwarzLine
import Cvs.Zeta.WeilPositivityStatement

/-!
# The self-convolution moves continuously with its function in L²

    |g_f(u) − g_h(u)| ≤ ‖f − h‖₂ · (‖f‖₂ + ‖h‖₂)      uniformly in the shift `u`

`selfConvolution` is bilinear, so `Cvs.Upstream.CauchySchwarzLine` bounds each of the two cross terms.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.SelfConvolutionL2Continuous

/-- **The self-convolution is `L²`-continuous, uniformly in the shift.** -/
theorem abs_selfConvolution_sub_le {f h : ℝ → ℝ} (u : ℝ)
    (hf : MemLp f 2 (volume : Measure ℝ)) (hh : MemLp h 2 (volume : Measure ℝ)) :
    |selfConvolution f u - selfConvolution h u|
      ≤ Real.sqrt (∫ x : ℝ, (f x - h x) ^ 2)
          * (Real.sqrt (∫ x : ℝ, f x ^ 2) + Real.sqrt (∫ x : ℝ, h x ^ 2)) := by
  have hfu : MemLp (fun s => f (s + u)) 2 (volume : Measure ℝ) :=
    hf.comp_measurePreserving (measurePreserving_add_right (volume : Measure ℝ) u)
  have hhu : MemLp (fun s => h (s + u)) 2 (volume : Measure ℝ) :=
    hh.comp_measurePreserving (measurePreserving_add_right (volume : Measure ℝ) u)
  have hd : MemLp (fun s => f s - h s) 2 (volume : Measure ℝ) := hf.sub hh
  have hdu : MemLp (fun s => f (s + u) - h (s + u)) 2 (volume : Measure ℝ) := hfu.sub hhu
  -- the two cross terms
  have hi1 : Integrable (fun s => (f s - h s) * f (s + u)) volume := hd.integrable_mul hfu
  have hi2 : Integrable (fun s => h s * (f (s + u) - h (s + u))) volume := hh.integrable_mul hdu
  have hif : Integrable (fun s => f s * f (s + u)) volume := hf.integrable_mul hfu
  have hih : Integrable (fun s => h s * h (s + u)) volume := hh.integrable_mul hhu
  have hsplit : selfConvolution f u - selfConvolution h u
      = (∫ s : ℝ, (f s - h s) * f (s + u)) + ∫ s : ℝ, h s * (f (s + u) - h (s + u)) := by
    rw [← integral_add hi1 hi2]
    have h1 : selfConvolution f u = ∫ s : ℝ, f s * f (s + u) := rfl
    have h2 : selfConvolution h u = ∫ s : ℝ, h s * h (s + u) := rfl
    rw [h1, h2, ← integral_sub hif hih]
    exact integral_congr_ae (Filter.Eventually.of_forall fun s => by ring)
  -- translation invariance of the two squared integrals
  have htr : ∀ k : ℝ → ℝ, (∫ s : ℝ, k (s + u) ^ 2) = ∫ s : ℝ, k s ^ 2 := fun k =>
    integral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun s : ℝ => k s ^ 2) u
  have hb1 : |∫ s : ℝ, (f s - h s) * f (s + u)|
      ≤ Real.sqrt (∫ x : ℝ, (f x - h x) ^ 2) * Real.sqrt (∫ x : ℝ, f x ^ 2) := by
    have := Cvs.Upstream.CauchySchwarzLine.abs_integral_mul_le hd hfu
    rwa [htr f] at this
  have hb2 : |∫ s : ℝ, h s * (f (s + u) - h (s + u))|
      ≤ Real.sqrt (∫ x : ℝ, h x ^ 2) * Real.sqrt (∫ x : ℝ, (f x - h x) ^ 2) := by
    have := Cvs.Upstream.CauchySchwarzLine.abs_integral_mul_le hh hdu
    rwa [htr (fun x => f x - h x)] at this
  rw [hsplit]
  calc |(∫ s : ℝ, (f s - h s) * f (s + u)) + ∫ s : ℝ, h s * (f (s + u) - h (s + u))|
      ≤ |∫ s : ℝ, (f s - h s) * f (s + u)| + |∫ s : ℝ, h s * (f (s + u) - h (s + u))| :=
        abs_add_le _ _
    _ ≤ Real.sqrt (∫ x : ℝ, (f x - h x) ^ 2) * Real.sqrt (∫ x : ℝ, f x ^ 2)
          + Real.sqrt (∫ x : ℝ, h x ^ 2) * Real.sqrt (∫ x : ℝ, (f x - h x) ^ 2) :=
        add_le_add hb1 hb2
    _ = Real.sqrt (∫ x : ℝ, (f x - h x) ^ 2)
          * (Real.sqrt (∫ x : ℝ, f x ^ 2) + Real.sqrt (∫ x : ℝ, h x ^ 2)) := by ring

end Cvs.WeilForm.SelfConvolutionL2Continuous
